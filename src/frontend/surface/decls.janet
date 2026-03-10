#!/usr/bin/env janet

(import ./ast :as a)
(import ./layout :as ly)
(import ./lexer :as lx)
(import ./pratt :as pr)
(import ./patterns :as pat)
(import ./syntax :as sx)

(def peg/prec-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :ws+ (some (set " \t"))
      :fix (+ (capture "infixl") (capture "infixr") (capture "prefix") (capture "postfix"))
      :lvl (capture (some (range "09")))
      :op (capture (thru -1))
      :main (* :ws* :fix :ws+ :lvl :ws+ :op :ws*)}))

(defn- is-upper-byte? [c]
  (and (>= c (chr "A")) (<= c (chr "Z"))))

(defn- is-lower-byte? [c]
  (and (>= c (chr "a")) (<= c (chr "z"))))

(defn- is-ident-start-byte? [c]
  (or (is-upper-byte? c) (is-lower-byte? c) (= c (chr "_"))))

(defn- find-top-level-colon [text]
  "Find the index of the last top-level colon respecting balanced parens."
  (let [n (length text)]
    (var depth 0)
    (var last-colon nil)
    (for i 0 n
      (let [c (text i)]
        (cond
          (= c (chr "(")) (++ depth)
          (= c (chr ")")) (when (> depth 0) (-- depth))
          (and (= c (chr ":")) (= depth 0))
          (set last-colon i))))
    last-colon))

(defn- extract-name-and-params [lhs]
  "From 'Name' or 'Name(params)', extract [name params-text-or-nil]."
  (let [t (ly/trim lhs)
        paren-idx (string/find "(" t)]
    (if (and paren-idx
             (string/has-suffix? ")" t))
      [(string/slice t 0 paren-idx)
       (string/slice t (+ paren-idx 1) (- (length t) 1))]
      [t nil])))

(def peg/split-eq-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :lhs (capture (some (if-not "=" 1)))
      :rhs (capture (thru -1))
      :main (* :lhs :ws* "=" :ws* :rhs)}))

(defn- indent/tokenize [src]
  (let [lines (string/split "\n" src)
        out @[]]
    (for i 0 (length lines)
      (let [line (ly/trimr (lines i))
            lnum (+ i 1)
            left (ly/triml line)]
        (when (and (not= left "")
                   (not (string/has-prefix? "--" left)))
          (var col 0)
          (while (and (< col (length line)) (= (line col) (chr " "))) (++ col))
          (array/push out {:line lnum :col col :text (string/slice line col)}))))
    out))

(defn- parse/type-params [params-text prec syntax]
  (if (or (nil? params-text) (= (ly/trim params-text) ""))
    @[]
    (let [parts (ly/split-top-level params-text (chr ","))
          out @[]]
      (each p parts
        (let [x (ly/trim p)]
          (when (not= x "")
            (if-let [ix (ly/find-top-level-char x (chr ":"))]
              (array/push out
                          (a/decl/param (ly/trim (string/slice x 0 ix))
                                        (pr/parse/type-text (string/slice x (+ ix 1)) prec syntax)
                                        (a/span/none)))
              (array/push out (a/decl/param x nil (a/span/none)))))))
      out)))

(defn- parse/field-fragment [frag prec syntax]
  (let [t (ly/trim frag)
        sp (a/span/none)]
    (if-let [ix (ly/find-top-level-char t (chr ":"))]
      (a/decl/field-named (ly/trim (string/slice t 0 ix))
                          (pr/parse/type-text (string/slice t (+ ix 1)) prec syntax)
                          sp)
      (a/decl/field-anon (pr/parse/type-text t prec syntax) sp))))

(defn- read-parenthesized-end [text start]
  (let [n (length text)]
    (var i start)
    (var depth 0)
    (var found false)
    (var result nil)
    (while (and (< i n) (not found))
      (let [c (text i)]
        (cond
          (= c (chr "(")) (++ depth)
          (= c (chr ")")) (when (> depth 0) (-- depth)))
        (++ i)
        (when (= depth 0)
          (set found true)
          (set result i))))
    result))

(defn- parse/fields [text prec syntax]
  (let [out @[]
        n (length text)]
    (var i 0)
    (while (< i n)
      (while (and (< i n) (lx/is-space-byte? (text i))) (++ i))
      (when (< i n)
        (if (= (text i) (chr "("))
          (if-let [end (read-parenthesized-end text i)]
            (do
              (array/push out
                          (parse/field-fragment
                            (string/slice text (+ i 1) (- end 1))
                            prec
                            syntax))
              (set i end))
            (errorf "unclosed field paren: %v" text))
          (let [start i]
            (while (and (< i n) (not (lx/is-space-byte? (text i)))) (++ i))
            (array/push out (parse/field-fragment (string/slice text start i) prec syntax))))))
    out))

(defn- parse/ctor-rhs [rhs prec syntax]
  (let [parts (ly/split-ws-top-level rhs)]
    (when (zero? (length parts))
      (error "empty constructor rhs"))
    (let [name (ly/trim (parts 0))
          rest (if (> (length parts) 1)
                 (string/slice rhs (+ (length (parts 0)) 1))
                 "")]
      [name (parse/fields rest prec syntax)])))

(defn- parse/data-body-line [text prec syntax]
  (if-let [eq (peg/match peg/split-eq-line text)]
    (let [lhs (ly/trim (eq 0))
          rhs (ly/trim (eq 1))
          idx-parts (ly/split-top-level lhs (chr ","))
          indices @[]]
      (each p idx-parts
        (array/push indices (pat/parse/pat-text p)))
      (let [[name fields] (parse/ctor-rhs rhs prec syntax)]
        (a/decl/ctor-indexed indices name fields (a/span/none))))
    (let [[name fields] (parse/ctor-rhs (ly/trim text) prec syntax)]
      (a/decl/ctor-plain name fields (a/span/none)))))

(defn- parse/term-body-line [text prec syntax]
  (print "Parsing clause: " text)
  (if-let [eq (peg/match peg/split-eq-line text)]
    (let [lhs (ly/trim (eq 0))
          rhs (ly/trim (eq 1))
          pats @[]]
      (each part (ly/split-ws-top-level lhs)
        (array/push pats (pat/parse/pat-text part)))
      (a/decl/clause pats (pr/parse/expr-text rhs prec syntax) (a/span/none)))
    (errorf "invalid clause line: %v" text)))

(defn- classify-top [text]
  (if-let [m (peg/match peg/prec-line text)]
    [:top/prec (m 0) (scan-number (ly/trim (m 1))) (ly/trim (m 2))]
    (if-let [colon-idx (find-top-level-colon text)]
      (let [lhs (ly/trim (string/slice text 0 colon-idx))
            rhs (ly/trim (string/slice text (+ colon-idx 1)))
            [name params-text] (extract-name-and-params lhs)]
        (if (and (> (length name) 0) (is-upper-byte? (name 0)))
          [:top/type-head name params-text rhs]
          [:top/term-head name params-text rhs]))
      (errorf "unknown top-level line (no colon found): %v" text))))

(defn- build-prec-table [entries]
  (let [prec @{}]
    (each e entries
      (when (= (e :kind) :prec)
        (put prec (e :op) {:fixity (e :fixity) :level (e :level)})))
    prec))

(defn parse/source [src &opt syntax]
  (def syn (or syntax (sx/syntax/default)))
  (let [lines (indent/tokenize src)
        entries @[]]
    (var current nil)

    (defn flush-current []
      (when current
        (array/push entries current)
        (set current nil)))

    (each ln lines
      (if (= (ln :col) 0)
        (do
          (flush-current)
          (let [top (classify-top (ln :text))]
            (match (top 0)
              :top/prec
              (let [fx (match (top 1)
                         "infixl" :infixl
                         "infixr" :infixr
                         "prefix" :prefix
                         "postfix" :postfix
                         (errorf "unknown fixity %v" (top 1)))]
                (array/push entries {:kind :prec
                                     :fixity fx
                                     :level (top 2)
                                     :op (top 3)}))

              :top/type-head
              (set current {:kind :data-head
                            :name (top 1)
                            :params-text (top 2)
                            :sort-text (top 3)
                            :body @[]})

              :top/term-head
              (set current {:kind :term-head
                            :name (top 1)
                            :params-text (top 2)
                            :type-text (top 3)
                            :body @[]}))))
        (if current
          (array/push (current :body) (ln :text))
          (errorf "indented line without declaration: %v" (ln :text)))))

    (flush-current)

    (let [prec (build-prec-table entries)
          decls @[]]
      (each e entries
        (match (e :kind)
          :prec
          (array/push decls (a/decl/prec (e :fixity) (e :level) (e :op) (a/span/none)))

          :data-head
          (let [params (parse/type-params (e :params-text) prec syn)
                ctors @[]]
            (each bl (e :body)
              (array/push ctors (parse/data-body-line bl prec syn)))
            (array/push decls (a/decl/data (e :name) params ctors (a/span/none))))

          :term-head
          (let [# Separate body into type-continuation lines and clause lines
                # Lines without '=' before the first clause line are type continuation
                body-lines (e :body)
                type-parts @[]
                clause-lines @[]
                _ (do
                    (var found-clause false)
                    (each bl body-lines
                      (if found-clause
                        (array/push clause-lines bl)
                        (if (peg/match peg/split-eq-line bl)
                          (do (set found-clause true)
                              (array/push clause-lines bl))
                          (array/push type-parts bl)))))
                # Build full type text: head type-text + continuation lines + params
                head-type (or (e :type-text) "")
                full-type-text
                (if (zero? (length type-parts))
                  head-type
                  (string head-type
                          (if (> (length head-type) 0) " " "")
                          (string/join type-parts " ")))
                # Weave params into type as Pi binders
                params-text (e :params-text)
                final-type-text
                (if params-text
                  (let [param-parts (ly/split-top-level params-text (chr ","))
                        pi-prefix @[]]
                    (each pp param-parts
                      (let [tp (ly/trim pp)]
                        (when (not= tp "")
                          (if-let [colon-ix (ly/find-top-level-char tp (chr ":"))]
                            # Split on colon: could be "n,m: Nat" or "A: Type"
                            (let [names-part (ly/trim (string/slice tp 0 colon-ix))
                                  ty-part (ly/trim (string/slice tp (+ colon-ix 1)))
                                  names (ly/split-top-level names-part (chr ","))]
                              (each nm names
                                (let [n (ly/trim nm)]
                                  (when (not= n "")
                                    (array/push pi-prefix
                                                (string "\xCE\xA0(" n ": " ty-part "). "))))))
                            (array/push pi-prefix (string "\xCE\xA0(" tp ": Type). "))))))
                    (string (string/join pi-prefix "") full-type-text))
                  full-type-text)
                ty (pr/parse/type-text final-type-text prec syn)
                clauses @[]]
            (each cl clause-lines
              (array/push clauses (parse/term-body-line cl prec syn)))
            (array/push decls (a/decl/func (e :name) ty clauses (a/span/none))))

          _ (errorf "unknown entry kind: %v" (e :kind))))
      (a/program decls (a/span/none)))))

(def exports
  {:parse/source parse/source})
