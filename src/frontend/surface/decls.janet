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

(def peg/type-head-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :name (capture (* (range "AZ") (any (range "AZ" "az" "09"))))
      :params (capture (to ")"))
      :main (* :ws* :name :ws* (? (* "(" :params ")")) :ws* ":" :ws*)}))

(def peg/term-head-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :lhs (capture (some (if-not ":" 1)))
      :rhs (capture (thru -1))
      :main (* :ws* :lhs :ws* ":" :ws* :rhs)}))

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
  (let [p (parser/new)
        n (length text)]
    (var i start)
    (while (< i n)
      (parser/byte p (text i))
      (when (= (parser/status p) :error)
        (errorf "parser error while scanning '%v': %v" text (parser/error p)))
      (++ i)
      (when (= (length (or (parser/state p :delimiters) "")) 0)
        (return i)))
    nil))

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
    (if-let [m (peg/match peg/type-head-line text)]
      [:top/type-head (m 0) (if (> (length m) 1) (m 1) nil)]
      (if-let [m (peg/match peg/term-head-line text)]
        [:top/term-head (ly/trim (m 0)) (ly/trim (m 1))]
        (errorf "unknown top-level line: %v" text)))))

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
                            :body @[]})

              :top/term-head
              (set current {:kind :term-head
                            :name (top 1)
                            :type-text (top 2)
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
          (let [ty (pr/parse/type-text (e :type-text) prec syn)
                clauses @[]]
            (each bl (e :body)
              (array/push clauses (parse/term-body-line bl prec syn)))
            (array/push decls (a/decl/func (e :name) ty clauses (a/span/none))))

          _ (errorf "unknown entry kind: %v" (e :kind))))
      (a/program decls (a/span/none)))))

(def exports
  {:parse/source parse/source})
