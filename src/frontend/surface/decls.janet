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

(def peg/alias-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :ws+ (some (set " \t"))
      :ident (capture (some (if-not (set " \t=") 1)))
      :main (* :ws* "alias" :ws+ :ident :ws* "=" :ws* :ident :ws*)}))

(def peg/import-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :ws+ (some (set " \t"))
      :path (capture (+ (* "\"" (some (if-not "\"" 1)) "\"")
                        (some (if-not (set " \t") 1))))
      :main (* :ws* "import" :ws+ :path :ws*)}))

(def peg/compute-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :ws+ (some (set " \t"))
      :tm (capture (thru -1))
      :main (* :ws* "compute" :ws+ :tm :ws*)}))

(def peg/check-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :ws+ (some (set " \t"))
      :tm (capture (some (if-not (set ":") 1)))
      :ty (capture (thru -1))
      :main (* :ws* "check" :ws+ :tm :ws* ":" :ws* :ty :ws*)}))

(def peg/split-eq-line
  (peg/compile
    ~{:ws* (any (set " \t"))
      :ws+ (some (set " \t"))
      :lhs (capture (any (if-not "=" 1)))
      :rhs (capture (thru -1))
      :main (* :ws* :lhs "=" :rhs)}))

(defn- is-upper-byte? [c]
  (and (>= c (chr "A")) (<= c (chr "Z"))))

(defn- is-lower-byte? [c]
  (and (>= c (chr "a")) (<= c (chr "z"))))

(defn- is-ident-start-byte? [c]
  (or (is-upper-byte? c) (is-lower-byte? c) (= c (chr "_"))))

(defn- find-top-level-colon [text]
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
  (if-let [lp (string/find "(" lhs)]
    (let [name (ly/trim (string/slice lhs 0 lp))
          params (string/slice lhs (+ lp 1) (- (length lhs) 1))]
      [name params])
    [(ly/trim lhs) nil]))

(defn read-parenthesized-end [text start]
  (let [n (length text)]
    (var depth 0)
    (var i start)
    (var found false)
    (while (and (< i n) (not found))
      (let [c (text i)]
        (cond
          (= c (chr "(")) (++ depth)
          (= c (chr ")")) (do
                          (-- depth)
                          (when (= depth 0)
                            (set found true)
                            (++ i)))
          true (++ i))))
    (if found i nil)))

(defn- parse/field-fragment [text syntax mk-named mk-anon]
  (let [colon-ix (find-top-level-colon text)]
    (if colon-ix
      (let [name (ly/trim (string/slice text 0 colon-ix))
            ty-text (ly/trim (string/slice text (+ colon-ix 1)))]
        (mk-named name (pr/parse/type-text ty-text syntax) (a/span/none)))
      (mk-anon (pr/parse/type-text text syntax) (a/span/none)))))

(defn parse/fields [text syntax mk-named mk-anon]
  (if (or (nil? text) (= text ""))
    @[]
    (let [parts (ly/split-top-level text (chr ","))
          out @[]]
      (each p parts
        (let [trimmed (ly/trim p)]
          (when (not= trimmed "")
            (if (and (string/has-prefix? "(" trimmed) (string/has-suffix? ")" trimmed))
              (array/push out (parse/field-fragment (string/slice trimmed 1 -2) syntax mk-named mk-anon))
              (array/push out (parse/field-fragment trimmed syntax mk-named mk-anon))))))
      out)))

(defn- parse/type-params [text syntax]
  (if (or (nil? text) (= (ly/trim text) ""))
    @[]
    (let [parts (ly/split-top-level text (chr ","))
          out @[]]
      (each p parts
        (let [x (ly/trim p)]
          (when (not= x "")
            (if-let [ix (ly/find-top-level-char x (chr ":"))]
              (array/push out
                          (a/decl/param (ly/trim (string/slice x 0 ix))
                                        (pr/parse/type-text (ly/trim (string/slice x (+ ix 1))) syntax)
                                        (a/span/none)))
              (array/push out (a/decl/param x nil (a/span/none)))))))
      out)))

(defn- parse/ctor-rhs [rhs syntax]
  (let [trimmed (ly/trim rhs)]
    (if (= trimmed "()")
      [nil @[]]
      (if-let [lp (string/find "(" trimmed)]
        (let [name (ly/trim (string/slice trimmed 0 lp))
              rest (string/slice trimmed (+ lp 1) (- (length trimmed) 1))]
          [name (parse/fields rest syntax a/decl/field-named a/decl/field-anon)])
        (let [parts (ly/split-ws-top-level trimmed)]
          (when (zero? (length parts))
            (error "empty constructor rhs"))
          (let [name (ly/trim (parts 0))
                rest (if (> (length parts) 1)
                       (string/slice trimmed (+ (length (parts 0)) 1))
                       "")]
            [name (parse/fields rest syntax a/decl/field-named a/decl/field-anon)]))))))

(defn- parse/data-body-line [text syntax]
  (if-let [eq (peg/match peg/split-eq-line text)]
    (let [lhs (ly/trim (eq 0))
          rhs (ly/trim (eq 1))
          idx-parts (ly/split-top-level lhs (chr ","))
          indices @[]]
      (each p idx-parts
        (array/push indices (pat/parse/pat-text p)))
      (let [[name fields] (parse/ctor-rhs rhs syntax)]
        (if name
          [(a/decl/ctor-indexed indices name fields (a/span/none))]
          [])))
    (let [[name fields] (parse/ctor-rhs (ly/trim text) syntax)]
      (if name
        [(a/decl/ctor-plain name fields (a/span/none))]
        []))))

(defn- parse/term-body-line [text syntax]
  (if-let [eq (peg/match peg/split-eq-line text)]
    (let [lhs (ly/trim (eq 0))
          rhs (ly/trim (eq 1))
          pats @[]]
      (each part (ly/split-ws-top-level lhs)
        (array/push pats (pat/parse/pat-text part)))
      (a/decl/clause pats (pr/parse/expr-text rhs syntax) (a/span/none)))
    (errorf "invalid clause line: %v" text)))

(defn- classify-top [text]
  (if (string/has-prefix? "#" (ly/trim text))
    [:top/comment]
    (if-let [m (peg/match peg/prec-line text)]
      [:top/prec (m 0) (scan-number (ly/trim (m 1))) (ly/trim (m 2))]
      (if-let [m (peg/match peg/alias-line text)]
        [:top/alias (m 0) (m 1)]
        (if-let [m (peg/match peg/import-line text)]
          [:top/import (m 0)]
          (if-let [m (peg/match peg/compute-line text)]
            [:top/compute (m 0)]
            (if-let [m (peg/match peg/check-line text)]
              [:top/check (m 0) (m 1)]
              (if-let [colon-idx (find-top-level-colon text)]
                (let [lhs (ly/trim (string/slice text 0 colon-idx))
                      rhs (ly/trim (string/slice text (+ colon-idx 1)))
                      [name params-text] (extract-name-and-params lhs)]
                  (if (and (> (length name) 0) (is-upper-byte? (name 0)))
                    [:top/type-head name params-text rhs]
                    [:top/term-head name params-text rhs]))
                (errorf "unknown top-level line (no colon found): %v" text)))))))))

(var parse/source nil)

(set parse/source
     (fn [src &opt syntax]
       (let [syn (or syntax (sx/syntax/default))
             lines (ly/indent/tokenize src)
             decls @[]]
         (var current nil)

         (defn flush-current []
           (when current
             (match (current :kind)
               :data-head
               (let [params (parse/type-params (current :params-text) syn)
                      ctors @[]]
                 (each bl (current :body)
                   (let [new-ctors (parse/data-body-line bl syn)]
                     (each c new-ctors (array/push ctors c))))
                 (array/push decls (a/decl/data (current :name) params ctors (a/span/none))))

               :term-head
               (let [body-lines (current :body)
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
                     head-type (or (current :type-text) "")
                     full-type-text (if (or (zero? (length type-parts)) (= (string/trim (string/join type-parts "")) ""))
                                     (if (and head-type (not= (string/trim head-type) "")) head-type "?")
                                     (string head-type " " (string/join type-parts " ")))
                     params-text (current :params-text)
                     # Weave params into type as Pi binders
                     final-type-text
                     (if (and params-text (not= params-text ""))
                       (let [param-parts (ly/split-top-level params-text (chr ","))
                             pi-prefix @[]]
                         (each pp param-parts
                           (let [tp (ly/trim pp)]
                             (when (not= tp "")
                               (if-let [colon-ix (ly/find-top-level-char tp (chr ":"))]
                                 (let [names-part (ly/trim (string/slice tp 0 colon-ix))
                                       ty-part (ly/trim (string/slice tp (+ colon-ix 1)))
                                       names (ly/split-top-level names-part (chr ","))]
                                   (each nm names
                                     (let [n (ly/trim nm)]
                                       (when (not= n "")
                                         (array/push pi-prefix (string "Pi(" n ": " ty-part "). "))))))
                                 (array/push pi-prefix (string "Pi(" tp ": Type). "))))))
                         (string (string/join pi-prefix "") full-type-text))
                       full-type-text)
                     ty (pr/parse/type-text final-type-text syn)
                     clauses @[]]
                 (each cl clause-lines
                   (array/push clauses (parse/term-body-line cl syn)))
                 (array/push decls (a/decl/func (current :name) ty clauses (a/span/none)))))
             (set current nil)))

         (each ln lines
           (if (= (ln :col) 0)
             (do
               (let [top (classify-top (ln :text))]
                 (match (top 0)
                   :top/comment nil
                   _ (do
                       (flush-current)
                       (match (top 0)
                         :top/prec
                         (let [fx (match (top 1)
                                    "infixl" :infixl
                                    "infixr" :infixr
                                    "prefix" :prefix
                                    "postfix" :postfix
                                    (errorf "unknown fixity %v" (top 1)))]
                           (sx/syntax/add-operator! syn (top 3) fx (top 2)))

                         :top/alias
                         (sx/syntax/add-alias! syn (top 1) (top 2))

                         :top/import
                         (let [path (top 1)
                               q "\""
                               path (if (and (string/has-prefix? q path) (string/has-suffix? q path))
                                      (string/slice path 1 -2)
                                      path)
                               ext (if (string/has-suffix? ".requiem" path) "" ".requiem")
                               full-path (string path ext)
                               content (if (os/stat full-path) (slurp full-path) nil)]
                           (if content
                             (let [prog (parse/source (string content) syn)
                                   ds (prog 1)]
                               (each d ds (array/push decls d)))
                             (errorf "could not import file: %v" full-path)))

                         :top/compute
                         (array/push decls (a/decl/compute (pr/parse/expr-text (top 1) syn) (a/span/none)))

                         :top/check
                         (array/push decls (a/decl/check (pr/parse/expr-text (top 1) syn)
                                                         (pr/parse/type-text (top 2) syn)
                                                         (a/span/none)))

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
                                       :body @[]}))))))
             (if current
               (array/push (current :body) (ln :text))
               (when (not (string/has-prefix? "#" (ly/trim (ln :text))))
                 (errorf "indented line without declaration: %v" (ln :text))))))

         (flush-current)
         (a/program decls (a/span/none)))))

(def exports
  {:parse/source parse/source})
