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
  (let [trimmed (ly/trim lhs)]
    (if-let [lp (string/find "(" trimmed)]
      (let [rp (- (length trimmed) 1)]
        (if (= (trimmed rp) (chr ")"))
          [(ly/trim (string/slice trimmed 0 lp))
           (string/slice trimmed (+ lp 1) rp)]
          [trimmed nil]))
      [trimmed nil])))

(defn read-parenthesized-end [text start]
  (let [n (length text)]
    (var depth 0)
    (var i start)
    (var found false)
    (while (and (< i n) (not found))
      (let [c (text i)]
        (cond
          (= c (chr "(")) (do
                           (++ depth)
                           (++ i))
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
              (array/push out (parse/field-fragment (string/slice trimmed 1 (- (length trimmed) 1)) syntax mk-named mk-anon))
              (array/push out (parse/field-fragment trimmed syntax mk-named mk-anon))))))
      out)))

(defn- strip-optional-parens [text]
  (let [trimmed (ly/trim text)
        n (length trimmed)]
    (if (and (> n 1)
             (= (trimmed 0) (chr "("))
             (= (trimmed (- n 1)) (chr ")"))
             (= (read-parenthesized-end trimmed 0) n))
      (string/slice trimmed 1 (- n 1))
      trimmed)))

(defn- parse/type-params [text syntax]
  (if (or (nil? text) (= (ly/trim text) ""))
    @[]
    (let [raw-parts (ly/split-top-level text (chr ","))
          parts @[]
          out @[]]
      (var pending nil)
      (each raw raw-parts
        (let [part (ly/trim raw)]
          (when (not= part "")
            (let [chunk (if pending
                          (string pending "," part)
                          part)]
              (if (ly/find-top-level-char chunk (chr ":"))
                (do
                  (array/push parts chunk)
                  (set pending nil))
                (set pending chunk))))))
      (when pending
        (array/push parts pending))
      (each p parts
        (let [x (ly/trim p)]
          (when (not= x "")
            (if-let [ix (ly/find-top-level-char x (chr ":"))]
              (let [names-part (ly/trim (string/slice x 0 ix))
                    ty (pr/parse/type-text (ly/trim (string/slice x (+ ix 1))) syntax)
                    names (ly/split-top-level names-part (chr ","))]
                (each name names
                  (let [trimmed-name (ly/trim name)]
                    (when (not= trimmed-name "")
                      (array/push out
                                  (a/decl/param trimmed-name
                                                ty
                                                (a/span/none)))))))
              (array/push out (a/decl/param x nil (a/span/none)))))))
      out)))

(defn- split-field-segments [text]
  (let [trimmed (ly/trim text)
        out @[]
        n (length trimmed)]
    (var i 0)
    (while (< i n)
      (while (and (< i n) (ly/is-space-byte? (trimmed i)))
        (++ i))
      (when (< i n)
        (if (= (trimmed i) (chr "("))
          (if-let [end (read-parenthesized-end trimmed i)]
            (do
              (array/push out (string/slice trimmed i end))
              (set i end))
            (errorf "unclosed constructor field list: %s" trimmed))
          (let [start i]
            (while (and (< i n) (not (ly/is-space-byte? (trimmed i))))
              (++ i))
            (array/push out (string/slice trimmed start i))))))
    out))

(defn- parse/field-segment [segment syntax mk-named mk-anon]
  (let [trimmed (ly/trim segment)
        n (length trimmed)]
    (if (or (= trimmed "") (= trimmed "()"))
      @[]
      (if (and (> n 1)
               (= (trimmed 0) (chr "("))
               (= (trimmed (- n 1)) (chr ")")))
        (parse/fields (string/slice trimmed 1 (- n 1)) syntax mk-named mk-anon)
        @[(parse/field-fragment trimmed syntax mk-named mk-anon)]))))

(defn- parse/ctor-rhs [rhs syntax]
  (let [trimmed (ly/trim rhs)
        n (length trimmed)]
    (cond
      (or (= trimmed "()") (= trimmed ""))
      [nil @[]]

      true
      (let [name-end (or (ly/find-top-level-char trimmed (chr " "))
                         (ly/find-top-level-char trimmed (chr "\t"))
                         (ly/find-top-level-char trimmed (chr "("))
                         n)
            name (ly/trim (string/slice trimmed 0 name-end))
            rest (ly/trim (string/slice trimmed name-end n))
            segments (ly/split-ws-top-level rest)
            fields @[]]
        (when (= name "")
          (error "empty constructor rhs"))
        (each segment segments
          (each field (parse/field-segment segment syntax a/decl/field-named a/decl/field-anon)
            (array/push fields field)))
        [name fields]))))

(defn- wrap-type-params [ty params]
  (reduce (fn [body param]
            (let [name (param 1)
                  dom (or (param 2) (a/ty/universe 0 (a/span/none)))]
              (a/ty/pi (a/ty/binder name dom (a/span/none)) body (a/span/none))))
          ty
          (reverse params)))

(defn- resolve-import-path [path]
  (if (string/has-prefix? "@examples/" path)
    (string "examples/" (string/slice path (length "@examples/")))
    path))

(defn- diag/error [ln message]
  (error {:kind :surface/diag
          :message message
          :line (ln :line)
          :column (+ (ln :col) 1)}))

(defn- parse/data-body-line [ln syntax]
  (let [text (ln :text)]
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
        [])))))

(defn- type/arity [ty]
  (match ty
    [:ty/pi _ body _] (+ 1 (type/arity body))
    [:ty/arrow _ cod _] (+ 1 (type/arity cod))
    _ 0))

(defn- ctor/arity [ctor]
  (match ctor
    [:ctor/plain _ fields _] (length fields)
    [:ctor/indexed _ _ fields _] (length fields)
    _ 0))

(defn- ctor-env/add! [env ctor]
  (match ctor
    [:ctor/plain name _ _] (put env name (ctor/arity ctor))
    [:ctor/indexed _ name _ _] (put env name (ctor/arity ctor))
    _ nil))

(defn- parse/pat-from-parts [parts start ctor-env]
  (let [part (parts start)
        trimmed (ly/trim part)
        n (length trimmed)
        paren-token? (and (> n 1)
                          (= (trimmed 0) (chr "("))
                          (= (trimmed (- n 1)) (chr ")")))]
    (cond
      paren-token?
      [(pat/parse/pat-text trimmed) (+ start 1)]

      (nil? (get ctor-env trimmed))
      [(pat/parse/pat-text trimmed) (+ start 1)]

      true
      (let [arity (get ctor-env trimmed)
            args @[]]
        (var i 0)
        (var cur (+ start 1))
        (while (< i arity)
          (when (>= cur (length parts))
            (errorf "constructor pattern %s expects %d argument(s)" trimmed arity))
          (let [[arg next-cur] (parse/pat-from-parts parts cur ctor-env)]
            (array/push args arg)
            (set cur next-cur))
          (++ i))
        [(a/pat/con trimmed args (a/span/none)) cur]))))

(defn- parse/clause-patterns [lhs arity ctor-env]
  (let [parts (ly/split-ws-top-level lhs)
        pats @[]]
    (var cur 0)
    (for _ 0 arity
      (when (>= cur (length parts))
        (errorf "expected %d pattern(s), got %d in clause: %s" arity (length pats) lhs))
      (let [[pat next-cur] (parse/pat-from-parts parts cur ctor-env)]
        (array/push pats pat)
        (set cur next-cur)))
    (when (< cur (length parts))
      (errorf "too many pattern fragments in clause: %s" lhs))
    pats))

(defn- parse/term-body-line [ln syntax arity ctor-env]
  (let [text (ln :text)]
    (if-let [eq (peg/match peg/split-eq-line text)]
    (let [lhs (ly/trim (eq 0))
          rhs (ly/trim (eq 1))
          pats (parse/clause-patterns lhs arity ctor-env)]
      (a/decl/clause pats (pr/parse/expr-text rhs syntax) (a/span/none)))
    (diag/error ln (string "invalid clause line: " text)))))

(defn- classify-top [ln]
  (let [text (ln :text)
        trimmed (ly/trim text)]
    (cond
      (string/has-prefix? "#" trimmed)
      [:top/comment]

      (peg/match peg/prec-line text)
      (let [m (peg/match peg/prec-line text)]
        [:top/prec (m 0) (scan-number (ly/trim (m 1))) (ly/trim (m 2))])

      (peg/match peg/alias-line text)
      (let [m (peg/match peg/alias-line text)]
        [:top/alias (m 0) (m 1)])

      (peg/match peg/import-line text)
      (let [m (peg/match peg/import-line text)]
        [:top/import (m 0)])

      (peg/match peg/compute-line text)
      (let [m (peg/match peg/compute-line text)]
        [:top/compute (m 0)])

      (peg/match peg/check-line text)
      (let [m (peg/match peg/check-line text)]
        [:top/check (m 0) (m 1)])

      true
      (if-let [colon-idx (find-top-level-colon text)]
        (let [lhs (ly/trim (string/slice text 0 colon-idx))
              rhs (ly/trim (string/slice text (+ colon-idx 1)))
              [name params-text] (extract-name-and-params lhs)]
          (if (and (> (length name) 0) (is-upper-byte? (name 0)))
            [:top/type-head name params-text rhs]
            [:top/term-head name params-text rhs]))
        (diag/error ln (string "unknown top-level line (no colon found): " text))))))

(var parse/source nil)

(set parse/source
     (fn [src &opt syntax]
       (let [syn (or syntax (sx/syntax/default))
              lines (ly/indent/tokenize src)
              decls @[]
              ctor-env @{}]
          (var current nil)

         (defn flush-current []
           (when current
             (match (current :kind)
               :data-head
                 (let [params (parse/type-params (current :params-text) syn)
                       sort-text (current :sort-text)
                       body-lines (current :body)
                       ctors @[]
                       source-for-ctors (if (and (nil? (next body-lines)) (not (= sort-text "")))
                                          (let [dummy-line {:text (string (current :name) ": " sort-text) :line 0 :col 0}]
                                            @[dummy-line])
                                          body-lines)]
                    (each bl source-for-ctors
                      (let [new-ctors (parse/data-body-line bl syn)]
                        (each c new-ctors (array/push ctors c))))
                    (let [sort (if (= (ly/trim sort-text) "")
                                 (a/ty/universe 0 (a/span/none))
                                 (pr/parse/type-text sort-text syn))
                          decl (a/decl/data (current :name) params sort ctors (a/span/none))]
                      (array/push decls decl)
                      (each ctor ctors
                        (ctor-env/add! ctor-env ctor))))

                :term-head
                (let [body-lines (current :body)
                      params (parse/type-params (current :params-text) syn)
                      type-parts @[]
                      clause-lines @[]
                      _ (do
                           (var found-clause false)
                           (each bl body-lines
                            (if found-clause
                              (array/push clause-lines bl)
                              (if (peg/match peg/split-eq-line (bl :text))
                                 (do (set found-clause true)
                                     (array/push clause-lines bl))
                                 (array/push type-parts bl)))))
                       head-type (or (current :type-text) "")
                       full-type-text (if (or (zero? (length type-parts)) (= (string/trim (string/join (map |($ :text) type-parts) "")) ""))
                                       (if (and head-type (not= (string/trim head-type) "")) head-type "?")
                                       (string head-type " " (string/join (map |($ :text) type-parts) " ")))
                       ty (wrap-type-params (pr/parse/type-text full-type-text syn) params)
                       arity (type/arity ty)
                       clauses @[]]
                   (each cl clause-lines
                     (array/push clauses (parse/term-body-line cl syn arity ctor-env)))
                  (array/push decls (a/decl/func (current :name) ty clauses (a/span/none)))))
             (set current nil)))

          (each ln lines
            (if (= (ln :col) 0)
              (do
                (let [top (classify-top ln)]
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
                                     (diag/error ln (string "unknown fixity " (top 1))))]
                            (sx/syntax/add-operator! syn (top 3) fx (top 2)))

                         :top/alias
                         (sx/syntax/add-alias! syn (top 1) (top 2))

                          :top/import
                          (let [path (top 1)
                                q "\""
                                path (if (and (string/has-prefix? q path) (string/has-suffix? q path))
                                       (string/slice path 1 (- (length path) 1))
                                       path)
                                path (resolve-import-path path)
                                ext (if (string/has-suffix? ".requiem" path) "" ".requiem")
                                full-path (string path ext)
                                content (if (os/stat full-path) (slurp full-path) nil)]
                            (if content
                              (let [prog (parse/source (string content) syn)
                                    ds (prog 1)]
                                (each d ds (array/push decls d)))
                              (diag/error ln (string "could not import file: " full-path))))

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
                (array/push (current :body) ln)
                (when (not (string/has-prefix? "#" (ly/trim (ln :text))))
                  (diag/error ln (string "indented line without declaration: " (ln :text)))))))

         (flush-current)
         (a/program decls (a/span/none)))))

(def exports
  {:parse/source parse/source})
