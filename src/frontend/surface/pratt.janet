#!/usr/bin/env janet

(import ./ast :as a)
(import ./syntax :as x)
(import ./lexer :as lx)

(defn- trim [s] (string/trim s))

(defn- pstate/new [tokens mode prec sx]
  @{:tokens tokens :i 0 :mode mode :prec prec :sx sx})

(defn- pstate/peek [st]
  (if (< (st :i) (length (st :tokens)))
    ((st :tokens) (st :i))
    {:k :eof :v nil}))

(defn- pstate/next [st]
  (let [t (pstate/peek st)]
    (put st :i (+ 1 (st :i)))
    t))

(defn- pstate/expect [st kind]
  (let [t (pstate/next st)]
    (when (not= (t :k) kind)
      (errorf "expected token %v, got %v" kind t))
    t))

(defn- prec/spec [prec op]
  (get prec op))

(defn- op-lbp [level] (+ 10 level))

(var parse/expr nil)

(defn- parse-binder [st]
  (pstate/expect st :lparen)
  (let [nm ((pstate/expect st :ident) :v)]
    (pstate/expect st :colon)
    (let [dom (parse/expr st 0)]
      (pstate/expect st :rparen)
      (a/ty/binder nm dom (a/span/none)))))

(defn- resolve-type-ident [st name]
  (var out nil)
  (each resolver ((st :sx) :type/ident-resolvers)
    (when (nil? out)
      (set out (resolver name (a/span/none)))))
  (or out (a/ty/var name (a/span/none))))

(defn- quant-builder [st q]
  (or (get ((st :sx) :type/quant-builders) q)
      (errorf "unknown quantified alias %v" q)))

(defn- nud/type [st tok]
  (match (tok :k)
    :hole (a/ty/hole (tok :v) (a/span/none))
    :ident (resolve-type-ident st (tok :v))
    :lparen (let [e (parse/expr st 0)]
              (pstate/expect st :rparen)
              e)
    :quant
    (let [q (tok :v)
          binder (parse-binder st)]
      (pstate/expect st :dot)
      (let [body (parse/expr st 0)
            mk (quant-builder st q)]
        (mk binder body (a/span/none))))
    :op
    (if-let [spec (prec/spec (st :prec) (tok :v))]
      (if (= (spec :fixity) :prefix)
        (let [rhs (parse/expr st (op-lbp (spec :level)))]
          (a/ty/op (tok :v) @[rhs] (a/span/none)))
        (errorf "operator %v is not prefix in type position" (tok :v)))
      (errorf "unknown prefix type operator %v" (tok :v)))
    _ (errorf "unexpected type token %v" tok)))

(defn- nud/term [st tok]
  (match (tok :k)
    :hole (a/tm/hole (tok :v) (a/span/none))
    :nat (a/tm/nat (tok :v) (a/span/none))
    :ident (a/tm/var (tok :v) (a/span/none))
    :lparen (let [e (parse/expr st 0)]
              (pstate/expect st :rparen)
              e)
    :lambda
    (let [params @[]]
      (while (= ((pstate/peek st) :k) :ident)
        (array/push params ((pstate/next st) :v)))
      (when (zero? (length params))
        (error "lambda expects at least one parameter"))
      (pstate/expect st :fat-arrow)
      (a/tm/lam params (parse/expr st 0) (a/span/none)))
    :kw/let
    (let [name ((pstate/expect st :ident) :v)]
      (pstate/expect st :eq)
      (let [v (parse/expr st 0)]
        (pstate/expect st :kw/in)
        (a/tm/let name v (parse/expr st 0) (a/span/none))))
    :op
    (if-let [spec (prec/spec (st :prec) (tok :v))]
      (if (= (spec :fixity) :prefix)
        (let [rhs (parse/expr st (op-lbp (spec :level)))]
          (a/tm/op (tok :v) @[rhs] (a/span/none)))
        (errorf "operator %v is not prefix in term position" (tok :v)))
      (errorf "unknown prefix term operator %v" (tok :v)))
    _ (errorf "unexpected term token %v" tok)))

(defn- can-start-atom? [tok]
  (let [k (tok :k)]
    (or (= k :hole) (= k :ident) (= k :nat) (= k :lparen))))

(set parse/expr
     (fn [st min-bp]
       (let [tok (pstate/next st)
             left (if (= (st :mode) :type)
                    (nud/type st tok)
                    (nud/term st tok))]
         (var out left)
         (while true
           (let [next (pstate/peek st)
                 nk (next :k)]
             (cond
               (and (can-start-atom? next) (< min-bp 1000))
               (let [rhs (parse/expr st 1000)]
                 (set out (if (= (st :mode) :type)
                            (a/ty/app out rhs (a/span/none))
                            (a/tm/app out rhs (a/span/none)))))

               (and (= (st :mode) :type) (= nk :arrow) (<= min-bp 20))
               (do
                 (pstate/next st)
                 (let [rhs (parse/expr st 20)]
                   (set out (a/ty/arrow out rhs (a/span/none)))))

               (and (= nk :op)
                    (if-let [spec (prec/spec (st :prec) (next :v))]
                      (or (= (spec :fixity) :infixl)
                          (= (spec :fixity) :infixr)
                          (= (spec :fixity) :postfix))
                      false))
               (let [spec (prec/spec (st :prec) (next :v))
                     p (op-lbp (spec :level))]
                 (if (<= p min-bp)
                   (break)
                   (do
                     (pstate/next st)
                     (if (= (spec :fixity) :postfix)
                       (set out (if (= (st :mode) :type)
                                  (a/ty/op (next :v) @[out] (a/span/none))
                                  (a/tm/op (next :v) @[out] (a/span/none))))
                       (let [rbp (if (= (spec :fixity) :infixl) (+ p 1) p)
                             rhs (parse/expr st rbp)]
                         (set out (if (= (st :mode) :type)
                                    (a/ty/op (next :v) @[out rhs] (a/span/none))
                                    (a/tm/op (next :v) @[out rhs] (a/span/none)))))))))

               true
               (break))))
         out)))

(defn- parse-with-pratt [text mode prec sx]
  (let [st (pstate/new (lx/lex text sx) mode prec sx)
        out (parse/expr st 0)]
    (when (not= ((pstate/peek st) :k) :eof)
      (errorf "unexpected trailing token: %v" (pstate/peek st)))
    out))

(defn parse/type-text [text &opt prec sx]
  (parse-with-pratt (trim text) :type (or prec @{}) (or sx (x/syntax/default))))

(defn parse/expr-text [text &opt prec sx]
  (parse-with-pratt (trim text) :term (or prec @{}) (or sx (x/syntax/default))))

(def exports
  {:parse/type-text parse/type-text
   :parse/expr-text parse/expr-text})
