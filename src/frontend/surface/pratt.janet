#!/usr/bin/env janet

(import ./ast :as a)
(import ./syntax :as x)
(import ./lexer :as lx)

(defn- trim [s] (string/trim s))

(defn- pstate/new [tokens mode sx]
  @{:tokens tokens :i 0 :mode mode :sx sx})

(defn- tok/at [tok]
  (if (and (tok :line) (tok :col))
    (string (tok :line) ":" (tok :col))
    "?:?"))

(defn- tok/render [tok]
  (if (= (tok :k) :eof)
    "end of input"
    (string (tok :k) (if (nil? (tok :v)) "" (string " '" (tok :v) "'")))))

(defn- pstate/peek [st]
  (if (< (st :i) (length (st :tokens)))
    ((st :tokens) (st :i))
    {:k :eof :v nil :line nil :col nil}))

(defn- pstate/next [st]
  (let [t (pstate/peek st)]
    (put st :i (+ 1 (st :i)))
    t))

(defn- pstate/expect [st kind]
  (let [t (pstate/next st)]
    (when (not= (t :k) kind)
      (errorf "parse error at %s: expected %v, got %s" (tok/at t) kind (tok/render t)))
    t))

(defn- prec/spec [st op]
  (get ((st :sx) :operators) op))

(defn- op-lbp [level] (+ 10 level))

(var parse/expr nil)

(defn- parse-binder [st]
  (pstate/expect st :lparen)
  (let [nm ((pstate/expect st :ident) :v)]
    (pstate/expect st :colon)
    (let [old-mode (st :mode)]
      (put st :mode :type)
      (let [dom (parse/expr st 0)]
        (put st :mode old-mode)
        (pstate/expect st :rparen)
        (a/ty/binder nm dom (a/span/none))))))

(defn- resolve-type-ident [st name]
  (var out nil)
  (each resolver ((st :sx) :type/ident-resolvers)
    (when (nil? out)
      (set out (resolver name (a/span/none)))))
  (or out (a/ty/var name (a/span/none))))

(defn- quant-builder [st q]
  (or (get ((st :sx) :type/quant-builders) q)
      (errorf "parse error: unknown quantified alias %v" q)))

(defn- nud/type [st tok]
  (match (tok :k)
    :hole (a/ty/hole (tok :v) (a/span/none))
    :nat (a/ty/universe (tok :v) (a/span/none))
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
    (if-let [spec (prec/spec st (tok :v))]
      (if (= (spec :fixity) :prefix)
        (let [rhs (parse/expr st (op-lbp (spec :level)))]
          (a/ty/op (tok :v) @[rhs] (a/span/none)))
        (errorf "parse error at %s: operator %v is not prefix in type position" (tok/at tok) (tok :v)))
      (errorf "parse error at %s: unknown prefix type operator %v" (tok/at tok) (tok :v)))
    _ (errorf "parse error at %s: unexpected type token %s" (tok/at tok) (tok/render tok))))

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
      (while true
        (let [pk (pstate/peek st)]
          (cond
            (= (pk :k) :ident)
            (array/push params ((pstate/next st) :v))

            (= (pk :k) :lparen)
            (array/push params (parse-binder st))

            true (break))))
      (when (zero? (length params))
        (errorf "parse error at %s: lambda expects at least one parameter" (tok/at tok)))
      (let [sep (pstate/next st)]
        (when (not= (sep :k) :dot)
          (errorf "parse error at %s: lambda expects '.', got %s" (tok/at sep) (tok/render sep))))
      (a/tm/lam params (parse/expr st 0) (a/span/none)))
    :kw/let
    (let [name ((pstate/expect st :ident) :v)]
      (pstate/expect st :eq)
      (let [v (parse/expr st 0)]
        (pstate/expect st :kw/in)
        (a/tm/let name v (parse/expr st 0) (a/span/none))))
    :op
    (if-let [spec (prec/spec st (tok :v))]
      (if (= (spec :fixity) :prefix)
        (let [rhs (parse/expr st (op-lbp (spec :level)))]
          (a/tm/op (tok :v) @[rhs] (a/span/none)))
        (errorf "parse error at %s: operator %v is not prefix in term position" (tok/at tok) (tok :v)))
      (errorf "parse error at %s: unknown prefix term operator %v" (tok/at tok) (tok :v)))
    _ (errorf "parse error at %s: unexpected term token %s" (tok/at tok) (tok/render tok))))

(defn- can-start-atom? [tok]
  (let [k (tok :k)]
    (or (= k :hole) (= k :ident) (= k :nat) (= k :lparen)
        (= k :quant) (= k :lambda) (= k :kw/let))))

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

               (let [spec (prec/spec st (next :v))
                     p (if spec (op-lbp (spec :level)) -1)]
                 (and (= nk :op)
                      (if spec
                        (and (> p min-bp)
                             (or (= (spec :fixity) :infixl)
                                 (= (spec :fixity) :infixr)
                                 (= (spec :fixity) :postfix)))
                        false)))
               (let [op-tok (pstate/next st)
                     spec (prec/spec st (op-tok :v))
                     p (op-lbp (spec :level))]
                 (if (= (spec :fixity) :postfix)
                   (set out (if (= (st :mode) :type)
                              (a/ty/op (op-tok :v) @[out] (a/span/none))
                              (a/tm/op (op-tok :v) @[out] (a/span/none))))
                   (let [rbp (if (= (spec :fixity) :infixr) (dec p) p)
                         rhs (parse/expr st rbp)]
                     (set out (if (= (st :mode) :type)
                                (if (or (= (op-tok :v) "->") (= (op-tok :v) "→"))
                                  (a/ty/arrow out rhs (a/span/none))
                                  (a/ty/op (op-tok :v) @[out rhs] (a/span/none)))
                                (a/tm/op (op-tok :v) @[out rhs] (a/span/none)))))))

               true
               (break))))
         out)))

(defn- parse-with-pratt [text mode sx]
  (let [st (pstate/new (lx/lex text sx) mode sx)
        out (parse/expr st 0)]
    (let [trail (pstate/peek st)]
      (when (not= (trail :k) :eof)
        (errorf "parse error at %s: unexpected trailing token %s" (tok/at trail) (tok/render trail))))
    out))

(defn parse/type-text [text &opt sx]
  (parse-with-pratt (trim text) :type (or sx (x/syntax/default))))

(defn parse/expr-text [text &opt sx]
  (parse-with-pratt (trim text) :term (or sx (x/syntax/default))))

(def exports
  {:parse/type-text parse/type-text
   :parse/expr-text parse/expr-text})
