#!/usr/bin/env janet

(import ./parser :as p)
(import ./lower :as l)

(defn env/lookup [env name]
  (defn scan [i]
    (if (< i 0) nil
      (let [entry (env i)]
        (if (= (entry 0) name)
          (entry 1)
          (scan (- i 1))))))
  (scan (- (length env) 1)))

(defn env/extend [env name value]
  [;env [name value]])

(defn sig/lookup [sig-env name]
  (env/lookup sig-env name))

(defn sig/from-decls [decls]
  (reduce (fn [acc decl]
            (match decl
              [:decl/func name params _ _]
              [;acc [name params]]
              _ acc))
          @[]
          decls))

(defn token/digits? [s]
  (and (> (length s) 0)
       (all |(let [ch (string/from-bytes $)]
               (and (>= ch "0") (<= ch "9")))
            s)))

(defn token/type-level [tok]
  (cond
    (= tok "Type") 0
    (= tok "U") 0
    (and (> (length tok) 4)
         (= (string/slice tok 0 4) "Type")
         (token/digits? (string/slice tok 4)))
    (scan-number (string/slice tok 4))
    true nil))

(defn token/hole-name [tok]
  (cond
    (= tok "_") "_"
    (= tok "?") "_"
    (and (> (length tok) 1)
         (= (string/slice tok 0 1) "?"))
    (string/slice tok 1)
    true nil))

(varfn elab/term [env sig-env node]
  (errorf "elab/term not yet defined"))

(defn term/app-chain [head args]
  (reduce (fn [acc arg] [:app acc arg])
          head
          args))

(defn elab/function-ref [name params]
  (let [n (length params)]
    (defn build [i args]
      (if (= i n)
        (term/app-chain [:var name] args)
        [:lam (fn [x] (build (+ i 1) [;args x]))]))
    (build 0 @[])))

(defn elab/pi-chain [env sig-env binders body]
  (if (zero? (length binders))
    (elab/term env sig-env body)
    (let [b (binders 0)
          name (b 1)
          dom (elab/term env sig-env (b 2))
          rest (slice binders 1)]
      [:t-pi dom (fn [x] (elab/pi-chain (env/extend env name x) sig-env rest body))])))

(defn elab/sigma-chain [env sig-env binders body]
  (if (zero? (length binders))
    (elab/term env sig-env body)
    (let [b (binders 0)
          name (b 1)
          dom (elab/term env sig-env (b 2))
          rest (slice binders 1)]
      [:t-sigma dom (fn [x] (elab/sigma-chain (env/extend env name x) sig-env rest body))])))

(defn elab/app-list [env sig-env xs]
  (when (zero? (length xs))
    (errorf "cannot elaborate empty application"))
  (reduce (fn [acc x] [:app acc (elab/term env sig-env x)])
          (elab/term env sig-env (xs 0))
          (slice xs 1)))

(defn elab/lam-chain [env sig-env params body]
  (if (zero? (length params))
    (elab/term env sig-env body)
    (let [b (params 0)
          name (b 1)
          rest (slice params 1)]
      [:lam (fn [x] (elab/lam-chain (env/extend env name x) sig-env rest body))])))

(defn list/head [xs]
  (if (and (> (length xs) 0) (l/node/atom? (xs 0)))
    (l/node/atom (xs 0))
    nil))

(defn list/expect-arity [form xs expected]
  (let [got (length xs)]
    (when (not= got expected)
      (errorf "%v expects %d argument(s), got %d: %v"
              form
              (- expected 1)
              (- got 1)
              [:list xs]))))

(defn list/parse-body [rest form]
  (when (zero? (length rest))
    (errorf "%v is missing a body" form))
  (if (l/node/atom= (rest 0) ".")
    (do
      (when (= (length rest) 1)
        (errorf "%v has dot but no body" form))
      (if (= (length rest) 2)
        (rest 1)
        [:list (slice rest 1)]))
    (if (= (length rest) 1)
      (rest 0)
      [:list rest])))

(defn list/parse-binders-body [xs form]
  (when (< (length xs) 3)
    (errorf "%v needs binders and a body: %v" form [:list xs]))
  (let [tail (slice xs 1)
        binders (l/binders/from-spec (tail 0))
        body (list/parse-body (slice tail 1) form)]
    [binders body]))

(defn list/parse-ann-binder [node]
  (match node
    [:list xs]
    (if (and (= (length xs) 3)
             (l/node/atom= (xs 0) "Ann")
             (l/node/atom? (xs 1)))
      [:bind (l/node/atom (xs 1)) (xs 2)]
      (errorf "invalid Ann binder: %v\nExpected form: (Ann x A)" node))
    _
    (errorf "invalid Ann binder: %v\nExpected form: (Ann x A)" node)))

(defn elab/list-pi [env sig-env node]
  (let [[binders body] (l/term/split-pi node)]
    (elab/pi-chain env sig-env binders body)))

(defn elab/list-lam [env sig-env xs]
  (let [[binders body] (list/parse-binders-body xs "lambda")]
    (elab/lam-chain env sig-env binders body)))

(defn elab/list-lam-ann [env sig-env xs]
  (list/expect-arity "Lam" xs 3)
  (let [b (list/parse-ann-binder (xs 1))
        name (b 1)
        body (xs 2)]
    [:lam (fn [x] (elab/term (env/extend env name x) sig-env body))]))

(defn elab/list-pi-ann [env sig-env xs]
  (list/expect-arity "Pi" xs 3)
  (let [b (list/parse-ann-binder (xs 1))
        name (b 1)
        dom (elab/term env sig-env (b 2))]
    [:t-pi dom (fn [x] (elab/term (env/extend env name x) sig-env (xs 2)))]))

(defn elab/list-ann [env sig-env xs]
  (list/expect-arity "Ann" xs 3)
  (elab/term env sig-env (xs 1)))

(defn elab/list-let [env sig-env xs]
  (list/expect-arity "let" xs 4)
  (let [bind (l/bind/from-node (xs 1))
        name (bind 1)
        val-core (elab/term env sig-env (xs 2))]
    (elab/term (env/extend env name val-core) sig-env (xs 3))))

(defn elab/list-sigma [env sig-env xs]
  (let [[binders body] (list/parse-binders-body xs "Sigma")]
    (elab/sigma-chain env sig-env binders body)))

(defn elab/list-pair [env sig-env xs]
  (list/expect-arity "pair" xs 3)
  [:pair (elab/term env sig-env (xs 1))
         (elab/term env sig-env (xs 2))])

(defn elab/list-fst [env sig-env xs]
  (list/expect-arity "fst" xs 2)
  [:fst (elab/term env sig-env (xs 1))])

(defn elab/list-snd [env sig-env xs]
  (list/expect-arity "snd" xs 2)
  [:snd (elab/term env sig-env (xs 1))])

(defn elab/list-id [env sig-env xs]
  (list/expect-arity "Id" xs 4)
  [:t-id (elab/term env sig-env (xs 1))
         (elab/term env sig-env (xs 2))
         (elab/term env sig-env (xs 3))])

(defn elab/list-refl [env sig-env xs]
  (list/expect-arity "refl" xs 2)
  [:t-refl (elab/term env sig-env (xs 1))])

(defn elab/list-j [env sig-env xs]
  (list/expect-arity "J" xs 7)
  [:t-J (elab/term env sig-env (xs 1))
        (elab/term env sig-env (xs 2))
        (elab/term env sig-env (xs 3))
        (elab/term env sig-env (xs 4))
        (elab/term env sig-env (xs 5))
        (elab/term env sig-env (xs 6))])

(def elab/list-dispatch
  {"fn" elab/list-lam
   "λ" elab/list-lam
   "lambda" elab/list-lam
   "Lam" elab/list-lam-ann
   "Pi" elab/list-pi-ann
   "Ann" elab/list-ann
   "let" elab/list-let
   "Sigma" elab/list-sigma
   "Σ" elab/list-sigma
   "exists" elab/list-sigma
   "pair" elab/list-pair
   "Pair" elab/list-pair
   "fst" elab/list-fst
   "Fst" elab/list-fst
   "snd" elab/list-snd
    "Snd" elab/list-snd
   "Id" elab/list-id
   "refl" elab/list-refl
   "Refl" elab/list-refl
   "J" elab/list-j})

(defn elab/list [env sig-env node xs]
  (if (or (l/term/forall? node) (l/term/arrow? node))
    (elab/list-pi env sig-env node)
    (if-let [handler (get elab/list-dispatch (list/head xs))]
      (handler env sig-env xs)
      (elab/app-list env sig-env xs))))

(set elab/term
     (fn [env sig-env node]
       (match node
         [:atom tok]
         (if-let [bound (env/lookup env tok)]
            bound
            (if-let [lvl (token/type-level tok)]
              [:type lvl]
              (if-let [hole (token/hole-name tok)]
                [:hole hole]
                (if-let [params (sig/lookup sig-env tok)]
                  (elab/function-ref tok params)
                  [:var tok]))))

          [:list xs]
          (elab/list env sig-env node xs)

          _
          (errorf "cannot elaborate node: %v" node))))

(defn binders/elab [env sig-env binders]
  (let [[out final-env]
        (reduce (fn [[acc cur-env] b]
                  (let [name (b 1)
                        ty-core (elab/term cur-env sig-env (b 2))]
                     [[;acc [:bind name ty-core]]
                      (env/extend cur-env name [:var name])]))
                [[] env]
                binders)]
    [out final-env]))

(defn clause/vars [patterns]
  (let [seen @{}
        out @[]]
    (defn collect [pat]
      (match pat
        [:pat/var x]
        (when (and (not= x "_") (not (has-key? seen x)))
          (put seen x true)
          (array/push out x))
        [:pat/con _ args]
        (each a args (collect a))
        _ nil))
    (each p patterns (collect p))
    out))

(defn clause/elab [base-env sig-env clause]
  (match clause
    [:clause patterns body]
    (let [vars (clause/vars patterns)
          env (reduce (fn [e name] (env/extend e name [:var name]))
                       base-env
                       vars)]
      [:core/clause patterns (elab/term env sig-env body)])
    _
    (errorf "invalid clause: %v" clause)))

(defn decl/elab [sig-env decl]
  (match decl
    [:decl/data name params sort ctors]
    (let [[core-params env] (binders/elab @[] sig-env params)
          core-sort (elab/term env sig-env sort)
          core-ctors (map (fn [ctor]
                            (match ctor
                              [:ctor ctor-name pat-binders patterns ctor-params encoded-type]
                              [:core/ctor ctor-name pat-binders patterns ctor-params
                               (elab/term env sig-env encoded-type)]
                              _ (errorf "invalid constructor: %v" ctor)))
                          ctors)]
      [:core/data name core-params core-sort core-ctors])

    [:decl/func name params result clauses]
    (let [[core-params env] (binders/elab @[] sig-env params)
          core-result (elab/term env sig-env result)
          core-type (elab/pi-chain @[] sig-env params result)
          core-clauses (map |(clause/elab env sig-env $) clauses)]
      [:core/func name core-params core-result core-type core-clauses])

    _
    (errorf "invalid declaration: %v" decl)))

(defn elab/program [decls]
  (let [sig-env (sig/from-decls decls)]
    (map |(decl/elab sig-env $) decls)))

(defn elab/forms [forms]
  (elab/program (l/lower/program forms)))

(defn elab/text [src]
  (elab/forms (p/parse/text src)))

(def exports
  {:elab/program elab/program
   :elab/forms elab/forms
   :elab/text elab/text
    :decl/elab (fn [decl] (decl/elab @[] decl))
    :term/elab (fn [env node] (elab/term env @[] node))
    :decl-elab (fn [decl] (decl/elab @[] decl))
    :term-elab (fn [env node] (elab/term env @[] node))})
