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

(defn elab/atom [env sig-env tok exact-ref?]
  (if-let [bound (env/lookup env tok)]
    bound
    (if-let [lvl (token/type-level tok)]
      [:type lvl]
      (if-let [hole (token/hole-name tok)]
        [:hole hole]
        (if-let [params (sig/lookup sig-env tok)]
          (if exact-ref?
            (elab/function-ref tok params)
            [:var tok])
          [:var tok])))))

(defn elab/callee [env sig-env node]
  (match node
    [:atom tok] (elab/atom env sig-env tok false)
    _ (elab/term env sig-env node)))

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
          (elab/callee env sig-env (xs 0))
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
         (elab/atom env sig-env tok true)

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

(defn seq/contains? [xs x]
  (not (nil? (find-index |(= $ x) xs))))

(defn clause/vars [patterns]
  "Collect unique pattern variables from clause patterns."
  (defn collect [pat seen]
    (match pat
      [:pat/var x]
      (if (or (= x "_") (seq/contains? seen x))
        seen
        [;seen x])
      [:pat/con _ args]
      (reduce collect seen args)
      seen))
  (reduce collect @[] patterns))

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

(defn text/contains? [s sub]
  (not (nil? (string/find sub (string s)))))

(defn node/atom/new [tok]
  [:atom tok])

(defn binder/to-node [b]
  [:list @[(node/atom/new (string (b 1) ":")) (b 2)]])

(defn line/items [line]
  (let [wrapped (string "(" (string/trim (string line)) ")")
        parsed (p/parse/one wrapped)]
    (if (and (tuple? parsed) (= (parsed 0) :list))
      (parsed 1)
      (errorf "cannot parse line: %v" line))))

(defn node/arrow-token? [node]
  (and (tuple? node)
       (= (node 0) :atom)
       (or (= (node 1) "->")
           (= (node 1) "→"))))

(defn node/forall-token? [node]
  (and (tuple? node)
       (= (node 0) :atom)
       (or (= (node 1) "forall")
           (= (node 1) "∀"))))

(defn items/to-term [items]
  (if (and (>= (length items) 4)
           (node/forall-token? (items 0))
           (tuple? (items 1))
           (= ((items 1) 0) :list)
           (tuple? (items 2))
           (= ((items 2) 0) :atom)
           (= ((items 2) 1) "."))
    [:list @[(items 0) (items 1) (items 2) (items/to-term (slice items 3 (length items)))]]
    (if-let [idx (find-index node/arrow-token? items)]
      (let [lhs-items (slice items 0 idx)
            rhs-items (slice items (+ idx 1) (length items))
            lhs (if (= (length lhs-items) 1)
                  (lhs-items 0)
                  [:list lhs-items])
            rhs (items/to-term rhs-items)]
        [:list @[lhs [:atom "->"] rhs]])
      (if (= (length items) 1)
        (items 0)
        [:list items]))))

(defn line/term [line]
  (items/to-term (line/items line)))

(defn header/split-colon [header]
  (let [s (string/trim (string header))
        n (length s)]
    (defn scan [i depth]
      (if (>= i n)
        nil
        (let [ch (string/slice s i (+ i 1))]
          (cond
            (= ch "(") (scan (+ i 1) (+ depth 1))
            (= ch ")") (scan (+ i 1) (max 0 (- depth 1)))
            (and (= ch ":") (= depth 0)) i
            true (scan (+ i 1) depth)))))
    (if-let [idx (scan 0 0)]
      (let [lhs (string/trim (string/slice s 0 idx))
            rhs0 (string/trim (string/slice s (+ idx 1) n))
            rhs (if (zero? (length rhs0)) nil rhs0)]
        [lhs rhs])
      [s nil])))

(defn header/name+params [lhs]
  (let [parsed (p/parse/one (string "(" lhs ")"))]
    (when (not (and (tuple? parsed) (= (parsed 0) :list)))
      (errorf "invalid record header: %v" lhs))
    (let [items (parsed 1)]
      (when (zero? (length items))
        (errorf "empty record header: %v" lhs))
      (when (not (and (tuple? (items 0)) (= ((items 0) 0) :atom)))
        (errorf "record name must be an atom in header: %v" lhs))
      (let [name ((items 0) 1)
            params (map l/bind/from-node (slice items 1 (length items)))]
        [name params]))))

(defn entry/line [entry]
  (entry 1))

(defn entry/children [entry]
  (entry 2))

(defn items/eq-index [items]
  (find-index |(and (tuple? $) (= ($ 0) :atom) (= ($ 1) "=")) items))

(defn entry/child-binder-node [entry]
  (let [items0 (line/items (entry/line entry))
        eq-index (items/eq-index items0)
        lhs-items (if (nil? eq-index)
                    items0
                    (slice items0 0 eq-index))]
    (if (and (= (length lhs-items) 1)
             (tuple? (lhs-items 0))
             (= ((lhs-items 0) 0) :list))
      (lhs-items 0)
      [:list lhs-items])))

(defn entry/ctor-items [entry]
  (let [base (line/items (entry/line entry))
        child-binders (map entry/child-binder-node (entry/children entry))]
    (reduce (fn [acc b] [;acc b]) base child-binders)))

(defn atom/type-token? [node]
  (and (tuple? node)
       (= (node 0) :atom)
       (let [tok (node 1)]
         (or (= tok "Type")
             (and (> (length tok) 4)
                  (= (string/slice tok 0 4) "Type"))))))

(defn params/index-positions [params]
  (reduce (fn [acc i]
            (if (atom/type-token? ((params i) 2))
              acc
              [;acc i]))
          @[]
          (range (length params))))

(defn selectors/for-clause [params selectors rhs]
  (let [k (length params)]
    (if (= (length selectors) k)
      selectors
      (let [defaults (map |[:atom ($ 1)] params)
            index-pos (params/index-positions params)
            assigned (reduce (fn [acc i]
                               (if (< i (length selectors))
                                 [;acc [(index-pos i) (selectors i)]]
                                 acc))
                             @[]
                             (range (min (length selectors) (length index-pos))))
            ctor-name (if (and (> (length rhs) 0)
                               (tuple? (rhs 0))
                               (= ((rhs 0) 0) :atom))
                        ((rhs 0) 1)
                        nil)
            completed
            (reduce (fn [acc pos]
                      (if (and (nil? (find-index |(= ($ 0) pos) assigned))
                               (= ctor-name "refl")
                               (> (length selectors) 0))
                        [;acc [pos (selectors 0)]]
                        acc))
                    assigned
                    index-pos)]
        (reduce (fn [acc i]
                  (if-let [entry (find |(= ($ 0) i) completed)]
                    [;acc (entry 1)]
                    [;acc (defaults i)]))
                @[]
                (range k))))))

(defn entry/data-clause-node [params entry]
  (let [items (entry/ctor-items entry)
        eq-index (items/eq-index items)]
    (if (nil? eq-index)
      [:list (reduce (fn [acc x] [;acc x])
                     @[[:atom "|"]]
                     items)]
      (let [selectors (slice items 0 eq-index)
            rhs (slice items (+ eq-index 1) (length items))
            full-selectors (selectors/for-clause params selectors rhs)]
        [:list (reduce (fn [acc x] [;acc x])
                       @[[:atom "|"]]
                       (reduce (fn [acc x] [;acc x])
                               (reduce (fn [acc x] [;acc x])
                                       full-selectors
                                       @[[:atom "="]])
                               rhs))]))))

(defn patterns/normalize-arity [pat-items arity]
  (cond
    (and (= arity 1) (> (length pat-items) 1))
    @[[:list pat-items]]

    true pat-items))

(defn entry/func-clause-node [arity entry]
  (let [items (line/items (entry/line entry))
        eq-index (items/eq-index items)]
    (if (nil? eq-index)
      [:list (reduce (fn [acc x] [;acc x])
                     @[[:atom "|"]]
                     items)]
      (let [patterns0 (slice items 0 eq-index)
            body (slice items (+ eq-index 1) (length items))
            patterns (patterns/normalize-arity patterns0 arity)]
        [:list (reduce (fn [acc x] [;acc x])
                       @[[:atom "|"]]
                       (reduce (fn [acc x] [;acc x])
                               (reduce (fn [acc x] [;acc x])
                                       patterns
                                       @[[:atom "="]])
                               body))]))))

(defn record/function-type-line? [line]
  (let [t (string/trim (string line))]
    (or (text/contains? t "->")
        (text/contains? t "→")
        (text/contains? t "∀"))))

(defn record->form [decl]
  (match decl
    [:decl/record header entries]
    (let [[lhs rhs] (header/split-colon header)
          [name params] (header/name+params lhs)
          param-nodes (map binder/to-node params)
          is-func
          (or (not (nil? rhs))
              (and (> (length entries) 0)
                   (record/function-type-line? (entry/line (entries 0)))))]
      (if is-func
        (let [ann-text (if rhs rhs (entry/line (entries 0)))
              ann (line/term ann-text)
              [fn-params _] (l/term/split-pi ann)
              arity (length fn-params)
              clause-entries (if rhs entries (slice entries 1 (length entries)))
              clauses (map |(entry/func-clause-node arity $) clause-entries)
              head-nodes
              (if (zero? (length param-nodes))
                @[[:atom "def"] [:atom (string name ":")] ann]
                (reduce (fn [acc x] [;acc x])
                        (reduce (fn [acc p] [;acc p])
                                @[[:atom "def"] [:atom name]]
                                param-nodes)
                        @[[:atom ":"] ann]))]
          [:list (reduce (fn [acc x] [;acc x])
                         head-nodes
                         clauses)])
        (let [sort (if rhs (line/term rhs) [:atom "Type"])
              clauses (map |(entry/data-clause-node params $) entries)]
          [:list (reduce (fn [acc x] [;acc x])
                         (reduce (fn [acc p] [;acc p])
                                 @[[:atom "data"] [:atom name]]
                                 param-nodes)
                         (reduce (fn [acc c] [;acc c])
                                 @[[:atom ":"] sort]
                                 clauses))])))
    _
    (errorf "expected :decl/record, got: %v" decl)))

(defn program/resolve-decls [decls]
  (let [[out _]
        (reduce (fn [[acc data-env] decl]
                  (let [resolved
                        (match decl
                          [:decl/record _ _]
                          (l/decl/lower (record->form decl) data-env)
                          _ decl)
                        next-data-env
                        (if (= (resolved 0) :decl/data)
                          [;data-env [(resolved 1) (resolved 4)]]
                          data-env)]
                    [[;acc resolved] next-data-env]))
                [@[] @[]]
                decls)]
    out))

(defn decl/elab [sig-env decl]
  (match decl
    [:decl/data name params sort ctors]
    (let [[core-params env] (binders/elab @[] sig-env params)
          core-sort (elab/term env sig-env sort)
          core-ctors (map (fn [ctor]
                            (match ctor
                              [:ctor ctor-name pat-binders patterns ctor-params encoded-type _]
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
  (let [resolved (program/resolve-decls decls)
        sig-env (sig/from-decls resolved)]
    (map |(decl/elab sig-env $) resolved)))

(defn elab/forms [forms]
  (elab/program (l/lower/program forms)))

(defn elab/text [src]
  (elab/forms (p/parse/text src)))

(def exports
  {:elab/program elab/program
   :elab/forms elab/forms
   :elab/text elab/text
    :record->form record->form
    :resolve/decls program/resolve-decls
     :decl/elab (fn [decl] (decl/elab @[] decl))
     :term/elab (fn [env node] (elab/term env @[] node))
     :decl-elab (fn [decl] (decl/elab @[] decl))
     :term-elab (fn [env node] (elab/term env @[] node))})
