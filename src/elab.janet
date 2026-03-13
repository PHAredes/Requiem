#!/usr/bin/env janet

(import ./frontend/sexpr/parser :as p)
(import ./frontend/sexpr/lower :as l)
(import ./frontend/surface/parser :as sp)
(import ./sig :as s)
(import ./coreTT :as tt)

(defn env/lookup [env name]
  (var i (- (length env) 1))
  (var result nil)
  (while (and (>= i 0) (nil? result))
    (let [entry (env i)]
      (if (= (entry 0) name)
        (set result (entry 1))
        (-- i))))
  result)

(defn env/extend [env name value]
  [;env [name value]])

(defn sig/from-decls [decls]
  (reduce (fn [acc decl]
            (match decl
              [:decl/func name params _ _]
              (array/push acc [name params]) 
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

    (and (> (length tok) 6)
         (= (string/slice tok 0 5) "Type(")
         (= (string/slice tok (- (length tok) 1) (length tok)) ")"))
    (let [parsed (sp/parse/type-text tok)]
      (match parsed
        [:ty/universe lvl _] lvl
        _ nil))

    (and (> (length tok) 3)
         (= (string/slice tok 0 2) "U(")
         (= (string/slice tok (- (length tok) 1) (length tok)) ")"))
    (let [parsed (sp/parse/type-text tok)]
      (match parsed
        [:ty/universe lvl _] lvl
        _ nil))

    true nil))

(defn token/hole-name [tok]
  (cond
    (= tok "_") "_"
    (= tok "?") "_"
    (and (> (length tok) 1)
         (= (string/slice tok 0 1) "?"))
    (string/slice tok 1)
    true nil))

(defn elab/state []
  @{:holes @{}
    :constraints @[]
    :next 0})

(defn- elab/fresh-mv! [state]
  (let [n (+ (state :next) 1)
        mv (symbol "?mv" n)]
    (put state :next n)
    mv))

(defn elab/hole [state name]
  (if name
    (if-let [mv (get (state :holes) name)]
      (tt/tm/hole mv)
      (let [mv (elab/fresh-mv! state)]
        (put (state :holes) name mv)
        (array/push (state :constraints) {:mv mv :name name :solution nil})
        (tt/tm/hole mv)))
    (let [mv (elab/fresh-mv! state)]
      (array/push (state :constraints) {:mv mv :name nil :solution nil})
      (tt/tm/hole mv))))

(defn elab/func-ref [sig name]
  (s/sig/delta-ref sig name))

(defn elab/ctor-call [env sig data-name type-args ctor-name args]
  (let [available (s/sig/available-ctors sig data-name type-args)
        hit (find |(= (($ :ctor) :name) ctor-name) available)]
    (when (nil? hit)
      (errorf "constructor %v is not available for %v %v"
              ctor-name
              data-name
              type-args))
    (let [ctor (hit :ctor)
          fields (or (ctor :params) @[])]
      (when (not= (length fields) (length args))
        (errorf "constructor %v expects %d argument(s), got %d"
                ctor-name
                (length fields)
                (length args)))
      (let [check-arg (or (env :check-arg) (fn [_env _sig arg _ty] arg))
            checked (reduce (fn [acc i]
                              [;acc (check-arg env sig (args i) ((fields i) :type))])
                            @[]
                            (range (length args)))
            term (reduce (fn [acc arg] [:app acc arg])
                         [:var ctor-name]
                         checked)]
        {:term term
         :subst (hit :subst)
         :ctor ctor}))))

(varfn elab/term [env sig-env node]
  (errorf "elab/term not yet defined"))

(defn term/app-chain [head args]
  (reduce (fn [acc arg] [:app acc arg])
          head
          args))

(defn node/app-chain [head args]
  (if (zero? (length args))
    head
    [:list (reduce (fn [acc arg] [;acc arg]) @[head] args)]))

(defn elab/function-ref [name params]
  (let [n (length params)]
    (defn build [i mk-app]
      (if (= i n)
        (mk-app [:var name])
        [:lam (fn [x]
                (build (+ i 1)
                       (fn [head]
                         (mk-app [:app head x]))))]))
    (build 0 (fn [head] head))))

(defn elab/atom [env sig-env tok exact-ref?]
  (if-let [bound (env/lookup env tok)]
    bound
    (if-let [lvl (token/type-level tok)]
      [:type lvl]
      (if-let [hole (token/hole-name tok)]
        [:hole hole]
        (if-let [params (env/lookup sig-env tok)]
          (if exact-ref?
            (elab/function-ref tok params)
            [:var tok])
          [:var tok])))))

(defn elab/callee [env sig-env node]
  (match node
    [:atom tok] (elab/atom env sig-env tok false)
    _ (elab/term env sig-env node)))

(defn elab/dependent-chain [tag env sig-env binders body]
  (if (zero? (length binders))
    (elab/term env sig-env body)
    (let [b (binders 0)
          name (b 1)
          dom (elab/term env sig-env (b 2))
          rest (slice binders 1)]
      [tag dom (fn [x] (elab/dependent-chain tag (env/extend env name x) sig-env rest body))])))

(defn elab/pi-chain [env sig-env binders body]
  (elab/dependent-chain :t-pi env sig-env binders body))

(defn elab/sigma-chain [env sig-env binders body]
  (elab/dependent-chain :t-sigma env sig-env binders body))

(defn elab/app-list [env sig-env xs]
  (when (zero? (length xs))
    (errorf "cannot elaborate empty application"))
  (term/app-chain (elab/callee env sig-env (xs 0))
                  (map |(elab/term env sig-env $) (slice xs 1))))

(defn param/name [param]
  (if (string? param)
    param
    (param 1)))

(defn elab/lam-chain [env sig-env params body]
  (if (zero? (length params))
    (elab/term env sig-env body)
    (let [b (params 0)
          name (param/name b)
          rest (slice params 1)]
      [:lam (fn [x] (elab/lam-chain (env/extend env name x) sig-env rest body))])))

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

(defn list/parse-lam-binders [spec]
  (cond
    (and (tuple? spec) (= (spec 0) :atom))
    @([:bind (spec 1) nil])

    (and (tuple? spec) (= (spec 0) :list))
    (let [xs (spec 1)]
      (if (l/bind/single-spec? spec)
        @[(l/bind/from-node spec)]
        (map (fn [item]
               (match item
                 [:atom name] [:bind name nil]
                 _ (l/bind/from-node item)))
             xs)))

    true
    (errorf "invalid lambda binder specification: %v\nSupported formats:\n  x - single untyped binder\n  (x y z) - multiple untyped binders\n  (x: A) - single typed binder\n  ((x: A) (y: B)) - multiple typed binders" spec)))

(defn list/parse-lam-body [xs]
  (when (< (length xs) 3)
    (errorf "lambda needs binders and a body: %v" [:list xs]))
  (let [tail (slice xs 1)
        binders (list/parse-lam-binders (tail 0))
        body (list/parse-body (slice tail 1) "lambda")]
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
  (let [[binders body] (list/parse-lam-body xs)]
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
        body (xs 2)]
    (elab/pi-chain env sig-env @[b] body)))

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

(def list/dispatch-aliases
  {"λ" "fn"
   "lambda" "fn"
   "Σ" "Sigma"
   "exists" "Sigma"
   "Pair" "pair"
   "Fst" "fst"
   "Snd" "snd"
   "Refl" "refl"})

(defn list/dispatch-key [head]
  (or (get list/dispatch-aliases head) head))

(def elab/list-dispatch
  {"fn" elab/list-lam
   "Lam" elab/list-lam-ann
   "Pi" elab/list-pi-ann
   "Ann" elab/list-ann
   "let" elab/list-let
   "Sigma" elab/list-sigma
   "pair" elab/list-pair
   "fst" elab/list-fst
   "snd" elab/list-snd
   "Id" elab/list-id
   "refl" elab/list-refl
   "J" elab/list-j})

(defn elab/list [env sig-env node xs]
  (if (or (l/term/forall? node) (l/term/arrow? node))
    (elab/list-pi env sig-env node)
    (let [head (if (and (> (length xs) 0) (l/node/atom? (xs 0)))
                 (l/node/atom (xs 0))
                 nil)]
      (if-let [handler (get elab/list-dispatch (list/dispatch-key head))]
        (handler env sig-env xs)
        (elab/app-list env sig-env xs)))))

(set elab/term
     (fn [env sig-env node]
       (match node
         [:atom tok] (elab/atom env sig-env tok true)
         [:nat n] [:var (string n)]
         [:list xs] (elab/list env sig-env node xs)

         # Surface AST nodes
         [:ty/universe lvl _] [:type lvl]
         [:ty/hole name _] [:hole name]
         [:ty/var x _] (elab/atom env sig-env x true)
         [:ty/name x _] (elab/atom env sig-env x true)
         [:ty/arrow dom cod _] [:t-pi (elab/term env sig-env dom) (fn [_] (elab/term env sig-env cod))]
         [:ty/app f a _] [:app (elab/term env sig-env f) (elab/term env sig-env a)]
         
         [:tm/nat n _] [:var (string n)]
         [:tm/var x _] (elab/atom env sig-env x true)
         [:tm/ref x _] (elab/atom env sig-env x true)
         [:tm/hole name _] [:hole name]
         [:tm/app f a _] [:app (elab/term env sig-env f) (elab/term env sig-env a)]
         [:tm/lam params body _] (elab/lam-chain env sig-env params body)

         _ (errorf "cannot elaborate node: %v" node))))

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
  "Collect unique pattern variables from clause patterns."
  (defn collect [pat seen]
    (match pat
      [:pat/var x]
      (if (or (= x "_") (find |(= $ x) seen))
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
  (let [arrow-idx (find-index node/arrow-token? items)
         forall-idx (find-index node/forall-token? items)]
    (cond
      (and forall-idx
           (tuple? (items (+ forall-idx 1)))
           (= ((items (+ forall-idx 1)) 0) :list)
           (tuple? (items (+ forall-idx 2)))
           (= ((items (+ forall-idx 2)) 0) :atom)
           (= ((items (+ forall-idx 2)) 1) "."))
      [:list @[(items forall-idx)
               (items (+ forall-idx 1))
               (items (+ forall-idx 2))
               (items/to-term (slice items (+ forall-idx 3) (length items)))]]
      
      arrow-idx
      (let [lhs-items (slice items 0 arrow-idx)
            rhs-items (slice items (+ arrow-idx 1) (length items))
            lhs (if (= (length lhs-items) 1)
                  (lhs-items 0)
                  [:list lhs-items])
            rhs (items/to-term rhs-items)]
        [:list @[lhs [:atom "->"] rhs]])
      
      (= (length items) 1)
      (items 0)
      
      true
      [:list items])))

(defn line/term [line]
  (items/to-term (line/items line)))

(defn atom/strip-trailing-colon [item]
  (if (and (tuple? item)
           (= (item 0) :atom)
           (> (length (item 1)) 1)
           (= (string/slice (item 1) -1) ":"))
    [:atom (string/slice (item 1) 0 -1)]
    item))

(defn header/split-colon [header]
  (let [s (string/trim (string header))
        parsed (p/parse/one (string "(" s ")"))]
    (if (not (and (tuple? parsed) (= (parsed 0) :list)))
      [s nil]
      (let [items (parsed 1)
            colon-idx (find-index (fn [item]
                                    (and (tuple? item)
                                         (= (item 0) :atom)
                                         (or (= (item 1) ":")
                                             (and (> (length (item 1)) 1)
                                                  (= (string/slice (item 1) -1) ":")))))
                                  items)]
        (if (nil? colon-idx)
          [s nil]
          (let [colon-item (items colon-idx)
                lhs-items (if (= (colon-item 1) ":")
                            (slice items 0 colon-idx)
                            (array/concat (slice items 0 colon-idx)
                                          @[(atom/strip-trailing-colon colon-item)]))
                rhs-items (slice items (+ colon-idx 1) (length items))
                lhs (if (zero? (length lhs-items))
                      ""
                      (string (string/join (map (fn [n]
                                                  (if (tuple? n)
                                                    (string "(" (n 1) ")")
                                                    (string n)))
                                            lhs-items) " ")))
                rhs (if (zero? (length rhs-items))
                      nil
                      (string (string/join (map (fn [n]
                                                  (if (tuple? n)
                                                    (string "(" (n 1) ")")
                                                    (string n)))
                                            rhs-items) " ")))]
            [lhs rhs]))))))

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

(defn items/eq-index [items]
  (find-index |(and (tuple? $) (= ($ 0) :atom) (= ($ 1) "=")) items))

(defn items/lhs-of-eq [items]
  (if-let [eq-index (items/eq-index items)]
    (slice items 0 eq-index)
    items))

(defn field/binder-from-line [line]
  (let [lhs-items (items/lhs-of-eq (line/items line))
        node (if (and (= (length lhs-items) 1)
                      (tuple? (lhs-items 0))
                      (= ((lhs-items 0) 0) :list))
               (lhs-items 0)
               [:list lhs-items])]
    (if (l/bind/single-spec? node)
      (l/bind/from-node node)
      nil)))

(defn entry/field-binders [entry]
  (map |(field/binder-from-line ($ 1)) (entry 2)))

(defn seq/concat [xs ys]
  (array/concat (array/slice xs) ys))

(defn node/list [items]
  [:list items])

(defn clause/list [items]
  (node/list (seq/concat @[[:atom "|"]] items)))

(defn term/sigma-from-binders [binders]
  (when (zero? (length binders))
    (errorf "record sigma encoding requires at least one field"))
  (if (= (length binders) 1)
    ((binders 0) 2)
    (let [b (binders 0)]
      [:list @[(node/atom/new "Sigma")
               (binder/to-node b)
               (node/atom/new ".")
               (term/sigma-from-binders (slice binders 1 (length binders)))]])))

(defn term/pair-from-names [names]
  (when (zero? (length names))
    (errorf "record constructor encoding requires at least one field name"))
  (if (= (length names) 1)
    [:atom (names 0)]
    [:list @[(node/atom/new "pair")
             [:atom (names 0)]
             (term/pair-from-names (slice names 1 (length names)))]]))

(defn term/app-head [head args]
  (node/app-chain [:atom head] (map |[:atom $] args)))

(defn form/def-from-type+clauses [name ann clauses]
  (node/list (seq/concat @[[:atom "def"] [:atom (string name ":")] ann]
                         clauses)))

(defn form/clause [patterns body]
  (clause/list
    (seq/concat
      (map |[:atom $] patterns)
      @[[:atom "="] body])))

(defn entry/child-binder-node [entry]
  (let [items0 (line/items (entry 1))
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
  (let [base (line/items (entry 1))
        child-binders (map entry/child-binder-node (entry 2))]
    (seq/concat base child-binders)))

(defn atom/type-token? [node]
  (and (tuple? node)
       (= (node 0) :atom)
       (not (nil? (token/type-level (node 1))))))

(defn params/index-positions [params]
  (reduce (fn [acc i]
            (if (atom/type-token? ((params i) 2))
              acc
              (do (array/push acc i))))
          @[]
          (range (length params))))

(defn selectors/for-clause [params selectors]
  (let [k (length params)]
    (if (= (length selectors) k)
      selectors
      (let [defaults (map |[:atom ($ 1)] params)
            index-pos (params/index-positions params)
            lookup (reduce (fn [acc i]
                             (if (< i (length selectors))
                               (put acc (index-pos i) (selectors i))
                               acc))
                           @{}
                           (range (length index-pos)))]
        (map (fn [pos]
               (or (get lookup pos) (defaults pos)))
             (range k))))))

(defn entry/data-clause-node [params entry]
  (let [items (entry/ctor-items entry)
        eq-index (items/eq-index items)]
    (if (nil? eq-index)
      (clause/list items)
      (let [selectors (slice items 0 eq-index)
            rhs (slice items (+ eq-index 1) (length items))
            ctor-name (if (and (> (length rhs) 0)
                               (tuple? (rhs 0))
                               (= ((rhs 0) 0) :atom))
                        ((rhs 0) 1)
                        nil)
            filled-selectors (selectors/for-clause params selectors)
            full-selectors (if (and (= ctor-name "refl")
                                     (> (length selectors) 0)
                                     (< (length selectors) (length params)))
                              (array/push (array/slice filled-selectors) (selectors 0))
                              filled-selectors)]
        (clause/list (seq/concat (seq/concat full-selectors @[[:atom "="]]) rhs))))))

(defn patterns/normalize-arity [pat-items arity]
  (cond
    (and (= arity 1) (> (length pat-items) 1))
    @[[:list pat-items]]

    true pat-items))

(defn entry/func-clause-node [arity entry]
  (let [items (line/items (entry 1))
        eq-index (items/eq-index items)]
    (if (nil? eq-index)
      (clause/list items)
      (let [patterns0 (slice items 0 eq-index)
            body (slice items (+ eq-index 1) (length items))
            patterns (patterns/normalize-arity patterns0 arity)]
        (clause/list (seq/concat (seq/concat patterns @[[:atom "="]]) body))))))

(defn record/function-type-line? [line]
  (let [t (string/trim (string line))]
    (or (string/find "->" t)
        (string/find "→" t)
        (string/find "∀" t))))

(defn record/sigma-shape? [entries]
  (let [has-single-entry (= (length entries) 1)
        has-children (> (length ((entries 0) 2)) 0)
        ctor-items (line/items ((entries 0) 1))
        ctor-line-has-no-equals (and (> (length ctor-items) 0)
                                      (tuple? (ctor-items 0))
                                      (= ((ctor-items 0) 0) :atom)
                                      (nil? (items/eq-index ctor-items)))
        binders (entry/field-binders (entries 0))
        all-binders-valid (all |(not (nil? $)) binders)]
    (and has-single-entry
         has-children
         ctor-line-has-no-equals
         all-binders-valid)))

(defn record->sigma-forms [name params entries]
  (let [ctor-entry (entries 0)
        ctor-items (line/items (ctor-entry 1))
        ctor-name ((ctor-items 0) 1)
        fields (entry/field-binders ctor-entry)
        sigma-body (term/sigma-from-binders fields)
        type-ann (l/term/build-forall params [:atom "Type"])
        type-clause (form/clause (map |($ 1) params) sigma-body)
        type-form (form/def-from-type+clauses name type-ann @[type-clause])
        ctor-ann (l/term/build-forall (seq/concat params fields)
                                      (term/app-head name (map |($ 1) params)))
        ctor-clause (form/clause (map |($ 1) (seq/concat params fields))
                                 (term/pair-from-names (map |($ 1) fields)))
        ctor-form (form/def-from-type+clauses ctor-name ctor-ann @[ctor-clause])]
    @[type-form ctor-form]))

(defn record->forms [decl]
  (match decl
    [:decl/record header entries]
    (let [[lhs rhs] (header/split-colon header)
          [name params] (header/name+params lhs)
          param-nodes (map binder/to-node params)
          has-explicit-type? (not (nil? rhs))
          is-sigma-record? (and (nil? rhs) (record/sigma-shape? entries))
          is-function-like? (or has-explicit-type?
                               (and (> (length entries) 0)
                                    (record/function-type-line? ((entries 0) 1))))]
      (cond
        is-sigma-record?
        (record->sigma-forms name params entries)
        
        is-function-like?
        (let [ann-text (if rhs rhs ((entries 0) 1))
              ann (line/term ann-text)
              [fn-params _] (l/term/split-pi ann)
              arity (length fn-params)
              clause-entries (if rhs entries (slice entries 1 (length entries)))
              clauses (map |(entry/func-clause-node arity $) clause-entries)
              head-nodes
              (if (zero? (length param-nodes))
                @[[:atom "def"] [:atom (string name ":")] ann]
                (seq/concat (seq/concat @[[:atom "def"] [:atom name]]
                                        param-nodes)
                            @[[:atom ":"] ann]))]
          @[(node/list (seq/concat head-nodes clauses))])
        
        true
        (let [sort (if rhs (line/term rhs) [:atom "Type"])
              clauses (map |(entry/data-clause-node params $) entries)
              data-nodes (seq/concat (seq/concat @[[:atom "data"] [:atom name]]
                                                 param-nodes)
                                     (seq/concat @[[:atom ":"] sort]
                                                 clauses))]
          @[(node/list data-nodes)])))
    _
    (errorf "expected :decl/record, got: %v" decl)))

(defn program/resolve-decls [decls]
  (let [out @[]
        data-env @[]]
    (each decl decls
      (let [resolved-list (match decl
                            [:decl/record _ _]
                            (map |(l/decl/lower $ data-env) (record->forms decl))
                            _ @[decl])]
        (each d resolved-list
          (when (= (d 0) :decl/data)
            (array/push data-env [(d 1) (d 4)])))
        (array/concat out resolved-list)))
    out))

(defn decl/elab [sig-env decl]
  (match decl
    [:decl/data name params sort ctors]
    (let [[core-params env] (binders/elab @[] sig-env params)
          core-sort (elab/term env sig-env sort)
          core-ctors (map (fn [ctor]
                            (match ctor
                              [:ctor ctor-name pat-binders patterns ctor-params encoded-type _]
                              [:core/ctor ctor-name
                               pat-binders
                               patterns
                               (map (fn [b]
                                      (match b
                                        [:bind bname bty]
                                        [:bind bname (elab/term env sig-env bty)]
                                        _ (errorf "invalid ctor parameter binder: %v" b)))
                                    ctor-params)
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

    [:decl/compute tm]
    [:core/compute (elab/term @[] sig-env tm)]

    [:decl/check tm ty]
    [:core/check (elab/term @[] sig-env tm) (elab/term @[] sig-env ty)]

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
  {:elab/state elab/state
   :elab/hole elab/hole
   :elab/func-ref elab/func-ref
   :elab/ctor-call elab/ctor-call
   :elab/program elab/program
   :elab/forms elab/forms
   :elab/text elab/text
   :record->forms record->forms
   :resolve-decls program/resolve-decls
   :decl/elab (fn [decl] (decl/elab @[] decl))
   :term/elab (fn [env node] (elab/term env @[] node))})
