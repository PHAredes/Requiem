#!/usr/bin/env janet

(import ./parser :as p)
(import ./desugar :as d)

(defn env/lookup [env name]
  (var i (- (length env) 1))
  (var found nil)
  (while (and (>= i 0) (nil? found))
    (let [entry (env i)]
      (when (= (entry 0) name)
        (set found (entry 1))))
    (-- i))
  found)

(defn env/extend [env name value]
  (let [out @[]]
    (each e env (array/push out e))
    (array/push out [name value])
    out))

(defn token/digits? [s]
  (if (zero? (length s))
    false
    (do
      (var ok true)
      (for i 0 (length s)
        (let [ch (string/slice s i (+ i 1))]
          (when (or (< ch "0") (> ch "9"))
            (set ok false)
            (break))))
      ok)))

(defn token/type-level [tok]
  (cond
    (= tok "Type") 0
    (= tok "U") 0
    (and (> (length tok) 4)
         (= (string/slice tok 0 4) "Type")
         (token/digits? (string/slice tok 4 (length tok))))
    (scan-number (string/slice tok 4 (length tok)))
    true nil))

(var elab/term nil)

(defn elab/pi-chain [env binders body]
  (if (zero? (length binders))
    (elab/term env body)
    (let [b (binders 0)
          name (b 1)
          ty-node (b 2)
          dom (elab/term env ty-node)
          rest (slice binders 1 (length binders))]
      [:t-pi dom (fn [x] (elab/pi-chain (env/extend env name x) rest body))])))

(defn elab/app-list [env xs]
  (when (zero? (length xs))
    (errorf "cannot elaborate empty application"))
  (var out (elab/term env (xs 0)))
  (for i 1 (length xs)
    (set out [:app out (elab/term env (xs i))]))
  out)

(set elab/term
     (fn [env node]
       (match node
         [:atom tok]
         (if-let [bound (env/lookup env tok)]
           bound
           (if-let [lvl (token/type-level tok)]
             [:type lvl]
             [:var tok]))

         [:list xs]
         (if (or (d/term/forall? node) (d/term/arrow? node))
           (let [[binders body] (d/term/split-pi node)]
             (elab/pi-chain env binders body))
           (elab/app-list env xs))

         _
         (errorf "cannot elaborate node: %v" node))))

(defn binders/elaborate [env binders]
  (let [out @[]]
    (var cur-env env)
    (each b binders
      (let [name (b 1)
            ty-node (b 2)
            ty-core (elab/term cur-env ty-node)]
        (array/push out [:bind name ty-core])
        (set cur-env (env/extend cur-env name [:var name]))))
    [out cur-env]))

(defn pat/collect-vars [pat seen out]
  (match pat
    [:pat/var x]
    (when (and (not= x "_") (not (has-key? seen x)))
      (put seen x true)
      (array/push out x))

    [:pat/con _ args]
    (each a args
      (pat/collect-vars a seen out))

    _ nil))

(defn clause/vars [patterns]
  (let [seen @{}
        out @[]]
    (each p patterns
      (pat/collect-vars p seen out))
    out))

(defn clause/elaborate [base-env clause]
  (match clause
    [:clause patterns body]
    (let [vars (clause/vars patterns)]
      (var env base-env)
      (each name vars
        (set env (env/extend env name [:var name])))
      [:core/clause patterns (elab/term env body)])
    _
    (errorf "invalid clause: %v" clause)))

(defn decl/elaborate [decl]
  (match decl
    [:decl/data name params sort ctors]
    (let [[core-params env] (binders/elaborate @[] params)
          core-sort (elab/term env sort)
          core-ctors @[]]
      (each ctor ctors
        (match ctor
          [:ctor ctor-name pat-binders patterns ctor-params encoded-type]
          (array/push core-ctors
                      [:core/ctor ctor-name pat-binders patterns ctor-params
                       (elab/term env encoded-type)])
          _ (errorf "invalid constructor: %v" ctor)))
      [:core/data name core-params core-sort core-ctors])

    [:decl/func name params result clauses]
    (let [[core-params env] (binders/elaborate @[] params)
          core-result (elab/term env result)
          core-type (elab/pi-chain @[] params result)
          core-clauses @[]]
      (each clause clauses
        (array/push core-clauses (clause/elaborate env clause)))
      [:core/func name core-params core-result core-type core-clauses])

    _
    (errorf "invalid declaration: %v" decl)))

(defn elaborate/program [decls]
  (map decl/elaborate decls))

(defn elaborate/forms [forms]
  (elaborate/program (d/desugar/program forms)))

(defn elaborate/text [src]
  (elaborate/forms (p/parse/text src)))

(def exports
  {:elaborate/program elaborate/program
   :elaborate/forms elaborate/forms
   :elaborate/text elaborate/text
   :decl/elaborate decl/elaborate
   :term/elaborate elab/term})
