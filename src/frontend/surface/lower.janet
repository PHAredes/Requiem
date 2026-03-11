#!/usr/bin/env janet

# Surface AST → internal (:atom/:list) lowering
#
# Converts the typed surface AST produced by the surface parser
# into the internal representation consumed by elab.janet.

(import ./ast :as a)

# ---------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------

(defn- atom [tok] [:atom tok])
(defn- lst [xs] [:list xs])

(defn- node/binder [name ty]
  [:list @[(atom (string name ":")) ty]])

(defn- assoc/get [pairs key]
  (defn scan [i]
    (if (< i 0)
      nil
      (let [entry (pairs i)]
        (if (= (entry 0) key)
          (entry 1)
          (scan (- i 1))))))
  (scan (- (length pairs) 1)))

(defn- binders/name->type [binders]
  (map |[($ 1) ($ 2)] binders))

(defn- binders/unique-by-name [binders]
  (let [step (fn [[seen out] b]
               (let [name (b 1)]
                  (if (not (nil? (find-index |(= $ name) seen)))
                    [seen out]
                    [[;seen name] [;out b]])))
        [_ out] (reduce step [@[] @[]] (reverse binders))]
    (reverse out)))

(defn- term/as-head-app [node]
  (cond
    (and (tuple? node) (= (node 0) :atom))
    [(node 1) @[]]

    (and (tuple? node) (= (node 0) :list))
    (let [xs (node 1)]
      (if (and (> (length xs) 0) (tuple? (xs 0)) (= ((xs 0) 0) :atom))
        [((xs 0) 1) (slice xs 1 (length xs))]
        [nil @[]]))

    true [nil @[]]))

(defn- term/collect-var-order [terms var-types]
  (defn walk [node seen out]
    (cond
      (and (tuple? node) (= (node 0) :atom))
      (let [tok (node 1)]
        (if (and (assoc/get var-types tok)
                 (nil? (find-index |(= $ tok) seen)))
          [[;seen tok] [;out tok]]
          [seen out]))

      (and (tuple? node) (= (node 0) :list))
      (reduce (fn [[s o] x] (walk x s o)) [seen out] (node 1))

      true [seen out]))
  (let [[_ out]
        (reduce (fn [[seen out] t] (walk t seen out)) [@[] @[]] terms)]
    out))

(defn- pat/from-term [term pat-var-set]
  (match term
    [:atom tok]
      (if (not (nil? (find-index |(= $ tok) pat-var-set)))
        [:pat/var tok]
        [:pat/con tok @[]])

    [:list xs]
    (if (and (> (length xs) 0) (tuple? (xs 0)) (= ((xs 0) 0) :atom))
      (let [head ((xs 0) 1)
            args (map |(pat/from-term $ pat-var-set) (slice xs 1 (length xs)))]
        [:pat/con head args])
      (errorf "cannot convert lowered term to pattern: %v" term))

    _
    (errorf "cannot convert lowered term to pattern: %v" term)))

(defn- term/build-id [ty lhs rhs]
  @["Id" ty lhs rhs])

(defn- build-forall [binders body]
  (defn fold-binders [acc binder]
    (let [name (if (>= (length binder) 2) (binder 1) "_")
          ty (if (>= (length binder) 3) (binder 2) (atom "Type"))
          binder-node (node/binder name ty)]
      (lst @[(atom "forall") binder-node (atom ".") acc])))
  (reduce fold-binders body (reverse binders)))

(defn- build-data-app [name args]
  (if (zero? (length args))
    (atom name)
    (lst (tuple/join @[(atom name)] args))))

(defn- term/build-lam [binders body]
  (if (zero? (length binders))
    body
    (let [spec
          (if (= (length binders) 1)
            (node/binder ((binders 0) 1) ((binders 0) 2))
            (lst (map |(node/binder ($ 1) ($ 2)) binders)))]
      (lst @[(atom "fn") spec body]))))

# ---------------------------------------------------------------
# Token helpers for split-pi
# ---------------------------------------------------------------

(defn- token/colon? [tok]
  (let [n (length tok)]
    (and (> n 0)
         (= ":" (string/slice tok (- n 1) n)))))

(defn- token/strip-colon [tok]
  (if (token/colon? tok)
    (string/slice tok 0 (- (length tok) 1))
    tok))

(defn- forall? [node]
  (and (tuple? node)
       (= (node 0) :list)
       (let [xs (node 1)]
         (and (> (length xs) 0)
              (tuple? (xs 0)) (= ((xs 0) 0) :atom)
              (let [head ((xs 0) 1)]
                (or (= head "forall") (= head "∀")))))))

(defn- arrow? [node]
  (and (tuple? node)
       (= (node 0) :list)
       (let [xs (node 1)]
         (and (= (length xs) 3)
              (tuple? (xs 1))
              (= ((xs 1) 0) :atom)
              (let [mid ((xs 1) 1)]
                (or (= mid "->") (= mid "→")))))))

(defn- bind/from-node [node]
  (let [xs (node 1)]
    (cond
      (and (= (length xs) 2)
           (tuple? (xs 0)) (= ((xs 0) 0) :atom)
           (token/colon? ((xs 0) 1)))
      [:bind (token/strip-colon ((xs 0) 1)) (xs 1)]

      (and (= (length xs) 3)
           (tuple? (xs 0)) (= ((xs 0) 0) :atom) (= ((xs 0) 1) ":")
           (tuple? (xs 1)) (= ((xs 1) 0) :atom))
      [:bind ((xs 1) 1) (xs 2)]

      true
      (errorf "lower: invalid binder syntax: %v" node))))

(defn- unpack-forall [node]
  (let [xs (node 1)
        n (length xs)]
    (when (< n 3)
      (errorf "lower: forall too short: %v" node))
    (let [binder-spec (xs 1)
          dot-index (find-index |(and (tuple? $) (= ($ 0) :atom) (= ($ 1) "."))
                                (slice xs 2 n))]
      (let [body
            (if dot-index
              (let [actual-index (+ dot-index 2)]
                (if (= actual-index (- n 2))
                  (xs (- n 1))
                  (lst (slice xs (+ actual-index 1) n))))
              (if (= n 3)
                (xs 2)
                (lst (slice xs 2 n))))]
        [(bind/from-node binder-spec) body]))))

(defn- split-pi [node]
  (defn split-loop [cur index binders]
    (cond
      (forall? cur)
      (let [[b body] (unpack-forall cur)]
        (split-loop body index [;binders b]))

      (arrow? cur)
      (let [xs (cur 1)
            dom (xs 0)
            cod (xs 2)
            name (string "_arg" index)]
        (split-loop cod (+ index 1) [;binders [:bind name dom]]))

      true
      [binders cur]))
  (split-loop node 0 @[]))

(defn- binder/name-hint [ty]
  (match ty
    [:ty/name name _sp]
    (if (> (length name) 0)
      (string/ascii-lower (string/slice name 0 1))
      "arg")

    [:ty/var name _sp]
    name

    [:ty/app f _ _sp]
    (binder/name-hint f)

    _ "arg"))

(defn- binder/fresh-name [used base index]
  (let [prefix (if (= base "") "arg" base)
        candidate (if (and (= index 0) (nil? (find-index |(= $ prefix) used)))
                    prefix
                    (string prefix index))]
    (if (find-index |(= $ candidate) used)
      (binder/fresh-name used prefix (+ index 1))
      candidate)))

# ---------------------------------------------------------------
# Type lowering
# ---------------------------------------------------------------

(defn- flatten-app [f x]
  (match f
    [:list xs] (lst @[;xs x])
    _ (lst @[f x])))

(defn- term/equal? [a b]
  (match [a b]
    [[:atom x] [:atom y]]
    (= x y)

    [[:list xs] [:list ys]]
    (and (= (length xs) (length ys))
         (reduce (fn [ok i]
                   (and ok (term/equal? (xs i) (ys i))))
                 true
                 (range (length xs))))

    _
    (= a b)))

(var lower/type nil)

(defn- lower/binder [binder]
  (match binder
    [:binder name ty _sp]
    (node/binder name (lower/type ty))
    _ (errorf "lower/binder: invalid binder %v" binder)))

(set lower/type
     (fn [node]
       (match node
         [:ty/hole name _sp]
         (if name (atom (string "?" name)) (atom "?"))

         [:ty/universe level _sp]
          (atom (string "Type" level))

         [:ty/name name _sp]
         (atom name)

         [:ty/var name _sp]
         (atom name)

         [:ty/app f x _sp]
         (flatten-app (lower/type f) (lower/type x))

         [:ty/arrow dom cod _sp]
         (lst @[(lower/type dom) (atom "->") (lower/type cod)])

         [:ty/pi binder body _sp]
         (lst @[(atom "forall") (lower/binder binder) (atom ".") (lower/type body)])

          [:ty/sigma binder body _sp]
          (lst @[(atom "Sigma") (lower/binder binder) (atom ".") (lower/type body)])

          [:ty/op op args _sp]
          (lst (tuple/join @[(atom op)] (map lower/type args)))

         _ (errorf "lower/type: unknown node %v" node))))

# ---------------------------------------------------------------
# Term lowering
# ---------------------------------------------------------------

(var lower/term nil)

(set lower/term
     (fn [node]
       (match node
         [:tm/hole name _sp]
         (if name (atom (string "?" name)) (atom "?"))

         [:tm/var name _sp]
         (atom name)

         [:tm/ref name _sp]
         (atom name)

         [:tm/nat value _sp]
         (atom (string value))

         [:tm/app f x _sp]
         (flatten-app (lower/term f) (lower/term x))

         [:tm/lam params body _sp]
         (let [lower-param (fn [p]
                              (if (string? p)
                                (atom p)
                                (let [[_ name ty _] p]
                                  (node/binder name (lower/type ty)))))
                binder-nodes (map lower-param params)]
            (lst @[(atom "fn")
                   (if (= (length binder-nodes) 1)
                     (binder-nodes 0)
                     (lst binder-nodes))
                   (lower/term body)]))

         [:tm/let name value body _sp]
          (lst @[(atom "let")
                 (atom (string name ":"))
                 (lower/term value)
                 (lower/term body)])

          [:tm/op op args _sp]
          (lst (tuple/join @[(atom op)] (map lower/term args)))

         _ (errorf "lower/term: unknown node %v" node))))

# ---------------------------------------------------------------
# Pattern & pat-to-term lowering
# ---------------------------------------------------------------

(defn lower/pat [node]
  (match node
    [:pat/wild _sp]
    [:pat/var "_"]

    [:pat/hole _name _sp]
    [:pat/var "_"]

    [:pat/var name _sp]
    [:pat/var name]

    [:pat/con name args _sp]
    [:pat/con name (map lower/pat args)]

    [:pat/nat value _sp]
    [:pat/con (string value) @[]]

    _ (errorf "lower/pat: unknown pattern %v" node)))

(defn- lower/pat-to-term [pat]
  (match pat
    [:pat/wild _sp]  (atom "_")
    [:pat/hole _ _sp] (atom "_")
    [:pat/var name _sp] (atom name)
    [:pat/nat value _sp] (atom (string value))
    [:pat/con name args _sp]
    (if (zero? (length args))
      (atom name)
      (lst (tuple/join @[(atom name)] (map lower/pat-to-term args))))
    _ (errorf "lower/pat-to-term: unknown pattern %v" pat)))

# ---------------------------------------------------------------
# Field / constructor lowering
# ---------------------------------------------------------------

(defn- lower/param [param]
  (match param
    [:param name maybe-ty _sp]
    (if maybe-ty
      [:bind name (lower/type maybe-ty)]
      [:bind name (atom "Type")])
    _ (errorf "lower/param: unknown param %v" param)))

(defn- lower/ctor-fields-as-binders [fields]
  (let [out @[]
        used @[]]
    (for i 0 (length fields)
      (let [f (fields i)]
        (match f
          [:field/named name ty _sp]
          (do
            (array/push out [:bind name (lower/type ty)])
            (array/push used name))

          [:field/anon ty _sp]
          (let [name (binder/fresh-name used (binder/name-hint ty) 0)]
            (array/push out [:bind name (lower/type ty)])
            (array/push used name))

          _ (errorf "lower/ctor-fields-as-binders: unknown field %v" f))))
    out))

# ---------------------------------------------------------------
# Ford encoding for indexed constructors
# ---------------------------------------------------------------

(defn- ctor/ford-eqs [data-params ret-args]
  (let [n (length data-params)]
    (reduce (fn [acc i]
              (let [p (data-params i)
                    name (p 1)
                    ty (p 2)
                    lhs (atom name)
                    rhs (ret-args i)
                    eq-name (string "_eq" i)
                    eq-ty (term/build-id ty lhs rhs)]
                [;acc [:bind eq-name eq-ty]]))
            @[]
            (range n))))

(defn- ctor/ford-encoded [data-name data-params pat-binders ctor-params eq-binders]
  (let [data-param-terms (map |(atom ($ 1)) data-params)
        result-term (build-data-app data-name data-param-terms)
        base-binders (binders/unique-by-name (tuple/join data-params pat-binders ctor-params))
        all-binders (tuple/join base-binders eq-binders)]
    (build-forall all-binders result-term)))

(defn- args/simple-return? [args data-params]
  (and (= (length args) (length data-params))
       (let [n (length args)]
         (defn check-index [i]
           (if (= i n)
             true
             (let [a (args i)
                   p (data-params i)]
               (and (tuple? a)
                    (= (a 0) :atom)
                    (= (a 1) (p 1))
                    (check-index (+ i 1))))))
          (check-index 0))))

(defn- ctor/lower-indexed [data-name data-params name ctor-binders ret-args]
  (let [var-types (binders/name->type (binders/unique-by-name (tuple/join data-params ctor-binders)))
        ordered-vars (term/collect-var-order ret-args var-types)
        pat-var-set ordered-vars
        pat-binders (map |[:bind $ (assoc/get var-types $)] ordered-vars)
        ctor-params (filter (fn [b] (nil? (find-index |(= $ (b 1)) pat-var-set))) ctor-binders)
        eq-binders (ctor/ford-eqs data-params ret-args)
        patterns (map |(pat/from-term $ pat-var-set) ret-args)
        encoded (ctor/ford-encoded data-name data-params pat-binders ctor-params eq-binders)]
    [:ctor name pat-binders patterns ctor-params encoded eq-binders]))

(defn- ctor/drop-index-echo-fields [indices fields]
  # Aya-style sugar: in indexed branches, ctor(arg) where arg repeats
  # the branch index is treated as an index echo, not a runtime field.
  (let [index-terms (map lower/pat-to-term indices)
        n-fields (length fields)
        n-index (length index-terms)]
    (var fi 0)
    (var ii 0)
    (while (and (< fi n-fields) (< ii n-index))
      (let [f (fields fi)]
        (match f
          [:field/anon ty _sp]
          (if (term/equal? (lower/type ty) (index-terms ii))
            (do (++ fi) (++ ii))
            (break))

          _
          (break))))
    (slice fields fi n-fields)))

# ---------------------------------------------------------------
# Constructor lowering (plain & indexed)
# ---------------------------------------------------------------

(defn- ctor/lower-plain [data-name data-params ctor-node]
  (match ctor-node
    [:ctor/plain name fields _sp]
    (let [ctor-binders (lower/ctor-fields-as-binders fields)
          data-param-terms (map |(atom ($ 1)) data-params)
          ret-term (build-data-app data-name data-param-terms)
          ctor-type (build-forall ctor-binders ret-term)]
      [:ctor name @[] @[] ctor-binders ctor-type @[]])

    _ (errorf "ctor/lower-plain: expected :ctor/plain, got %v" ctor-node)))

(defn- ctor/lower-indexed-ctor [data-name data-params ctor-node]
  (match ctor-node
    [:ctor/indexed indices name fields _sp]
    (let [effective-fields (ctor/drop-index-echo-fields indices fields)
          ctor-binders (lower/ctor-fields-as-binders effective-fields)
          ret-args (map lower/pat-to-term indices)]
      (if (args/simple-return? ret-args data-params)
        (let [data-param-terms (map |(atom ($ 1)) data-params)
              ret-term (build-data-app data-name data-param-terms)
              ctor-type (build-forall ctor-binders ret-term)]
          [:ctor name @[] @[] ctor-binders ctor-type @[]])
        (ctor/lower-indexed data-name data-params name ctor-binders ret-args)))

    _ (errorf "ctor/lower-indexed-ctor: expected :ctor/indexed, got %v" ctor-node)))

(defn- ctor/lower [data-name data-params ctor-node]
  (match (a/node/tag ctor-node)
    :ctor/plain (ctor/lower-plain data-name data-params ctor-node)
    :ctor/indexed (ctor/lower-indexed-ctor data-name data-params ctor-node)
    _ (errorf "ctor/lower: unknown constructor kind %v" ctor-node)))

# ---------------------------------------------------------------
# Clause lowering
# ---------------------------------------------------------------

(defn- data/env-get [data-env name]
  (assoc/get data-env name))

(defn- type/ctor-names [ty data-env]
  (let [[head _] (term/as-head-app ty)]
    (if-let [ctors (data/env-get data-env head)]
      (map |($ 1) ctors)
      @[])))

(defn- data/ctor-names [data-env]
  (reduce (fn [acc entry]
            (reduce (fn [inner ctor]
                      [;inner (ctor 1)])
                    acc
                    (entry 1)))
          @[]
          data-env))

(defn lower/clause [clause data-env params]
  (match clause
    [:clause patterns body _sp]
    (let [lowered-pats
          (reduce (fn [acc i]
                    (let [p (patterns i)
                          lowered (lower/pat p)
                          expected-ty (if (< i (length params))
                                        ((params i) 2)
                                        nil)
                          ctor-names (if expected-ty
                                      (type/ctor-names expected-ty data-env)
                                      (data/ctor-names data-env))]
                      # Re-classify: if the surface parser emitted [:pat/var name]
                      # but that name is actually a 0-ary constructor, fix it
                      (match lowered
                        [:pat/var name]
                        (if (and (not= name "_")
                                 (not (nil? (find-index |(= $ name) ctor-names))))
                          [;acc [:pat/con name @[]]]
                          [;acc lowered])
                        _ [;acc lowered])))
                  @[]
                  (range (length patterns)))
          consumed (length lowered-pats)
          wildcard-pats (map (fn [_] [:pat/var "_"])
                             (range (- (length params) consumed)))
          all-pats (tuple/join lowered-pats wildcard-pats)
          rest-params (slice params consumed (length params))
          lowered-body (lower/term body)
          wrapped-body (term/build-lam rest-params lowered-body)]
      [:clause all-pats wrapped-body])

    _ (errorf "lower/clause: unknown clause %v" clause)))

# ---------------------------------------------------------------
# Declaration lowering
# ---------------------------------------------------------------

(defn- data/env-extend [data-env name ctors]
  [;data-env [name ctors]])

(defn lower/decl [decl data-env]
  (match decl
    [:decl/prec fixity level op _sp]
    [:decl/prec fixity level op]

    [:decl/data name params sort ctors _sp]
    (let [lowered-params (map lower/param params)
          sort (lower/type sort)
          lowered-ctors (map |(ctor/lower name lowered-params $) ctors)]
      [:decl/data name lowered-params sort lowered-ctors])

    [:decl/func name ty clauses _sp]
    (let [lowered-ty (lower/type ty)
          [lowered-params result] (split-pi lowered-ty)
          lowered-clauses (map |(lower/clause $ data-env lowered-params) clauses)]
      [:decl/func name lowered-params result lowered-clauses])

    [:decl/compute tm _sp]
    [:decl/compute (lower/term tm)]

    [:decl/check tm ty _sp]
    [:decl/check (lower/term tm) (lower/type ty)]

    _ (errorf "lower/decl: unknown declaration %v" decl)))

# ---------------------------------------------------------------
# Program lowering
# ---------------------------------------------------------------

(defn lower/program [prog]
  (let [decls (match prog
                [:program ds _sp] ds
                _ (errorf "lower/program: expected :program, got %v" prog))
        [out _]
        (reduce (fn [[acc data-env] decl]
                  (if (= (a/node/tag decl) :decl/prec)
                    [acc data-env]
                    (let [lowered (lower/decl decl data-env)
                          next-data-env
                          (if (= (lowered 0) :decl/data)
                            (data/env-extend data-env (lowered 1) (lowered 4))
                            data-env)]
                      [[;acc lowered] next-data-env])))
                [@[] @[]]
                decls)]
    out))

(def exports
  {:lower/type lower/type
   :lower/term lower/term
   :lower/pat lower/pat
   :lower/decl lower/decl
   :lower/clause lower/clause
   :lower/program lower/program})
