#!/usr/bin/env janet

(import ./lowered_syntax :as l)
(import ./frontend/surface/ast :as a)
(import ./frontend/surface/layout :as ly)
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

(defn header/split-colon [header]
  (let [s (string/trim (string header))]
    (if-let [idx (ly/find-top-level-char s (chr ":"))]
      (let [rhs (string/trim (string/slice s (+ idx 1)))]
        [(string/trim (string/slice s 0 idx))
         (if (= rhs "") nil rhs)])
      [s nil])))

(defn- header/read-parenthesized-end [text start]
  (let [n (length text)]
    (var depth 0)
    (var i start)
    (var found false)
    (while (and (< i n) (not found))
      (let [c (text i)]
        (cond
          (= c (chr "(")) (do (++ depth) (++ i))
          (= c (chr ")")) (do (-- depth)
                               (when (= depth 0)
                                 (set found true)
                                 (++ i)))
          true (++ i))))
    (if found i nil)))

(defn- header/extract-name-and-params [lhs]
  (let [trimmed (string/trim lhs)]
    (if (zero? (length trimmed))
      [trimmed nil]
      (if-let [lp (ly/find-top-level-char trimmed (chr "("))]
        (if-let [end (header/read-parenthesized-end trimmed lp)]
          (if (= end (length trimmed))
            [(string/trim (string/slice trimmed 0 lp))
             (string/slice trimmed (+ lp 1) (- end 1))]
            [trimmed nil])
          [trimmed nil])
        [trimmed nil]))))

(defn- header/params [text]
  (if (or (nil? text) (= (string/trim text) ""))
    @[]
    (let [raw-parts (ly/split-top-level text (chr ","))
          parts @[]
          out @[]]
      (var pending nil)
      (each raw raw-parts
        (let [part (string/trim raw)]
          (when (not= part "")
            (let [chunk (if pending (string pending "," part) part)]
              (if (ly/find-top-level-char chunk (chr ":"))
                (do
                  (array/push parts chunk)
                  (set pending nil))
                (set pending chunk))))))
      (when pending
        (array/push parts pending))
      (each p parts
        (let [x (string/trim p)]
          (when (not= x "")
            (if-let [ix (ly/find-top-level-char x (chr ":"))]
              (let [names-part (string/trim (string/slice x 0 ix))
                    ty (sp/parse/type-text (string/trim (string/slice x (+ ix 1))))
                    names (ly/split-top-level names-part (chr ","))]
                (each name names
                  (let [trimmed-name (string/trim name)]
                    (when (not= trimmed-name "")
                      (array/push out (a/decl/param trimmed-name ty (a/span/none)))))))
              (array/push out (a/decl/param x nil (a/span/none)))))))
      out)))

(defn header/name+params [lhs]
  (let [[name params-text] (header/extract-name-and-params lhs)]
    (when (= name "")
      (errorf "empty record header: %v" lhs))
    [name (header/params params-text)]))

(defn- line/lhs-of-eq [line]
  (let [text (string/trim (string line))]
    (if-let [idx (ly/find-top-level-char text (chr "="))]
      (string/trim (string/slice text 0 idx))
      text)))

(defn field/binder-from-line [line]
  (let [lhs (line/lhs-of-eq line)
        trimmed (string/trim lhs)
        inner (if (and (> (length trimmed) 1)
                       (= (trimmed 0) (chr "("))
                       (= (trimmed (- (length trimmed) 1)) (chr ")")))
                (string/slice trimmed 1 (- (length trimmed) 1))
                trimmed)]
    (if-let [idx (ly/find-top-level-char inner (chr ":"))]
      (let [name (string/trim (string/slice inner 0 idx))
            ty-text (string/trim (string/slice inner (+ idx 1)))]
        (if (= name "")
          nil
          (a/decl/param name (sp/parse/type-text ty-text) (a/span/none))))
      nil)))

(defn entry/field-binders [entry]
  (map |(field/binder-from-line ($ 1)) (entry 2)))

(defn- record/flatten-entry-lines [entry]
  (reduce (fn [acc child]
            (array/concat acc (record/flatten-entry-lines child)))
          @[(entry 1)]
          (entry 2)))

(defn- record/flatten-lines [entries]
  (reduce (fn [acc entry]
            (array/concat acc (record/flatten-entry-lines entry)))
          @[]
          entries))

(defn- type/arity [ty]
  (match ty
    [:ty/pi _ body _] (+ 1 (type/arity body))
    [:ty/arrow _ cod _] (+ 1 (type/arity cod))
    _ 0))

(defn- type/wrap-params [body params]
  (reduce (fn [acc param]
            (let [name (param 1)
                  dom (or (param 2) (a/ty/universe 0 (a/span/none)))]
              (a/ty/pi (a/ty/binder name dom (a/span/none)) acc (a/span/none))))
          body
          (reverse params)))

(defn- type/app-head [head args]
  (reduce (fn [acc arg]
            (a/ty/app acc (a/ty/var arg (a/span/none)) (a/span/none)))
          (a/ty/name head (a/span/none))
          args))

(defn- term/pair-from-names [names]
  (when (zero? (length names))
    (errorf "record constructor encoding requires at least one field name"))
  (if (= (length names) 1)
    (a/tm/var (names 0) (a/span/none))
    (a/tm/op "pair"
             @[(a/tm/var (names 0) (a/span/none))
               (term/pair-from-names (slice names 1 (length names)))]
             (a/span/none))))

(defn- type/sigma-from-fields [fields]
  (when (zero? (length fields))
    (errorf "record sigma encoding requires at least one field"))
  (if (= (length fields) 1)
    ((fields 0) 2)
    (let [field (fields 0)
          binder (a/ty/binder (field 1) (field 2) (a/span/none))]
      (a/ty/sigma binder (type/sigma-from-fields (slice fields 1 (length fields))) (a/span/none)))))

(defn- clause/from-vars [names body]
  (a/decl/clause (map |(a/pat/var $ (a/span/none)) names) body (a/span/none)))

(defn- params/names [params]
  (map |($ 1) params))

(defn- record->sigma-decls [name params entries]
  (let [ctor-entry (entries 0)
        ctor-line (ctor-entry 1)
        ctor-tokens (ly/split-ws-top-level (string/trim ctor-line))
        ctor-name (if (> (length ctor-tokens) 0)
                    (ctor-tokens 0)
                    (errorf "record constructor line is empty: %v" ctor-entry))
        fields (entry/field-binders ctor-entry)
        sigma-body (type/sigma-from-fields fields)
        type-ann (type/wrap-params (a/ty/universe 0 (a/span/none)) params)
        type-clause (clause/from-vars (params/names params) sigma-body)
        type-decl (a/decl/func name type-ann @[type-clause] (a/span/none))
        ctor-params (array/concat (array/slice params) fields)
        ctor-ann (type/wrap-params (type/app-head name (params/names params)) ctor-params)
        ctor-clause (clause/from-vars (params/names ctor-params)
                                      (term/pair-from-names (params/names fields)))
        ctor-decl (a/decl/func ctor-name ctor-ann @[ctor-clause] (a/span/none))]
    @[type-decl ctor-decl]))

(defn- ctor/rhs [rhs]
  (let [trimmed (string/trim rhs)
        n (length trimmed)]
    (cond
      (or (= trimmed "") (= trimmed "()")) [nil @[]]
      true
      (let [name-end (or (ly/find-first-top-level-char trimmed @[(chr " ") (chr "\t") (chr "(")])
                         n)
            ctor-name (string/trim (string/slice trimmed 0 name-end))
            rest (string/trim (string/slice trimmed name-end n))
            fields (sp/parse/fields rest nil a/decl/field-named a/decl/field-anon)]
        (when (= ctor-name "")
          (errorf "empty constructor rhs: %q" rhs))
        [ctor-name fields]))))

(defn- record->data-decls [name params rhs entries]
  (let [sort (if rhs
               (sp/parse/type-text rhs)
               (a/ty/universe 0 (a/span/none)))
        ctors (reduce (fn [acc entry]
                        (let [line (string/trim (entry 1))]
                          (if-let [idx (ly/find-top-level-char line (chr "="))]
                            (let [lhs (string/trim (string/slice line 0 idx))
                                  rhs (string/trim (string/slice line (+ idx 1)))
                                  indices @[]]
                              (each p (ly/split-top-level lhs (chr ","))
                                (array/push indices (sp/parse/pat-text p)))
                              (let [[ctor-name fields] (ctor/rhs rhs)]
                                (if ctor-name
                                  [;acc (a/decl/ctor-indexed indices ctor-name fields (a/span/none))]
                                  acc)))
                            (let [[ctor-name fields] (ctor/rhs line)]
                              (if ctor-name
                                [;acc (a/decl/ctor-plain ctor-name fields (a/span/none))]
                                acc)))))
                      @[]
                      entries)]
    @[(a/decl/data name params sort ctors (a/span/none))]))

(defn- parse/clause-patterns [lhs arity]
  (let [parts (ly/split-ws-top-level lhs)
        pats @[]]
    (var cur 0)
    (for _ 0 arity
      (when (>= cur (length parts))
        (errorf "expected %d pattern(s), got %d in clause: %s" arity (length pats) lhs))
      (array/push pats (sp/parse/pat-text (parts cur)))
      (++ cur))
    (when (< cur (length parts))
      (errorf "too many pattern fragments in clause: %s" lhs))
    pats))

(defn- record->function-decls [name params ann-text clause-entries]
  (let [lines (record/flatten-lines clause-entries)
        type-parts @[]
        clause-lines @[]]
    (var found-clause false)
    (each line lines
      (let [trimmed (string/trim line)]
        (if found-clause
          (array/push clause-lines trimmed)
          (if (ly/find-top-level-char trimmed (chr "="))
            (do
              (set found-clause true)
              (array/push clause-lines trimmed))
            (array/push type-parts trimmed)))))
    (let [full-type-text (if (zero? (length type-parts))
                           ann-text
                           (string ann-text " " (string/join type-parts " ")))
          body-ty (sp/parse/type-text full-type-text)
          ty (type/wrap-params body-ty params)
          arity (type/arity body-ty)
          clauses (map (fn [line]
                         (if-let [idx (ly/find-top-level-char line (chr "="))]
                           (let [lhs (string/trim (string/slice line 0 idx))
                                 rhs (string/trim (string/slice line (+ idx 1)))
                                 pats (parse/clause-patterns lhs arity)]
                             (a/decl/clause pats (sp/parse/expr-text rhs) (a/span/none)))
                           (errorf "invalid clause line: %s" line)))
                       clause-lines)]
      @[(a/decl/func name ty clauses (a/span/none))])))

(defn record/function-type-line? [line]
  (let [t (string/trim (string line))]
    (or (string/find "->" t)
        (string/find "→" t)
        (string/find "∀" t))))

(defn record/sigma-shape? [entries]
  (let [has-single-entry (= (length entries) 1)
         has-children (> (length ((entries 0) 2)) 0)
        ctor-line ((entries 0) 1)
        ctor-items (ly/split-ws-top-level (string/trim ctor-line))
        ctor-line-has-no-equals (and (> (length ctor-items) 0)
                                     (nil? (ly/find-top-level-char ctor-line (chr "="))))
        binders (entry/field-binders (entries 0))
        all-binders-valid (all |(not (nil? $)) binders)]
    (and has-single-entry
         has-children
         ctor-line-has-no-equals
         all-binders-valid)))

(defn record->decls [decl]
  (match decl
    [:decl/record header entries]
    (let [[lhs rhs] (header/split-colon header)
           [name params] (header/name+params lhs)
          has-explicit-type? (not (nil? rhs))
          is-sigma-record? (and (nil? rhs) (record/sigma-shape? entries))
          is-function-like? (or has-explicit-type?
                                 (and (> (length entries) 0)
                                      (record/function-type-line? ((entries 0) 1))))]
      (cond
        is-sigma-record?
        (record->sigma-decls name params entries)

        is-function-like?
        (let [ann-text (if rhs rhs ((entries 0) 1))
              clause-entries (if rhs entries (slice entries 1 (length entries)))]
          (record->function-decls name params ann-text clause-entries))

        true
        (record->data-decls name params rhs entries)))
    _
    (errorf "expected :decl/record, got: %v" decl)))

(defn program/resolve-decls [decls]
  (let [out @[]
        data-env @[]]
    (each decl decls
      (let [resolved-list (match decl
                             [:decl/record _ _]
                             (sp/lower/program (a/program (record->decls decl) (a/span/none)))
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

(def exports
  {:elab/state elab/state
   :elab/hole elab/hole
   :elab/func-ref elab/func-ref
   :elab/ctor-call elab/ctor-call
   :elab/program elab/program
   :record->decls record->decls
   :resolve-decls program/resolve-decls
   :decl/elab (fn [decl] (decl/elab @[] decl))
   :term/elab-in-sig elab/term
   :term/elab (fn [env node] (elab/term env @[] node))})
