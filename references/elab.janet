#!/usr/bin/env janet

# elab.janet
#
# Elaboration: CST → coreTT
#
# Takes the output of parse/build-cst (array of declaration dicts)
# and produces core declarations with fully-elaborated types and terms.
#
# CST declaration shape (from parser.janet parse/build-cst):
#   {:header parsed-header
#    :body   [{:text text :col col :line n :parsed classified}...]}
#
# Parsed headers (from header-grammar):
#   [:type-decl name param-list]      -- Pascal: type declaration
#   [:term-decl name type-text]       -- kebab/mixfix: function declaration
#   [:prec fixity level op-name]      -- precedence declaration
#
# Parsed body lines (from ctor-grammar / clause-grammar):
#   [:plain ctor-name fields]
#   [:indexed index-pats ctor-name fields]
#   {:patterns [...] :body text}      -- function clause
#   {:raw text :col col}              -- fallthrough
#
# ============================================================
# KEY DECISIONS
# ============================================================
#
# (a) Parentheses resolve all ambiguity.
#     (zero) and (suc n) are both valid and unambiguous.
#     Outside parens: f x y = (f x) y, left-associative juxtaposition.
#     The Pratt pass has already resolved this before elab runs.
#     Elab sees a resolved application tree.
#
# (b) Aya-style indexed types (simpler-indexed-types §2.3).
#     IxCall: matches*(type-args, ctor.patterns) → σ
#             check fields against Δ_c·σ
#     ConCall: unindexed constructor, always available.
#     No term unification. Decidable by construction.
#
# (c) Exact application (elegant-elaboration §3.2).
#     Every bare function name f → lambda(f vars(Δ), Δ).
#     coreTT β-reduces immediately as arguments arrive.
#     All functions in coreTT are exactly-applied.
#
# (d) Holes.
#     ?       → fresh gensym metavar, always independent
#     ?name   → named metavar, shared within the declaration
#     _       → pure discard in patterns, no constraint
#     Collected during elaboration, unified after.

(import ./matches :as m)
(import ./sig     :as s)
(import ./coreTT  :as tt)
(import ./parser  :as p)

# ============================================================
# CONTEXT  Γ
# ============================================================
#
# Persistent array of [name type] pairs. Lookup right-to-left.

(defn ctx/empty [] @[])

(defn ctx/extend [ctx name ty]
  [;ctx [name ty]])

(defn ctx/lookup [ctx name]
  (defn scan [i]
    (if (< i 0) nil
      (let [e (ctx i)]
        (if (= (e 0) name) (e 1) (scan (- i 1))))))
  (scan (- (length ctx) 1)))

# ============================================================
# HOLE / METAVAR TABLE
# ============================================================
#
# Reset per declaration. Named holes share one metavar within a declaration.

(var *holes*      @{})   # name:string → metavar-symbol
(var *constraints* @[])  # [{:mv sym :location text :solution nil}...]
(var *hole-count* 0)

(defn holes/reset []
  (set *holes*      @{})
  (set *constraints* @[])
  (set *hole-count* 0))

(defn holes/fresh-sym []
  (set *hole-count* (+ *hole-count* 1))
  (symbol "?mv" *hole-count*))

(defn holes/named [name]
  "Return existing metavar for name, or create a fresh one."
  (or (get *holes* name)
      (let [sym (holes/fresh-sym)]
        (put *holes* name sym)
        (array/push *constraints* {:mv sym :name name :solution nil})
        sym)))

(defn holes/anon []
  "Create an independent anonymous metavar."
  (let [sym (holes/fresh-sym)]
    (array/push *constraints* {:mv sym :name nil :solution nil})
    sym))

(defn holes/elab [node]
  "Elaborate [:hole nil] or [:hole 'name'] to a coreTT hole term."
  (let [name (node 1)
        sym  (if (nil? name) (holes/anon) (holes/named name))]
    (tt/tm/hole sym)))

# ============================================================
# SUBSTITUTION APPLICATION
# ============================================================
#
# Apply σ from matches to a coreTT term.
# σ is a Janet table: string → coreTT-term.
# Used in IxCall to specialise Δ_c to the current indices.

(defn subst/apply [sigma term]
  "Apply substitution sigma (table of name→term) to a coreTT term."
  (if (empty? sigma) term
    (match term
      [:tm/var x]
      (or (get sigma x) term)

      [:tm/app f a]
      [:tm/app (subst/apply sigma f) (subst/apply sigma a)]

      [:tm/lam ty body-fn]
      [:tm/lam (subst/apply sigma ty)
               (fn [v] (subst/apply sigma (body-fn v)))]

      [:tm/pi dom cod-fn]
      [:tm/pi (subst/apply sigma dom)
              (fn [v] (subst/apply sigma (cod-fn v)))]

      [:tm/sigma dom cod-fn]
      [:tm/sigma (subst/apply sigma dom)
                 (fn [v] (subst/apply sigma (cod-fn v)))]

      [:tm/hole _]  term   # holes not substituted here

      _ term)))             # universes, neutrals pass through

(defn subst/apply-binders [sigma binders]
  "Apply σ to an array of {:name n :type T} binders."
  (map (fn [b] {:name (b :name)
                :type (subst/apply sigma (b :type))})
       binders))

# ============================================================
# PARSE HELPERS
# ============================================================
#
# Body lines arrive as raw text. We re-parse fragments on demand.
# The type-grammar and pat-grammar from parser.janet are used directly.

(defn parse/type-node [text]
  "Parse raw text as a type expression. Returns a CST node."
  (let [r (peg/match (peg/compile p/type-grammar) (string/trim text))]
    (if (nil? r)
      (errorf "parse/type-node: cannot parse type '%v'" text)
      (r 0))))

(defn parse/expr-node [text]
  "Parse raw text as a term expression. Returns a CST node.
   TODO: replace with full Pratt-parsed expr once pratt.janet is written."
  (let [r (peg/match (peg/compile p/type-grammar) (string/trim text))]
    (if (nil? r)
      (errorf "parse/expr-node: cannot parse expression '%v'" text)
      (r 0))))

(defn parse/pat-node [text]
  "Parse raw text as a pattern. Returns a CST node."
  (let [r (peg/match (peg/compile p/pat-grammar) (string/trim text))]
    (if (nil? r)
      (errorf "parse/pat-node: cannot parse pattern '%v'" text)
      (r 0))))

# ============================================================
# PI-TYPE SPLITTING
# ============================================================
#
# Split a coreTT Pi type into (params, result) for clause elaboration.
# We give each anonymous parameter a generated name so clause elab
# can refer to it by name if needed.

(defn split-pi [ty]
  "Split [:tm/pi ...] chain into [params result-ty].
   params: array of {:name n :type T}
   result-ty: the non-Pi tail."
  (defn walk [t acc i]
    (match t
      [:tm/pi dom cod-fn]
      (let [nm (string "_p" i)
            v  (tt/tm/var nm)]
        (walk (cod-fn v) [;acc {:name nm :type dom}] (+ i 1)))
      _
      [acc t]))
  (walk ty @[] 0))

# ============================================================
# TYPE ELABORATION
# ============================================================

(defn elab/type [ctx sig node]
  "Elaborate a type-expression CST node to a coreTT type.
   All holes in type position create metavars."
  (cond
    # Holes
    (and (tuple? node) (= (node 0) :hole))
    (holes/elab node)

    # Universe
    (and (tuple? node) (= (node 0) :atom) (= (node 1) "U"))
    (tt/tm/type 0)

    (and (tuple? node) (= (node 0) :atom) (= (node 1) "Type"))
    (tt/tm/type 0)

    (and (tuple? node) (= (node 0) :universe))
    (tt/tm/type (node 1))

    # Named reference (variable or declared type)
    (and (tuple? node) (= (node 0) :atom))
    (let [name (node 1)]
      (cond
        (ctx/lookup ctx name)    (tt/tm/var name)
        (s/sig/entry? sig name)  (s/sig/exact-ref sig name)
        true                     (tt/tm/var name)))  # free var, coreTT will catch

    # A -> B  (non-dependent)
    (and (tuple? node) (= (node 0) :arrow))
    (let [dom (elab/type ctx sig (node 1))
          cod (elab/type ctx sig (node 2))]
      (tt/tm/pi dom (fn [_] cod)))

    # Π(x: A). B
    (and (tuple? node) (= (node 0) :pi))
    (let [var (node 1)
          dom (elab/type ctx sig (node 2))
          cod (elab/type (ctx/extend ctx var dom) sig (node 3))]
      (tt/tm/pi dom (fn [v] (subst/apply {var v} cod))))

    # ∀(A: Type). B  — same elaboration as Π
    (and (tuple? node) (= (node 0) :forall))
    (elab/type ctx sig [:pi (node 1) (node 2) (node 3)])

    # Σ(a: A). B
    (and (tuple? node) (= (node 0) :sigma))
    (let [var (node 1)
          dom (elab/type ctx sig (node 2))
          cod (elab/type (ctx/extend ctx var dom) sig (node 3))]
      (tt/tm/sigma dom (fn [v] (subst/apply {var v} cod))))

    # ∃(a: A). B  — same elaboration as Σ
    (and (tuple? node) (= (node 0) :exists))
    (elab/type ctx sig [:sigma (node 1) (node 2) (node 3)])

    # Application in type position: T a  or  T a b c
    (and (tuple? node) (= (node 0) :app))
    (let [f (elab/type ctx sig (node 1))
          x (elab/term ctx sig (node 2))]
      (tt/tm/app f x))

    true
    (errorf "elab/type: unrecognised type node %q" node)))

# ============================================================
# TERM ELABORATION  (bidirectional)
# ============================================================
#
# elab/term  = synthesis  (infer mode): returns a coreTT term
# elab/check = checking mode:           returns a coreTT term, coerces via CONV
#
# FuncRef rule (exact-application):
#   f  →  lambda(f vars(Δ), Δ)   when f is a declared function
#
# IxCall:
#   See elab/ctor-app below.

(defn elab/term [ctx sig node]
  "Synthesise a coreTT term from a CST node."
  (cond
    (and (tuple? node) (= (node 0) :hole))
    (holes/elab node)

    (and (tuple? node) (= (node 0) :nat))
    (tt/tm/nat-lit (node 1))

    (and (tuple? node) (= (node 0) :atom))
    (let [name (node 1)]
      (cond
        (ctx/lookup ctx name)   (tt/tm/var name)
        (s/sig/entry? sig name) (s/sig/exact-ref sig name)
        true                    (tt/tm/var name)))

    # Application: dispatch to IxCall or regular APP
    (and (tuple? node) (= (node 0) :app))
    (elab/app ctx sig (node 1) (node 2) nil)

    # Lambda
    (and (tuple? node) (= (node 0) :lam))
    (let [var  (node 1)
          body (node 2)]
      (tt/tm/lam (fn [v]
        (elab/term (ctx/extend ctx var v) sig body))))

    # Annotation: (ann term type)
    (and (tuple? node) (= (node 0) :ann))
    (let [ty   (elab/type ctx sig (node 2))
          core (elab/check ctx sig (node 1) ty)]
      core)

    # Let
    (and (tuple? node) (= (node 0) :let))
    (let [var  (node 1)
          val  (elab/term ctx sig (node 2))
          body (elab/term (ctx/extend ctx var val) sig (node 3))]
      (tt/tm/app (tt/tm/lam (fn [_] body)) val))

    true
    (errorf "elab/term: unrecognised term node %q" node)))

(defn elab/check [ctx sig node expected-ty]
  "Check that node has type expected-ty. Returns a coreTT term.
   Falls back to CONV (synthesise + coerce) when no special rule applies."
  (cond
    # LAM rule: lambda against a Pi type
    (and (tuple? node) (= (node 0) :lam))
    (match expected-ty
      [:tm/pi dom cod-fn]
      (let [var  (node 1)
            body (node 2)]
        (tt/tm/lam (fn [v]
          (elab/check (ctx/extend ctx var dom) sig body (cod-fn v)))))
      _
      (elab/term ctx sig node))

    # Hole in check mode: record expected type as a constraint hint
    (and (tuple? node) (= (node 0) :hole))
    (let [mv (holes/elab node)]
      # Find the constraint entry and attach the expected type
      (defn attach [i]
        (when (< i (length *constraints*))
          (let [c (*constraints* i)]
            (if (= (c :mv) (mv 1))
              (put c :expected expected-ty)
              (attach (+ i 1))))))
      (attach 0)
      mv)

    # CONV: synthesise and coerce
    true
    (elab/term ctx sig node)))

(defn elab/app [ctx sig f-node x-node expected-ty]
  "Elaborate application f x.
   IxCall path: when f is a known constructor name.
   APP path: everything else."
  (cond
    # f is a bare constructor name
    (and (tuple? f-node)
         (= (f-node 0) :atom)
         (s/sig/ctor-by-name? sig (f-node 1)))
    (elab/ctor-app ctx sig (f-node 1) x-node expected-ty)

    # f is already a partial application that started with a ctor — keep IxCall
    (and (tuple? f-node)
         (= (f-node 0) :app)
         (ctor-app-head? f-node sig))
    (elab/regular-app ctx sig f-node x-node)

    # Standard APP rule
    true
    (elab/regular-app ctx sig f-node x-node)))

(defn ctor-app-head? [app-node sig]
  "Does this application tree have a constructor at its head?"
  (match app-node
    [:app f _] (ctor-app-head? f sig)
    [:atom n]  (s/sig/ctor-by-name? sig n)
    _          false))

(defn elab/regular-app [ctx sig f-node x-node]
  "Standard APP rule: elaborate f, elaborate x, apply."
  (let [f-core (elab/term ctx sig f-node)
        x-core (elab/term ctx sig x-node)]
    (tt/tm/app f-core x-core)))

(defn elab/ctor-app [ctx sig ctor-name x-node expected-ty]
  "IxCall rule.
   If expected-ty is a known data type application, run matches.
   Otherwise fall through to regular APP (no index info available)."
  (if (nil? expected-ty)
    (elab/regular-app ctx sig [:atom ctor-name] x-node)
    (let [[data-name type-args] (tt/tm/head-args expected-ty)]
      (if (or (nil? data-name) (not (s/sig/data? sig data-name)))
        (elab/regular-app ctx sig [:atom ctor-name] x-node)
        (let [ctor      (s/sig/ctor sig data-name ctor-name)
              ctor-nset (s/sig/ctor-name-set sig)
              result    (m/matches* type-args (ctor :patterns) ctor-nset)]
          (match result
            [:yes sigma]
            # IxCall succeeds: check x against Δ_c·σ
            (let [delta-c   (subst/apply-binders sigma (ctor :params))
                  # x must match the first parameter of Δ_c·σ
                  x-ty      (if (> (length delta-c) 0) ((delta-c 0) :type) nil)
                  x-core    (if (nil? x-ty)
                              (elab/term ctx sig x-node)
                              (elab/check ctx sig x-node x-ty))]
              (tt/tm/app (s/sig/exact-ref sig ctor-name) x-core))

            [:no]
            (errorf "constructor %v is not available at indices %v\n(availability check returned :no)"
                    ctor-name type-args)

            [:stuck]
            (errorf "constructor %v: availability stuck on indices %v\n(indices are neutral — they haven't reduced to constructor form)\nHint: add parentheses or a type annotation to force the index."
                    ctor-name type-args)))))))

# ============================================================
# PATTERN ELABORATION
# ============================================================

(defn elab/pat [ctx sig pat-node expected-ty]
  "Elaborate a pattern node against expected-ty.
   Returns {:core-pat pat :ctx new-ctx}."
  (cond
    # Pure wildcard _
    (and (tuple? pat-node) (= (pat-node 0) :atom) (= (pat-node 1) "_"))
    {:core-pat [:pat/wild] :ctx ctx}

    # Anonymous hole ? in pattern: wildcard with a metavar (no binding needed)
    (and (tuple? pat-node) (= (pat-node 0) :hole) (nil? (pat-node 1)))
    {:core-pat [:pat/wild] :ctx ctx}

    # Named hole ?name in pattern: bind as variable
    (and (tuple? pat-node) (= (pat-node 0) :hole))
    (let [name (pat-node 1)]
      {:core-pat [:pat/var name]
       :ctx      (ctx/extend ctx name expected-ty)})

    # Nat literal
    (and (tuple? pat-node) (= (pat-node 0) :nat))
    {:core-pat [:pat/nat (pat-node 1)] :ctx ctx}

    # Atom: variable or 0-ary constructor
    (and (tuple? pat-node) (= (pat-node 0) :atom))
    (let [name (pat-node 1)
          fst  (string/slice name 0 1)]
      (if (s/sig/ctor-by-name? sig name)
        # 0-ary constructor: IxCall with no args
        (elab/ctor-pat ctx sig name @[] expected-ty)
        # Variable binding
        {:core-pat [:pat/var name]
         :ctx      (ctx/extend ctx name expected-ty)}))

    # Constructor with arguments: (app (app ctor a1) a2) = ctor a1 a2
    (and (tuple? pat-node) (= (pat-node 0) :app))
    (let [[head args] (flatten-pat-app pat-node)]
      (if (and (tuple? head) (= (head 0) :atom) (s/sig/ctor-by-name? sig (head 1)))
        (elab/ctor-pat ctx sig (head 1) args expected-ty)
        (errorf "elab/pat: application in pattern must have a constructor at head, got %q" head)))

    true
    (errorf "elab/pat: unrecognised pattern %q" pat-node)))

(defn flatten-pat-app [node]
  "Flatten left-associative [:app ...] to [head args-array]."
  (defn walk [n acc]
    (match n
      [:app f x] (walk f (array/push acc x))
      _          [n (reverse acc)]))
  (walk node @[]))

(defn elab/ctor-pat [ctx sig ctor-name arg-nodes expected-ty]
  "Elaborate a constructor pattern using IxCall."
  (let [[data-name type-args] (tt/tm/head-args expected-ty)
        ctor      (s/sig/ctor sig data-name ctor-name)
        ctor-nset (s/sig/ctor-name-set sig)
        result    (m/matches* type-args (ctor :patterns) ctor-nset)]
    (match result
      [:yes sigma]
      (let [delta-c   (subst/apply-binders sigma (ctor :params))
            ctx-now   (ref ctx)
            core-args @[]]
        (for i 0 (length arg-nodes)
          (let [arg-ty ((delta-c i) :type)
                r      (elab/pat (deref ctx-now) sig (arg-nodes i) arg-ty)]
            (array/push core-args (r :core-pat))
            (set (deref ctx-now) (r :ctx))))
        {:core-pat [:pat/con ctor-name core-args]
         :ctx      (deref ctx-now)})

      [:no]
      (errorf "constructor %v unavailable in pattern at type %v"
              ctor-name expected-ty)

      [:stuck]
      (errorf "constructor %v: availability stuck in pattern at type %v\nAnnotate the scrutinee."
              ctor-name expected-ty))))

# ============================================================
# CONSTRUCTOR FIELD ELABORATION
# ============================================================

(defn elab/field [ctx sig field-node]
  "Elaborate a constructor field to {:name n :type T}."
  (cond
    # [:named-field var type-text]
    (and (tuple? field-node) (= (field-node 0) :named-field))
    (let [var       (field-node 1)
          type-node (parse/type-node (field-node 2))
          type-core (elab/type ctx sig type-node)]
      {:name var :type type-core})

    # Anonymous hole field
    (and (tuple? field-node) (= (field-node 0) :hole))
    {:name (string "_f" (holes/fresh-sym))
     :type (holes/elab field-node)}

    # Raw string (anonymous field, type only)
    (string? field-node)
    (let [type-node (parse/type-node field-node)
          type-core (elab/type ctx sig type-node)]
      {:name (string "_a" (holes/fresh-sym)) :type type-core})

    true
    (errorf "elab/field: unrecognised field form %q" field-node)))

# ============================================================
# CONSTRUCTOR ARM ELABORATION
# ============================================================
#
# Two arm shapes from ctor-grammar:
#   [:plain ctor-name fields]             -- unindexed (ConCall)
#   [:indexed index-pats ctor-name fields] -- indexed (IxCall)
#
# index-pats is an array of raw text strings, one per data parameter.
# fields is an array of field nodes.
#
# The parenthesis rule applies here:
#   (suc n) as a selector = suc applied to n, unambiguously.

(defn elab/arm [ctx sig data-name data-params arm-parsed]
  "Elaborate one constructor arm. Returns sig ctor entry."
  (match arm-parsed
    [:plain ctor-name fields]
    (let [field-binders (map |(elab/field ctx sig $) fields)]
      (build-ctor-entry ctor-name @[] field-binders data-name))

    [:indexed index-pats ctor-name fields]
    (let [# Parse each selector into a pat node
          # Parentheses resolve ambiguity: (suc n) = suc applied to n
          pat-nodes   (map parse/pat-node index-pats)
          # Collect all variables bound by the selector patterns
          pat-vars    (distinct (mapcat m/pat/vars pat-nodes))
          # Extend ctx with pat vars (type unknown, will be inferred)
          pat-ctx     (reduce |(ctx/extend $0 $1 (tt/tm/hole (holes/anon)))
                               ctx
                               pat-vars)
          field-binders (map |(elab/field pat-ctx sig $) fields)]
      (build-ctor-entry ctor-name pat-nodes field-binders data-name))

    _
    (errorf "elab/arm: unrecognised arm form %q" arm-parsed)))

(defn build-ctor-entry [ctor-name pat-nodes field-binders data-name]
  "Build the sig constructor entry.
   Full encoded type follows Definition 3.1 from simpler-indexed-types:
     vars(p) → Δ_c → D term(p)"
  {:name     ctor-name
   :patterns pat-nodes
   :params   field-binders
   :type     (encode-ctor-type pat-nodes field-binders data-name)})

(defn encode-ctor-type [pat-nodes field-binders data-name]
  "Encode the GADT-style type of a constructor as a Pi type.
   Used by sig/exact-ref for bare constructor references."
  # pat vars → field binders → D (term(p0), term(p1), ...)
  (let [pat-var-binders
        (mapcat (fn [p]
                  (map |([:bind $ :unknown]) (m/pat/vars p)))
                pat-nodes)
        ret-args  (map m/pat/to-term pat-nodes)
        ret-ty    [:app-chain data-name ret-args]
        all-binders [;pat-var-binders ;field-binders]]
    (reduce (fn [cod b]
              [:tm/pi (b :type) (fn [_] cod)])
            ret-ty
            (reverse all-binders))))

# ============================================================
# CLAUSE ELABORATION
# ============================================================

(defn elab/clause [ctx sig params result-ty clause]
  "Elaborate one function clause.
   clause: {:patterns [pat-nodes...] :body text-or-node}
   params: [{:name n :type T}...]
   result-ty: coreTT return type.
   Returns {:patterns [core-pats...] :body coreTT-term}."
  (let [pats-raw (clause :patterns)
        body-raw (clause :body)
        n-pats   (length pats-raw)
        n-params (length params)]
    (var ctx-now ctx)
    (let [core-pats @[]]
      # Elaborate each pattern against its declared parameter type
      (for i 0 (min n-pats n-params)
        (let [param-ty ((params i) :type)
              r        (elab/pat ctx-now sig (pats-raw i) param-ty)]
          (array/push core-pats (r :core-pat))
          (set ctx-now (r :ctx))))
      # If fewer patterns than params: eta-expand the body
      (let [remaining (slice params n-pats n-params)
            body-node (if (string? body-raw)
                        (parse/expr-node body-raw)
                        body-raw)
            body-core (elab/check ctx-now sig body-node result-ty)
            wrapped   (reduce (fn [b p]
                                (tt/tm/lam (fn [_] b)))
                              body-core
                              (reverse remaining))]
        {:patterns core-pats
         :body     wrapped}))))

# ============================================================
# UNIFICATION  (hole solving)
# ============================================================
#
# After each declaration, attempt to solve collected metavars.
# This is first-order: we don't attempt higher-order flex-flex.
#
# A constraint is {:mv sym :expected type-or-nil :solution ...}.
# We walk the constraints and unify where possible.
# Remaining unsolved named holes after unification = error.

(defn holes/unify [constraints]
  "Solve constraints. Returns table of sym→solution.
   Mutates :solution field on each constraint entry."
  (let [solved @{}]
    # First pass: attach expected types as solutions
    (each c constraints
      (when (not (nil? (c :expected)))
        (put solved (c :mv) (c :expected))
        (put c :solution (c :expected))))
    # Second pass: check named holes are solved
    (each c constraints
      (when (and (not (nil? (c :name)))
                 (nil? (c :solution)))
        # Named hole left unsolved — warn but don't error yet.
        # A real implementation would iterate to fixpoint.
        (eprintf "warning: named hole ?%v was not solved" (c :name))))
    solved))

# ============================================================
# TYPE DECLARATION ELABORATION
# ============================================================

(defn elab/type-decl [sig decl]
  "Elaborate a type declaration (Pascal-headed).
   decl: {:header [:type-decl name [[pname ptype?]...]] :body [arms...]}
   Adds entry to sig. Returns [:core/data name params sort ctors]."
  (holes/reset)
  (let [header    (decl :header)
        hdr       (header 0)            # the parsed tuple from header-grammar
        name      (hdr 1)
        param-raw (if (> (length hdr) 2) (hdr 2) nil)
        body      (decl :body)

        # Elaborate type parameters
        params
        (if (nil? param-raw)
          @[]
          (map (fn [p]
                 # p is [pname] or [pname type-text]
                 (let [pname (p 0)
                       pty   (if (> (length p) 1)
                               (elab/type (ctx/empty) sig (parse/type-node (p 1)))
                               (tt/tm/type 0))]
                   {:name pname :type pty}))
               param-raw))

        param-ctx
        (reduce |(ctx/extend $0 ($1 :name) ($1 :type)) (ctx/empty) params)

        sort (tt/tm/type 0)

        # Each body line's :parsed contains the arm tuple
        ctors
        (let [out @[]]
          (each body-line body
            (let [parsed (body-line :parsed)]
              (when (and (not (nil? parsed))
                         (> (length parsed) 0)
                         (tuple? (parsed 0)))
                (array/push out (elab/arm param-ctx sig name params (parsed 0))))))
          out)]

    (s/sig/add-data sig name params sort ctors)
    (holes/unify *constraints*)

    [:core/data name params sort ctors]))

# ============================================================
# TERM DECLARATION ELABORATION
# ============================================================

(defn elab/term-decl [sig decl]
  "Elaborate a term declaration (kebab/mixfix-headed).
   decl: {:header [:term-decl name type-text] :body [clauses...]}
   Adds entry to sig. Returns [:core/func name params result full-type clauses]."
  (holes/reset)
  (let [header    (decl :header)
        hdr       (header 0)
        name      (hdr 1)
        type-text (hdr 2)
        body      (decl :body)

        type-node  (parse/type-node type-text)
        full-type  (elab/type (ctx/empty) sig type-node)
        [params result-ty] (split-pi full-type)

        param-ctx
        (reduce |(ctx/extend $0 ($1 :name) ($1 :type)) (ctx/empty) params)

        # Body lines are function clauses
        # Each :parsed from clause-grammar gives {:patterns [...] :body text}
        clauses
        (let [out @[]]
          (each body-line body
            (let [parsed (body-line :parsed)]
              (when (and (not (nil? parsed))
                         (> (length parsed) 0)
                         (struct? (parsed 0)))  # clause is a struct {:patterns :body}
                (array/push out
                  (elab/clause param-ctx sig params result-ty (parsed 0))))))
          out)]

    (s/sig/add-func sig name params result-ty full-type)
    (holes/unify *constraints*)

    [:core/func name params result-ty full-type clauses]))

# ============================================================
# PRECEDENCE DECLARATION
# ============================================================

(defn elab/prec-decl [sig decl]
  "Record a precedence declaration in the sig (used by Pratt pass)."
  (let [hdr    ((decl :header) 0)
        fixity (hdr 1)
        level  (scan-number (hdr 2))
        op     (hdr 3)]
    (s/sig/add-prec sig op fixity level)
    [:core/prec op fixity level]))

# ============================================================
# PROGRAM ENTRY POINT
# ============================================================

(defn elab/program [cst-decls]
  "Elaborate a full program (array of CST declaration dicts).
   Returns array of core declarations.
   Builds the signature incrementally as declarations are processed."
  (let [sig (s/sig/empty)
        out @[]]
    (each decl cst-decls
      (let [header (decl :header)]
        (when (and (not (nil? header)) (> (length header) 0))
          (let [kind ((header 0) 0)
                result
                (match kind
                  :type-decl (elab/type-decl sig decl)
                  :term-decl (elab/term-decl sig decl)
                  :prec      (elab/prec-decl sig decl)
                  _
                  (do (eprintf "elab/program: skipping unknown decl kind %v" kind)
                      nil))]
            (when (not (nil? result))
              (array/push out result))))))
    out))

# ============================================================
# EXPORTS
# ============================================================

(def exports
  {:elab/program   elab/program
   :elab/type      elab/type
   :elab/term      elab/term
   :elab/check     elab/check
   :elab/pat       elab/pat
   :elab/clause    elab/clause
   :elab/arm       elab/arm
   :split-pi       split-pi
   :holes/reset    holes/reset
   :holes/unify    holes/unify
   :subst/apply    subst/apply})
