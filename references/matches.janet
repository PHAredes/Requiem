#!/usr/bin/env janet

# matches.janet
#
# matches(u, p) → σ | ⊥ | stuck
#
# This is term-match-pattern, NOT term-match-term.
# That distinction is the entire point of simpler indexed types.
# It's decidable and terminating because patterns are structurally finite.
#
# Three outcomes (mirror the paper exactly):
#   [:yes subst]  -- pattern matched, subst maps pattern vars to terms
#   [:no]         -- definite mismatch (different ctor heads)
#   [:stuck]      -- neutral/unknown term, cannot decide availability
#
# Reference: Tesla Zhang, "A Simpler Encoding of Indexed Types", §2.2

# ============================================================
# OUTCOME CONSTRUCTORS
# ============================================================

(def YES :yes)
(def NO  :no)
(def STUCK :stuck)

(defn outcome/yes [subst] [YES subst])
(defn outcome/no  []      [NO])
(defn outcome/stuck []    [STUCK])

(defn outcome/yes? [r] (and (tuple? r) (= (r 0) YES)))
(defn outcome/no?  [r] (and (tuple? r) (= (r 0) NO)))
(defn outcome/stuck? [r] (and (tuple? r) (= (r 0) STUCK)))

(defn outcome/subst [r]
  (if (outcome/yes? r)
    (r 1)
    (errorf "outcome/subst called on non-yes result: %v" r)))

# ============================================================
# SUBSTITUTION
# ============================================================

(defn subst/empty [] @{})

(defn subst/lookup [σ x] (get σ x))

(defn subst/extend [σ x u]
  # Returns new substitution with x → u added.
  # Does not mutate σ.
  (let [s2 (table ;(kvs σ))]
    (put s2 x u)
    s2))

(defn subst/merge [σ1 σ2]
  # Merge two substitutions. Fails (returns nil) on conflicting bindings.
  # Conflicting = same key bound to structurally different terms.
  (let [out (table ;(kvs σ1))]
    (var ok true)
    (eachp [k v] σ2
      (if-let [existing (get out k)]
        (when (not= existing v)
          (set ok false))
        (put out k v)))
    (if ok out nil)))

# ============================================================
# TERM UTILITIES
# ============================================================
#
# Terms here are coreTT semantic values or surface CST nodes.
# We need to be able to:
#   - tell if a term is a constructor application (head is in ctor-name-set)
#   - extract head and args from an application

(defn term/head-args [u]
  "Return [head args] for an application, or [nil []] if not applicable."
  (match u
    [:atom name]     [name @[]]
    [:list xs]
    (if (and (> (length xs) 0)
             (tuple? (xs 0))
             (= ((xs 0) 0) :atom))
      [((xs 0) 1) (slice xs 1)]
      [nil @[]])
    # coreTT neutral form [:napp ...]
    [:napp f x]      [nil @[]]   # stuck, treat as neutral
    [:nvar x]        [x @[]]
    _ [nil @[]]))

(defn term/ctor? [u ctor-name-set]
  "Is u a constructor application (head is a known constructor)?"
  (let [[head _] (term/head-args u)]
    (and (not (nil? head))
         (has-key? ctor-name-set head))))

(defn term/neutral? [u]
  "Is u a stuck/neutral term that cannot be pattern matched?"
  (match u
    [:nvar _]    true
    [:napp _ _]  true
    [:nfst _]    true
    [:nsnd _]    true
    _            false))

# ============================================================
# PATTERN UTILITIES
# ============================================================

(defn pat/var? [p]  (and (tuple? p) (= (p 0) :pat/var)))
(defn pat/con? [p]  (and (tuple? p) (= (p 0) :pat/con)))
(defn pat/hole? [p] (and (tuple? p) (= (p 0) :hole)))
(defn pat/wild? [p]
  (or (and (pat/var? p) (= (p 1) "_"))
      (and (pat/hole? p) (nil? (p 1)))))  # anonymous hole in pattern = wildcard

(defn pat/var-name [p] (p 1))
(defn pat/con-name [p] (p 1))
(defn pat/con-args [p] (p 2))

# vars(p): extract all variable bindings from a pattern
# Returns array of name strings
(defn pat/vars [p]
  (match p
    [:pat/var x]   (if (= x "_") @[] @[x])
    [:hole name]   (if (nil? name) @[] @[name])
    [:pat/con _ args]
    (reduce (fn [acc a] [;acc ;(pat/vars a)]) @[] args)
    [:pat/impossible] @[]
    _ @[]))

# term(p): the canonical term that exactly matches pattern p
# Used to construct the return type of a translated constructor
(defn pat/to-term [p]
  (match p
    [:pat/var x]   [:atom x]
    [:hole name]   [:atom (or name "_")]
    [:pat/con c args]
    (if (zero? (length args))
      [:atom c]
      [:list [[:atom c] ;(map pat/to-term args)]])
    [:pat/impossible]
    (errorf "pat/to-term: impossible pattern has no term representation")
    _
    (errorf "pat/to-term: unknown pattern %v" p)))

# ============================================================
# CORE: matches(u, p) → outcome
# ============================================================
#
# Rules from Fig 2.3 of the paper:
#
#   matches(u, x)       → [u/x]                 variable capture
#   matches(c u, c p)   → matches*(u, p)         same constructor
#   matches(c1 u, c2 p) → ⊥   (c1 ≠ c2)         ctor mismatch
#   matches(u, p)       → ⊥   if u stuck          neutral term
#
# Extension: anonymous hole and _ always succeed without binding.

(defn matches [u p ctor-name-set]
  "Match term u against pattern p.
   ctor-name-set: set of known constructor names (to distinguish ctors from vars).
   Returns [:yes subst] | [:no] | [:stuck]."

  (cond
    # wildcard _ : always yes, no binding
    (and (tuple? p) (= (p 0) :pat/var) (= (p 1) "_"))
    (outcome/yes (subst/empty))

    # anonymous hole ? in pattern: yes, no binding (elaborator handles it upstream)
    (and (tuple? p) (= (p 0) :hole) (nil? (p 1)))
    (outcome/yes (subst/empty))

    # named hole ?name in pattern: bind like a variable
    (and (tuple? p) (= (p 0) :hole) (not (nil? (p 1))))
    (outcome/yes (subst/extend (subst/empty) (p 1) u))

    # variable pattern: bind x to u
    (pat/var? p)
    (let [x (pat/var-name p)]
      (if (= x "_")
        (outcome/yes (subst/empty))
        (outcome/yes (subst/extend (subst/empty) x u))))

    # constructor pattern: check if u is same ctor, recurse on args
    (pat/con? p)
    (let [ctor (pat/con-name p)
          pats (pat/con-args p)
          [head args] (term/head-args u)]
      (cond
        # u is neutral: cannot decide
        (term/neutral? u)
        (outcome/stuck)

        # u has no recognizable head: stuck
        (nil? head)
        (outcome/stuck)

        # u's head is not a known constructor: stuck
        (not (has-key? ctor-name-set head))
        (outcome/stuck)

        # u's head is a different constructor: definite no
        (not= head ctor)
        (outcome/no)

        # arity mismatch: definite no
        (not= (length args) (length pats))
        (outcome/no)

        # same constructor, same arity: recurse on args
        true
        (matches* args pats ctor-name-set (subst/empty))))

    # impossible pattern: always no
    (and (tuple? p) (= (p 0) :pat/impossible))
    (outcome/no)

    true
    (errorf "matches: unknown pattern form %v" p)))

(defn matches* [us ps ctor-name-set initial-subst]
  "Match a list of terms against a list of patterns.
   Merges substitutions left-to-right. Fails on first No or merge conflict."
  (when (not= (length us) (length ps))
    (break (outcome/no)))
  (var status YES)
  (var sigma initial-subst)
  (var i 0)
  (while (and (< i (length us)) (= status YES))
    (let [r (matches (us i) (ps i) ctor-name-set)]
      (match r
        [:yes s2]
        (if-let [merged (subst/merge sigma s2)]
          (do (set sigma merged) (++ i))
          (do (set status NO) (++ i)))   # conflicting bindings = no
        [:no]    (set status NO)
        [:stuck] (set status STUCK)))
    (++ i))
  (match status
    :yes   (outcome/yes sigma)
    :no    (outcome/no)
    :stuck (outcome/stuck)))

# ============================================================
# AVAILABILITY CHECK
# ============================================================
#
# Given a list of selector terms (the current type arguments)
# and a constructor's selector patterns, determine availability.
#
# Used by the elaborator when encountering a constructor reference
# or when doing coverage checking.

(defn ctor/available? [type-args ctor ctor-name-set]
  "Check if ctor is available when the type is applied to type-args.
   Returns [:yes σ] | [:no] | [:stuck]."
  (let [patterns (ctor :patterns)]
    (if (zero? (length patterns))
      # unindexed constructor: always available
      (outcome/yes (subst/empty))
      (matches* type-args patterns ctor-name-set (subst/empty)))))

(defn ctors/available [type-args ctors ctor-name-set]
  "Filter ctors to those available at type-args.
   Returns array of {:ctor c :subst σ} for each [:yes σ] result.
   Errors on any [:stuck] result — indices must be in normal form."
  (let [out @[]]
    (each ctor ctors
      (let [r (ctor/available? type-args ctor ctor-name-set)]
        (match r
          [:yes sigma] (array/push out {:ctor ctor :subst sigma})
          [:no]        nil
          [:stuck]
          (errorf "constructor %v: availability is stuck on indices %v\nIndices must reduce to constructor form before pattern matching."
                  (ctor :name) type-args))))
    out))

# ============================================================
# EXPORTS
# ============================================================

(def exports
  {:YES YES
   :NO  NO
   :STUCK STUCK
   :outcome/yes    outcome/yes
   :outcome/no     outcome/no
   :outcome/stuck  outcome/stuck
   :outcome/yes?   outcome/yes?
   :outcome/no?    outcome/no?
   :outcome/stuck? outcome/stuck?
   :outcome/subst  outcome/subst
   :subst/empty    subst/empty
   :subst/lookup   subst/lookup
   :subst/extend   subst/extend
   :subst/merge    subst/merge
   :pat/vars       pat/vars
   :pat/to-term    pat/to-term
   :matches        matches
   :matches*       matches*
   :ctor/available?  ctor/available?
   :ctors/available  ctors/available})
