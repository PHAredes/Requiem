#!/usr/bin/env janet

# sig.janet
#
# Signature management.
#
# The signature Σ holds every declared name and what the elaborator
# needs to know about it:
#   - data type: params, sort, constructors (with their selector patterns)
#   - function:  params, result type, full Pi type
#
# Two operations per function (from elegant-elaboration paper §3.2):
#   params(Γ, f) → Δ       the parameter telescope
#   typeOf(Γ, f) → A       the full type (Pi over Δ, then result)
#
# And exact-application (FuncRef rule, §3.2):
#   f → lambda(f vars(Δ), Δ)
# Every bare function reference immediately eta-expands to its fully-applied form.
# coreTT reduces it via β as arguments arrive.

(import ./matches :as m)
(import ./coreTT :as tt)

# ============================================================
# SIGNATURE ENTRIES
# ============================================================

(defn sig/empty [] @{})

# Add a data type declaration to the signature.
#
# ctors: array of
#   {:name    string
#    :patterns array of pat  -- selector patterns (from ctor arm LHS)
#    :params  array of binder -- constructor fields (from ctor arm RHS)
#    :type    coreTT-term    -- full encoded type (for exact-ref)}
(defn sig/add-data [sig name params sort ctors]
  (let [entry {:kind    :data
               :name    name
               :params  params
               :sort    sort
               :ctors   ctors}]
    (put sig name entry)
    sig))

# Add a function/operator declaration to the signature.
#
# params:  array of binder (name + type)
# result:  return type coreTT term
# type:    full Pi type (for exact-ref and typeOf)
(defn sig/add-func [sig name params result core-type]
  (let [entry {:kind    :func
               :name    name
               :params  params
               :result  result
               :type    core-type}]
    (put sig name entry)
    sig))

# ============================================================
# LOOKUPS
# ============================================================

(defn sig/entry [sig name]
  (or (get sig name)
      (errorf "sig/entry: unknown name '%v'\nDeclare it before use." name)))

(defn sig/params [sig name]
  ((sig/entry sig name) :params))

(defn sig/type-of [sig name]
  (let [e (sig/entry sig name)]
    (match (e :kind)
      :func (e :type)
      :data (e :sort)
      _ (errorf "sig/type-of: unexpected kind for '%v'" name))))

(defn sig/ctors [sig data-name]
  (let [e (sig/entry sig data-name)]
    (when (not= (e :kind) :data)
      (errorf "sig/ctors: '%v' is not a data type" data-name))
    (e :ctors)))

(defn sig/ctor [sig data-name ctor-name]
  (let [ctors (sig/ctors sig data-name)]
    (or (find |(= ($ :name) ctor-name) ctors)
        (errorf "sig/ctor: unknown constructor '%v' in '%v'" ctor-name data-name))))

# Build the set of all constructor names across all data types.
# Used by matches to distinguish constructors from variables.
(defn sig/ctor-name-set [sig]
  (let [out @{}]
    (eachp [_ entry] sig
      (when (= (entry :kind) :data)
        (each ctor (entry :ctors)
          (put out (ctor :name) true))))
    out))

# ============================================================
# EXACT APPLICATION  (FuncRef rule from elegant-elaboration §3.2)
# ============================================================
#
# Every bare function reference f in the source elaborates to:
#   lambda(f vars(Δ), Δ)
# where Δ = params(Σ, f).
#
# This guarantees functions are always exactly-applied in coreTT.
# When arguments arrive via APP, coreTT immediately β-reduces.
#
# For f with params [x:A, y:B]:
#   vars(Δ) = [x, y]
#   f vars(Δ) = f x y  (exactly-applied spine)
#   lambda(f x y, Δ) = λx. λy. (f x y)

(defn vars [delta]
  "Extract variable names from a parameter telescope."
  (map |($ :name) delta))

(defn app-spine [name args]
  "Build exactly-applied coreTT term: (f a1 a2 ... an)"
  (reduce (fn [acc arg] (tt/tm/app acc (tt/tm/var arg)))
          (tt/tm/var name)
          args))

(defn build-lambda [body delta]
  "Wrap body in lambdas for each binder in delta (left to right)."
  (reduce (fn [inner binder]
            (tt/tm/lam (fn [_] inner)))   # HOAS: body is closed over binder value
          body
          (reverse delta)))

(defn sig/exact-ref [sig name]
  "FuncRef rule: elaborate bare function name to eta-expanded, exactly-applied form."
  (let [delta (sig/params sig name)
       vs    (vars delta)
       spine (app-spine name vs)]
    (build-lambda spine delta)))

# ============================================================
# CONSTRUCTOR AVAILABILITY
# ============================================================
#
# Given a data type applied to some index terms (type-args),
# return the constructors available at those indices.
#
# This is used by:
#   - IxCall: when the user writes a constructor, check it's available
#   - Coverage: enumerate available constructors for exhaustiveness

(defn sig/available-ctors [sig data-name type-args]
  (let [ctors (sig/ctors sig data-name)
        ctor-names (sig/ctor-name-set sig)]
    (m/ctors/available type-args ctors ctor-names)))

# ============================================================
# BUILD SIGNATURE FROM ELABORATED DECLARATIONS
# ============================================================
#
# Called once per declaration, in order.
# Latter declarations may refer to earlier ones.

(defn sig/process-decl [sig decl]
  "Add a single elaborated declaration to the signature.
   decl is a CST/elaborated form, not yet fully coreTT."
  (match decl
    [:core/data name params sort ctors]
    (sig/add-data sig name params sort ctors)

    [:core/func name params result core-type _clauses]
    (sig/add-func sig name params result core-type)

    _
    (do (eprintf "sig/process-decl: ignoring unknown decl form %v" (decl 0))
        sig)))

(defn sig/build [decls]
  "Build a complete signature from a list of elaborated declarations."
  (reduce sig/process-decl (sig/empty) decls))

# ============================================================
# EXPORTS
# ============================================================

(def exports
  {:sig/empty          sig/empty
   :sig/add-data       sig/add-data
   :sig/add-func       sig/add-func
   :sig/entry          sig/entry
   :sig/params         sig/params
   :sig/type-of        sig/type-of
   :sig/ctors          sig/ctors
   :sig/ctor           sig/ctor
   :sig/ctor-name-set  sig/ctor-name-set
   :sig/exact-ref      sig/exact-ref
   :sig/available-ctors sig/available-ctors
   :sig/build          sig/build
   :vars               vars
   :app-spine          app-spine
   :build-lambda       build-lambda})
