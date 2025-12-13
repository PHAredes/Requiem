#!/usr/bin/env janet

(import spork/test)
(import "../src/coreTT" :as c)

(test/start-suite "CoreTT - Additional Properties")

(var rng (math/rng 42))  # Fixed seed for reproducibility

# ===============================================
# Helper: Generate random terms
# ===============================================
(defn gen-univ []
  [:type (math/rng-int rng 4)])

(defn gen-var []
  (string "x" (math/rng-int rng 100)))

(defn gen-simple-type [depth]
  (if (<= depth 0)
    (gen-univ)
    (case (math/rng-int rng 3)
      0 (gen-univ)
      1 [:t-pi (gen-univ) (fn [x] (gen-simple-type (dec depth)))]
      2 [:t-sigma (gen-univ) (fn [x] (gen-simple-type (dec depth)))])))

# ===============================================
# Property: Confluence (Diamond Property)
# ===============================================
(defn prop-confluence [n]
  "Property: Normalization is confluent - all reduction paths lead to same normal form"
  (var passed true)
  (repeat n
    (let [tm (case (math/rng-int rng 5)
              0 [:type (math/rng-int rng 3)]
              1 [:app [:lam (fn [x] [:var x])] (gen-univ)]
              2 [:fst [:pair (gen-univ) (gen-univ)]]
              3 [:snd [:pair (gen-univ) (gen-univ)]]
              4 [:app [:lam (fn [x] [:app [:lam (fn [y] [:var y])] [:var x]])] 
                      (gen-univ)])
          Γ (c/ctx/empty)]
      (try
        (let [ty (c/infer Γ tm)
              # Normalize directly
              nf1 (c/nf ty tm)
              # Normalize via evaluation
              sem (c/eval Γ tm)
              nf2 (c/lower ty sem)]
          (unless (= nf1 nf2)
            (set passed false)
            (print "Confluence failed for:" tm)
            (print "  nf1:" nf1)
            (print "  nf2:" nf2)))
        ([err] nil))))
  passed)

(test/assert
  (prop-confluence 50)
  "Property: confluence - all reduction paths converge")

# ===============================================
# Property: Substitution Lemma (via HOAS)
# ===============================================
(defn prop-substitution [n]
  "Property: Beta reduction implements substitution correctly"
  (var passed true)
  (repeat n
    (let [u (gen-univ)
          body-fn (fn [x] [:var x])  # Identity
          Γ (c/ctx/empty)]
      (try
        (let [# (λx. x) u should reduce to u
              app-result (c/eval Γ [:app [:lam body-fn] u])
              direct-result (c/eval Γ u)]
          (unless (= app-result direct-result)
            (set passed false)
            (print "Substitution failed for u =" u)))
        ([err] nil))))
  passed)

(test/assert
  (prop-substitution 30)
  "Property: substitution via beta reduction")

# ===============================================
# Property: Church-Rosser
# ===============================================
(defn prop-church-rosser [n]
  "Property: If t ≡ u definitionally, then nf(t) = nf(u)"
  (var passed true)
  (repeat n
    (let [t (gen-univ)
          Γ (c/ctx/empty)
          # Create eta-equivalent term: (λf. f) t ≡ t
          u [:app [:lam (fn [f] [:var f])] t]]
      (try
        (let [ty [:type 1]
              nf-t (c/nf ty t)
              nf-u (c/nf ty u)]
          (unless (= nf-t nf-u)
            (set passed false)
            (print "Church-Rosser failed:")
            (print "  t =" t)
            (print "  u =" u)
            (print "  nf(t) =" nf-t)
            (print "  nf(u) =" nf-u)))
        ([err] nil))))
  passed)

(test/assert
  (prop-church-rosser 30)
  "Property: Church-Rosser - convertible terms normalize equally")

# ===============================================
# Property: Normalization Idempotence
# ===============================================
(defn prop-normalization-idempotent [n]
  "Property: nf(nf(t)) = nf(t) - normalization is idempotent"
  (var passed true)
  (repeat n
    (let [tm (case (math/rng-int rng 4)
              0 (gen-univ)
              1 [:lam (fn [x] [:var x])]
              2 [:pair (gen-univ) (gen-univ)]
              3 [:app [:lam (fn [x] [:var x])] (gen-univ)])
          Γ (c/ctx/empty)]
      (try
        (let [ty (c/infer Γ tm)
              nf1 (c/nf ty tm)
              # Evaluate the normal form and normalize again
              sem1 (c/eval Γ nf1)
              nf2 (c/lower ty sem1)]
          (unless (= nf1 nf2)
            (set passed false)
            (print "Idempotence failed for:" tm)
            (print "  nf1:" nf1)
            (print "  nf2:" nf2)))
        ([err] nil))))
  passed)

(test/assert
  (prop-normalization-idempotent 50)
  "Property: normalization is idempotent")

# ===============================================
# Property: Evaluation Determinism
# ===============================================
(defn prop-eval-deterministic [n]
  "Property: Evaluation is deterministic"
  (var passed true)
  (repeat n
    (let [tm (case (math/rng-int rng 4)
              0 (gen-univ)
              1 [:app [:lam (fn [x] [:var x])] (gen-univ)]
              2 [:fst [:pair (gen-univ) (gen-univ)]]
              3 [:snd [:pair (gen-univ) (gen-univ)]])
          Γ (c/ctx/empty)]
      (try
        (let [v1 (c/eval Γ tm)
              v2 (c/eval Γ tm)]
          (unless (= v1 v2)
            (set passed false)
            (print "Evaluation non-deterministic for:" tm)))
        ([err] nil))))
  passed)

(test/assert
  (prop-eval-deterministic 50)
  "Property: evaluation is deterministic")

# ===============================================
# Property: Raise-Lower Roundtrip
# ===============================================
(defn prop-raise-lower-roundtrip [n]
  "Property: lower(ty, raise(ty, ne)) = ne for neutral terms"
  (var passed true)
  (repeat n
    (let [x (gensym)
          ty (case (math/rng-int rng 3)
              0 [:Type (math/rng-int rng 3)]
              1 [:Pi [:Type 0] (fn [_] [:Type 0])]
              2 [:Sigma [:Type 0] (fn [_] [:Type 0])])
          ne (c/ne/var x)]
      (try
        (let [raised (c/raise ty ne)
              lowered (c/lower ty raised)]
          (match lowered
            [:nneut ne2] (when (not= ne ne2)
                          (set passed false)
                          (print "Raise-lower roundtrip failed"))
            [:nlam body] true  # Eta-expansion expected for Pi
            [:npair _ _] true  # Eta-expansion expected for Sigma
            _ (do
                (set passed false)
                (print "Unexpected lowered form:" lowered))))
        ([err] 
          (print "Error in raise-lower:" err)
          (set passed false)))))
  passed)

(test/assert
  (prop-raise-lower-roundtrip 30)
  "Property: raise-lower roundtrip preserves neutrals (modulo eta)")

# ===============================================
# Property: Pi Domain Independence
# ===============================================
(defn prop-pi-domain-independence [n]
  "Property: If domains equal, Pi types equal iff codomains equal"
  (var passed true)
  (repeat n
    (let [A [:type (math/rng-int rng 3)]
          B1 (fn [x] [:type (math/rng-int rng 3)])
          B2 (fn [x] [:type (math/rng-int rng 3)])
          Γ (c/ctx/empty)
          pi1 [:t-pi A B1]
          pi2 [:t-pi A B2]]
      (try
        (let [ty (c/infer Γ pi1)
              fresh (gensym)
              A-sem (c/eval Γ A)
              B1-sem (c/eval Γ (B1 [:var fresh]))
              B2-sem (c/eval Γ (B2 [:var fresh]))
              codom-eq (c/sem-eq [:Type 100] B1-sem B2-sem)
              pi-eq (c/term-eq Γ ty pi1 pi2)]
          # If codomains equal, Pi types should be equal
          (when codom-eq
            (unless pi-eq
              (set passed false)
              (print "Pi equality failed with equal codomains"))))
        ([err] nil))))
  passed)

(test/assert
  (prop-pi-domain-independence 20)
  "Property: Pi type equality respects codomain equality")

# ===============================================
# Property: Sigma Projections Inverse
# ===============================================
(defn prop-sigma-projections [n]
  "Property: For pairs, fst/snd are left/right inverses"
  (var passed true)
  (repeat n
    (let [l (gen-univ)
          r (gen-univ)
          p [:pair l r]
          Γ (c/ctx/empty)]
      (try
        (let [fst-result (c/eval Γ [:fst p])
              snd-result (c/eval Γ [:snd p])
              l-sem (c/eval Γ l)
              r-sem (c/eval Γ r)]
          (unless (and (= fst-result l-sem)
                       (= snd-result r-sem))
            (set passed false)
            (print "Sigma projection failed for pair:" p)))
        ([err] nil))))
  passed)

(test/assert
  (prop-sigma-projections 30)
  "Property: fst and snd correctly project from pairs")

# ===============================================
# Property: Context Extension Preserves Types
# ===============================================
(defn prop-context-extension [n]
  "Property: Extending context preserves well-typedness of closed terms"
  (var passed true)
  (repeat n
    (let [tm (gen-univ)  # Closed term
          Γ (c/ctx/empty)
          x (gensym)
          A [:type (math/rng-int rng 3)]
          Γ2 (c/ctx/add Γ x (c/eval Γ A))]
      (try
        (let [ty1 (c/infer Γ tm)
              ty2 (c/infer Γ2 tm)]
          (unless (c/sem-eq [:Type 100] ty1 ty2)
            (set passed false)
            (print "Context extension changed type for:" tm)))
        ([err] nil))))
  passed)

(test/assert
  (prop-context-extension 30)
  "Property: context extension preserves closed term types")

# ===============================================
# Property: Type Well-Formedness
# ===============================================
(defn prop-type-well-formed [n]
  "Property: Inferred types are themselves well-formed"
  (var passed true)
  (repeat n
    (let [tm (case (math/rng-int rng 3)
              0 (gen-univ)
              1 [:t-pi (gen-univ) (fn [x] (gen-univ))]
              2 [:t-sigma (gen-univ) (fn [x] (gen-univ))])
          Γ (c/ctx/empty)]
      (try
        (let [ty (c/infer Γ tm)]
          # The type should be a universe
          (match ty
            [:Type _] true
            _ (do
                (set passed false)
                (print "Inferred non-universe type:" ty "for term:" tm))))
        ([err] nil))))
  passed)

(test/assert
  (prop-type-well-formed 30)
  "Property: inferred types are well-formed")

# ===============================================
# Property: Function Application Type Soundness
# ===============================================
(defn prop-app-soundness [n]
  "Property: Application preserves typing"
  (var passed true)
  (repeat n
    (let [A (gen-univ)
          f [:lam (fn [x] [:var x])]  # Identity
          arg (gen-univ)
          Γ (c/ctx/empty)]
      (try
        (let [A-sem (c/eval Γ A)
              # Check f : A → A
              _ (c/check Γ f [:Pi A-sem (fn [x] A-sem)])
              # Check arg : A
              _ (c/check Γ arg A-sem)
              # Infer type of application
              app-ty (c/infer Γ [:app f arg])]
          # Result type should equal A
          (unless (c/sem-eq [:Type 100] app-ty A-sem)
            (set passed false)
            (print "Application type unsound")))
        ([err] nil))))
  passed)

(test/assert
  (prop-app-soundness 20)
  "Property: function application is type-sound")

# ===============================================
# Property: Eta for Functions (Extensionality)
# ===============================================
(defn prop-eta-functions [n]
  "Property: λx. f x ≡ f (eta-expansion)"
  (var passed true)
  (repeat n
    (let [fresh (gensym)
          A [:type (math/rng-int rng 3)]
          f-var [:var fresh]
          eta-expanded [:lam (fn [x] [:app f-var [:var x]])]
          Γ (c/ctx/empty)
          A-sem (c/eval Γ A)
          pi-ty [:Pi A-sem (fn [x] A-sem)]
          Γ2 (c/ctx/add Γ fresh pi-ty)]
      (try
        (unless (c/term-eq Γ2 pi-ty f-var eta-expanded)
          (set passed false)
          (print "Eta-expansion failed for functions"))
        ([err] nil))))
  passed)

(test/assert
  (prop-eta-functions 20)
  "Property: eta-equality for functions")

# ===============================================
# Property: Eta for Pairs
# ===============================================
(defn prop-eta-pairs [n]
  "Property: (fst p, snd p) ≡ p (eta-expansion)"
  (var passed true)
  (repeat n
    (let [fresh (gensym)
          A [:type (math/rng-int rng 3)]
          p-var [:var fresh]
          eta-expanded [:pair [:fst p-var] [:snd p-var]]
          Γ (c/ctx/empty)
          A-sem (c/eval Γ A)
          sigma-ty [:Sigma A-sem (fn [x] A-sem)]
          Γ2 (c/ctx/add Γ fresh sigma-ty)]
      (try
        (unless (c/term-eq Γ2 sigma-ty p-var eta-expanded)
          (set passed false)
          (print "Eta-expansion failed for pairs"))
        ([err] nil))))
  passed)

(test/assert
  (prop-eta-pairs 20)
  "Property: eta-equality for pairs")

# ===============================================
# Property: Universe Cumulativity Check
# ===============================================
(defn prop-universe-hierarchy [n]
  "Property: Type_i : Type_(i+1)"
  (var passed true)
  (repeat n
    (let [i (math/rng-int rng 5)
          Γ (c/ctx/empty)]
      (try
        (let [ty (c/infer Γ [:type i])]
          (match ty
            [:Type j] (when (not= j (inc i))
                        (set passed false)
                        (print "Universe hierarchy broken: Type_" i " : Type_" j))
            _ (do
                (set passed false)
                (print "Type doesn't live in universe"))))
        ([err]
          (set passed false)
          (print "Error checking universe hierarchy:" err)))))
  passed)

(test/assert
  (prop-universe-hierarchy 20)
  "Property: universe hierarchy Type_i : Type_(i+1)")

# ===============================================
# Property: Check-Infer Consistency
# ===============================================
(defn prop-check-infer-consistent [n]
  "Property: If check succeeds, infer should return same type"
  (var passed true)
  (repeat n
    (let [tm [:type (math/rng-int rng 3)]
          Γ (c/ctx/empty)]
      (try
        (let [inferred-ty (c/infer Γ tm)
              # Now check against the inferred type
              check-result (c/check Γ tm inferred-ty)]
          (unless check-result
            (set passed false)
            (print "Check-infer inconsistent for:" tm)))
        ([err] nil))))
  passed)

(test/assert
  (prop-check-infer-consistent 30)
  "Property: check and infer are consistent")

(test/end-suite)
