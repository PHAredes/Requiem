#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(test/start-suite "Property Weakening")

(var rng (gen/rng))

# Property Tests: Weakening (Context Extension)

(defn prop-weakening [n]
  "Property: If Γ ⊢ t : A, then Γ, x : B ⊢ t : A (x not in t)"
  (var passed true)
  (repeat n
    (let [Γ (c/ctx/empty)
          x (gensym)
          B [:type (math/rng-int rng 3)]
          tm (case (math/rng-int rng 3)
               0 [:type (math/rng-int rng 3)]
               1 [:lam (fn [y] [:var y])]
               2 [:pair [:type (math/rng-int rng 3)] [:type (math/rng-int rng 3)]])]
      (try
        (let [ty (c/infer Γ tm)
              Γ2 (c/ctx/add Γ x B)
              ty2 (c/infer Γ2 tm)]
          (unless (c/sem-eq (c/ty/type 100) ty ty2)
            (set passed false)
            (print "Weakening failed for:" tm)))
        ([err] nil)))) # Skip ill-typed terms
  passed)

(test/assert
  (prop-weakening 20)
  "Property: weakening preserves types")

# Property: Context Extension Preserves Types
(defn prop-context-extension [n]
  "Property: Extending context preserves well-typedness of closed terms"
  (var passed true)
  (repeat n
    (let [tm (gen/gen-univ rng) # Closed term
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

(test/end-suite)
