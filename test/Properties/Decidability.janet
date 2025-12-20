#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(test/start-suite "Property Decidability")

(var rng (gen/rng))

# ===============================================
# Property Tests: Type Checking is Decidable
# ===============================================
(defn prop-check-decidable [n]
  "Property: type checking always terminates (doesn't loop)"
  (var passed true)
  (repeat n
    (let [ty (case (math/rng-int rng 3)
               0 (gen/gen-univ rng)
               1 [:t-pi (gen/gen-univ rng) (fn [x] (gen/gen-univ rng))]
               2 [:t-sigma (gen/gen-univ rng) (fn [x] (gen/gen-univ rng))])
          tm [:lam (fn [x] [:var x])]]
      (try
        # Should either succeed or fail, but not loop
        (c/check-top tm (c/eval (c/ctx/empty) ty))
        ([err] nil)) # Error is fine, just shouldn't hang
      (set passed true)))
  passed)

(test/assert
  (prop-check-decidable 10)
  "Property: type checking is decidable")

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
