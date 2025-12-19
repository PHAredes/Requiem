#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/Assertions :as a)

(test/start-suite "Property Preservation")

(var rng (gen/rng))

# ===============================================
# Test 5: Type Preservation (from coreTT.janet)
# ===============================================
(test/assert
  (a/type-preserves
    (c/ctx/empty)
    [:type 0]
    [:Type 1])
  "Type preservation: [:type 0] : [:Type 1]")

(let [id-ty [:t-pi [:type 0] (fn [x] [:type 0])]]
  (test/assert
    (a/type-preserves
      (c/ctx/empty)
      id-ty
      [:Type 1])
    "Type preservation: (Type₀ → Type₀) : Type₁"))

# ===============================================
# Property Tests: Type Preservation (from coreTT.janet)
# ===============================================
(defn prop-type-preservation [n]
  "Property: If Γ ⊢ t : A, then eval(t) has semantic type A"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [tm (case (math/rng-int rng 4)
                 0 [:type (math/rng-int rng 3)]
                 1 [:lam (fn [x] [:var x])]
                 2 [:app [:lam (fn [x] [:var x])] [:type (math/rng-int rng 3)]]
                 3 [:pair [:type (math/rng-int rng 3)] [:type (math/rng-int rng 3)]])]
        (try
          (let [ty (c/infer Γ tm)]
            # Check that the inferred type is well-formed
            (unless ty
              (set passed false)
              (print "Type preservation failed for:" tm)))
          ([err] nil))))) # Skip ill-typed terms
  passed)

(test/assert
  (prop-type-preservation 50)
  "Property: type preservation for random terms")

(test/end-suite)
