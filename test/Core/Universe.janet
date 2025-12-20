#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(test/start-suite "Core Universe")

(var rng (gen/rng))

# ===============================================
# Test 8: Universe Levels
# ===============================================
(test/assert
  (= (c/infer-top [:type 0]) [:Type 1])
  "Universe hierarchy: Type₀ : Type₁")

(test/assert
  (= (c/infer-top [:type 5]) [:Type 6])
  "Universe hierarchy: Type₅ : Type₆")

# ===============================================
# Property Tests: Universe Hierarchy
# ===============================================
(defn prop-universe-hierarchy [n]
  "Property: Type_l : Type_(l+1)"
  (var passed true)
  (repeat n
    (let [l (math/rng-int rng 5)]
      (try
        (let [ty (c/infer-top [:type l])]
          # Check that Type_l : Type_(l+1)
          (unless (c/sem-eq [:Type 100] ty [:Type (inc l)])
            (set passed false)
            (print "Universe hierarchy failed for Type_" l)))
        ([err]
          (set passed false)
          (print "Error in universe hierarchy")))))
  passed)

(test/assert
  (prop-universe-hierarchy 10)
  "Property: universe hierarchy")

# ===============================================
# Property: Universe Cumulativity Check (from coreTT-plus.janet)
# ===============================================
(defn prop-universe-hierarchy-strict [n]
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
  (prop-universe-hierarchy-strict 20)
  "Property: universe hierarchy Type_i : Type_(i+1)")

(test/end-suite)
