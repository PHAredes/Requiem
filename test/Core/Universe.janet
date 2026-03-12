#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(def suite (test/start-suite "Core Universe"))

(var rng (gen/rng 42))

# Test 8: Universe Levels
# Test 8: Universe Levels
(test/assert suite
  (= (c/infer-top [:type 0]) [c/T/Type 1])
  "Universe hierarchy: Type₀ : Type₁")

(test/assert suite
  (= (c/infer-top [:type 5]) [c/T/Type 6])
  "Universe hierarchy: Type₅ : Type₆")

(test/assert suite
  (c/check-top [:type 0] (c/ty/type 3))
  "Cumulativity: Type₀ checks against Type₃")

(test/assert-error suite
  (fn [] (c/check-top [:type 3] (c/ty/type 1)))
  "Cumulativity is not symmetric")

(test/assert suite
  (c/subtype (c/ty/type 0) (c/ty/type 4))
  "Subtype: Type₀ <: Type₄")

(test/assert suite
  (not (c/subtype (c/ty/type 4) (c/ty/type 0)))
  "Subtype: Type₄ is not a subtype of Type₀")

# Property Tests: Universe Hierarchy
(defn prop-universe-hierarchy [n]
  "Property: Type_l : Type_(l+1)"
  (var passed true)
  (repeat n
    (let [l (math/rng-int rng 5)]
      (try
        (let [ty (c/infer-top [:type l])]
          # Check that Type_l : Type_(l+1)
          (unless (c/sem-eq [c/T/Type 100] ty [c/T/Type (inc l)])
            (set passed false)
            (print "Universe hierarchy failed for Type_" l)))
        ([err]
          (set passed false)
          (print "Error in universe hierarchy")))))
  passed)

(test/assert suite
  (prop-universe-hierarchy 10)
  "Property: universe hierarchy")

# Property: Universe Cumulativity Check
(defn prop-universe-hierarchy-strict [n]
  "Property: Type_i : Type_(i+1)"
  (var passed true)
  (repeat n
    (let [i (math/rng-int rng 5)
          Γ (c/ctx/empty)]
      (try
        (let [ty (c/infer Γ [:type i])
              tag (if (tuple? ty) (get ty 0) 0)]
          (if (= tag c/T/Type)
            (let [j (get ty 1)]
              (when (not= j (inc i))
                (set passed false)
                (print "Universe hierarchy broken: Type_" i " : Type_" j)))
            (do
              (set passed false)
              (print "Type doesn't live in universe"))))
        ([err]
          (set passed false)
          (print "Error checking universe hierarchy:" err)))))
  passed)

(test/assert suite
  (prop-universe-hierarchy-strict 20)
  "Property: universe hierarchy Type_i : Type_(i+1)")

# Property: cumulative universe subsumption chains
(defn prop-universe-subsumption-chains [n]
  "Property: Type_i <: Type_j <: Type_k implies Type_i <: Type_k"
  (var passed true)
  (repeat n
    (let [i (math/rng-int rng 6)
          d1 (inc (math/rng-int rng 4))
          d2 (inc (math/rng-int rng 4))
          j (+ i d1)
          k (+ j d2)
          Ti (c/ty/type i)
          Tj (c/ty/type j)
          Tk (c/ty/type k)]
      (try
        (unless (and (c/subtype Ti Ti)
                     (c/subtype Ti Tj)
                     (c/subtype Tj Tk)
                     (c/subtype Ti Tk)
                     (not (c/subtype Tk Ti)))
          (set passed false)
          (print "Universe subsumption chain failed:" i j k))
        ([err]
          (set passed false)
          (print "Universe subsumption chain error:" err)))))
  passed)

(test/assert suite
  (prop-universe-subsumption-chains 40)
  "Property: cumulative universe subsumption chains")

(test/end-suite suite)
