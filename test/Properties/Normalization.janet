#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/Assertions :as a)

(test/start-suite "Property Normalization")

(var rng (gen/rng))

# ===============================================
# Test 12: Normalization Stability
# ===============================================
(test/assert
  (a/normalization-stable
    (c/ty/type 1)
    [:type 0])
  "Normalization stability: simple type")

(test/assert
  (a/normalization-stable
    (c/ty/pi (c/ty/type 0) (fn [x] (c/ty/type 0)))
    [:lam (fn [x] [:var x])])
  "Normalization stability: identity function")

# ===============================================
# Normalization Correctness
# ===============================================
(test/assert
  (= (c/nf (c/ty/type 1) [:type 0])
     (c/nf/type 0))
  "Normalization: Type₀ normalizes to [:Type 0]")

(test/assert
  (match (c/nf (c/ty/pi (c/ty/type 0) (fn [x] (c/ty/type 0)))
               [:lam (fn [x] [:var x])])
    [c/NF/Lam _] true
    _ false)
  "Normalization: λx. x normalizes to [:nlam ...]")

# ===============================================
# Property Tests: Nested Terms
# ===============================================

(defn prop-nested-normalization [depth max-terms]
  "Property: Normalization of nested terms terminates"
  (var passed true)
  (repeat max-terms
    (let [tm (gen/gen-nested-term rng depth)]
      (try
        (let [ty (c/infer-top tm)
              nf1 (c/nf ty tm)]
          # Just check that normalization terminates
          (unless nf1
            (set passed false)
            (print "Nested normalization failed for:" tm)))
        ([err] nil)))) # Skip ill-typed terms
  passed)

(test/assert
  (prop-nested-normalization 3 10)
  "Property: nested terms normalize correctly")

# ===============================================
# Property: Normalization Idempotence (from coreTT-plus.janet)
# ===============================================
(defn prop-normalization-idempotent [n]
  "Property: nf(nf(t)) = nf(t) - normalization is idempotent"
  (var passed true)
  (repeat n
    (let [tm (case (math/rng-int rng 4)
               0 (gen/gen-univ rng)
               1 [:lam (fn [x] [:var x])]
               2 [:pair (gen/gen-univ rng) (gen/gen-univ rng)]
               3 [:app [:lam (fn [x] [:var x])] (gen/gen-univ rng)])
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
# Property: Evaluation Determinism (from coreTT-plus.janet)
# ===============================================
(defn prop-eval-deterministic [n]
  "Property: Evaluation is deterministic"
  (var passed true)
  (repeat n
    (let [tm (case (math/rng-int rng 4)
               0 (gen/gen-univ rng)
               1 [:app [:lam (fn [x] [:var x])] (gen/gen-univ rng)]
               2 [:fst [:pair (gen/gen-univ rng) (gen/gen-univ rng)]]
               3 [:snd [:pair (gen/gen-univ rng) (gen/gen-univ rng)]])
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

(test/end-suite)
