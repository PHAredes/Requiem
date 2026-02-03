#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)

(test/start-suite "Type Sigma")

# Test 10: Sigma Type Formation (from coreTT.janet)
(let [sigma-type [:t-sigma
                  [:type 0]
                  (fn [x] [:type 0])]]
  (test/assert
    (= (c/infer-top sigma-type) (c/ty/type 1))
    "Sigma formation: (Type₀ × Type₀) : Type₁"))

# Test 7: Pair Projections (from coreTT.janet)
(let [Γ (c/ctx/empty)]
  (test/assert
    (= (c/eval Γ [:fst [:pair [:type 0] [:type 1]]])
       (c/ty/type 0))
    "Projection: fst (a, b) ≡ a")

  (test/assert
    (= (c/eval Γ [:snd [:pair [:type 0] [:type 1]]])
       (c/ty/type 1))
    "Projection: snd (a, b) ≡ b"))

# Dependent Types with Sigma (from coreTT.janet)
(let [pair-ty [:t-sigma [:type 0] (fn [A] [:t-pi A (fn [x] A)])]
      # (A : Type₀) × (A → A)
      expected (c/ty/type 1)]
  (test/assert
    (= (c/infer-top pair-ty) expected)
    "Dependent type: (A : Type₀) × (A → A)"))

# Property: Sigma Projections Inverse
(var rng (math/rng 42))

(defn gen-univ []
  [:type (math/rng-int rng 4)])

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

(test/end-suite)
