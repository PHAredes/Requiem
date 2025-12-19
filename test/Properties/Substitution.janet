#!/usr/bin/env janet

(import spork/test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(test/start-suite "Property Substitution")

(var rng (gen/rng))

# ===============================================
# Property: Substitution Lemma (via HOAS)
# ===============================================
(defn prop-substitution [n]
  "Property: Beta reduction implements substitution correctly"
  (var passed true)
  (repeat n
    (let [u (gen/gen-univ rng)
          body-fn (fn [x] [:var x]) # Identity
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

(test/end-suite)
