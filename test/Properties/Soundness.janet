#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(test/start-suite "Property Soundness")

(var rng (gen/rng))

# ===============================================
# Property: Function Application Type Soundness
# ===============================================
(defn prop-app-soundness [n]
  "Property: Application preserves typing"
  (var passed true)
  (repeat n
    (let [A (gen/gen-univ rng)
          f [:lam (fn [x] [:var x])] # Identity
          arg (gen/gen-univ rng)
          Γ (c/ctx/empty)]
      (try
        (let [A-sem (c/eval Γ A)
              # Check f : A → A
              _ (c/check Γ f (c/ty/pi A-sem (fn [x] A-sem)))
              # Check arg : A
              _ (c/check Γ arg A-sem)
              # Infer type of application
              app-ty (c/infer Γ [:app f arg])]
          # Result type should equal A
          (unless (c/sem-eq (c/ty/type 100) app-ty A-sem)
            (set passed false)
            (print "Application type unsound")))
        ([err] nil))))
  passed)

(test/assert
  (prop-app-soundness 20)
  "Property: function application is type-sound")

# ===============================================
# Property: Type Well-Formedness
# ===============================================
(defn prop-type-well-formed [n]
  "Property: Inferred types are themselves well-formed"
  (var passed true)
  (repeat n
    (let [tm (case (math/rng-int rng 3)
               0 (gen/gen-univ rng)
               1 [:t-pi (gen/gen-univ rng) (fn [x] (gen/gen-univ rng))]
               2 [:t-sigma (gen/gen-univ rng) (fn [x] (gen/gen-univ rng))])
          Γ (c/ctx/empty)]
      (try
        (let [ty (c/infer Γ tm)]
          # The type should be a universe
          (match ty
            [c/T/Type _] true
            _ (do
                (set passed false)
                (print "Inferred non-universe type:" ty "for term:" tm))))
        ([err] nil))))
  passed)

(test/assert
  (prop-type-well-formed 30)
  "Property: inferred types are well-formed")

(test/end-suite)
