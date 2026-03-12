#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)

(def suite (test/start-suite "Type Pi"))

# Test 9: Pi Type Formation (from coreTT.janet)
(let [pi-type [:t-pi
               [:type 0]
               (fn [x] [:type 0])]]
  (test/assert suite
    (= (c/infer-top pi-type) (c/ty/type 1))
    "Pi formation: (Type₀ → Type₀) : Type₁"))

(let [pi-type [:t-pi
               [:type 0]
               (fn [x] [:type 1])]]
  (test/assert suite
    (= (c/infer-top pi-type) (c/ty/type 2))
    "Pi formation: (Type₀ → Type₁) : Type₂ (max rule)"))

# Test 11: Dependent Function Types (from coreTT.janet)
(let [dep-fn-type [:t-pi
                   [:type 0]
                   (fn [A] [:t-pi A (fn [x] A)])]
      expected (c/ty/type 1)]
  (test/assert suite
    (= (c/infer-top dep-fn-type) expected)
    "Dependent function: ∀(A : Type₀). A → A"))

(let [id-ty (c/ty/pi (c/ty/type 0) (fn [A] (c/ty/pi A (fn [_] A))))
      id-fn [:lam (fn [_] [:lam (fn [x] x)])]]
  (test/assert suite
    (c/check-top id-fn id-ty)
    "Lambda checks against dependent Pi via shared binder helper"))

(test/end-suite suite)
