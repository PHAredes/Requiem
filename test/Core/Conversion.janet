#!/usr/bin/env janet
(import ../../src/coreTT :as c)
(import ../Utils/TestRunner :as test)

(def suite (test/start-suite "Core Conversion"))

# Test 3: Eta-Equality for Functions
# λx. f x ≡ f (when x not free in f)
(let [id-ty (c/ty/pi (c/ty/type 0) (fn [_] (c/ty/type 0)))
      f [:var "f"]
      eta-expanded [:lam (fn [x] [:app f x])]
      Γ (c/ctx/add (c/ctx/empty) "f" id-ty)]
  (test/assert suite
    (c/term-eq Γ id-ty f eta-expanded)
    "Eta-equality: λx. f x ≡ f"))

# Test 4: Eta-Equality for Pairs
# (fst p, snd p) ≡ p
(let [pair-ty (c/ty/sigma (c/ty/type 0) (fn [_] (c/ty/type 0)))
      p [:var "p"]
      eta-expanded [:pair [:fst p] [:snd p]]
      Γ (c/ctx/add (c/ctx/empty) "p" pair-ty)]
  (test/assert suite
    (c/term-eq Γ pair-ty p eta-expanded)
    "Eta-equality: (fst p, snd p) ≡ p"))

# Semantic Equality Tests
(test/assert suite
  (c/sem-eq (c/ty/type 0) (c/ty/type 0) (c/ty/type 0))
  "Semantic equality: Type₀ ≡ Type₀")

(test/assert suite
  (not (c/sem-eq (c/ty/type 0) (c/ty/type 0) (c/ty/type 1)))
  "Semantic inequality: Type₀ ≢ Type₁")

(let [f1 (fn [x] x)
      f2 (fn [x] x)
      ty (c/ty/pi (c/ty/type 0) (fn [x] (c/ty/type 0)))]
  (test/assert suite
    (c/sem-eq ty f1 f2)
    "Semantic equality: extensional function equality"))

(test/end-suite suite)
