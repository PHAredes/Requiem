#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)

(test/start-suite "Core Conversion")

# ===============================================
# Test 3: Eta-Equality for Functions
# ===============================================
# λx. f x ≡ f (when x not free in f)
(let [id-ty (c/tm/pi [:type 0] (fn [x] [:type 0]))
      f [:var "f"]
      eta-expanded [:lam (fn [x] [:app f x])]
      Γ (c/ctx/add (c/ctx/empty) "f" id-ty)]
  (test/assert
    (c/term-eq Γ id-ty f eta-expanded)
    "Eta-equality: λx. f x ≡ f"))

# ===============================================
# Test 4: Eta-Equality for Pairs
# ===============================================
# (fst p, snd p) ≡ p
(let [pair-ty (c/tm/sigma [:type 0] (fn [x] [:type 0]))
      p [:var "p"]
      eta-expanded [:pair [:fst p] [:snd p]]
      Γ (c/ctx/add (c/ctx/empty) "p" pair-ty)]
  (test/assert
    (c/term-eq Γ pair-ty p eta-expanded)
    "Eta-equality: (fst p, snd p) ≡ p"))

# ===============================================
# Semantic Equality Tests
# ===============================================
(test/assert
  (c/sem-eq [:Type 0] [:Type 0] [:Type 0])
  "Semantic equality: Type₀ ≡ Type₀")

(test/assert
  (not (c/sem-eq [:Type 0] [:Type 0] [:Type 1]))
  "Semantic inequality: Type₀ ≢ Type₁")

(let [f1 (fn [x] x)
      f2 (fn [x] x)
      ty [:Pi [:Type 0] (fn [x] [:Type 0])]]
  (test/assert
    (c/sem-eq ty f1 f2)
    "Semantic equality: extensional function equality"))

(test/end-suite)
