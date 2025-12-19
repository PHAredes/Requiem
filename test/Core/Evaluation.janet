#!/usr/bin/env janet

(import spork/test)
(import ../../src/coreTT :as c)

(test/start-suite "Core Evaluation")

# ===============================================
# Test 1: Semantic Domain Separation
# ===============================================
(test/assert
  (= (c/eval (c/ctx/empty) [:type 0]) [:Type 0])
  "eval returns semantic universe [:Type 0], not [:nType 0]")

(test/assert
  (function? (c/eval (c/ctx/empty) [:lam (fn [x] [:var x])]))
  "eval returns Janet function for lambda")

(test/assert
  (= (c/eval (c/ctx/empty) [:pair [:type 0] [:type 1]])
     [[:Type 0] [:Type 1]])
  "eval returns Janet pair for semantic pair")

# ===============================================
# Test 6: Beta-Reduction
# ===============================================
# (λx. t) u ≡ t[u/x]
(let [id (fn [x] [:var x])
      Γ (c/ctx/empty)
      app-result (c/eval Γ [:app [:lam id] [:type 0]])
      direct-result (c/eval Γ [:type 0])]
  (test/assert
    (= app-result direct-result)
    "Beta-reduction: (λx. x) Type₀ ≡ Type₀"))

# ===============================================
# Test 7: Pair Projections
# ===============================================
(let [Γ (c/ctx/empty)]
  (test/assert
    (= (c/eval Γ [:fst [:pair [:type 0] [:type 1]]])
       [:Type 0])
    "Projection: fst (a, b) ≡ a")

  (test/assert
    (= (c/eval Γ [:snd [:pair [:type 0] [:type 1]]])
       [:Type 1])
    "Projection: snd (a, b) ≡ b"))

# ===============================================
# Variable Handling
# ===============================================
(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "x" [:type 0])]
  (test/assert
    (= (c/eval Γ1 [:var "x"]) [:neutral [:nvar "x"]])
    "String variables evaluate to neutrals"))

(let [Γ (c/ctx/empty)
      fresh (gensym)
      Γ1 (c/ctx/add Γ fresh [:type 0])]
  (test/assert
    (= (c/eval Γ1 [:var fresh]) [:neutral [:nvar fresh]])
    "Symbol variables (gensyms) evaluate to neutrals"))

(test/end-suite)
