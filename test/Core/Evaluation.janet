#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)

(def suite (test/start-suite "Core Evaluation"))

# Test 1: Semantic Domain Separation
(test/assert suite
  (= (c/eval (c/ctx/empty) [:type 0]) (c/ty/type 0))
  "eval returns semantic universe [:Type 0], not [:nType 0]")

(test/assert suite
  (function? (c/eval (c/ctx/empty) [:lam (fn [x] [:var x])]))
  "eval returns Janet function for lambda")

(test/assert suite
  (= (c/eval (c/ctx/empty) [:pair [:type 0] [:type 1]])
     (c/ty/pair (c/ty/type 0) (c/ty/type 1)))
  "eval returns Janet pair for semantic pair")

# Test 6: Beta-Reduction
# (λx. t) u ≡ t[u/x]
(let [id (fn [x] [:var x])
      Γ (c/ctx/empty)
      app-result (c/eval Γ [:app [:lam id] [:type 0]])
      direct-result (c/eval Γ [:type 0])]
  (test/assert suite
    (= app-result direct-result)
    "Beta-reduction: (λx. x) Type₀ ≡ Type₀"))

# Test 7: Pair Projections
(let [Γ (c/ctx/empty)]
  (test/assert suite
    (= (c/eval Γ [:fst [:pair [:type 0] [:type 1]]])
       (c/ty/type 0))
    "Projection: fst (a, b) ≡ a")

  (test/assert suite
    (= (c/eval Γ [:snd [:pair [:type 0] [:type 1]]])
       (c/ty/type 1))
    "Projection: snd (a, b) ≡ b"))

# Variable Handling
(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "x" (c/ty/type 0))]
  (test/assert suite
    (= (c/eval Γ1 [:var "x"]) [c/T/Neutral [:nvar "x"]])
    "String variables evaluate to neutrals"))

(let [Γ (c/ctx/empty)
      fresh (gensym)
      Γ1 (c/ctx/add Γ fresh (c/ty/type 0))]
  (test/assert suite
    (= (c/eval Γ1 [:var fresh]) [c/T/Neutral [:nvar fresh]])
    "Symbol variables (gensyms) evaluate to neutrals"))

(let [dom (c/ty/pi (c/ty/type 0) (fn [_] (c/ty/type 0)))
      Γ (c/ctx/add (c/ctx/empty) "f" (c/ty/pi dom (fn [_] (c/ty/type 0))))
      sem (c/eval Γ [:app [:var "f"] [:lam (fn [x] [:var x])]])
      ne (get sem 1)
      arg (get ne 2)]
  (test/assert suite
    (and (= (get sem 0) c/T/Neutral)
         (= (get ne 0) :napp)
         (= (get arg 0) c/NF/Lam))
    "Neutral applications keep the lowered argument shape"))

(test/end-suite suite)
