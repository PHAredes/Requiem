#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../../src/sig :as sig)

(def suite (test/start-suite "Core Evaluation"))

# Test 1: Semantic Domain Separation
(test/assert suite
  (= (c/eval (c/ctx/empty) [:type 0]) (c/ty/type 0))
  "eval returns semantic universe [:Type 0], not [:nType 0]")

(let [sem (c/ty/pair (c/ty/type 0) (c/ty/type 1))]
  (test/assert suite
    (= (c/eval (c/ctx/empty) sem) sem)
    "eval preserves semantic values without dead keyword arms"))

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

(test/assert suite
  (= (c/eval (c/ctx/empty) [:hole "goal"])
     [c/T/Meta "goal"])
  "Named holes survive evaluation as semantic metas")

(test/assert suite
  (= (c/eval (c/ctx/empty) [:fst [:hole "pair-goal"]])
     [c/T/Neutral [:nfst [:nmeta "pair-goal"]]])
  "Metas survive projections through neutral structure")

(test/assert suite
  (c/term-eq (c/ctx/empty) (c/ty/type 0) [:hole "goal"] [:hole "goal"])
  "Semantic equality treats the same named meta as rigidly equal")

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

(let [bool-decl
      [:core/data "Bool" @[] [:type 0]
       @[
         [:core/ctor "true" @[] @[] @[] [:var "Bool"]]
         [:core/ctor "false" @[] @[] @[] [:var "Bool"]]]]
      nat-decl
      [:core/data "Nat" @[] [:type 0]
       @[
         [:core/ctor "zero" @[] @[] @[] [:var "Nat"]]
         [:core/ctor "succ" @[] @[] @[[ :bind "pred" [:var "Nat"] ]]
          [:t-pi [:var "Nat"] (fn [_] [:var "Nat"])]]]]
      not-decl
      [:core/func "not"
       @[[ :bind "b" [:var "Bool"] ]]
       [:var "Bool"]
       [:t-pi [:var "Bool"] (fn [_] [:var "Bool"])]
       @[
         [:core/clause @[[:pat/con "true" @[]]] [:var "false"]]
         [:core/clause @[[:pat/con "false" @[]]] [:var "true"]]]]
      plus-decl
      [:core/func "plus"
       @[[ :bind "m" [:var "Nat"] ]
         [ :bind "n" [:var "Nat"] ]]
       [:var "Nat"]
       [:t-pi [:var "Nat"] (fn [_] [:t-pi [:var "Nat"] (fn [_] [:var "Nat"])])]
       @[
         [:core/clause @[[:pat/con "zero" @[]] [:pat/var "n"]] [:var "n"]]
         [:core/clause @[[:pat/con "succ" @[[:pat/var "m"]]] [:pat/var "n"]]
          [:app [:var "succ"] [:app [:app [:var "plus"] [:var "m"]] [:var "n"]]]]]]
       core @[bool-decl nat-decl not-decl plus-decl]
       runtime-sig (sig/sig/build core)
       bool-sem (c/eval (c/ctx/empty) [:var "Bool"])
       nat-sem (c/eval (c/ctx/empty) [:var "Nat"])
       succ-sem (c/ty/pi nat-sem (fn [_] nat-sem))
       not-sem (c/ty/pi bool-sem (fn [_] bool-sem))
       plus-sem (c/ty/pi nat-sem (fn [_] (c/ty/pi nat-sem (fn [_] nat-sem))))
       Γ0 (c/ctx/empty)
       Γ1 (c/ctx/add Γ0 "Bool" (c/ty/type 0))
       Γ2 (c/ctx/add Γ1 "true" bool-sem)
       Γ3 (c/ctx/add Γ2 "false" bool-sem)
       Γ4 (c/ctx/add Γ3 "Nat" (c/ty/type 0))
       Γ5 (c/ctx/add Γ4 "zero" nat-sem)
       Γ6 (c/ctx/add Γ5 "succ" succ-sem)
       Γ7 (c/ctx/add Γ6 "not" not-sem)
       Γ8 (c/ctx/add Γ7 "plus" plus-sem)
       bool-ty bool-sem
       nat-ty nat-sem
       succ3 [:app [:var "succ"]
                    [:app [:var "succ"]
                          [:app [:var "succ"] [:var "zero"]]]]]
  (test/assert suite
    (= (c/nf/in-sig Γ8 runtime-sig bool-ty [:app [:var "not"] [:var "true"]])
       (c/nf/in-sig Γ8 runtime-sig bool-ty [:var "false"]))
    "User-defined functions delta-reduce through the runtime signature")

  (test/assert suite
    (= (c/nf/in-sig Γ8
                    runtime-sig
                    nat-ty
                    [:app [:app [:var "plus"]
                                 [:app [:var "succ"] [:app [:var "succ"] [:var "zero"]]]]
                          [:app [:var "succ"] [:var "zero"]]])
       (c/nf/in-sig Γ8 runtime-sig nat-ty succ3))
    "Recursive user-defined functions compute via ordered clauses"))

(test/end-suite suite)
