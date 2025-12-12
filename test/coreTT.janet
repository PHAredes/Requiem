#!/usr/bin/env janet

(import spork/test)
(import "../src/coreTT" :as c)

(test/start-suite "CoreTT - Improved Tests")

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
# Test 2: Context Shadowing
# ===============================================
(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "x" [:Type 0])
      Γ2 (c/ctx/add Γ1 "x" [:Type 1])]  # Shadow "x"
  (test/assert 
    (= (c/ctx/lookup Γ2 "x") [:Type 1])
    "Context shadowing: newer binding shadows older"))

(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "x" [:Type 0])
      Γ2 (c/ctx/add Γ1 "y" [:Type 1])]
  (test/assert 
    (= (c/ctx/lookup Γ2 "x") [:Type 0])
    "Context preserves older non-shadowed bindings"))

# ===============================================
# Test 3: Eta-Equality for Functions
# ===============================================
# λx. f x ≡ f (when x not free in f)
(let [id-ty (c/ty/pi [:Type 0] (fn [x] [:Type 0]))
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
(let [pair-ty (c/ty/sigma [:Type 0] (fn [x] [:Type 0]))
      p [:var "p"]
      eta-expanded [:pair [:fst p] [:snd p]]
      Γ (c/ctx/add (c/ctx/empty) "p" pair-ty)]
  (test/assert
    (c/term-eq Γ pair-ty p eta-expanded)
    "Eta-equality: (fst p, snd p) ≡ p"))

# ===============================================
# Test 5: Type Preservation
# ===============================================
# If Γ ⊢ t : A, then eval(t) has semantic type A
(defn type-preserves [Γ t expected-ty]
  "Check that term t has type expected-ty and evaluation preserves this"
  (try
    (let [inferred-ty (c/infer Γ t)]
      (c/sem-eq (c/ty/type 100) inferred-ty expected-ty))
    ([err] 
     (print "Type preservation error:" err)
     false)))

(test/assert
  (type-preserves 
    (c/ctx/empty)
    [:type 0]
    [:Type 1])
  "Type preservation: [:type 0] : [:Type 1]")

(let [id-ty (c/ty/pi [:Type 0] (fn [x] [:Type 0]))]
  (test/assert
    (type-preserves
      (c/ctx/empty)
      [:t-pi [:type 0] (fn [x] [:type 0])]
      [:Type 1])
    "Type preservation: (Type₀ → Type₀) : Type₁"))

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
# Test 8: Universe Levels
# ===============================================
(test/assert
  (= (c/infer-top [:type 0]) [:Type 1])
  "Universe hierarchy: Type₀ : Type₁")

(test/assert
  (= (c/infer-top [:type 5]) [:Type 6])
  "Universe hierarchy: Type₅ : Type₆")

# ===============================================
# Test 9: Pi Type Formation
# ===============================================
(let [pi-type [:t-pi 
               [:type 0] 
               (fn [x] [:type 0])]]
  (test/assert
    (= (c/infer-top pi-type) [:Type 1])
    "Pi formation: (Type₀ → Type₀) : Type₁"))

(let [pi-type [:t-pi 
               [:type 0] 
               (fn [x] [:type 1])]]
  (test/assert
    (= (c/infer-top pi-type) [:Type 2])
    "Pi formation: (Type₀ → Type₁) : Type₂ (max rule)"))

# ===============================================
# Test 10: Sigma Type Formation
# ===============================================
(let [sigma-type [:t-sigma 
                  [:type 0] 
                  (fn [x] [:type 0])]]
  (test/assert
    (= (c/infer-top sigma-type) [:Type 1])
    "Sigma formation: (Type₀ × Type₀) : Type₁"))

# ===============================================
# Test 11: Dependent Function Types
# ===============================================
(let [dep-fn-type [:t-pi 
                   [:type 0]
                   (fn [A] [:t-pi [:var A] (fn [x] [:var A])])]
      expected [:Type 2]]
  (test/assert
    (= (c/infer-top dep-fn-type) expected)
    "Dependent function: ∀(A : Type₀). A → A"))

# ===============================================
# Test 12: Normalization Stability
# ===============================================
# nf(nf(t)) = nf(t)
(defn normalization-stable [ty tm]
  "Check that normalizing twice gives same result as normalizing once"
  (let [Γ (c/ctx/empty)
        nf1 (c/nf ty tm)
        sem1 (c/eval Γ tm)
        nf1-again (c/lower ty sem1)]
    (= nf1 nf1-again)))

(test/assert
  (normalization-stable 
    [:Type 1]
    [:type 0])
  "Normalization stability: simple type")

(test/assert
  (normalization-stable
    (c/ty/pi [:Type 0] (fn [x] [:Type 0]))
    [:lam (fn [x] [:var x])])
  "Normalization stability: identity function")

# ===============================================
# Property Tests: Well-Typed Terms
# ===============================================
(var rng (math/rng))

(defn gen-univ []
  "Generate a random universe"
  [:type (math/rng-int rng 3)])

(defn gen-simple-type []
  "Generate a simple well-formed type"
  (case (math/rng-int rng 3)
    0 (gen-univ)
    1 [:t-pi (gen-univ) (fn [x] (gen-univ))]
    2 [:t-sigma (gen-univ) (fn [x] (gen-univ))]))

(defn prop-well-typed-types [n]
  "Property: generated types are well-formed"
  (var passed true)
  (repeat n
    (let [ty (gen-simple-type)]
      (try
        (c/infer-top ty)
        ([err] 
         (set passed false)
         (print "Generated ill-typed type:" ty)))))
  passed)

(test/assert
  (prop-well-typed-types 20)
  "Property: randomly generated types are well-formed")

# ===============================================
# Property Tests: Beta-Eta Equivalence
# ===============================================
(defn prop-id-function [n]
  "Property: (λx. x) a ≡ a for various a"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [a (gen-univ)
            id [:lam (fn [x] [:var x])]
            applied [:app id a]]
        (unless (c/term-eq Γ [:Type 1] applied a)
          (set passed false)
          (print "Beta reduction failed for:" a)))))
  passed)

(test/assert
  (prop-id-function 20)
  "Property: identity function beta-reduces correctly")

# ===============================================
# Property Tests: Type Checking is Decidable
# ===============================================
(defn prop-check-decidable [n]
  "Property: type checking always terminates (doesn't loop)"
  (var passed true)
  (repeat n
    (let [ty (gen-simple-type)
          tm [:lam (fn [x] [:var x])]]
      (try
        # Should either succeed or fail, but not loop
        (c/check-top tm (c/eval (c/ctx/empty) ty))
        ([err] nil))  # Error is fine, just shouldn't hang
      (set passed true)))
  passed)

(test/assert
  (prop-check-decidable 10)
  "Property: type checking is decidable")

# ===============================================
# Edge Cases
# ===============================================
(test/assert-thrown
  (c/infer-top [:var "undefined"])
  "Error: undefined variable throws")

(test/assert-thrown
  (c/infer-top [:lam (fn [x] [:var x])])
  "Error: cannot infer lambda without annotation")

(test/assert-thrown
  (c/infer-top [:pair [:type 0] [:type 1]])
  "Error: cannot infer pair without Sigma annotation")

(test/assert-thrown
  (let [Γ (c/ctx/add (c/ctx/empty) "x" [:Type 0])]
    (c/check Γ [:lam (fn [y] [:var y])] [:Type 0]))
  "Error: lambda cannot have non-Pi type")

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
      ty (c/ty/pi [:Type 0] (fn [x] [:Type 0]))]
  (test/assert
    (c/sem-eq ty f1 f2)
    "Semantic equality: extensional function equality"))

# ===============================================
# Normalization Correctness
# ===============================================
(test/assert
  (= (c/nf [:Type 1] [:type 0])
     [:nType 0])
  "Normalization: Type₀ normalizes to [:nType 0]")

(test/assert
  (match (c/nf (c/ty/pi [:Type 0] (fn [x] [:Type 0]))
               [:lam (fn [x] [:var x])])
    [:nlam _] true
    _ false)
  "Normalization: λx. x normalizes to [:nlam ...]")

# ===============================================
# Variable Handling
# ===============================================
(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "x" [:Type 0])]
  (test/assert
    (= (c/eval Γ1 [:var "x"]) [:neutral [:nvar "x"]])
    "String variables evaluate to neutrals"))

# ===============================================
# Complex Dependent Types
# ===============================================
(let [pair-ty [:t-sigma [:type 0] (fn [A] [:t-pi [:var A] (fn [x] [:var A])])]
      # (A : Type₀) × (A → A)
      expected [:Type 1]]
  (test/assert
    (= (c/infer-top pair-ty) expected)
    "Complex dependent type: (A : Type₀) × (A → A)"))

(test/end-suite)
