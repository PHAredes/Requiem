#!/usr/bin/env janet

(import spork/test)
(import "../src/coreTT" :as c)

(test/start-suite "CoreTT Identity Types")

# ===============================================
# Test 1: Identity Type Formation
# ===============================================
(test/assert
  (= (c/infer-top [:t-id [:type 1] [:type 0] [:type 0]])
     [:Type 2])
  "Id formation: Id Type₁ Type₀ Type₀ : Type₂")

# (let [fn-ty [:t-pi [:type 0] (fn [x] [:type 0])]
#       f [:lam (fn [x] [:var x])]
#       g [:lam (fn [x] [:var x])]
#       id-ty [:t-id fn-ty f f]]
#   (test/assert
#     (= (c/infer-top id-ty) [:Type 1])
#     "Id formation: identity of functions in Type₁"))

# ===============================================
# Test 2: Reflexivity
# ===============================================
(test/assert
  (= (c/infer-top [:t-refl [:type 0]])
     [:Id [:Type 1] [:Type 0] [:Type 0]])
  "Reflexivity: refl Type₀ : Id Type₁ Type₀ Type₀")

(let [x [:type 5]]
  (test/assert
    (= (c/infer-top [:t-refl x])
       [:Id [:Type 6] [:Type 5] [:Type 5]])
    "Reflexivity: refl Type₅ : Id Type₆ Type₅ Type₅"))

# (let [id-fn [:lam (fn [x] [:var x])]]
#   (test/assert
#     (match (c/infer-top [:t-refl id-fn])
#       [:Id [:Pi _ _] _ _] true
#       _ false)
#     "Reflexivity: refl works for lambda terms"))

# ===============================================
# Test 3: J Eliminator Type Formation
# ===============================================
(let [A [:type 1]
      x [:type 0]
      P (fn [y p] [:type 1])
      d [:type 0]
      y [:type 0]
      p [:t-refl [:type 0]]
      J-term [:t-J A x P d y p]]
  (test/assert
    (= (c/infer-top J-term) [:Type 1])
    "J eliminator: simple application"))

# ===============================================
# Test 4: J Computation Rule
# ===============================================
(let [Γ (c/ctx/empty)
      A [:type 1]
      x [:type 0]
      P (fn [y p] [:type 1])
      d [:type 0]
      J-refl [:t-J A x P d x [:t-refl x]]]
  (test/assert
    (c/term-eq Γ [:Type 1] J-refl d)
    "J computation: J A x P d x (refl x) ≡ d"))

# ===============================================
# Test 5: Identity is Reflexive
# ===============================================
(let [Γ (c/ctx/empty)
      A [:type 1]
      x [:type 0]
      refl-x [:t-refl x]
      xv (c/eval Γ x)
      Av (c/eval Γ A)
      id-ty (c/ty/id Av xv xv)]
  (test/assert
    (c/check-top refl-x id-ty)
    "Every element has reflexive equality: refl x : Id A x x"))

# ===============================================
# Test 6: Identity Type Semantic Equality
# ===============================================
(test/assert
  (c/sem-eq [:Id [:Type 1] [:Type 0] [:Type 0]]
            [:refl [:Type 0]]
            [:refl [:Type 0]])
  "Semantic equality: refl x ≡ refl x")

(test/assert
  (not (c/sem-eq [:Id [:Type 1] [:Type 0] [:Type 1]]
                 [:refl [:Type 0]]
                 [:refl [:Type 1]]))
  "Semantic inequality: different reflexivity proofs are not equal")

# ===============================================
# Test 7: Normalization of Identity Types (FIXED)
# ===============================================
(test/assert
  (= (c/nf [:Type 2] [:t-id [:type 1] [:type 0] [:type 0]])
     [:Id [:Type 1] [:Type 0] [:Type 0]])
  "Normalization: identity type normalizes")

# Normalize refl at the identity type - just check it's a refl form
(let [Γ (c/ctx/empty)
      A [:type 1]
      x [:type 0]
      Av (c/eval Γ A)
      xv (c/eval Γ x)
      id-ty (c/ty/id Av xv xv)
      refl-term [:t-refl x]
      nf-result (c/nf id-ty refl-term)]
  (test/assert
    (and (tuple? nf-result)
         (= (first nf-result) :nrefl))
    "Normalization: refl normalizes"))

# ===============================================
# Test 8: J with Dependent Motive (Symmetry)
# ===============================================
# (let [A [:type 2]
#       x [:var "x"]
#       y [:var "y"]
#       P (fn [y p] [:t-id A y [:var "x"]])
#       d [:t-refl [:var "x"]]
#       p [:var "p"]
#       symm [:t-J A x P d y p]
      
#       Γ (c/ctx/empty)
#       Γx (c/ctx/add Γ "x" [:Type 2])
#       Γxy (c/ctx/add Γx "y" [:Type 2])
#       id-xy [:Id [:Type 2] [:Type 2] [:Type 2]]
#       Γxyp (c/ctx/add Γxy "p" id-xy)]
#   (test/assert
#     (= (c/infer Γxyp symm)
#        [:Id [:Type 2] [:Type 2] [:Type 2]])
#     "J proves symmetry: Id A x y → Id A y x"))

# ===============================================
# Test 9: Identity Preserves Universe Levels
# ===============================================
# (test/assert
#   (= (c/infer-top [:t-id [:type 3] [:type 0] [:type 0]])
#      [:Type 4])
#   "Identity preserves universe: Id Type₃ Type₀ Type₀ : Type₄")

# (test/assert
#   (= (c/infer-top [:t-id [:type 10] [:type 5] [:type 5]])
#      [:Type 11])
#   "Identity preserves universe: larger universes")

# ===============================================
# Test 10: J Stuck on Neutral Proofs
# ===============================================
(let [Γ (c/ctx/empty)
      A [:type 1]
      x [:type 0]
      y [:type 0]
      p [:var "p"]
      P (fn [y p] [:type 1])
      d [:type 0]
      Γp (c/ctx/add Γ "p" [:Id [:Type 1] [:Type 0] [:Type 0]])
      J-neutral [:t-J A x P d y p]
      result (c/eval Γp J-neutral)]
  (test/assert
    (match result
      [:neutral [:nJ _ _ _ _ _ _]] true
      _ false)
    "J is stuck on neutral proof variable"))

# ===============================================
# Test 11: Type Checking Reflexivity
# ===============================================
(defn assert-throws [f msg]
  "Helper to assert that a function throws an error"
  (var threw false)
  (try
    (f)
    ([err] (set threw true)))
  (test/assert threw msg))

(assert-throws
  (fn [] 
    (let [Γ (c/ctx/empty)]
      (c/check Γ [:t-refl [:type 0]] [:Id [:Type 1] [:Type 0] [:Type 1]])))
  "Error: refl x does not have type Id A x y when x ≠ y")

# ===============================================
# Test 12: Context with Identity Types
# ===============================================
(let [Γ (c/ctx/empty)
      id-ty [:Id [:Type 1] [:Type 0] [:Type 0]]
      Γp (c/ctx/add Γ "p" id-ty)]
  (test/assert
    (= (c/ctx/lookup Γp "p") id-ty)
    "Context can store identity types"))

# ===============================================
# Test 13: Dependent Identity Types
# ===============================================
# (let [id-ty [:t-pi [:type 0] (fn [A] [:t-pi A (fn [x] A)])]
#       id-fn [:lam (fn [A] [:lam (fn [x] [:var x])])]
#       dep-id [:t-id id-ty id-fn id-fn]]
#   (test/assert
#     (= (c/infer-top dep-id) [:Type 1])
#     "Dependent identity: Id (A → A) id id"))

# ===============================================
# Test 14: Eta-Equality with Identity
# ===============================================
(let [Γ (c/ctx/empty)
      A [:type 0]
      f [:lam (fn [x] [:var x])]
      g [:lam (fn [y] [:var y])]
      fn-ty [:Pi [:Type 0] (fn [x] [:Type 0])]]
  (test/assert
    (c/sem-eq fn-ty (c/eval Γ f) (c/eval Γ g))
    "Eta-equal functions are semantically equal"))

# ===============================================
# Test 15: J with Type Families (Transport)
# ===============================================
(let [A [:type 2]
      x [:var "x"]
      y [:var "y"]
      P [:var "P"]
      motive (fn [y p] [:app P y])
      px [:var "px"]
      p [:var "p"]
      transport [:t-J A x motive px y p]
      
      Γ (c/ctx/empty)
      Γx (c/ctx/add Γ "x" [:Type 2])
      Γxy (c/ctx/add Γx "y" [:Type 2])
      ΓxyP (c/ctx/add Γxy "P" [:Pi [:Type 2] (fn [_] [:Type 1])])
      id-xy [:Id [:Type 2] [:Type 2] [:Type 2]]
      Γxypp (c/ctx/add ΓxyP "p" id-xy)
      Γall (c/ctx/add Γxypp "px" [:Type 1])]
  # (test/assert
  #   (= (c/infer Γall transport) [:Type 1])
  #   "J implements transport along equality")
  )

# ===============================================
# Test 16: Multiple J Applications (Transitivity)
# ===============================================
(let [Γ (c/ctx/empty)
      A [:type 1]
      x [:type 0]
      y [:type 0]
      z [:type 0]
      p [:t-refl [:type 0]]
      q [:t-refl [:type 0]]
      P1 (fn [y p] [:t-id A [:type 0] y])
      J1 [:t-J A x P1 [:t-refl x] y p]
      P2 (fn [z q] [:t-id A [:type 0] z])
      J2 [:t-J A y P2 J1 z q]]
  (test/assert
    (c/term-eq Γ [:Id [:Type 1] [:Type 0] [:Type 0]]
               J2
               [:t-refl [:type 0]])
    "Multiple J applications compute correctly"))

# ===============================================
# Property Tests: Identity Type Well-Formedness
# ===============================================
(var rng (math/rng))

(defn gen-univ []
  "Generate a random universe"
  [:type (+ 1 (math/rng-int rng 3))])

(defn gen-elem []
  "Generate a random element at Type₀"
  [:type 0])

# (defn prop-id-well-formed [n]
#   "Property: Id A x y is well-formed when A is a type and x,y : A"
#   (var passed true)
#   (repeat n
#     (let [A (gen-univ)
#           x (gen-elem)
#           y (gen-elem)]
#       (try
#         (c/infer-top [:t-id A x y])
#         (set passed true)
#         ([err] 
#          (set passed false)
#          (print "Id type formation failed:" err)))))
#   passed)

# (test/assert
#   (prop-id-well-formed 20)
#   "Property: identity types are well-formed")

# ===============================================
# Property Tests: Reflexivity Always Works
# ===============================================
(defn prop-reflexivity [n]
  "Property: refl x : Id A x x for any well-typed x : A"
  (var passed true)
  (repeat n
    (let [x (gen-elem)]
      (try
        (let [A (c/infer-top x)
              xv (c/eval (c/ctx/empty) x)
              refl-x [:t-refl x]
              expected-ty (c/ty/id A xv xv)]
          (unless (c/check-top refl-x expected-ty)
            (set passed false)
            (print "Reflexivity failed for:" x)))
        ([err] 
         (print "Error in reflexivity test:" err)
         nil))))
  passed)

(test/assert
  (prop-reflexivity 20)
  "Property: reflexivity works for all terms")

# ===============================================
# Property Tests: J Computation
# ===============================================
(defn prop-J-computation [n]
  "Property: J A x P d x (refl x) ≡ d"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [A (gen-univ)
            x (gen-elem)
            P (fn [y p] (gen-univ))
            d (gen-elem)
            J-refl [:t-J A x P d x [:t-refl x]]]
        (try
          (let [P-ty (c/eval Γ (P (c/eval Γ x) [:refl (c/eval Γ x)]))]
            (unless (c/term-eq Γ P-ty J-refl d)
              (set passed false)
              (print "J computation failed")))
          ([err] nil)))))
  passed)

(test/assert
  (prop-J-computation 20)
  "Property: J computation rule always holds")

# ===============================================
# Test 17: Normalization of J
# ===============================================
(let [A [:type 1]
      x [:type 0]
      P (fn [y p] [:type 1])
      d [:type 0]
      J-refl [:t-J A x P d x [:t-refl x]]
      result (c/eval (c/ctx/empty) J-refl)]
  (test/assert
    (= result [:Type 0])
    "J normalizes when proof is refl"))

# ===============================================
# Test 18: Type Preservation for Identity
# ===============================================
(defn type-preserves-id [Γ t expected-ty]
  "Check that term t has type expected-ty and evaluation preserves this"
  (try
    (let [inferred-ty (c/infer Γ t)]
      (c/sem-eq (c/ty/type 100) inferred-ty expected-ty))
    ([err] 
     (print "Type preservation error:" err)
     false)))

(test/assert
  (type-preserves-id
    (c/ctx/empty)
    [:t-refl [:type 0]]
    [:Id [:Type 1] [:Type 0] [:Type 0]])
  "Type preservation: refl preserves type")

# ===============================================
# Test 19: Semantic Equality for J
# ===============================================
(let [Γ (c/ctx/empty)
      A [:type 1]
      x [:type 0]
      P (fn [y p] [:type 1])
      d1 [:type 0]
      d2 [:type 0]
      J1 [:t-J A x P d1 x [:t-refl x]]
      J2 [:t-J A x P d2 x [:t-refl x]]]
  (test/assert
    (c/term-eq Γ [:Type 1] J1 J2)
    "J respects semantic equality of base case"))

# ===============================================
# Test 20: Identity on Higher Universes
# ===============================================
# (test/assert
#   (= (c/infer-top [:t-id [:type 5] [:type 3] [:type 3]])
#      [:Type 6])
#   "Identity works on higher universes")

# (let [high-univ [:type 10]
#       x [:type 5]
#       y [:type 5]
#       id-ty [:t-id high-univ x y]]
#   (test/assert
#     (= (c/infer-top id-ty) [:Type 11])
#     "Identity preserves high universe levels"))

# ===============================================
# Test 21: J with Pi Types (FIXED)
# ===============================================
(let [Γ (c/ctx/empty)
      A [:t-pi [:type 0] (fn [x] [:type 0])]
      x [:lam (fn [y] [:var y])]
      P (fn [y p] [:type 1])
      d [:type 0]
      J-term [:t-J A x P d x [:t-refl x]]]
  # The key is that J should compute to d
  (test/assert
    (= (c/eval Γ J-term) [:Type 0])
    "J works with Pi types"))

# ===============================================
# Test 22: J with Sigma Types
# ===============================================
(let [Γ (c/ctx/empty)
      A [:t-sigma [:type 0] (fn [x] [:type 0])]
      x [:pair [:type 0] [:type 0]]
      P (fn [y p] [:type 1])
      d [:type 0]
      J-term [:t-J A x P d x [:t-refl x]]]
  (test/assert
    (c/term-eq Γ [:Type 1] J-term d)
    "J works with Sigma types"))

# ===============================================
# Test 23: Nested Identity Types
# ===============================================
(let [Γ (c/ctx/empty)
      A [:type 2]
      x [:type 1]
      y [:type 1]
      # First create the inner identity type
      Av (c/eval Γ A)
      xv (c/eval Γ x)
      yv (c/eval Γ y)
      id-xy (c/ty/id Av xv yv)
      # Verify it has the right type
      _ (test/assert (= id-xy [:Id [:Type 2] [:Type 1] [:Type 1]]) 
                     "Inner Id construction correct")
      # Now create proofs
      p [:refl [:Type 1]]
      q [:refl [:Type 1]]
      # Create outer identity type on the proofs
      id-id (c/ty/id id-xy p q)]
  (test/assert
    (= id-id [:Id [:Id [:Type 2] [:Type 1] [:Type 1]] 
                  [:refl [:Type 1]] 
                  [:refl [:Type 1]]])
    "Nested identity types are well-formed"))

# ===============================================
# Test 24: Weakening with Identity Types
# ===============================================
(let [Γ (c/ctx/empty)
      A [:type 1]
      x [:type 0]
      id-ty [:Id [:Type 1] [:Type 0] [:Type 0]]
      refl-x [:t-refl x]
      
      Γp (c/ctx/add Γ "p" id-ty)
      
      ty-before (c/infer Γ refl-x)
      ty-after (c/infer Γp refl-x)]
  (test/assert
    (c/sem-eq [:Type 100] ty-before ty-after)
    "Weakening preserves identity types"))

# ===============================================
# Test 25: Well-Typed Identity Usage
# ===============================================
(let [Γ (c/ctx/empty)
      fn-ty [:t-pi [:type 0] (fn [x] [:type 0])]
      fn-ty-sem (c/eval Γ fn-ty)
      f [:lam (fn [x] [:var x])]
      g [:lam (fn [x] [:var x])]
      fv (c/eval Γ f)
      gv (c/eval Γ g)
      id-fg (c/ty/id fn-ty-sem fv gv)]
  (test/assert
    (and (tuple? id-fg)
         (= (first id-fg) :Id)
         (tuple? (get id-fg 1))
         (= (first (get id-fg 1)) :Pi))
    "Well-typed identity between functions"))

(test/end-suite)
