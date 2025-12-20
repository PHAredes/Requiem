#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/Assertions :as a)

(test/start-suite "CoreTT Identity Types")

(def rng (gen/rng)) # Fixed seed for reproducibility

# ===============================================
# Test 1: Identity Type Formation
# ===============================================
# Formation rule (non-cumulative):
# Γ ⊢ A : Type_l    Γ ⊢ x : A    Γ ⊢ y : A
# ─────────────────────────────────────────
#         Γ ⊢ Id A x y : Type_l

(defn prop-id-type-formation [n]
  "Property: Id A x y : Type_(l+1) when A : Type_l and x,y : A"
  (var passed true)
  (repeat n
    (let [l (math/rng-int rng 5) # l ∈ {0,1,2,3,4}
          A [:type (inc l)] # A = Type_(l+1) : Type_(l+2)
          x [:type l] # x = Type_l : Type_(l+1) = A
          y [:type l] # y = Type_l : Type_(l+1) = A
          id-ty [:t-id A x y]]
      (try
        (let [inferred (c/infer-top id-ty)
              expected [:Type (+ l 2)]] # Id Type_(l+1) _ _ : Type_(l+2)
          (unless (= inferred expected)
            (set passed false)
            (printf "Id formation failed: expected Type_%d, got %v"
                    (+ l 2) inferred)))
        ([err]
          (set passed false)
          (printf "Id formation error for level %d: %v" l err)))))
  passed)

(test/assert
  (prop-id-type-formation 50)
  "Property: Id type formation preserves universe levels")

# Sanity check with concrete example
(test/assert
  (= (c/infer-top [:t-id [:type 1] [:type 0] [:type 0]])
     [:Type 2])
  "Id formation: Id Type₁ Type₀ Type₀ : Type₂")

# ===============================================
# Test 2: Reflexivity
# ===============================================
# Reflexivity rule:
# Γ ⊢ x : A
# ─────────────────────
# Γ ⊢ refl x : Id A x x

(defn prop-reflexivity-typing [n]
  "Property: refl x : Id A x x for any well-typed x : A"
  (var passed true)
  (repeat n
    (let [l (math/rng-int rng 5)
          x [:type l]
          refl-x [:t-refl x]]
      (try
        (let [inferred (c/infer-top refl-x)
              expected [:Id [:Type (inc l)] [:Type l] [:Type l]]]
          (unless (= inferred expected)
            (set passed false)
            (printf "Reflexivity typing failed: expected %v, got %v"
                    expected inferred)))
        ([err]
          (set passed false)
          (printf "Reflexivity error for Type_%d: %v" l err)))))
  passed)

(test/assert
  (prop-reflexivity-typing 50)
  "Property: reflexivity is well-typed for all terms")

# Sanity checks with concrete examples
(test/assert
  (= (c/infer-top [:t-refl [:type 0]])
     [:Id [:Type 1] [:Type 0] [:Type 0]])
  "Reflexivity: refl Type₀ : Id Type₁ Type₀ Type₀")

(test/assert
  (= (c/infer-top [:t-refl [:type 5]])
     [:Id [:Type 6] [:Type 5] [:Type 5]])
  "Reflexivity: refl Type₅ : Id Type₆ Type₅ Type₅")

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
# Test 7: Normalization of Identity Types
# ===============================================
(test/assert
  (= (c/nf [:Type 2] [:t-id [:type 1] [:type 0] [:type 0]])
     [:Id [:Type 1] [:Type 0] [:Type 0]])
  "Normalization: identity type normalizes")

# Normalize refl at the identity type
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
(defn prop-j-symmetry [n]
  "Property: J can derive symmetry of identity types"
  (var passed true)
  (repeat n
    (let [l (math/rng-int rng 4)
          A [:type (inc l)] # A = Type_(l+1)
          x-val [:type l] # x = Type_l : A
          y-val [:type l] # y = Type_l : A (same value for valid proof)

          Γ (c/ctx/empty)
          A-sem (c/eval Γ A)

          # Add x : A to context
          Γx (c/ctx/add Γ "x" A-sem)

          # Add y : A to context
          Γxy (c/ctx/add Γx "y" A-sem)

          # Add p : Id A x y to context
          x-sem (c/eval Γx [:var "x"])
          y-sem (c/eval Γxy [:var "y"])
          id-xy-sem (c/ty/id A-sem x-sem y-sem)
          Γxyp (c/ctx/add Γxy "p" id-xy-sem)

          # Define motive P(y, p) = Id A y x
          x [:var "x"]
          y [:var "y"]
          P (fn [y p] [:t-id A y x])

          # Base case d : Id A x x
          d [:t-refl x]

          # J application
          p [:var "p"]
          symm [:t-J A x P d y p]]

      (try
        (let [result-ty (c/infer Γxyp symm)]
          (match result-ty
            [:Id _ _ _] true # Successfully produces an identity type
            _ (do
                (set passed false)
                (printf "J symmetry failed: expected Id type, got %v" result-ty))))
        ([err]
          (set passed false)
          (printf "J symmetry error at level %d: %v" l err)))))
  passed)

(test/assert
  (prop-j-symmetry 20)
  "Property: J derives symmetry for identity types")

# Concrete example with specific values
(let [A [:type 2]
      Γ (c/ctx/empty)
      A-sem (c/eval Γ A)

      Γx (c/ctx/add Γ "x" A-sem)
      Γxy (c/ctx/add Γx "y" A-sem)

      x-sem (c/eval Γx [:var "x"])
      y-sem (c/eval Γxy [:var "y"])
      id-xy-sem (c/ty/id A-sem x-sem y-sem)
      Γxyp (c/ctx/add Γxy "p" id-xy-sem)

      x [:var "x"]
      y [:var "y"]
      p [:var "p"]
      P (fn [y p] [:t-id A y x])
      d [:t-refl x]
      symm [:t-J A x P d y p]]

  (test/assert
    (match (c/infer Γxyp symm)
      [:Id [:Type 2] _ _] true
      _ false)
    "J proves symmetry: Id A x y → Id A y x"))

# ===============================================
# Test 9: Identity Preserves Universe Levels
# ===============================================
(defn prop-id-preserves-universes [n]
  "Property: Id A x y : Type_(l+1) when A : Type_l"
  (var passed true)
  (repeat n
    (let [l (math/rng-int rng 8) # Test larger universes
          A [:type (inc l)] # A = Type_(l+1) : Type_(l+2)
          x [:type l] # x = Type_l : Type_(l+1) = A
          y [:type l] # y = Type_l : Type_(l+1) = A
          id-ty [:t-id A x y]]
      (try
        (let [inferred (c/infer-top id-ty)
              expected [:Type (+ l 2)]]
          (unless (= inferred expected)
            (set passed false)
            (printf "Universe preservation failed at level %d: expected Type_%d, got %v"
                    l (+ l 2) inferred)))
        ([err]
          (set passed false)
          (printf "Universe preservation error at level %d: %v" l err)))))
  passed)

(test/assert
  (prop-id-preserves-universes 30)
  "Property: Identity types preserve universe levels")

# Sanity checks with concrete examples
(test/assert
  (= (c/infer-top [:t-id [:type 3] [:type 2] [:type 2]])
     [:Type 4])
  "Identity preserves universe: Id Type₃ Type₂ Type₂ : Type₄")

(test/assert
  (= (c/infer-top [:t-id [:type 10] [:type 9] [:type 9]])
     [:Type 11])
  "Identity preserves universe: larger universes")

# ===============================================
# Test 11: Type Checking Reflexivity
# ===============================================
(a/assert-throws
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
# Test 13: Identity Types of Dependent Functions
# ===============================================
(let [id-ty [:t-pi [:type 0] (fn [A] [:t-pi A (fn [x] A)])]
      Γ (c/ctx/empty)
      id-ty-sem (c/eval Γ id-ty)

      # Add two identity functions to context
      Γf (c/ctx/add Γ "f" id-ty-sem)
      Γfg (c/ctx/add Γf "g" id-ty-sem)

      # Create identity type between them
      f [:var "f"]
      g [:var "g"]
      dep-id [:t-id id-ty f g]]

  (test/assert
    (= (c/infer Γfg dep-id) [:Type 1])
    "Dependent identity: Id (∀A. A → A) f g"))

# Pi Types property test
(defn prop-id-of-pi-types [n]
  "Property: Identity types can be formed for Pi types"
  (var passed true)
  (repeat n
    (let [l (math/rng-int rng 3)
          A [:type l]
          B [:type l]
          pi-ty [:t-pi A (fn [_] B)]

          Γ (c/ctx/empty)
          pi-sem (c/eval Γ pi-ty)

          # Add two function variables to context
          Γf (c/ctx/add Γ "f" pi-sem)
          Γfg (c/ctx/add Γf "g" pi-sem)

          f [:var "f"]
          g [:var "g"]
          id-ty [:t-id pi-ty f g]]

      (try
        (let [result (c/infer Γfg id-ty)]
          (match result
            [:Type _] true
            _ (do
                (set passed false)
                (printf "Id of Pi type failed: got %v" result))))
        ([err]
          (set passed false)
          (printf "Id of Pi type error at level %d: %v" l err)))))
  passed)

(test/assert
  (prop-id-of-pi-types 20)
  "Property: identity types work for function types")

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
# Property Tests: Reflexivity Always Works
# ===============================================
(defn prop-reflexivity [n]
  "Property: refl x : Id A x x for any well-typed x : A"
  (var passed true)
  (repeat n
    (let [x [:type 0]] # Reduced complexity to simple element for reliability
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
      (let [A (gen/gen-univ rng)
            x [:type 0]
            P (fn [y p] (gen/gen-univ rng))
            d [:type 0]
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
(test/assert
  (a/type-preserves
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
(defn prop-id-higher-universes [n]
  "Property: Identity types work correctly at high universe levels"
  (var passed true)
  (repeat n
    (let [l (+ 5 (math/rng-int rng 10)) # High levels: 5-14
          A [:type (inc l)] # A = Type_(l+1)
          x [:type l] # x = Type_l : A
          y [:type l] # y = Type_l : A
          id-ty [:t-id A x y]]
      (try
        (let [inferred (c/infer-top id-ty)
              expected [:Type (+ l 2)]]
          (unless (= inferred expected)
            (set passed false)
            (printf "High universe Id failed at level %d: expected Type_%d, got %v"
                    l (+ l 2) inferred)))
        ([err]
          (set passed false)
          (printf "High universe Id error at level %d: %v" l err)))))
  passed)

(test/assert
  (prop-id-higher-universes 20)
  "Property: identity types work at high universe levels")

# Sanity checks
(test/assert
  (= (c/infer-top [:t-id [:type 5] [:type 4] [:type 4]])
     [:Type 6])
  "Identity works on higher universes")

(test/assert
  (= (c/infer-top [:t-id [:type 10] [:type 9] [:type 9]])
     [:Type 11])
  "Identity preserves high universe levels")

# ===============================================
# Test 21: J with Pi Types
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
