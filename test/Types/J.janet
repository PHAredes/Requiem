# test/coreTT-J-advanced.janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)

(test/start-suite "J Eliminator - Advanced Properties")

# Test: Transport (J as cast along equality)
(defn test-transport []
  "Given p : Id A x y, transport P from x to y"
  (let [Γ (c/ctx/empty)
        A [:type 1]
        x [:type 0]
        y [:type 0] # Same value for valid proof

        # Motive: P(z, _) = Type₀ → z
        P (fn [z _p] [:t-pi [:type 0] (fn [_] z)])

        # Element: id_Type₀ : Type₀ → Type₀
        id-fn [:lam (fn [t] [:var t])]

        # Proof: p : Id Type₁ Type₀ Type₀
        p [:t-refl [:type 0]]

        # Transport: J gives us (Type₀ → Type₀) at position y
        transported [:t-J A x P id-fn y p]]

    (test/assert
      (c/term-eq Γ (c/ty/pi (c/ty/type 0) (fn [_] (c/ty/type 0)))
                 transported id-fn)
      "Transport: J transports functions along equality")))

(test-transport)

# Test: Symmetry (full derivation)
(defn test-symmetry-derivation []
  "Derive sym : ∀A x y. Id A x y → Id A y x using J"
  (let [Γ (c/ctx/empty)
        A [:type 1]

        # Add x, y, p to context
        Γx (c/ctx/add Γ "x" (c/ty/type 1))
        Γxy (c/ctx/add Γx "y" (c/ty/type 1))
        x-sem (c/eval Γx [:var "x"])
        y-sem (c/eval Γxy [:var "y"])
        id-xy-sem (c/ty/id (c/ty/type 1) x-sem y-sem)
        Γxyp (c/ctx/add Γxy "p" id-xy-sem)

        x [:var "x"]
        y [:var "y"]
        p [:var "p"]

        # Motive: P(y, p) = Id A y x
        motive (fn [y _p] [:t-id A y x])

        # Base: refl x : Id A x x
        base [:t-refl x]

        # Symmetry: J A x P (refl x) y p : Id A y x
        sym [:t-J A x motive base y p]]

    (test/assert
      (let [res (c/infer Γxyp sym)]
        (and (= (get res 0) c/T/Id)
             (= (get (get res 1) 0) c/T/Type)))
      "Symmetry: J derives Id A y x from Id A x y")))

(test-symmetry-derivation)

# Test: Transitivity (composition of paths)
(defn test-transitivity []
  "Derive trans : ∀A x y z. Id A x y → Id A y z → Id A x z"
  (let [Γ (c/ctx/empty)
        A [:type 1]
        x [:type 0]
        y [:type 0]
        z [:type 0]

        # p : Id A x y
        p [:t-refl [:type 0]]
        # q : Id A y z  
        q [:t-refl [:type 0]]

        # Motive for first J: P(y, p) = Id A y z → Id A x z
        motive1 (fn [y _p]
                  [:t-pi [:t-id A y z]
                   (fn [_q] [:t-id A x z])])

        # Base for first J: λq. q : Id A x z → Id A x z
        base1 [:lam (fn [q] [:var q])]

        # First J: J A x P₁ base₁ y p : Id A y z → Id A x z
        j1 [:t-J A x motive1 base1 y p]

        # Apply to q: (J ...) q : Id A x z
        trans [:app j1 q]]

    (test/assert
      (c/term-eq Γ (c/ty/id (c/ty/type 1) (c/ty/type 0) (c/ty/type 0))
                 trans [:t-refl [:type 0]])
      "Transitivity: composing refl ∘ refl = refl")))

(test-transitivity)
# Test: Congruence (ap/cong via J)
(defn test-congruence []
  "Derive ap : ∀f x y. Id A x y → Id B (f x) (f y)"
  (let [Γ (c/ctx/empty)
        A [:type 1]
        B [:type 1]

        # f : A → B - add to context instead of bare lambda
        fn-ty (c/ty/pi (c/ty/type 1) (fn [_] (c/ty/type 1)))
        Γf (c/ctx/add Γ "f" fn-ty)
        f [:var "f"]

        x [:type 0]
        y [:type 0]
        p [:t-refl [:type 0]]

        # Motive: P(y, p) = Id B (f x) (f y)
        motive (fn [y _p] [:t-id B [:app f x] [:app f y]])

        # Base: refl (f x) : Id B (f x) (f x)
        base [:t-refl [:app f x]]

        # Congruence: J A x P base y p : Id B (f x) (f y)
        ap [:t-J A x motive base y p]]

    (test/assert
      (let [res (c/infer Γf ap)]
        (and (= (get res 0) c/T/Id)))
      "Congruence: J derives ap for functions")))
(test-congruence)

# Test: Subst (substitution principle)
(defn test-subst []
  "Derive subst : ∀P x y. Id A x y → P x → P y"
  (let [Γ (c/ctx/empty)
        A [:type 1]
        x [:type 0]
        y [:type 0]

        # P : A → Type (constant for simplicity)
        P [:lam (fn [_] [:type 0])]

        # p : Id A x y
        p [:t-refl [:type 0]]

        # px : P x = Type₀
        px [:type 0]

        # Motive: M(y, p) = P y
        motive (fn [y _p] [:app P y])

        # Subst: J A x M px y p : P y
        subst [:t-J A x motive px y p]]

    (test/assert
      (c/term-eq Γ (c/ty/type 1) subst px)
      "Subst: J implements type substitution")))

(test-subst)

# Test: Uniqueness of Identity Proofs (UIP)
(defn test-UIP-k-axiom []
  "In MLTT without K, we can't prove UIP, but test behavior"
  (let [Γ (c/ctx/empty)
        A [:type 1]
        x [:type 0]

        # Two proofs of x = x
        p [:t-refl [:type 0]]
        q [:t-refl [:type 0]]

        # These are not definitionally equal without K
        # But they are propositionally equal via J
        id-ty (c/ty/id (c/ty/id (c/ty/type 1) (c/ty/type 0) (c/ty/type 0))
                       [c/T/Refl (c/ty/type 0)]
                       [c/T/Refl (c/ty/type 0)])]

    (test/assert
      # Both are inhabitants of Id A x x
      (and (c/check-top p (c/ty/id (c/ty/type 1) (c/ty/type 0) (c/ty/type 0)))
           (c/check-top q (c/ty/id (c/ty/type 1) (c/ty/type 0) (c/ty/type 0))))
      "UIP: Multiple proofs of equality exist")))

(test-UIP-k-axiom)

(test/end-suite)
