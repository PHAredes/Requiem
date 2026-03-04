{-# OPTIONS --cubical --safe #-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; rec to ⊥-rec)
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Algebra
open import Level using (Level) renaming (_⊔_ to l-max; suc to lsuc)

private variable
  n m : Nat
  a b c ℓ : Level

-- a pair of nats, left element is the positive part, right element is the negative part
IntCarrier : Type 
IntCarrier = Nat × Nat

same-diff : Rel IntCarrier IntCarrier ℓ-zero
same-diff (a , b) (c , d) = a + d ≡ b + c

syntax same-diff a b = a ≈ b

negation : ∀ (int : Nat × Nat) → (Nat × Nat)
negation (a , b) = (b , a)

transpose-pos : (a b c d : Nat) → (a , b) ≈ (c , d) → (d , b) ≈ (c , a)
transpose-pos a _ _ d p = +-comm d a ∙ p

transpose-neg : (a b c d : Nat) → (a , b) ≈ (c , d) → (a , c) ≈ (b , d)
transpose-neg _ b c _ p = p ∙ +-comm b c

invert : ∀ (a b c d : Nat) → (a , b) ≈ (c , d) → (d , c) ≈ (b , a)
invert a b c d p = +-comm d a ∙ p ∙ +-comm b c

neg-preserves-eq : ∀ (n m : IntCarrier) → n ≈ m → negation n ≈ negation m
neg-preserves-eq (a , b) (c , d) p = sym p

_-_ : ∀ (n m : IntCarrier) → IntCarrier
(a , b) - (c , d) = a + c , b + d

-- Prove it's an equivalence relation
≈-refl : (x : IntCarrier) → x ≈ x
≈-refl (a , b) = +-comm a b

≈-sym : (x y : IntCarrier) → x ≈ y → y ≈ x
≈-sym (a , b) (c , d) p = sym (+-comm d a ∙ p ∙ +-comm b c)

-- Discrete fact uses `with` or trichotomy which leads to convoluted goals (same for `subst`)
≈-trans : (x y z : IntCarrier) → x ≈ y → y ≈ z → x ≈ z
≈-trans (a , b) (c , d) (e , f) p q =
-- let step = (a + f) (c + d) ≡ (b + e) (c + d) → (a + f) ≡ (b + e)
-- we prove step holds by _+_ properties, then prove its implication holds by injectiveness
  let step = 
        (a + f) + (c + d)       ≡⟨ +-comm (a + f) (c + d) ⟩
        (c + d) + (a + f)       ≡⟨ sym (+-assoc c d (a + f)) ⟩ 
        c + (d + (a + f))       ≡⟨ cong (c +_) (+-assoc d a f) ⟩
        c + ((d + a) + f)       ≡⟨ cong (λ x → c + (x + f)) (+-comm d a) ⟩
        c + ((a + d) + f)       ≡⟨ cong (λ x → c + (x + f)) p ⟩
        c + ((b + c) + f)       ≡⟨ cong (c +_) (sym (+-assoc b c f)) ⟩
        c + (b + (c + f))       ≡⟨ cong (λ x → c + (b + x)) q ⟩
        c + (b + (d + e))       ≡⟨ cong (c +_) (cong (b +_) (+-comm d e))⟩
        c + (b + (e + d))       ≡⟨ cong (c +_) (+-assoc b e d) ⟩
        c + (b + e + d)         ≡⟨ cong (c +_) (+-comm (b + e) d) ⟩
        c + (d + (b + e))       ≡⟨ +-assoc c d (b + e) ⟩ 
        (c + d) + (b + e)       ≡⟨ +-comm (c + d) (b + e) ⟩
        (b + e) + (c + d)       ∎
  in (inj-+m step)

isEquiv-≈ : EquivRel IntCarrier ℓ-zero
isEquiv-≈ = same-diff , BinaryRelation.equivRel (≈-refl) (≈-sym) (≈-trans)

-- equivalence classes

-- suc and pred applicatives
+'_ : IntCarrier → IntCarrier
+' (a , b) = suc a , b

-_ : IntCarrier → IntCarrier
- (a , b) = a , suc b

-- zero equiv class, ∀ int `i` such that its positive and negative parts are equivalent, `i` is equivalent to zero
0# : IntCarrier
0# = 0 , 0

suc# : ∀ {n : Nat} → IntCarrier
suc# {n} = n , 0

pred# : ∀ {m : Nat} → IntCarrier
pred# {m} = 0 , m

0eq : ∀ {a b} → a ≡ b → (a , b) ≈ 0# -- TODO: prove it is unique
0eq {zero} {suc b} p = ⊥-rec (znots p)
0eq {suc a} {zero} p = ⊥-rec (snotz p)
0eq {suc a} {suc b} p = cong suc (+-zero a) ∙ p ∙ cong suc (sym (+-zero b)) 
0eq {zero}  {zero}  _ = refl

suc-eq : ∀ (a b : Nat) → a > b → Σ[ n ∈ Nat ] (same-diff (a , b) (suc# {n})) -- TODO: prove it for ∃!
suc-eq zero (suc b) p = ⊥-rec (¬-<-zero p)
suc-eq (suc a) zero p = suc a , +-comm (suc a) zero
suc-eq (suc a) (suc b) p = fst (suc-eq a b (pred-≤-pred p)) , cong suc (snd (suc-eq a b (pred-≤-pred p)))
suc-eq zero zero p = ⊥-rec (¬-<-zero p)

pred-eq : ∀ (a b : Nat) → a < b → Σ[ n ∈ Nat ] (same-diff (a , b) (pred# {n})) -- TODO: prove it for ∃!
pred-eq (suc a) zero p = ⊥-rec (¬-<-zero p)
pred-eq zero (suc b) p = suc b , +-comm zero (suc b)
pred-eq (suc a) (suc b) p = fst (pred-eq a b (pred-≤-pred p)) , cong suc (snd (pred-eq a b (pred-≤-pred p)))
pred-eq zero zero    p = ⊥-rec (¬-<-zero p)

record Setoid {ℓ₁ ℓ₂} : Type (lsuc (l-max ℓ₁ ℓ₂)) where -- to generic, but I don't need further properties. One could show it forms a ring
  field
    Carrier : Type ℓ₁
    _≈_ : Rel Carrier Carrier ℓ₂
    IsRelEquiv : EquivRel Carrier ℓ₂
    IsSetCarrier : isSet Carrier

IntSetoid : Setoid {ℓ-zero} {ℓ-zero}
IntSetoid = record 
  { Carrier = IntCarrier
  ; _≈_ = same-diff
  ; IsRelEquiv = isEquiv-≈  
  ; IsSetCarrier = Discrete→isSet (discreteΣ discreteℕ λ _ → discreteℕ)
  }

record Int : Type₁ where
  constructor _/_
  field
    num : IntCarrier
    .eq/ : num ≈ num
    pos : Nat  -- Canonical positive part
    neg : Nat  -- Canonical negative part
    .canon : num ≈ (pos , neg)
    .IsSetoid : Setoid {ℓ-zero} {ℓ-zero}

mkInt : (a b : Nat) → Int
mkInt a b with a ≟ b
... | lt x = record { num = (0 , b ∸ a); eq/ = ≈-refl (zero , b ∸ a); pos = 0; neg = b ∸ a; canon = +-comm zero (b ∸ a); IsSetoid = IntSetoid }
... | eq x = record { num = (0 , 0); eq/ = ≈-refl (zero , zero); pos = 0; neg = 0; canon = refl; IsSetoid = IntSetoid }
... | gt x = record { num = (a ∸ b , 0); eq/ = ≈-refl (a ∸ b , zero); pos = a ∸ b; neg = 0; canon = +-comm (a ∸ b) zero ; IsSetoid = IntSetoid  }

ℤtoℕ : Nat → Int
ℤtoℕ n = mkInt n 0

ℕtoℤ : Int → Nat -- sum of the modules
ℕtoℤ ((_ / _) pos neg _ _) = pos + neg

ℕtoℤ' : Int → Nat -- module of the canonical rep
ℕtoℤ' ((_ / _) pos neg _ _) with pos ≟ neg
... | lt x = neg ∸ pos
... | eq x = 0
... | gt x = pos ∸ neg
