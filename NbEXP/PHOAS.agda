-- This is an extension on the Oleg implementation of PHOAS NbE
-- to support builtin natural numbers, products and general recursion via fixed-points
-- https://oleg.fi/gists/posts/2025-02-11-nbe-phoas.html

module PHOAS where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)

module Lib where
  _×_ : ∀ (A : Set) (B : Set) → Set
  A × B = Σ A (λ _ → B)
  
  case_of_ : ∀ {A B : Set} → A → (A → B) → B
  case x of f = f x
  {-# INLINE case_of_ #-}
open Lib

data Ty : Set where
  emp : Ty
  nat : Ty
  fun : Ty → Ty → Ty
  par : Ty → Ty → Ty

private
  variable
    v : Ty → Set
    a b c d e : Ty
    n : ℕ

data Tm (v : Ty → Set) : Ty → Set where
  var  : v a → Tm v a
  app  : Tm v (fun a b) → Tm v a → Tm v b
  lam  : (v a → Tm v b) → Tm v (fun a b)
  zero : Tm v nat
  succ : Tm v nat → Tm v nat
  case : Tm v nat → Tm v a → (v nat → Tm v a) → Tm v a
  fix  : (v a → Tm v a) → Tm v a
  pair : Tm v a → Tm v b → Tm v (par a b)
  fst  : Tm v (par a b) → Tm v a
  snd  : Tm v (par a b) → Tm v b

syntax lam (λ x → bod) = ƛ x => bod
syntax case s z (λ x → sc) = match s zero => z succ x => sc
syntax fix (λ x → bod) = µ x => bod

-- Normal forms and neutral terms with proper support for all types
data Nf (v : Ty → Set) : Ty → Set
data Ne (v : Ty → Set) : Ty → Set

data Ne v where
  nvar  : v a → Ne v a
  napp  : Ne v (fun a b) → Nf v a → Ne v b
  nsucc : Ne v nat → Ne v nat
  ncase : Ne v nat → Nf v a → (v nat → Nf v a) → Ne v a
  nepair : Ne v a → Ne v b → Ne v (par a b)
  nfst  : Ne v (par a b) → Ne v a
  nsnd  : Ne v (par a b) → Ne v b

data Nf v where
  nneut : Ne v a → Nf v a
  nlam  : (v a → Nf v b) → Nf v (fun a b)
  nnat  : ℕ → Nf v nat
  npair : Nf v a → Nf v b → Nf v (par a b)

-- Semantic domain: for emp and nat we use Nf, for functions we use actual functions
Sem : (Ty → Set) → Ty → Set
Sem v emp = Nf v emp
Sem v nat = Nf v nat
Sem v (fun a b) = Sem v a → Sem v b
Sem v (par a b) = Sem v a × Sem v b

-- raise converts neutral terms to semantic values (reify)
-- lower converts semantic values to normal forms  (reflects)
raise : ∀ (a : Ty) → Ne v a → Sem v a
lower : ∀ (a : Ty) → Sem v a → Nf v a

raise emp ne = nneut ne
raise nat ne = nneut ne
raise (fun a b) ne = λ x → raise b (napp ne (lower a x))
raise (par a b) ne = raise a (nfst ne) , raise b (nsnd ne)

lower emp nf = nf
lower nat nf = nf
lower (fun a b) f = nlam (λ x → lower b (f (raise a (nvar x))))
lower (par a b) (x , y) = npair (lower a x) (lower b y)

{-# TERMINATING #-}
eval : Tm (Sem v) a → Sem v a
eval (var x) = x
eval (app f t) = eval f (eval t)
eval (lam t) = λ x → eval (t x)
eval zero = nnat 0
eval (succ t) = case eval t of λ where
  (nnat n) → nnat (suc n)
  (nneut ne) → nneut (nsucc ne)
eval (case s z sc) = case eval s of λ where
  (nnat zero) → eval z
  (nnat (suc n)) → eval (sc (nnat n))
  (nneut ne) → raise _ (ncase ne (lower _ (eval z)) (λ x → lower _ (eval (sc (raise nat (nvar x))))))
eval (fix f) = eval (f (eval (fix f)))
eval (pair l r) = (eval l , eval r)
eval (fst l) with eval l
... | (pl , _) = pl
eval (snd r) with eval r
... | (_ , pr) = pr

nf : Tm (Sem v) a → Nf v a
nf {a = a} t = lower a (eval t)

nf_parametric : ({v : Ty → Set} → Tm v a) → ({v : Ty → Set} → Nf v a)
nf_parametric t = nf t

-- -- Programs in our language

-- add : Tm v (fun nat (fun nat nat))
-- add = µ rec => ƛ n => ƛ m =>
--   match var n
--     zero => var m
--     succ n' => succ (app (app (var rec) (var n')) (var m))

-- fib : Tm v (fun nat nat)
-- fib = µ rec => ƛ n =>
--   match var n
--     zero    => zero
--     succ n' => match var n'
--                  zero     => succ zero
--                  succ n'' => app (app add 
--                                        (app (var rec) (var n')))
--                                        (app (var rec) (var n''))

-- loop : Tm v (fun nat nat)
-- loop = µ rec => ƛ n => app (var rec) (var n)

-- true : Tm v (fun emp (fun emp emp))
-- true = ƛ t => ƛ f => var t

-- false : Tm v (fun emp (fun emp emp))
-- false = ƛ t => ƛ f => var f

-- if_then_else_ : Tm v (fun emp (fun emp emp)) → Tm v emp → Tm v emp → Tm v emp
-- if b then this else that = app (app b this) that

-- -- Helper to translate from Agda Nat to PHOAS Nat
-- nat→Tm : ℕ → Tm v nat
-- nat→Tm 0 = zero
-- nat→Tm (suc n) = succ (nat→Tm n)

-- -- Extract ℕ from semantic value
-- sem→ℕ : Sem v nat → ℕ
-- sem→ℕ (nnat n) = n
-- sem→ℕ (nneut _) = 0  -- Neutral - shouldn't happen for closed terms

-- -- Eval functions that return Agda ℕ
-- fib-eval : ∀ n → ℕ
-- fib-eval n = sem→ℕ (eval {λ _ → Sem (λ _ → ℕ) emp} (app fib (nat→Tm n)))

-- add-eval : ∀ n m → ℕ
-- add-eval n m = sem→ℕ (eval {λ _ → Sem (λ _ → ℕ) emp} (app (app add (nat→Tm n)) (nat→Tm m)))

-- -- Normal form functions
-- fib-nf : ∀ n → Nf v nat
-- fib-nf n = nf (app fib (nat→Tm n))

-- add-nf : ∀ n m → Nf v nat
-- add-nf n m = nf (app (app add (nat→Tm n)) (nat→Tm m))

-- -- Uncurry for arbitrary arity - the Agda way
-- -- We define a family of uncurry functions for different arities
-- -- This is the most practical approach that actually type-checks

-- -- For 0 arguments (identity)
-- uncurry0 : Tm v a → Tm v a
-- uncurry0 f = f

-- -- For 1 argument (just app)
-- uncurry1 : Tm v (fun a b) → Tm v a → Tm v b
-- uncurry1 f x = app f x

-- -- For 2 arguments
-- uncurry2 : Tm v (fun a (fun b c)) → Tm v a → Tm v b → Tm v c
-- uncurry2 f x y = app (app f x) y

-- -- For 3 arguments
-- uncurry3 : Tm v (fun a (fun b (fun c d))) → Tm v a → Tm v b → Tm v c → Tm v d
-- uncurry3 f x y z = app (app (app f x) y) z

-- -- Example: using uncurry2 with add
-- add-uncurried : Tm v nat → Tm v nat → Tm v nat
-- add-uncurried = uncurry2 add

-- -- Test
-- test-uncurry2 : Tm v nat
-- test-uncurry2 = add-uncurried zero zero
