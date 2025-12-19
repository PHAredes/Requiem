#!/usr/bin/env janet

(import spork/test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(test/start-suite "Equality Eta")

(var rng (gen/rng))

# ===============================================
# Property: Eta for Functions (Extensionality)
# ===============================================
(defn prop-eta-functions [n]
  "Property: λx. f x ≡ f (eta-expansion)"
  (var passed true)
  (repeat n
    (let [fresh (gensym)
          A [:type (math/rng-int rng 3)]
          f-var [:var fresh]
          eta-expanded [:lam (fn [x] [:app f-var [:var x]])]
          Γ (c/ctx/empty)
          A-sem (c/eval Γ A)
          pi-ty [:Pi A-sem (fn [x] A-sem)]
          Γ2 (c/ctx/add Γ fresh pi-ty)]
      (try
        (unless (c/term-eq Γ2 pi-ty f-var eta-expanded)
          (set passed false)
          (print "Eta-expansion failed for functions"))
        ([err] nil))))
  passed)

(test/assert
  (prop-eta-functions 20)
  "Property: eta-equality for functions")

# ===============================================
# Property: Eta for Pairs
# ===============================================
(defn prop-eta-pairs [n]
  "Property: (fst p, snd p) ≡ p (eta-expansion)"
  (var passed true)
  (repeat n
    (let [fresh (gensym)
          A [:type (math/rng-int rng 3)]
          p-var [:var fresh]
          eta-expanded [:pair [:fst p-var] [:snd p-var]]
          Γ (c/ctx/empty)
          A-sem (c/eval Γ A)
          sigma-ty [:Sigma A-sem (fn [x] A-sem)]
          Γ2 (c/ctx/add Γ fresh sigma-ty)]
      (try
        (unless (c/term-eq Γ2 sigma-ty p-var eta-expanded)
          (set passed false)
          (print "Eta-expansion failed for pairs"))
        ([err] nil))))
  passed)

(test/assert
  (prop-eta-pairs 20)
  "Property: eta-equality for pairs")

(test/end-suite)
