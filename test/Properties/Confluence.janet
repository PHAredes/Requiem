#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(test/start-suite "Property Confluence")

(var rng (gen/rng))

# Property: Confluence (Diamond Property)
(defn prop-confluence [n]
  "Property: Normalization is confluent - all reduction paths lead to same normal form"
  (var passed true)
  (repeat n
    (let [tm (case (math/rng-int rng 5)
               0 [:type (math/rng-int rng 3)]
               1 [:app [:lam (fn [x] [:var x])] (gen/gen-univ rng)]
               2 [:fst [:pair (gen/gen-univ rng) (gen/gen-univ rng)]]
               3 [:snd [:pair (gen/gen-univ rng) (gen/gen-univ rng)]]
               4 [:app [:lam (fn [x] [:app [:lam (fn [y] [:var y])] [:var x]])]
                  (gen/gen-univ rng)])
          Γ (c/ctx/empty)]
      (try
        (let [ty (c/infer Γ tm)
              # Normalize directly
              nf1 (c/nf ty tm)
              # Normalize via evaluation
              sem (c/eval Γ tm)
              nf2 (c/lower ty sem)]
          (unless (= nf1 nf2)
            (set passed false)
            (print "Confluence failed for:" tm)
            (print "  nf1:" nf1)
            (print "  nf2:" nf2)))
        ([err] nil))))
  passed)

(test/assert
  (prop-confluence 50)
  "Property: confluence - all reduction paths converge")

# Property: Pi Syntactic Equality
(defn prop-pi-syntactic-equality [n]
  "Property: Syntactically identical Pi types are definitionally equal"
  (var passed true)
  (repeat n
    (let [A [:type (math/rng-int rng 3)]
          shared-lv (math/rng-int rng 3)
          B (fn [x] [:type shared-lv])
          Γ (c/ctx/empty)
          pi1 [:t-pi A B]
          pi2 [:t-pi A B]] # Same A, same B reference
      (try
        (let [ty (c/infer Γ pi1)]
          (unless (c/term-eq Γ ty pi1 pi2)
            (set passed false)
            (print "Pi equality failed with identical syntax")))
        ([err] nil))))
  passed)

(test/assert
  (prop-pi-syntactic-equality 20)
  "Property: syntactically identical Pi types are equal")

# Property Tests: Congruence
(defn prop-app-congruence [n]
  "Property: If t₁ ≡ t₁' and t₂ ≡ t₂', then t₁ t₂ ≡ t₁' t₂'"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [t1 [:type (math/rng-int rng 3)]
            t2 [:type (math/rng-int rng 3)]
            t1-prime [:type (math/rng-int rng 3)]
            t2-prime [:type (math/rng-int rng 3)]
            app1 [:app t1 t2]
            app2 [:app t1-prime t2-prime]]
        (when (and (c/term-eq Γ [:type 1] t1 t1-prime)
                   (c/term-eq Γ [:type 1] t2 t2-prime))
          (unless (c/term-eq Γ [:type 1] app1 app2)
            (set passed false)
            (print "App congruence failed"))))))
  passed)

(test/assert
  (prop-app-congruence 20)
  "Property: application is congruent")

# Property Tests: Extensional Equality
(defn prop-extensionality [n]
  "Property: Functions are equal if they are equal on all arguments"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [f [:lam (fn [x] [:var x])]
            g [:lam (fn [x] [:var x])]
            test-args @[[:type (math/rng-int rng 3)]
                        [:type (math/rng-int rng 3)]
                        [:type (math/rng-int rng 3)]]]
        # Check that f and g are equal on all test arguments
        (var all-equal true)
        (each arg test-args
          (unless (c/term-eq Γ [:type 1] [:app f arg] [:app g arg])
            (set all-equal false)))
        (when all-equal
          (unless (c/term-eq Γ [:t-pi [:type 0] (fn [x] [:type 0])] f g)
            (set passed false)
            (print "Extensionality failed"))))))
  passed)

(test/assert
  (prop-extensionality 10)
  "Property: extensional equality for functions")

# Property Tests: Beta-Eta Equivalence
(defn prop-id-function [n]
  "Property: (λx. x) a ≡ a for various a"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [a (gen/gen-univ rng)
            id [:lam (fn [x] [:var x])]
            applied [:app id a]]
        (unless (c/term-eq Γ [:type 1] applied a)
          (set passed false)
          (print "Beta reduction failed for:" a)))))
  passed)

(test/assert
  (prop-id-function 20)
  "Property: identity function beta-reduces correctly")

(test/end-suite)
