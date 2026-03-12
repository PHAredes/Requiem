#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/Assertions :as a)

(def suite (test/start-suite "Property Church-Rosser"))

(var rng (gen/rng))

(defn prop-convertible-terms-share-normal-form [n]
  "Property: each witnessed one-step contraction lands in the same normal form"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen/gen-convertible-pair rng)
          tm (sample :term)
          u (sample :contractum)
          ty (c/eval Γ (sample :type))
          nf-t (c/nf ty tm)
          nf-u (c/nf ty u)]
      (unless (a/nf-eq? nf-t nf-u)
        (set passed false)
        (print "Church-Rosser failed:")
        (print "  seed =" (gen/seed/current))
        (print "  kind =" (sample :kind))
        (print "  t =" tm)
        (print "  u =" u)
        (print "  nf(t) =" nf-t)
        (print "  nf(u) =" nf-u)))))
  passed)

(test/assert suite
  (prop-convertible-terms-share-normal-form (test/property-count 50))
  "Property: one-step convertible terms normalize equally")

(defn prop-convertible-terms-are-definitionally-equal [n]
  "Property: witnessed contractions preserve definitional equality at their declared type"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
        (let [sample (gen/gen-convertible-pair rng)
            tm (sample :term)
            u (sample :contractum)
            ty (sample :type)
            ty-sem (c/eval Γ ty)]
        (unless (c/term-eq Γ ty tm u)
          (set passed false)
          (print "Definitional equality failed:")
          (print "  seed =" (gen/seed/current))
          (print "  kind =" (sample :kind))
          (print "  type =" ty)
          (print "  t =" tm)
          (print "  u =" u)
          (print "  nf(t) =" (c/nf ty-sem tm))
          (print "  nf(u) =" (c/nf ty-sem u))))))
  passed)

(test/assert suite
  (prop-convertible-terms-are-definitionally-equal (test/property-count 50))
  "Property: witnessed contractions are definitionally equal")

(defn prop-raise-lower-roundtrip [n]
  "Property: lower(ty, raise(ty, ne)) preserves neutrals up to eta"
  (var passed true)
  (repeat n
    (let [x (gensym)
          ty (case (math/rng-int rng 3)
               0 (c/ty/type (math/rng-int rng 3))
               1 (c/ty/pi (c/ty/type 0) (fn [_] (c/ty/type 0)))
               2 (c/ty/sigma (c/ty/type 0) (fn [_] (c/ty/type 0))))
          ne (c/ne/var x)
          raised (c/raise ty ne)
          lowered (c/lower ty raised)
          ltag (if (tuple? lowered) (get lowered 0) 0)]
      (cond
        (= ltag c/NF/Neut)
        (unless (= ne (get lowered 1))
          (set passed false)
          (print "Raise/lower neutral mismatch:")
          (print "  ty =" ty)
          (print "  expected =" ne)
          (print "  got =" lowered))

        (or (= ltag c/NF/Lam) (= ltag c/NF/Pair)) true

        true
        (do
          (set passed false)
          (print "Unexpected lowered form:")
          (print "  ty =" ty)
          (print "  lowered =" lowered)))))
  passed)

(test/assert suite
  (prop-raise-lower-roundtrip (test/property-count 30))
  "Property: raise/lower preserves neutrals modulo eta")

(test/end-suite suite)
