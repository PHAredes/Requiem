#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/Assertions :as a)

(def suite (test/start-suite "Property Normalization"))

(var rng (gen/rng))

(test/assert suite
  (a/normalization-stable
    (c/ty/type 1)
    [:type 0])
  "Normalization stability: simple type")

(test/assert suite
  (a/normalization-stable
    (c/ty/pi (c/ty/type 0) (fn [_] (c/ty/type 0)))
    [:lam (fn [x] x)])
  "Normalization stability: identity function")

(defn prop-values-normalize-to-canonical-forms [n]
  "Property: generated closed values normalize to the expected canonical shape"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen/gen-canonical-sample rng)
            nf (c/nf (c/eval Γ (sample :type-tm)) (sample :term))
            ok? (case (sample :kind)
                  :universe (match nf [c/NF/Type _] true _ false)
                  :identity (match nf [c/NF/Lam _] true _ false)
                  :constant (match nf [c/NF/Lam _] true _ false)
                  :pair (match nf [c/NF/Pair _ _] true _ false)
                  :refl (match nf [c/NF/Refl _] true _ false)
                  :pi-type (match nf [c/NF/Pi _ _] true _ false)
                  :sigma-type (match nf [c/NF/Sigma _ _] true _ false)
                  false)]
        (unless ok?
          (set passed false)
          (print "Unexpected canonical form:")
          (print "  seed =" (gen/seed/current))
          (print "  kind =" (sample :kind))
          (print "  term =" (sample :term))
          (print "  nf =" nf)))))
  passed)

(test/assert suite
  (prop-values-normalize-to-canonical-forms (test/property-count 50))
  "Property: generated closed values normalize canonically")

(defn prop-reduction-normalizes-to-contractum [n]
  "Property: reducible witnesses normalize to the same form as their contractum"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen/gen-reducible-sample rng)
          ty (c/eval Γ (sample :type-tm))
          tm (sample :term)
          contractum (sample :contractum)
          nf-tm (c/nf ty tm)
          nf-contractum (c/nf ty contractum)]
      (unless (a/nf-eq? nf-tm nf-contractum)
        (set passed false)
        (print "Reduction normalization failed:")
        (print "  seed =" (gen/seed/current))
        (print "  kind =" (sample :kind))
        (print "  term =" tm)
        (print "  contractum =" contractum)
        (print "  nf(term) =" nf-tm)
        (print "  nf(contractum) =" nf-contractum)))))
  passed)

(test/assert suite
  (prop-reduction-normalizes-to-contractum (test/property-count 50))
  "Property: reducible witnesses normalize like their contracta")

(defn prop-eval-deterministic [n]
  "Property: repeated evaluation lowers to the same normal form"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen/gen-fragment-sample rng)
            tm (sample :term)
            ty (c/eval Γ (sample :type-tm))
            v1 (c/eval Γ tm)
            v2 (c/eval Γ tm)
            nf1 (c/lower ty v1)
            nf2 (c/lower ty v2)]
        (unless (a/nf-eq? nf1 nf2)
          (set passed false)
          (print "Evaluation/lowering mismatch:")
          (print "  seed =" (gen/seed/current))
          (print "  kind =" (sample :kind))
          (print "  term =" tm)
          (print "  nf1 =" nf1)
          (print "  nf2 =" nf2)))))
  passed)

(test/assert suite
  (prop-eval-deterministic (test/property-count 50))
  "Property: evaluation is deterministic")

(test/end-suite suite)
