#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/ReductionPaths :as red)

(def suite (test/start-suite "Property Soundness"))

(var rng (gen/rng))

(defn value? [tm]
  (if (not (tuple? tm))
    false
    (case (tm 0)
      :type true
      :t-pi true
      :t-sigma true
      :t-id true
      :lam true
      :pair (and (value? (tm 1)) (value? (tm 2)))
      :t-refl (value? (tm 1))
      false)))

(defn prop-progress [n]
  "Property: every generated closed witness in the fragment is a value or takes a step"
  (var passed true)
  (repeat n
    (let [sample (gen/gen-fragment-sample rng)
          tm (sample :term)
          step (red/step-reduce tm)]
      (unless (or (value? tm) step)
        (set passed false)
        (print "Progress failed:")
        (print "  seed =" (gen/seed/current))
        (print "  kind =" (sample :kind))
        (print "  term =" tm)
        (print "  type =" (sample :type-tm)))))
  passed)

(test/assert suite
  (prop-progress (test/property-count 50))
  "Property: generated closed witnesses satisfy progress")

(defn prop-witnessed-step-is-the-next-step [n]
  "Property: reducible witnesses step exactly to their declared contractum"
  (var passed true)
  (repeat n
    (let [sample (gen/gen-reducible-sample rng)
          tm (sample :term)
          expected-step (sample :contractum)
          actual-step (red/step-reduce tm)]
      (unless (= actual-step expected-step)
        (set passed false)
        (print "Unexpected reduction step:")
        (print "  seed =" (gen/seed/current))
        (print "  kind =" (sample :kind))
        (print "  term =" tm)
        (print "  expected =" expected-step)
        (print "  actual =" actual-step))))
  passed)

(test/assert suite
  (prop-witnessed-step-is-the-next-step (test/property-count 50))
  "Property: reducible witnesses contract as expected")

(defn prop-normal-forms-are-values [n]
  "Property: normalizing a generated witness produces a canonical value"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen/gen-fragment-sample rng)
            ty (c/eval Γ (sample :type-tm))
            nf (c/nf ty (sample :term))]
      (match nf
        [c/NF/Type _] true
        [c/NF/Lam _] true
        [c/NF/Pair _ _] true
        [c/NF/Refl _] true
        _ (do
            (set passed false)
            (print "Unexpected normal form:")
            (print "  seed =" (gen/seed/current))
            (print "  kind =" (sample :kind))
            (print "  term =" (sample :term))
            (print "  nf =" nf))))))
  passed)

(test/assert suite
  (prop-normal-forms-are-values (test/property-count 50))
  "Property: generated witnesses normalize to canonical values")

(test/end-suite suite)
