#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/Assertions :as a)
(import ../Utils/ReductionPaths :as red)

(def suite (test/start-suite "Property Preservation"))

(var rng (gen/rng))

(defn prop-inferable-judgments-match-declared-types [n]
  "Property: each inferable judgment has the declared type"
  (var passed true)
  (repeat n
    (let [sample (gen/gen-inferable-judgment rng)
          Γ (sample :ctx)
          tm (sample :term)
          type-tm (sample :type-tm)
          expected (c/eval Γ type-tm)]
        (try
          (do
            (unless (c/sem-eq (c/ty/type 100) (c/infer Γ tm) expected)
              (set passed false)
              (print "Declared type mismatch:")
              (print "  seed =" (gen/seed/current))
              (print "  kind =" (sample :kind))
              (print "  ctx =" Γ)
              (print "  term =" tm)
              (print "  declared =" type-tm)))
          ([err]
            (set passed false)
            (print "Generated witness rejected:")
            (print "  seed =" (gen/seed/current))
            (print "  kind =" (sample :kind))
            (print "  ctx =" Γ)
            (print "  term =" tm)
            (print "  type =" type-tm)
            (print "  err =" err)))))
  passed)

(test/assert suite
  (prop-inferable-judgments-match-declared-types (test/property-count 50))
  "Property: inferable judgments have their declared types")

(defn prop-reduction-witness-contracts [n]
  "Property: each reducible witness contracts to its declared contractum"
  (var passed true)
  (repeat n
    (let [sample (gen/gen-reducible-sample rng)
          tm (sample :term)
          tm-next (sample :contractum)
          actual-step (red/step-reduce tm)]
      (unless (= actual-step tm-next)
        (set passed false)
        (print "Reduction witness mismatch:")
        (print "  seed =" (gen/seed/current))
        (print "  kind =" (sample :kind))
        (print "  term =" tm)
        (print "  expected step =" tm-next)
        (print "  actual step =" actual-step))))
  passed)

(test/assert suite
  (prop-reduction-witness-contracts (test/property-count 50))
  "Property: reducible witnesses contract as declared")

(defn prop-preservation-via-normalization [n]
  "Property: reducing a witnessed redex does not change its normal form"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen/gen-reducible-sample rng)
          tm (sample :term)
          tm-next (sample :contractum)
          ty (c/eval Γ (sample :type-tm))
          nf-tm (c/nf ty tm)
          nf-step (c/nf ty tm-next)]
      (unless (a/nf-eq? nf-tm nf-step)
        (set passed false)
        (print "Normalization witness mismatch:")
        (print "  seed =" (gen/seed/current))
        (print "  kind =" (sample :kind))
        (print "  term =" tm)
        (print "  step =" tm-next)
        (print "  nf(term) =" nf-tm)
        (print "  nf(step) =" nf-step)))))
  passed)

(test/assert suite
  (prop-preservation-via-normalization (test/property-count 50))
  "Property: witnessed reductions preserve normal forms")

(test/end-suite suite)
