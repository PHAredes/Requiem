#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(def suite (test/start-suite "Property Decidability"))

(var rng (gen/rng))

(defn prop-check-infer-consistent [n]
  "Property: inferred types are accepted by checking on generated inferable judgments"
  (var passed true)
  (repeat n
    (let [sample (gen/gen-inferable-judgment rng)
          Γ (sample :ctx)
          tm (sample :term)]
        (try
          (let [inferred (c/infer Γ tm)]
            (c/check Γ tm inferred))
          ([err]
            (set passed false)
            (print "Check/infer inconsistency:")
            (print "  seed =" (gen/seed/current))
            (print "  kind =" (sample :kind))
            (print "  ctx =" Γ)
            (print "  term =" tm)
            (print "  err =" err)))))
  passed)

(test/assert suite
  (prop-check-infer-consistent (test/property-count 50))
  "Property: generated closed witnesses satisfy check/infer consistency")

(defn prop-negative-examples-reject [n]
  "Property: known ill-typed forms are rejected"
  (var passed true)
  (repeat n
    (let [bad (case (math/rng-int rng 4)
                0 [:app [:type 0] [:type 0]]
                1 [:fst [:type 0]]
                2 [:snd [:type 0]]
                3 [:t-refl [:lam (fn [x] [:var x])]])]
      (try
        (do
          (c/infer-top bad)
          (set passed false)
          (print "Ill-typed term unexpectedly inferred:")
          (print "  seed =" (gen/seed/current))
          (print "  term =" bad))
        ([err] nil))))
  passed)

(test/assert suite
  (prop-negative-examples-reject (test/property-count 30))
  "Property: representative ill-typed forms are rejected")

(test/end-suite suite)
