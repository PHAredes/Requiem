#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

(def suite (test/start-suite "Property Weakening"))

(var rng (gen/rng))

(defn prop-judgments-ignore-extra-bindings [n]
  "Property: adding an irrelevant binding does not change the inferred type of an inferable judgment"
  (var passed true)
  (repeat n
    (let [sample (gen/gen-inferable-judgment rng)
          tm (sample :term)
          Γ (sample :ctx)
          x (gensym)
          extra-ty (c/eval (c/ctx/empty) (gen/gen-simple-type rng))
          Γ+ (c/ctx/add Γ x extra-ty)]
      (try
        (let [ty (c/infer Γ tm)
              ty+ (c/infer Γ+ tm)]
          (unless (c/sem-eq (c/ty/type 100) ty ty+)
            (set passed false)
            (print "Weakening inference failed:")
            (print "  seed =" (gen/seed/current))
            (print "  kind =" (sample :kind))
            (print "  term =" tm)
            (print "  ty =" ty)
            (print "  ty+ =" ty+)))
        ([err]
          (set passed false)
          (print "Inferable judgment rejected during weakening:")
          (print "  seed =" (gen/seed/current))
          (print "  kind =" (sample :kind))
          (print "  ctx =" Γ)
          (print "  term =" tm)
          (print "  err =" err)))))
  passed)

(test/assert suite
  (prop-judgments-ignore-extra-bindings (test/property-count 50))
  "Property: irrelevant context extension preserves inferred types")

(defn prop-judgments-keep-declared-types [n]
  "Property: adding an irrelevant binding keeps the inferred type equal to the declared type"
  (var passed true)
  (repeat n
    (let [sample (gen/gen-inferable-judgment rng)
          tm (sample :term)
          type-tm (sample :type-tm)
          Γ (sample :ctx)
          x (gensym)
          extra-ty (c/eval (c/ctx/empty) (gen/gen-simple-type rng))
          Γ+ (c/ctx/add Γ x extra-ty)]
      (try
        (do
          (let [expected (c/eval Γ type-tm)
                expected+ (c/eval Γ+ type-tm)
                ty (c/infer Γ tm)
                ty+ (c/infer Γ+ tm)]
            (unless (and (c/sem-eq (c/ty/type 100) ty expected)
                         (c/sem-eq (c/ty/type 100) ty+ expected+))
              (set passed false)
              (print "Weakening declared-type mismatch:")
              (print "  seed =" (gen/seed/current))
              (print "  kind =" (sample :kind))
              (print "  ctx =" Γ)
              (print "  term =" tm)
              (print "  expected =" type-tm)
              (print "  ty =" ty)
              (print "  ty+ =" ty+))))
        ([err]
          (set passed false)
          (print "Weakening declared-type check failed:")
          (print "  seed =" (gen/seed/current))
          (print "  kind =" (sample :kind))
          (print "  ctx =" Γ)
          (print "  term =" tm)
          (print "  type =" type-tm)
          (print "  err =" err)))))
  passed)

(test/assert suite
  (prop-judgments-keep-declared-types (test/property-count 50))
  "Property: irrelevant context extension preserves declared types")

(test/end-suite suite)
