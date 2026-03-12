#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/Assertions :as a)
(import ../Utils/ReductionPaths :as red)

(def suite (test/start-suite "Property Substitution"))

(var rng (gen/rng))

(defn substitution-sample/identity [rng]
  (let [arg-lvl (gen/gen-level rng 3)
        arg [:type arg-lvl]
        A [:type (inc arg-lvl)]
        body (fn [x] x)]
    @{:kind :identity
      :arg arg
      :type-tm A
      :app [:app [:lam body] arg]
      :beta-step arg
      :direct arg}))

(defn substitution-sample/duplicate [rng]
  (let [arg-lvl (gen/gen-level rng 3)
        arg [:type arg-lvl]
        A [:type (inc arg-lvl)]
        body (fn [x] [:pair x x])
        result-ty [:t-sigma A (fn [_] A)]]
    @{:kind :duplicate
      :arg arg
      :type-tm result-ty
      :app [:app [:lam body] arg]
      :beta-step [:pair arg arg]
      :direct [:pair arg arg]}))

(defn substitution-sample/projection [rng]
  (let [arg-lvl (gen/gen-level rng 3)
        arg [:type arg-lvl]
        A [:type (inc arg-lvl)]
        body (fn [x] [:fst [:pair x [:type 0]]])]
    @{:kind :projection
      :arg arg
      :type-tm A
      :app [:app [:lam body] arg]
      :beta-step [:fst [:pair arg [:type 0]]]
      :direct arg}))

(defn gen-substitution-sample [rng]
  ((gen/choose rng @[
     substitution-sample/identity
     substitution-sample/duplicate
     substitution-sample/projection
   ]) rng))

(defn prop-beta-realizes-substitution [n]
  "Property: beta reduction agrees with direct HOAS substitution on witnessed families"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen-substitution-sample rng)
          ty (c/eval Γ (sample :type-tm))
          app-result (c/nf ty (sample :app))
          direct-result (c/nf ty (sample :direct))]
      (unless (a/nf-eq? app-result direct-result)
        (set passed false)
        (print "Substitution failed:")
        (print "  seed =" (gen/seed/current))
        (print "  kind =" (sample :kind))
        (print "  arg =" (sample :arg))
        (print "  app =" (sample :app))
        (print "  direct =" (sample :direct))
        (print "  nf(app) =" app-result)
        (print "  nf(direct) =" direct-result)))))
  passed)

(test/assert suite
  (prop-beta-realizes-substitution (test/property-count 50))
  "Property: beta implements substitution on witnessed bodies")

(defn prop-substitution-witness-contracts [n]
  "Property: each substitution witness contracts in one step to the direct substitution result"
  (var passed true)
  (repeat n
    (let [sample (gen-substitution-sample rng)
          step (red/step-reduce (sample :app))]
      (unless (= step (sample :beta-step))
        (set passed false)
        (print "Substitution step mismatch:")
        (print "  seed =" (gen/seed/current))
        (print "  kind =" (sample :kind))
        (print "  app =" (sample :app))
        (print "  expected =" (sample :beta-step))
        (print "  actual =" step))))
  passed)

(test/assert suite
  (prop-substitution-witness-contracts (test/property-count 50))
  "Property: substitution witnesses contract to direct substitution")

(test/end-suite suite)
