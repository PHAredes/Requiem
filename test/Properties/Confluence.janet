#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/ReductionPaths :as red)
(import ../Utils/Assertions :as a)

(def suite (test/start-suite "Property Confluence"))

(var rng (gen/rng))

(defn prop-local-diamond [n]
  "Property: the explicit overlapping beta-redex witness is locally confluent"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen/gen-reduction-diamond rng)
          ty (c/eval Γ (sample :type))
          left (sample :left)
          right (sample :right)
          join (sample :join)
          nf-left (c/nf ty left)
          nf-right (c/nf ty right)
          nf-join (c/nf ty join)]
      (unless (and (a/nf-eq? nf-left nf-join)
                   (a/nf-eq? nf-right nf-join))
        (set passed false)
        (print "Local confluence failed:")
        (print "  seed =" (gen/seed/current))
        (print "  term =" (sample :term))
        (print "  left =" left)
        (print "  right =" right)
        (print "  join =" join)
        (print "  nf(left) =" nf-left)
        (print "  nf(right) =" nf-right)
        (print "  nf(join) =" nf-join)))))
  passed)

(test/assert suite
  (prop-local-diamond (test/property-count 50))
  "Property: local diamond witnesses rejoin")

(defn prop-leftmost-rightmost-agree [n]
  "Property: both reduction strategies reach the same normal form on the diamond witness"
  (var passed true)
  (let [Γ (c/ctx/empty)]
    (repeat n
      (let [sample (gen/gen-reduction-diamond rng)
          tm (sample :term)
          ty (c/eval Γ (sample :type))
          paths (red/get-reduction-paths tm)
          left-path (paths 0)
          right-path (paths 1)
          left-step (if (> (length left-path) 1) (left-path 1) nil)
          right-step (if (> (length right-path) 1) (right-path 1) nil)
          left-final (left-path (dec (length left-path)))
          right-final (right-path (dec (length right-path)))
          left-nf (c/nf ty left-final)
          right-nf (c/nf ty right-final)]
      (unless (and left-step
                   right-step
                   (not (= left-step right-step))
                   (a/nf-eq? left-nf right-nf))
        (set passed false)
        (print "Strategy join failed:")
        (print "  seed =" (gen/seed/current))
        (print "  term =" tm)
        (print "  actual left step =" left-step)
        (print "  actual right step =" right-step)
        (print "  left path =" left-path)
        (print "  right path =" right-path)
        (print "  left nf =" left-nf)
        (print "  right nf =" right-nf)))))
  passed)

(test/assert suite
  (prop-leftmost-rightmost-agree (test/property-count 50))
  "Property: leftmost and rightmost reduction agree on normal forms")

(test/end-suite suite)
