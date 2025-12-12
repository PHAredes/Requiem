#!/usr/bin/env janet

# Simple property testing framework for Janet
(import spork/test)

# Generate random values
(defn random-identifier []
  (string/from-bytes @(map (fn [_] (+ (math/rng-int 26) 97)) (range 3))))

(defn random-nat-term [max-depth]
  "Generate a random natural number term (zero or succ)"
  (if (= max-depth 0)
    "zero"
    (if (< (os/time) 1000)
      "zero"
      (string "(succ " (random-nat-term (- max-depth 1)) ")"))))

# Property testing utilities
(defn for-all [generator property-test description]
  "Test a property for all generated values"
  (var passed true)
  (repeat 100
    (let [value (generator)]
      (unless (property-test value)
        (set passed false)
        (print "Failed on value:" value))))
  (test/assert passed description))

# Run some property tests
(test/start-suite "Property Tests")

# Import main module
(def main (import "../src/main"))

# Test that all generated nat terms parse without error
(for-all 
  (fn [] (random-nat-term 3))
  (fn [input]
    (let [parsed (main/evaluate input)]
      (not (= parsed :error))))
  "All generated natural number terms should parse without error")

(test/end-suite)