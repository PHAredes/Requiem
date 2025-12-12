#!/usr/bin/env janet

# Property testing for all term types
(import spork/test)

# Create a global RNG for consistent randomness
(def rng (math/rng))

# Generate random values
(defn random-identifier []
  # Generate a 3-letter random identifier
  (string 
    (string/from-bytes (+ (math/rng-int rng 26) 97))
    (string/from-bytes (+ (math/rng-int rng 26) 97))
    (string/from-bytes (+ (math/rng-int rng 26) 97))))

(defn random-nat-term [max-depth]
  "Generate a random natural number term (zero or succ)"
  (if (= max-depth 0)
    "zero"
    (if (< (math/rng-int rng 2) 1) # 50% chance
      "zero"
      (string "(succ " (random-nat-term (- max-depth 1)) ")"))))

(defn random-pair-term [max-depth]
  "Generate a random pair term"
  (if (= max-depth 0)
    (string "(pair " (random-identifier) " " (random-identifier) ")")
    (string "(pair " (random-identifier) " " (random-pair-term (- max-depth 1)) ")")))

(defn random-app-term [max-depth]
  "Generate a random application term"
  (if (= max-depth 0)
    (string "(app " (random-identifier) " " (random-identifier) ")")
    (string "(app " (random-app-term (- max-depth 1)) " " (random-identifier) ")")))

(defn random-lam-term [max-depth]
  "Generate a random lambda term"
  (if (= max-depth 0)
    (string "(lam " (random-identifier) " . " (random-identifier) ")")
    (string "(lam " (random-identifier) " . " (random-lam-term (- max-depth 1)) ")")))

(defn random-case-term [max-depth]
  "Generate a random case term"
  (if (= max-depth 0)
    (string "(case " (random-identifier) " " (random-identifier) " " (random-identifier) ")")
    (string "(case " (random-identifier) " " (random-case-term (- max-depth 1)) " " (random-identifier) ")")))

# Property testing utilities
(defn for-all [generator property-test description]
  "Test a property for all generated values"
  (var passed true)
  (repeat 50 # Reduced for faster testing
    (let [value (generator)]
      (unless (property-test value)
        (set passed false)
        (print "Failed on value:" value))))
  (test/assert passed description))

# Run property tests
(test/start-suite "Property Tests for All Term Types")

# Import main module
(def main (import "../src/main"))

# Test natural number terms
(for-all 
  (fn [] (random-nat-term 3))
  (fn [input]
    (let [parsed (main/evaluate input)]
      (not (= parsed :error))))
  "All generated natural number terms should parse without error")

# Test pair terms
(for-all 
  (fn [] (random-pair-term 2))
  (fn [input]
    (let [parsed (main/evaluate input)]
      (not (= parsed :error))))
  "All generated pair terms should parse without error")

# Test application terms
(for-all 
  (fn [] (random-app-term 2))
  (fn [input]
    (let [parsed (main/evaluate input)]
      (not (= parsed :error))))
  "All generated application terms should parse without error")

# Test lambda terms
(for-all 
  (fn [] (random-lam-term 2))
  (fn [input]
    (let [parsed (main/evaluate input)]
      (not (= parsed :error))))
  "All generated lambda terms should parse without error")

# Test case terms
(for-all 
  (fn [] (random-case-term 2))
  (fn [input]
    (let [parsed (main/evaluate input)]
      (not (= parsed :error))))
  "All generated case terms should parse without error")

(test/end-suite)
