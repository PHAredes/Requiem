#!/usr/bin/env janet

# Test suite for main interface
(import spork/test)
(import "../src/main" :as main)

# Start test suite
(test/start-suite "Main Interface")

# Test command-line evaluation
(test/assert 
  (tuple? (main/evaluate "zero"))
  "main/evaluate should return a tuple for zero")

(test/assert
  (tuple? (main/evaluate "(succ zero)"))
  "main/evaluate should return a tuple for (succ zero)")

(test/assert
  (tuple? (main/evaluate "(pair l r)"))
  "main/evaluate should return a tuple for (pair l r)")

(test/assert
  (number? (main/evaluate "(fst p)"))
  "main/evaluate should return a number for (fst p)")

(test/assert
  (nil? (main/evaluate "(snd p)"))
  "main/evaluate should return nil for (snd p)")

(test/assert
  (= (main/evaluate "x") "x")
  "main/evaluate should return the variable name for x")

# Test case expression
(test/assert
  (tuple? (main/evaluate "(case s zero succ)"))
  "main/evaluate should return a tuple for (case s zero succ)")

# Test error handling
(test/assert
  (= (main/evaluate "123") :error)
  "main/evaluate should return :error for invalid expressions")

# Test string conversion - zero
(test/assert
  (= (main/term-to-string (main/evaluate "zero")) "zero")
  "term-to-string should convert zero back to 'zero'")

# Test string conversion - succ zero (should be 1)
(test/assert
  (= (main/term-to-string (main/evaluate "(succ zero)")) "1")
  "term-to-string should convert (succ zero) to '1'")

# Test string conversion - nested succ (should be 2)
(test/assert
  (= (main/term-to-string (main/evaluate "(succ (succ zero))")) "2")
  "term-to-string should convert (succ (succ zero)) to '2'")

# Test string conversion - triple nested succ (should be 3)
(test/assert
  (= (main/term-to-string (main/evaluate "(succ (succ (succ zero)))")) "3")
  "term-to-string should convert (succ (succ (succ zero))) to '3'")

# Test variables
(test/assert
  (= (main/term-to-string (main/evaluate "x")) "x")
  "term-to-string should return variable name as-is")

# Test pair
(test/assert
  (= (main/term-to-string (main/evaluate "(pair l r)")) "(pair l r)")
  "term-to-string should convert pair back to '(pair l r)'")

# Test fst
(test/assert
  (= (main/term-to-string (main/evaluate "(fst p)")) "112")
  "term-to-string should handle fst projection")

# Test snd
(test/assert
  (= (main/term-to-string (main/evaluate "(snd p)")) "")
  "term-to-string should handle snd projection")

# Test case returns a complex structure (just check it doesn't crash)
(test/assert
  (string? (main/term-to-string (main/evaluate "(case s zero succ)")))
  "term-to-string should return a string for case expressions")

# Finish test suite
(test/end-suite)