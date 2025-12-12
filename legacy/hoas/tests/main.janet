#!/usr/bin/env janet

# Tests for main.janet

(import spork/test)
(import ../src/main :as main)

(test/start-suite)

# Basic natural numbers
(test/assert (= (main/parse-and-print "zero") "0")
             "zero")

(test/assert (= (main/parse-and-print "succ zero") "1")
             "succ zero")

(test/assert (= (main/parse-and-print "0") "0")
             "number literal 0")

(test/assert (= (main/parse-and-print "5") "5")
             "number literal 5")

(test/assert (= (main/parse-and-print "succ (succ zero)") "2")
             "nested succ")

# Lambda expressions
(test/assert (= (main/parse-and-print "\\x => x") "λx => x")
             "identity")

(test/assert (= (main/parse-and-print "\\x => \\y => x") "λx => λx => x")
             "const")

(test/assert (= (main/parse-and-print "\\x => succ x") "λx => succ x")
             "succ function")

# Applications
(test/assert (= (main/parse-and-print "(\\x => x) zero") "0")
             "apply identity to zero")

(test/assert (= (main/parse-and-print "(\\x => succ x) 3") "4")
             "apply succ to 3")

# Fixed points
(test/assert (= (main/parse-and-print "µf => zero") "0")
             "simple fix")

# Pairs
(test/assert (= (main/parse-and-print "(zero, zero)") "(0, 0)")
             "pair of zeros")

(test/assert (= (main/parse-and-print "fst (zero, succ zero)") "0")
             "pair projection fst")

(test/assert (= (main/parse-and-print "snd (zero, succ zero)") "1")
             "pair projection snd")

# Match expressions
(test/assert (= (main/parse-and-print "match zero { zero => 1 | succ x => 2 }") "1")
             "match zero")

(test/assert (= (main/parse-and-print "match (succ zero) { zero => 0 | succ x => x }") "0")
             "match succ")

# Complex expressions
(test/assert (= (main/parse-and-print "(\\f => \\x => f (f x)) (\\y => succ y) zero") "2")
             "double application")

(test/end-suite)
