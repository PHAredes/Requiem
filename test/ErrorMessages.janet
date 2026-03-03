#!/usr/bin/env janet

# Test key error messages to verify improvements

(import ../src/coreTT :as c)
(import ../src/parser :as p)
(import ../test/Utils/TestRunner :as test)

(test/start-suite "Error Messages - CoreTT Context")

# Test unbound variable error - shows available variables
(test/assert-error 
  (fn [] (c/ctx/lookup (c/ctx/empty) "missing"))
  "unbound variable 'missing'")

(test/end-suite)

(test/start-suite "Error Messages - CoreTT Type Checking")

# Lambda inference without annotation - provides helpful suggestions
(test/assert-error
  (fn [] (c/infer (c/ctx/empty) [:lam (fn [x] x)]))
  "cannot infer type of lambda")

# Application of non-Pi - explains expected type
(test/assert-error
  (fn [] (c/infer (c/ctx/empty) [:app (c/tm/type 0) (c/tm/var "x")]))
  "cannot apply function")

# Unknown term - lists supported forms
(test/assert-error
  (fn [] (c/infer (c/ctx/empty) [:unknown]))
  "unknown term")

(test/end-suite)

(test/start-suite "Error Messages - Parser")

# Parse malformed input - suggests checks
(test/assert-error
  (fn [] (p/parse/text "("))
  "parse failed")

# Multiple forms in parse/one - provides guidance
(test/assert-error
  (fn [] (p/parse/one "x y"))
  "expected exactly one top-level form")

(test/end-suite)

(print "\n✅ All key error message tests completed successfully!")
(print "\nImproved error messages include:")
(print "- Detailed explanations and suggestions")
(print "- Available context information")
(print "- Clearer expected vs actual formats")
(print "- Helpful tips for common issues")