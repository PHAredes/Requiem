#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)

(def suite (test/start-suite "Property Consistency"))

(test/assert-error suite
  (fn []
    (c/check-top
      [:t-refl [:type 0]]
      (c/eval (c/ctx/empty) [:t-id [:type 1] [:type 0] [:type 1]])))
  "refl does not inhabit a false identity type")

(test/assert-error suite
  (fn []
    (c/check-top
      [:lam (fn [x] [:var x])]
      (c/eval (c/ctx/empty) [:t-id [:type 1] [:type 0] [:type 1]])))
  "identity function does not inhabit an arbitrary identity type")

(test/end-suite suite)
