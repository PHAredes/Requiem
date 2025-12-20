#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Assertions :as a)

(test/start-suite "Regression EdgeCases")

# ===============================================
# Edge Cases
# ===============================================

(a/assert-throws
  (fn [] (c/infer-top [:var "undefined"]))
  "Error: undefined variable throws")

(a/assert-throws
  (fn [] (c/infer-top [:lam (fn [x] [:var x])]))
  "Error: cannot infer lambda without annotation")

(a/assert-throws
  (fn [] (c/infer-top [:pair [:type 0] [:type 1]]))
  "Error: cannot infer pair without Sigma annotation")

(a/assert-throws
  (fn []
    (let [Γ (c/ctx/add (c/ctx/empty) "x" [:type 0])]
      (c/check Γ [:lam (fn [y] [:var y])] [:type 0])))
  "Error: lambda cannot have non-Pi type")

(test/end-suite)
