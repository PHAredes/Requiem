#!/usr/bin/env janet

(import ../../src/coreTT :as c)
(import ../Utils/TestRunner :as test)

(test/start-suite "Core Context")

# ===============================================
# Test 2: Context Shadowing
# ===============================================
(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "x" [:Type 0])
      Γ2 (c/ctx/add Γ1 "x" [:Type 1])] # Shadow "x"
  (test/assert
    (= (c/ctx/lookup Γ2 "x") [:Type 1])
    "Context shadowing: newest binding is returned"))

(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "x" [:Type 0])
      Γ2 (c/ctx/add Γ1 "y" [:Type 1])] # Add unrelated binding
  (test/assert
    (= (c/ctx/lookup Γ2 "x") [:Type 0])
    "Context preserves older bindings"))

(test/end-suite)
