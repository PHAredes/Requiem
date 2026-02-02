#!/usr/bin/env janet

(import ../../src/coreTT :as c)
(import ../Utils/TestRunner :as test)

(test/start-suite "Core Context")

# ===============================================
# Test: Context Shadowing
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

# ===============================================
# Test: Empty context lookup throws error
# ===============================================
(test/assert-error
  (fn [] (c/ctx/lookup (c/ctx/empty) "nonexistent"))
  "Lookup on empty context throws error")

# ===============================================
# Test: Context immutability (HAMT property)
# ===============================================
(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "x" [:Type 0])]
  (test/assert-error
    (fn [] (c/ctx/lookup Γ "x"))
    "Original context unchanged after add (immutability)"))

# ===============================================
# Test: Symbol keys work (converted to string)
# ===============================================
(let [Γ (c/ctx/add (c/ctx/empty) 'x [:Type 0])]
  (test/assert
    (= (c/ctx/lookup Γ 'x) [:Type 0])
    "Symbol keys work for context"))

# ===============================================
# Test: Multiple distinct bindings
# ===============================================
(let [Γ (c/ctx/empty)
      Γ1 (c/ctx/add Γ "a" [:Type 0])
      Γ2 (c/ctx/add Γ1 "b" [:Type 1])
      Γ3 (c/ctx/add Γ2 "c" [:Type 2])]
  (test/assert
    (and (= (c/ctx/lookup Γ3 "a") [:Type 0])
         (= (c/ctx/lookup Γ3 "b") [:Type 1])
         (= (c/ctx/lookup Γ3 "c") [:Type 2]))
    "Multiple distinct bindings all accessible"))

# ===============================================
# Test: Deep context chain
# ===============================================
(var Γ (c/ctx/empty))
(for i 0 100
  (set Γ (c/ctx/add Γ (string "var" i) [:Type i])))
(test/assert
  (and (= (c/ctx/lookup Γ "var0") [:Type 0])
       (= (c/ctx/lookup Γ "var50") [:Type 50])
       (= (c/ctx/lookup Γ "var99") [:Type 99]))
  "Deep context chain with 100 bindings")

(test/end-suite)
