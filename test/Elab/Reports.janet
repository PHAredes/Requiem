#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/constraints :as c)
(import ../../src/goals :as g)
(import ../../src/reports :as r)
(import ../../src/unify :as u)

(def suite (test/start-suite "Elab Reports"))

(test/assert suite
  (let [named (g/goal/make :term "named" [:type 0] @[])
        anonymous (g/goal/make :term nil [:type 0] @[])
        names (g/goals/name-set @[named anonymous])]
    (and (has-key? names "named")
         (not (has-key? names nil))))
  "Goal name sets ignore anonymous goals")

(test/assert suite
  (let [constraints @[(c/constraint/make '?mv "named" nil nil @[] :test)]
         goals @[(g/goal/make :term "named" [:type 0] @[])
                (g/goal/make :term nil [:type 1] @[])]
         report (r/report/from-state constraints goals @{})]
    (and (= (length (report :constraints)) 1)
         (= (((report :constraints) 0) :expected) [:type 0])
         (= (length (report :pending-goals)) 1)
         (nil? (((report :pending-goals) 0) :name))))
  "Anonymous goals stay pending after named goal reconciliation")

(test/assert suite
  (let [constraints @[(c/constraint/make '?mv1 "named" nil nil @[] :test)
                      (c/constraint/make '?mv2 "named" nil [:type 0] @[] :test)]
        _ (u/unify/solve constraints)
        names (c/constraint/solved-name-set constraints)]
    (has-key? names "named"))
  "Solved name sets only include propagated named-hole solutions")

(test/end-suite suite)
