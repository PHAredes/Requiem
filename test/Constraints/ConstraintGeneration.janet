#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/constraints :as c)
(import ../../src/levels :as lvl)
(import ../../src/unify :as u)

(def suite (test/start-suite "Constraints"))

(test/assert suite
  (let [constraints @[(c/constraint/make '?mv1 "goal" nil nil @[] :test)
                      (c/constraint/make '?mv2 "goal" [:type 0] nil @[] :test)]
        solved (u/unify/solve constraints)]
    (and (= (length solved) 2)
         (= ((constraints 0) :solution) [:type 0])
         (= ((constraints 1) :solution) [:type 0])))
  "Named expected evidence propagates across matching constraints")

(test/assert suite
  (let [constraints @[(c/constraint/make '?mv nil [:type 0] nil @[] :test)]
        solved (u/unify/solve constraints)]
    (and (= (length solved) 0)
         (nil? ((constraints 0) :solution))))
  "Anonymous expected constraints stay unsolved")

(test/assert-error suite
  (fn []
    (u/unify/solve @[(c/constraint/make '?mv1 "goal" [:type 0] nil @[] :test)
                     (c/constraint/make '?mv2 "goal" [:type 1] nil @[] :test)]))
  "Named constraints reject inconsistent evidence")

(test/assert-error suite
  (fn []
    (u/unify/solve @[(c/constraint/make '?mv "goal" nil nil @[] :test)]))
  "Named constraints without evidence remain errors")

(test/assert-error suite
  (fn []
    (u/unify/solve @[(c/constraint/make '?mv nil nil nil @[] :test @[]
                                        @[[:eq (lvl/closed 0) (lvl/closed 1)]])]))
  "Ground level inconsistencies are rejected")

(test/end-suite suite)
