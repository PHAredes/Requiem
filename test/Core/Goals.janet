#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as tt)

(def suite (test/start-suite "Core Goals"))

(test/assert suite
  (let [saved (tt/goals/collect?)]
    (tt/goals/set-collect! (not saved))
    (let [updated (tt/goals/collect?)]
      (tt/goals/set-collect! saved)
      (and (= updated (not saved))
           (= (tt/goals/collect?) saved))))
  "Goal collection mode is observable and restorable")

(test/end-suite suite)
