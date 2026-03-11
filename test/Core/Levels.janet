#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/levels :as lvl)

(test/start-suite "Core Levels")

(test/assert
  (<= (lvl/value (lvl/const 0)) (lvl/value (lvl/const 3)))
  "const comparison")

(test/assert
  (= (lvl/value (lvl/compose (lvl/shift 1) (lvl/shift 2))) 3)
  "shift composition")

(test/assert
  (= (lvl/apply-shift (lvl/shift 2) (lvl/const 1)) 3)
  "shift application")

(test/assert
  (= (lvl/succ (lvl/const 4)) 5)
  "successor")

(test/end-suite)
