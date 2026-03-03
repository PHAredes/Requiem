#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/levels :as lvl)

(test/start-suite "Core Levels")

(test/assert
  (lvl/lvl/<= (lvl/lvl/const 0) (lvl/lvl/const 3))
  "const comparison")

(test/assert
  (= (lvl/lvl/value (lvl/lvl/compose (lvl/lvl/shift 1) (lvl/lvl/shift 2))) 3)
  "shift composition")

(test/assert
  (= (lvl/lvl/apply-shift (lvl/lvl/shift 2) (lvl/lvl/const 1)) 3)
  "shift application")

(test/assert
  (= (lvl/lvl/succ (lvl/lvl/const 4)) 5)
  "successor")

(test/end-suite)
