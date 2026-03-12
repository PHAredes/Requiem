#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/levels :as lvl)

(def suite (test/start-suite "Core Levels"))

(test/assert suite
  (<= (lvl/value (lvl/const 0)) (lvl/value (lvl/const 3)))
  "const comparison")

(test/assert suite
  (let [composed (lvl/compose (lvl/shift 1) (lvl/shift 2))]
    (and (lvl/shift? composed)
         (= (composed 1) 3)))
  "shift composition")

(test/assert suite
  (let [shifted (lvl/apply-shift (lvl/shift 2) (lvl/const 1))]
    (and (lvl/const? shifted)
         (= (lvl/value shifted) 3)))
  "shift application")

(test/assert suite
  (let [next (lvl/succ (lvl/const 4))]
    (and (lvl/const? next)
         (= (lvl/value next) 5)))
  "successor")

(test/assert suite
  (lvl/<= (lvl/const 1) (lvl/const 1))
  "<= alias delegates to leq")

(test/assert suite
  (let [top (lvl/max (lvl/const 2) (lvl/const 5))]
    (and (lvl/const? top)
         (= (lvl/value top) 5)))
  "max alias delegates to max*")

(test/assert suite
  (let [z (lvl/normalize (lvl/shift 0))]
    (and (lvl/shift? lvl/id)
         (lvl/const? z)
         (= (lvl/value z) 0)))
  "normalize canonically produces constants")

(test/end-suite suite)
