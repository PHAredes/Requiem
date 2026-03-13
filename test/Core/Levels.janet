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
  (let [shifted (lvl/apply-shift (lvl/shift 2) (lvl/uvar 'u))]
    (and (lvl/plus? shifted)
         (= (shifted 1) 'u)
         (= (shifted 2) 2)))
  "shift application preserves universe variables")

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
  (let [top (lvl/max (lvl/apply-shift (lvl/shift 1) (lvl/uvar 'u))
                     (lvl/apply-shift (lvl/shift 3) (lvl/uvar 'u)))]
    (and (lvl/plus? top)
         (= (top 1) 'u)
         (= (top 2) 3)))
  "max collapses same-base symbolic levels")

(test/assert suite
  (let [top (lvl/max (lvl/uvar 'u) (lvl/const 2))]
    (and (lvl/max? top)
         (= (length top) 3)))
  "max keeps incomparable bases")

(test/assert suite
  (and (lvl/<= (lvl/uvar 'u)
               (lvl/max (lvl/uvar 'u) (lvl/uvar 'v)))
       (lvl/<= (lvl/max (lvl/const 1) (lvl/uvar 'u))
               (lvl/max (lvl/const 3)
                        (lvl/apply-shift (lvl/shift 2) (lvl/uvar 'u))))
       (not (lvl/<= (lvl/uvar 'u) (lvl/const 0))))
  "symbolic ordering is pointwise")

(test/assert suite
  (lvl/<= (lvl/const 1)
          (lvl/apply-shift (lvl/shift 1) (lvl/uvar 'u)))
  "constants compare against shifted variables semantically")

(test/assert suite
  (lvl/<= (lvl/max (lvl/const 1) (lvl/uvar 'u))
          (lvl/apply-shift (lvl/shift 1) (lvl/uvar 'u)))
  "max bounds compare atomwise against a larger atom")

(test/assert suite
  (lvl/<= (lvl/const 2)
          (lvl/max (lvl/apply-shift (lvl/shift 2) (lvl/uvar 'u))
                   (lvl/apply-shift (lvl/shift 2) (lvl/uvar 'v))))
  "constants compare against symbolic maxima")

(test/assert suite
  (not (lvl/<= (lvl/uvar 'u) (lvl/const 3)))
  "variables do not compare below unrelated constants")

(test/assert-error suite
  (fn [] (lvl/value (lvl/uvar 'u)))
  "open levels do not have concrete values")

(test/assert suite
  (let [z (lvl/normalize (lvl/shift 0))]
    (and (lvl/shift? lvl/id)
         (lvl/const? z)
         (= (lvl/value z) 0)))
  "normalize canonically produces constants")

(test/assert suite
  (= (lvl/str (lvl/max (lvl/const 1)
                       (lvl/apply-shift (lvl/shift 2) (lvl/uvar 'u))))
     "1 \\/ u + 2")
  "string rendering shows symbolic maxima")

(test/end-suite suite)
