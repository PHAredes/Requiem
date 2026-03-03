#!/usr/bin/env janet

# Universe levels and displacement algebra.

(def L/Const 0x01)
(def L/Shift 0x02)

(defn- lvl/check-nat [n who]
  (when (or (not (int? n)) (< n 0))
    (errorf "%v expects a non-negative integer, got: %v" who n))
  n)

(defn lvl/const [n]
  [L/Const (lvl/check-nat n "lvl/const")])

(defn lvl/shift [n]
  [L/Shift (lvl/check-nat n "lvl/shift")])

(def lvl/id (lvl/const 0))

(defn lvl/const? [l]
  (and (tuple? l) (= (get l 0) L/Const)))

(defn lvl/shift? [l]
  (and (tuple? l) (= (get l 0) L/Shift)))

(defn lvl/value [l]
  "Normalize a level expression to a concrete natural number."
  (cond
    (int? l) (lvl/check-nat l "lvl/value")
    (lvl/const? l) (lvl/check-nat (get l 1) "lvl/value")
    (lvl/shift? l) (lvl/check-nat (get l 1) "lvl/value")
    true (errorf "invalid level expression: %v" l)))

(defn lvl/<= [l1 l2]
  (<= (lvl/value l1) (lvl/value l2)))

(defn lvl/< [l1 l2]
  (< (lvl/value l1) (lvl/value l2)))

(defn lvl/eq? [l1 l2]
  (= (lvl/value l1) (lvl/value l2)))

(defn lvl/succ [l]
  (inc (lvl/value l)))

(defn lvl/max [l1 l2]
  (max (lvl/value l1) (lvl/value l2)))

(defn lvl/apply-shift [shift l]
  (+ (lvl/value shift) (lvl/value l)))

(defn lvl/compose [s1 s2]
  (lvl/shift (+ (lvl/value s1) (lvl/value s2))))

(defn lvl/str [l]
  (string "l" (lvl/value l)))

(def exports
  {:L/Const L/Const
   :L/Shift L/Shift
   :const lvl/const
   :shift lvl/shift
   :id lvl/id
   :const? lvl/const?
   :shift? lvl/shift?
   :value lvl/value
   :<= lvl/<=
   :< lvl/<
   :eq? lvl/eq?
   :succ lvl/succ
   :max lvl/max
   :apply-shift lvl/apply-shift
   :compose lvl/compose
   :str lvl/str})
