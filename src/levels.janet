#!/usr/bin/env janet

# Universe levels and displacement algebra.

(def L/Const 0x01)
(def L/Shift 0x02)

(defn- check-nat [n who]
  (when (or (not (int? n)) (< n 0))
    (errorf "%v expects a non-negative integer, got: %v" who n))
  n)

(defn const [n]
  [L/Const (check-nat n "lvl/const")])

(defn shift [n]
  [L/Shift (check-nat n "lvl/shift")])

(def id (const 0))

(defn const? [l]
  (and (tuple? l) (= (get l 0) L/Const)))

(defn shift? [l]
  (and (tuple? l) (= (get l 0) L/Shift)))

(defn value [l]
  "Normalize a level expression to a concrete natural number."
  (cond
    (int? l) (check-nat l "lvl/value")
    (const? l) (check-nat (get l 1) "lvl/value")
    (shift? l) (check-nat (get l 1) "lvl/value")
    true (errorf "invalid level expression: %v" l)))

(defn leq [l1 l2]
  (<= (value l1) (value l2)))

(defn lt [l1 l2]
  (< (value l1) (value l2)))

(defn eq? [l1 l2]
  (= (value l1) (value l2)))

(defn succ [l]
  (inc (value l)))

(defn max* [l1 l2]
  (max (value l1) (value l2)))

(defn apply-shift [shift-val l]
  (+ (value shift-val) (value l)))

(defn compose [s1 s2]
  (shift (+ (value s1) (value s2))))

(defn str [l]
  (string "l" (value l)))

(def exports
  {:L/Const L/Const
   :L/Shift L/Shift
   :const const
   :shift shift
   :id id
   :const? const?
   :shift? shift?
   :value value
   :leq leq
   :lt lt
   :eq? eq?
   :succ succ
   :max max*
   :apply-shift apply-shift
   :compose compose
   :str str})
