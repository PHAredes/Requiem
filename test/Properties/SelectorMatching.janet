#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/parser :as p)
(import ../../src/lower :as l)

(defn lower/ok? [src]
  (try
    (do
      (l/lower/program (p/parse/text src))
      true)
    ([err] false)))

(defn lower/error-contains? [src needle]
  (try
    (do
      (l/lower/program (p/parse/text src))
      false)
    ([err]
     (and (string? err)
          (not (nil? (string/find needle err)))))))

(defn mk-base-prefix []
  (string
    "(data Nat: Type ((zero Nat) (succ (forall (k: Nat). Nat)))) "
    "(data Vec (A: Type) (n: Nat): Type "
    "  (| A zero = vnil) "
    "  (| A (succ n) = vcons (x: A) (xs: (Vec A n)))) "))

(defn mk-match-src-ambiguous [suffix]
  (string
    (mk-base-prefix)
    "(def bad" suffix ": (forall (A: Type). (forall (n: Nat). (forall (xs: (Vec A n)). Nat))) "
    "  (match xs: "
    "    (case vnil: zero) "
    "    (case (vcons x xs'): (succ zero))))"))

(defn mk-match-src-zero [suffix]
  (string
    (mk-base-prefix)
    "(def okZero" suffix ": (forall (A: Type). (forall (xs: (Vec A zero)). Nat)) "
    "  (match xs: "
    "    (case vnil: zero) "
    "    (case _: zero)))"))

(defn mk-match-src-succ [suffix]
  (string
    (mk-base-prefix)
    "(def okSucc" suffix ": (forall (A: Type). (forall (k: Nat). (forall (xs: (Vec A (succ k))). Nat))) "
    "  (match xs: "
    "    (case _: zero) "
    "    (case (vcons x xs'): (succ zero))))"))

(defn mk-repeat-selector-prefix []
  (string
    "(data Nat: Type ((zero Nat) (succ (forall (k: Nat). Nat)))) "
    "(data EqNat (a: Nat) (b: Nat): Type "
    "  (| a a = refl)) "))

(defn mk-repeat-selector-ambiguous [suffix]
  (string
    (mk-repeat-selector-prefix)
    "(def badRepeat" suffix ": (forall (n: Nat). (forall (m: Nat). (forall (p: (EqNat n m)). Nat))) "
    "  (match p: "
    "    (case refl: zero)))"))

(defn mk-repeat-selector-concrete-no [suffix]
  (string
    (mk-repeat-selector-prefix)
    "(def okRepeat" suffix ": (forall (k: Nat). (forall (p: (EqNat zero (succ k))). Nat)) "
    "  (match p: "
    "    (case _: zero)))"))

(defn mk-shadowed-ctor-name-ambiguous [suffix]
  (string
    (mk-base-prefix)
    "(def badShadow" suffix ": (forall (A: Type). (forall (zero: Nat). (forall (xs: (Vec A zero)). Nat))) "
    "  (match xs: "
    "    (case vnil: zero) "
    "    (case (vcons x xs'): (succ zero))))"))

(defn mk-shadowed-later-binder-decidable [suffix]
  (string
    (mk-base-prefix)
    "(def okLaterShadow" suffix ": (forall (A: Type). (forall (xs: (Vec A zero)). (forall (zero: Nat). Nat))) "
    "  (match xs: "
    "    (case vnil: zero) "
    "    (case _: zero)))"))

(defn mk-unreachable-explicit-case [suffix]
  (string
    (mk-base-prefix)
    "(def badNoCase" suffix ": (forall (A: Type). (forall (xs: (Vec A zero)). Nat)) "
    "  (match xs: "
    "    (case vnil: zero) "
    "    (case (vcons x xs'): zero)))"))

(test/start-suite "Property Selector Matching")

(let [rng (math/rng 789)]
  (for _ 0 40
    (let [suffix (string (math/rng-int rng 100000))
          src (mk-match-src-ambiguous suffix)]
      (test/assert
       (lower/error-contains? src "ambiguous selector matching")
       "variable index match is rejected with stuck selector diagnostics"))))

(let [rng (math/rng 790)]
  (for _ 0 40
    (let [suffix (string (math/rng-int rng 100000))
          src (mk-match-src-zero suffix)]
      (test/assert
       (lower/ok? src)
       "concrete zero index is decidable (no stuck selector matching)"))))

(let [rng (math/rng 791)]
  (for _ 0 40
    (let [suffix (string (math/rng-int rng 100000))
          src (mk-match-src-succ suffix)]
      (test/assert
       (lower/ok? src)
       "concrete succ index is decidable (no stuck selector matching)"))))

(let [rng (math/rng 792)]
  (for _ 0 40
    (let [suffix (string (math/rng-int rng 100000))
          src (mk-repeat-selector-ambiguous suffix)]
      (test/assert
       (lower/error-contains? src "ambiguous selector matching")
       "repeated selector vars over unresolved indices are ambiguous"))))

(let [rng (math/rng 793)]
  (for _ 0 40
    (let [suffix (string (math/rng-int rng 100000))
          src (mk-repeat-selector-concrete-no suffix)]
      (test/assert
       (lower/ok? src)
       "repeated selector vars on concrete unequal constructors are decidable"))))

(let [rng (math/rng 794)]
  (for _ 0 40
    (let [suffix (string (math/rng-int rng 100000))
          src (mk-shadowed-ctor-name-ambiguous suffix)]
      (test/assert
       (lower/error-contains? src "ambiguous selector matching")
       "shadowed constructor names in indices are treated as ambiguous"))))

(let [rng (math/rng 795)]
  (for _ 0 40
    (let [suffix (string (math/rng-int rng 100000))
          src (mk-shadowed-later-binder-decidable suffix)]
      (test/assert
       (lower/ok? src)
       "later binders do not shadow constructor heads in target indices"))))

(let [rng (math/rng 796)]
  (for _ 0 40
    (let [suffix (string (math/rng-int rng 100000))
          src (mk-unreachable-explicit-case suffix)]
      (test/assert
       (lower/error-contains? src "unreachable constructor case")
       "explicit clauses for selector-no constructors are rejected"))))

(test/end-suite)
