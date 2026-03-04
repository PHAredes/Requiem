#!/usr/bin/env janet

(import ./src/parser :as p)
(import ./src/lower :as l)

# Test just one iteration like the ZhangEncoding test does
(def rng (math/rng 123))
(def rec-var (string "r" (math/rng-int rng 10000)))
(def src (string
  "(data Nat: Type ((zero Nat) (succ (forall (k: Nat). Nat))))"
  " (def sum: (forall (n: Nat). (forall (m: Nat). Nat))"
  "   (match m:"
  "     (case zero: n)"
  "     (case (succ " rec-var "): (succ (sum n " rec-var ")))))"))

(print "Testing with rec-var:" rec-var)

(def forms (p/parse/text src))
(print "Parsed" (length forms) "forms")

(def lowered (try
  (l/lower/program forms)
  ([err] (print "ERROR during lowering:" err) nil)))

(if lowered
  (do
    (print "Success! Lowered result has" (length lowered) "declarations")
    (def sum-decl (get lowered 1))
    (print "Sum declaration type:" (sum-decl 0)))
  (print "Failed to lower"))