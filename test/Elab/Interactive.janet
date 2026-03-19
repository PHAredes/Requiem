#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as tt)
(import ../../src/elab :as e)

(def suite (test/start-suite "Interactive Elaboration"))

(def Type1 (tt/ty/type 1))

(test/assert suite
  (let [term ((e/exports :term/elab) @[] [:atom "?goal"])
        result (tt/check/c (tt/ctx/empty) term Type1)
        constraints (result :constraints)]
    (and (= (length constraints) 1)
         (= ((constraints 0) :name) "goal")
         (= (((constraints 0) :expected) 0) tt/T/Type)
         (nil? ((constraints 0) :solution))))
  "Elaborated named holes become live checking constraints")

(test/assert suite
  (let [term [:pair [:hole "goal"] [:hole "goal"]]
        sigma (tt/ty/sigma Type1 (fn [_] Type1))
        initial (tt/check/c (tt/ctx/empty) term sigma)
        filled (tt/fill-hole-top term sigma "goal" (tt/tm/type 0))
        check (filled :check)]
    (and (= (length (initial :constraints)) 1)
         (nil? (check :error))
         (= (length (check :constraints)) 0)
         (= (filled :term) [:pair [:type 0] [:type 0]])))
  "Filling one named hole updates all occurrences and rechecks the term")

(test/assert suite
  (let [sigma (tt/ty/sigma Type1 (fn [_] Type1))
        failed (tt/fill-hole-top [:hole "goal"] sigma "goal" (tt/tm/type 0))]
    (not (nil? ((failed :check) :error))))
  "Ill-typed hole fillings are rejected by the live checking path")

(test/end-suite suite)
