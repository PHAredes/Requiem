#!/usr/bin/env janet

# Test suite for HOAS interpreter
(import spork/test)
(import "../src/core" :as h)

# Start test suite
(test/start-suite "HOAS Core")

# Type definitions
(test/assert (= (h/ty/emp) :emp) "ty/emp")
(test/assert (= (h/ty/nat) :nat) "ty/nat")
(test/assert (= (h/ty/fun :nat :nat) [:fun :nat :nat]) "ty/fun")
(test/assert (= (h/ty/par :nat :nat) [:par :nat :nat]) "ty/par")

# Term constructors
(test/assert (= (h/tm/var "x") [:var "x"]) "tm/var")
(test/assert (= (h/tm/app [:var "f"] [:var "x"]) [:app [:var "f"] [:var "x"]]) "tm/app")
(test/assert (= (h/tm/zero) [:zero]) "tm/zero")
(test/assert (= (h/tm/succ [:zero]) [:succ [:zero]]) "tm/succ")
(test/assert (= (h/tm/pair [:zero] [:zero]) [:pair [:zero] [:zero]]) "tm/pair")
(test/assert (= (h/tm/fst [:pair [:zero] [:zero]]) [:fst [:pair [:zero] [:zero]]]) "tm/fst")
(test/assert (= (h/tm/snd [:pair [:zero] [:zero]]) [:snd [:pair [:zero] [:zero]]]) "tm/snd")

# Neutral terms
(test/assert (= (h/ne/var "x") [:nvar "x"]) "ne/var")
(test/assert (= (h/ne/app [:nvar "f"] [:nvar "x"]) [:napp [:nvar "f"] [:nvar "x"]]) "ne/app")
(test/assert (= (h/ne/succ [:nvar "n"]) [:nsucc [:nvar "n"]]) "ne/succ")
(test/assert (= (h/ne/fst [:nvar "p"]) [:nfst [:nvar "p"]]) "ne/fst")
(test/assert (= (h/ne/snd [:nvar "p"]) [:nsnd [:nvar "p"]]) "ne/snd")

# Normal forms
(test/assert (= (h/nf/neut [:nvar "x"]) [:nneut [:nvar "x"]]) "nf/neut")
(test/assert (= (h/nf/nat 0) [:nnat 0]) "nf/nat")
(test/assert (= (h/nf/pair [:nnat 0] [:nnat 1]) [:npair [:nnat 0] [:nnat 1]]) "nf/pair")

# Evaluation basics
(test/assert (= (h/eval [:zero]) [:nnat 0]) "eval zero")
(test/assert (= (h/eval [:succ [:zero]]) [:nnat 1]) "eval succ zero")
(test/assert (= (h/eval [:succ [:succ [:zero]]]) [:nnat 2]) "eval succ succ zero")

# Pairs
(test/assert (= (h/eval [:pair [:zero] [:zero]]) [[:nnat 0] [:nnat 0]]) "eval pair")
(test/assert (= (h/eval [:pair [:zero] [:succ [:zero]]]) [[:nnat 0] [:nnat 1]]) "eval pair mixed")
(test/assert (= (h/eval [:fst [:pair [:zero] [:succ [:zero]]]]) [:nnat 0]) "eval fst")
(test/assert (= (h/eval [:snd [:pair [:zero] [:succ [:zero]]]]) [:nnat 1]) "eval snd")

# End test suite
(test/end-suite)
