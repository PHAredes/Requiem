#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/frontend/surface/layout :as ly)

(def suite (test/start-suite "Surface Layout"))

(test/assert suite
  (deep= (ly/split-top-level "a,(b,c),d" (chr ","))
         @[
           "a"
           "(b,c)"
           "d"])
  "Top-level splitting ignores nested commas")

(test/assert suite
  (= (ly/find-top-level-char "f (g, h), i" (chr ",")) 8)
  "Top-level char search skips nested delimiters")

(test/assert suite
  (= (ly/find-first-top-level-char "name(arg)\trest" @[(chr " ") (chr "\t") (chr "(")]) 9)
  "First top-level char search uses shared predicate walker")

(test/assert suite
  (deep= (ly/indent/tokenize "\n  foo\n\n    bar\n")
         @[
           @{:text "foo" :col 2 :line 2}
           @{:text "bar" :col 4 :line 4}])
  "Indent tokenizer skips blank lines and tracks columns")

(test/end-suite suite)
