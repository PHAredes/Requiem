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

(test/assert suite
  (deep= (ly/indent/blockize "Foo: Nat -> Nat\n  x = x\n\nBar:\n  baz\n")
         @[
           @{:head @{:text "Foo: Nat -> Nat" :col 0 :line 1}
             :body @[@{:text "x = x" :col 2 :line 2}]}
           @{:head @{:text "Bar:" :col 0 :line 4}
             :body @[@{:text "baz" :col 2 :line 5}]}])
  "Blockizer groups top-level declarations by indentation")

(test/end-suite suite)
