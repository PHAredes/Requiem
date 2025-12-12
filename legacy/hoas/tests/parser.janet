#!/usr/bin/env janet

# Test suite for HOAS parser with new syntax
(import spork/test)
(import "../src/parser" :as parser)

# Start test suite
(test/start-suite "HOAS Parser - New Syntax")

# Helper to check parse results
(defn parse-ok? [text]
  (not (nil? (parser/term-parser text))))

(defn parse-result [text]
  (parser/term-parser text))

# 1. Variables
(test/assert (parse-ok? "x") "should parse variable 'x'")
(test/assert (parse-ok? "foo") "should parse variable 'foo'")
(test/assert (parse-ok? "bar123") "should parse variable 'bar123'")
(test/assert (parse-ok? "foo_bar") "should parse variable 'foo_bar'")
(test/assert (parse-ok? "zerox") "should parse 'zerox' as variable")

# 2. Zero
(test/assert (parse-ok? "zero") "should parse 'zero'")

# 3. Successor
(test/assert (parse-ok? "succ zero") "should parse 'succ zero'")
(test/assert (parse-ok? "succ succ zero") "should parse nested succ")
(test/assert (parse-ok? "succ (succ zero)") "should parse succ with parens")

# 4. Numbers (syntactic sugar)
(test/assert (parse-ok? "0") "should parse number 0")
(test/assert (parse-ok? "42") "should parse number 42")
(test/assert (parse-ok? "123") "should parse number 123")

# 5. Lambda - backslash syntax
(test/assert (parse-ok? "\\x => x") "should parse lambda '\\x => x'")
(test/assert (parse-ok? "\\x => zero") "should parse lambda '\\x => zero'")
(test/assert (parse-ok? "\\foo => bar") "should parse lambda '\\foo => bar'")
(test/assert (parse-ok? "\\x => \\y => x") "should parse nested lambda")

# 6. Lambda - unicode syntax
(test/assert (parse-ok? "λx => x") "should parse lambda 'λx => x'")
(test/assert (parse-ok? "λ x => x") "should parse lambda with space 'λ x => x'")

# 7. Application
(test/assert (parse-ok? "f x") "should parse application 'f x'")
(test/assert (parse-ok? "foo bar") "should parse application 'foo bar'")
(test/assert (parse-ok? "f x y") "should parse multi-arg application 'f x y'")
(test/assert (parse-ok? "(\\x => x) y") "should parse lambda application")

# 8. Fixed point
(test/assert (parse-ok? "µ f => f") "should parse fix 'µ f => f'")
(test/assert (parse-ok? "mu f => f") "should parse fix 'mu f => f'")
(test/assert (parse-ok? "mu f => zero") "should parse fix with body")

# 9. Case analysis
(test/assert (parse-ok? "match n { zero => z | succ x => x }") 
             "should parse case expression")
(test/assert (parse-ok? "match zero { zero => zero | succ n => n }") 
             "should parse case with zero scrutinee")
(test/assert (parse-ok? "match n { zero => zero | succ x => succ x }") 
             "should parse case with succ in branch")

# 10. Pairs
(test/assert (parse-ok? "(zero, zero)") "should parse pair '(zero, zero)'")
(test/assert (parse-ok? "(x, y)") "should parse pair '(x, y)'")
(test/assert (parse-ok? "((zero, zero), x)") "should parse nested pair")

# 11. Projections
(test/assert (parse-ok? "fst p") "should parse 'fst p'")
(test/assert (parse-ok? "snd p") "should parse 'snd p'")
(test/assert (parse-ok? "fst (x, y)") "should parse fst of pair")
(test/assert (parse-ok? "snd (x, y)") "should parse snd of pair")

# 12. Parenthesized expressions
(test/assert (parse-ok? "(zero)") "should parse '(zero)'")
(test/assert (parse-ok? "(x)") "should parse '(x)'")
(test/assert (parse-ok? "((x))") "should parse nested parens")

# 13. Whitespace handling
(test/assert (parse-ok? "  x  ") "should handle leading/trailing whitespace")
(test/assert (parse-ok? "\\x  =>  x") "should handle whitespace in lambda")
(test/assert (parse-ok? "f   x   y") "should handle multiple spaces in app")

# 14. Comments
(test/assert (parse-ok? "x # this is a comment") "should handle comments")
(test/assert (parse-ok? "# comment\nx") "should handle leading comment")

# 15. Complex expressions
(test/assert (parse-ok? "\\f => \\x => f (f x)") 
             "should parse Church numeral 2")
(test/assert (parse-ok? "mu fact => \\n => match n { zero => succ zero | succ m => n }") 
             "should parse factorial skeleton")
(test/assert (parse-ok? "fst (\\x => x, \\y => y)") 
             "should parse fst of lambda pair")

# 16. Check structure of parsed results
(def lambda-result (parse-result "\\x => x"))
(test/assert (= (get (first lambda-result) 0) :lam) 
             "lambda should parse to :lam")

(def app-result (parse-result "f x"))
(test/assert (= (get (first app-result) 0) :app) 
             "application should parse to :app")

(def case-result (parse-result "match n { zero => z | succ x => x }"))
(test/assert (= (get (first case-result) 0) :case) 
             "case should parse to :case")

# End test suite
(test/end-suite)
