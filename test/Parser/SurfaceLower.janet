#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/frontend/surface/parser :as s)

(test/start-suite "Surface Lowering")

(test/assert
  (let [ty (s/parse/type-text "A -> B -> C")
        lowered (s/lower/type ty)]
    (deep= lowered [:list @[[:atom "A"] [:atom "->"] [:list @[[:atom "B"] [:atom "->"] [:atom "C"]]]]]))
  "Arrows are lowered and right-associative")

(test/assert
  (let [tm (s/parse/expr-text "f x y")
        lowered (s/lower/term tm)]
    (deep= lowered [:list @[[:atom "f"] [:atom "x"] [:atom "y"]]]))
  "Term applications are flattened during lowering")

(test/assert
  (let [ty (s/parse/type-text "F a b c")
        lowered (s/lower/type ty)]
    (deep= lowered [:list @[[:atom "F"] [:atom "a"] [:atom "b"] [:atom "c"]]]))
  "Type applications are flattened during lowering")

(test/assert
  (let [prog (s/parse/program "Bool:\n  true\n  false\nnot(b: Bool): Bool\n  true = false\n  false = true\n")
        lowered (s/lower/program prog)]
    (and (= (length lowered) 2)
         (= ((lowered 0) 0) :decl/data)
         (= ((lowered 1) 0) :decl/func)))
  "Full program lowers correctly")

(test/end-suite)
