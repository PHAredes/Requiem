#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/frontend/surface/parser :as s)
(import ../../src/elab :as e)
(import ../../src/coreTT :as tt)
(import ../../src/core_printer :as pp)
(import ../../src/levels :as lvl)

(defn lower/ok? [src]
  (try
    (do
      (s/lower/program (s/parse/program src))
      true)
    ([err] false)))

(defn lower/error-contains? [src needle]
  (try
    (do
      (s/lower/program (s/parse/program src))
      false)
    ([err]
     (and (string? err)
          (not (nil? (string/find needle err)))))))

(def suite (test/start-suite "Surface Lowering"))

(test/assert suite
  (let [ty (s/parse/type-text "A -> B -> C")
        lowered (s/lower/type ty)]
    (deep= lowered [:list @[[:atom "A"] [:atom "->"] [:list @[[:atom "B"] [:atom "->"] [:atom "C"]]]]]))
  "Arrows are lowered and right-associative")

(test/assert suite
  (let [tm (s/parse/expr-text "f x y")
        lowered (s/lower/term tm)]
    (deep= lowered [:list @[[:atom "f"] [:atom "x"] [:atom "y"]]]))
  "Term applications are flattened during lowering")

(test/assert suite
  (let [ty (s/parse/type-text "F a b c")
        lowered (s/lower/type ty)]
    (deep= lowered [:list @[[:atom "F"] [:atom "a"] [:atom "b"] [:atom "c"]]]))
  "Type applications are flattened during lowering")

(test/assert suite
  (let [ty (s/parse/type-text "Type(u + 1 + 2)")
        lowered (s/lower/type ty)
        term ((e/exports :term/elab) @[] lowered)
        inferred (tt/infer-top term)]
    (and (= lowered [:atom "Type(u + 3)"])
         (= (pp/print/tm term) "Typeu + 3")
         (= (pp/print/sem inferred) "Typeu + 4")
         (lvl/eq? (get inferred 1)
                  (lvl/apply-shift (lvl/shift 4) (lvl/uvar "u")))))
  "Symbolic universes survive lowering elaboration and printing")

(test/assert suite
  (let [prog (s/parse/program "Bool:\n  true\n  false\nnot(b: Bool): Bool\n  true = false\n  false = true\n")
        lowered (s/lower/program prog)]
    (and (= (length lowered) 2)
         (= ((lowered 0) 0) :decl/data)
         (= ((lowered 1) 0) :decl/func)))
  "Full program lowers correctly")

(test/assert suite
  (let [prog (s/parse/program "Nat:\n  zero\n  succ Nat\n\nBool:\n  true\n  false\n\nisZero: Nat -> Nat -> Bool\n  zero m = true\n  (succ k) m = false\n")
        lowered (s/lower/program prog)
        isZero (lowered 2)
        clauses (isZero 4)
        c0 (clauses 0)
        c1 (clauses 1)]
    (and (= (isZero 0) :decl/func)
         (= (isZero 1) "isZero")
         (= (length clauses) 2)
         (= (((c0 1) 0) 0) :pat/con)
         (= (((c0 1) 0) 1) "zero")
          (= (((c1 1) 0) 0) :pat/con)
          (= (((c1 1) 0) 1) "succ")
          (= (((((c1 1) 0) 2) 0) 1) "k")))
  "Current selector-style syntax lowers first-parameter constructor clauses")

(test/assert suite
  (let [prog (s/parse/program "Wrap(A: Type):\n  A = mk\n  A = box (value: A)\n")
        lowered (s/lower/program prog)
        wrap (lowered 0)
        ctors (wrap 4)
        mk (ctors 0)
        box (ctors 1)]
    (and (= (mk 0) :ctor)
         (= (mk 1) "mk")
         (= (length (mk 4)) 0)
         (= (box 0) :ctor)
         (= (box 1) "box")
         (= (length (box 4)) 1)))
  "Indexed constructor lowering keeps simple-return constructors stable")

(test/end-suite suite)
