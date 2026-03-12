#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/frontend/surface/parser :as s)

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
  (lower/error-contains? "Bool:\n  true\n  false\n\nnot(b: Bool): Bool\n  true = false\n"
                        "non-exhaustive clauses")
  "Missing constructor clauses are rejected")

(test/assert suite
  (lower/error-contains? "Bool:\n  true\n  false\n\nf(b: Bool): Bool\n  true = true\n  true = false\n  false = true\n"
                        "overlapping clause")
  "Repeated constructor clauses are rejected")

(test/assert suite
  (lower/error-contains? "Bool:\n  true\n  false\n\nf(b: Bool): Bool\n  true = true\n  _ = false\n  false = true\n"
                        "overlapping clause")
  "Wildcard-shadowed clauses are rejected")

(test/assert suite
  (lower/ok? "Bool:\n  true\n  false\n\nf(b: Bool): Bool\n  true = false\n  false = true\n")
  "Exhaustive non-overlapping clauses still lower")

(test/assert suite
  (lower/ok? "Nat:\n  zero\n  succ Nat\n\nVec(A: Type0, n: Nat): Type0\n  A, zero = vnil\n  A, (succ n) = vcons (x: A) (xs: Vec A n)\n\nhead: ∀(A: Type0). Π(n: Nat). Vec A (succ n) -> A\n  A n (vcons x _) = x\n")
  "Indexed families do not spuriously fail coverage checks")

(test/end-suite suite)
