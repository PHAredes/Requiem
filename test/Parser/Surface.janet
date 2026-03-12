#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../Utils/SurfaceSchema :as schema)
(import ../../src/frontend/surface/parser :as s)

(def suite (test/start-suite "Surface Parser"))

(test/assert suite
  (= (s/node/tag (s/parse/type-text "Π(A: U0). A")) :ty/pi)
  "Pi quantifier parses to :ty/pi")

(test/assert suite
  (= (s/node/tag (s/parse/type-text "∀(A: U0). A")) :ty/pi)
  "Forall aliases to :ty/pi")

(test/assert suite
  (= (s/node/tag (s/parse/type-text "Σ(x: U0). U0")) :ty/sigma)
  "Sigma quantifier parses to :ty/sigma")

(test/assert suite
  (= (s/node/tag (s/parse/type-text "∃(x: U0). U0")) :ty/sigma)
  "Exists aliases to :ty/sigma")

(test/assert suite
  (let [sx (s/syntax/clone (s/syntax/default))]
    (s/syntax/add-quant-alias! sx "Forall" :pi)
    (= (s/node/tag (s/parse/type-text "Forall(A: U0). A" nil sx)) :ty/pi))
  "Custom quantifier alias composes via syntax map")

(test/assert suite
  (let [sx (s/syntax/clone (s/syntax/default))]
    (s/syntax/add-literal! sx "EX" :quant :sigma)
    (= (s/node/tag (s/parse/type-text "EX(x: U0). U0" nil sx)) :ty/sigma))
  "Custom literal token maps to quantifier kind")

(test/assert suite
  (let [ty (s/parse/type-text "A -> B -> C")]
    (and (= (s/node/tag ty) :ty/arrow)
         (= (s/node/tag (ty 2)) :ty/arrow)))
  "Arrow type is right associative")

(test/assert suite
  (let [prec @{"*+*" {:fixity :infixl :level 6}}
        tm (s/parse/expr-text "f x *+* y" prec)]
    (and (= (s/node/tag tm) :tm/op)
         (= (tm 1) "*+*")))
  "Infix operator precedence is applied")

(test/assert suite
  (let [src "
infixl 6 *+*
Vec(A, n: Nat):
  zero = vnil
  succ n = vcons(x: A)(xs: Vec A n)

id: ∀(A: U0). A -> A
  x = x
"
        prog (s/parse/program src)]
    (do
      (schema/assert/program prog)
      (= (s/node/tag prog) :program)))
  "Program parse output matches schema tool")

(test/assert suite
  (let [prog (s/parse/program "sum(n,m: Nat): Nat\n  n zero = n\n")
        decls (prog 1)
        sum (decls 0)
        ty (sum 2)]
    (and (= (sum 0) :decl/func)
         (= (s/node/tag ty) :ty/pi)
         (= ((ty 1) 1) "n")
         (= (s/node/tag (ty 2)) :ty/pi)
         (= (((ty 2) 1) 1) "m")))
  "Grouped function parameters expand to separate Pi binders")

(test/assert suite
  (let [prog (s/parse/program "Vec(A: Type, n: Nat):\n  A, (succ n) = vcons (x: A) (xs: Vec A n)\n")
        decls (prog 1)
        vec (decls 0)
        ctor ((vec 4) 0)]
    (and (= (ctor 0) :ctor/indexed)
         (= (ctor 2) "vcons")
         (= (length (ctor 3)) 2)))
  "Adjacent parenthesized constructor fields parse separately")

(test/assert suite
  (let [prog (s/parse/program "Nat:\n  zero\n  succ Nat\n\nclassify: Nat -> Nat\n  zero = zero\n  succ zero = succ zero\n  succ succ n = succ succ n\n")
        decls (prog 1)
        classify (decls 1)
        clauses (classify 3)
        c1 ((clauses 1) 1)
        c2 ((clauses 2) 1)
        nested (((c2 0) 2) 0)]
    (and (= (length clauses) 3)
         (= ((c1 0) 0) :pat/con)
         (= ((c1 0) 1) "succ")
         (= ((((c1 0) 2) 0) 1) "zero")
         (= ((c2 0) 0) :pat/con)
         (= (nested 0) :pat/con)
         (= (nested 1) "succ")
         (= (((nested 2) 0) 1) "n")))
  "Single-argument nested constructor patterns do not need parens")

(test/assert suite
  (let [prog (s/parse/program "Nat: Type3\n  zero\n")
        decls (prog 1)
        nat (decls 0)
        sort (nat 3)]
    (and (= (nat 0) :decl/data)
         (= (s/node/tag sort) :ty/universe)
         (= (sort 1) 3)))
  "Data headers accept explicit universe levels")

(test/assert-error suite
  (fn []
    (s/parse/type-text "Forall(A: U0). A"))
  "Unknown quantifier alias fails without syntax extension")

(test/end-suite suite)
