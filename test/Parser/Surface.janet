#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../Utils/SurfaceSchema :as schema)
(import ../../src/surface :as s)

(test/start-suite "Surface Parser")

(test/assert
  (= (s/node/tag (s/parse/type-text "Π(A: U0). A")) :ty/pi)
  "Pi quantifier parses to :ty/pi")

(test/assert
  (= (s/node/tag (s/parse/type-text "∀(A: U0). A")) :ty/pi)
  "Forall aliases to :ty/pi")

(test/assert
  (= (s/node/tag (s/parse/type-text "Σ(x: U0). U0")) :ty/sigma)
  "Sigma quantifier parses to :ty/sigma")

(test/assert
  (= (s/node/tag (s/parse/type-text "∃(x: U0). U0")) :ty/sigma)
  "Exists aliases to :ty/sigma")

(test/assert
  (let [sx (s/syntax/clone (s/syntax/default))]
    (s/syntax/add-quant-alias! sx "Forall" :pi)
    (= (s/node/tag (s/parse/type-text "Forall(A: U0). A" nil sx)) :ty/pi))
  "Custom quantifier alias composes via syntax map")

(test/assert
  (let [sx (s/syntax/clone (s/syntax/default))]
    (s/syntax/add-literal! sx "EX" :quant :sigma)
    (= (s/node/tag (s/parse/type-text "EX(x: U0). U0" nil sx)) :ty/sigma))
  "Custom literal token maps to quantifier kind")

(test/assert
  (let [ty (s/parse/type-text "A -> B -> C")]
    (and (= (s/node/tag ty) :ty/arrow)
         (= (s/node/tag (ty 2)) :ty/arrow)))
  "Arrow type is right associative")

(test/assert
  (let [prec @{"*+*" {:fixity :infixl :level 6}}
        tm (s/parse/expr-text "f x *+* y" prec)]
    (and (= (s/node/tag tm) :tm/op)
         (= (tm 1) "*+*")))
  "Infix operator precedence is applied")

(test/assert
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

(test/assert-error
  (fn []
    (s/parse/type-text "Forall(A: U0). A"))
  "Unknown quantifier alias fails without syntax extension")

(test/end-suite)
