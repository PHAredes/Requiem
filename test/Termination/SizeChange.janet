#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/termination :as term)

(def suite (test/start-suite "Termination Size Change"))

(def nat-type [:var "Nat"])

(def plus-decl
  [:core/func "plus"
   @[[ :bind "m" nat-type ]
     [ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]] [:pat/var "n"]]
      [:var "n"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "m"]]] [:pat/var "n"]]
      [:app [:var "succ"] [:app [:app [:var "plus"] [:var "m"]] [:var "n"]]]]]])

(def loop-decl
  [:core/func "loop"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "loop"] [:app [:var "succ"] [:var "n"]]]]]])

(def even-decl
  [:core/func "even"
   @[[ :bind "n" nat-type ]]
   [:var "Bool"]
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "true"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "odd"] [:var "n"]]]]])

(def odd-decl
  [:core/func "odd"
   @[[ :bind "n" nat-type ]]
   [:var "Bool"]
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "false"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "even"] [:var "n"]]]]])

(def ping-decl
  [:core/func "ping"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "pong"] [:app [:var "succ"] [:var "n"]]]]]])

(def pong-decl
  [:core/func "pong"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "ping"] [:app [:var "succ"] [:var "n"]]]]]])

(def shrink-left-decl
  [:core/func "shrink-left"
   @[[ :bind "m" nat-type ]
     [ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]] [:pat/var "n"]]
      [:var "n"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "m"]]] [:pat/var "n"]]
      [:app [:var "one-arg"] [:var "m"]]]]])

(def one-arg-decl
  [:core/func "one-arg"
   @[[ :bind "k" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
      [:core/clause @[[:pat/con "succ" @[[:pat/var "k"]]]]
       [:app [:app [:var "shrink-left"] [:var "k"]] [:var "k"]]]]])

(def apply-loop-decl
  [:core/func "apply-loop"
   @[[ :bind "f" [:var "Nat->Nat"] ]
     [ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/var "f"] [:pat/var "n"]]
      [:app [:app [:var "apply-loop"] [:app [:var "f"] [:var "n"]]] [:var "n"]]]]])

(def proj-loop-decl
  [:core/func "proj-loop"
   @[[ :bind "p" [:var "PairNat"] ]]
   nat-type
   nil
    @[
      [:core/clause @[[:pat/var "p"]]
       [:app [:var "proj-loop"] [:fst [:var "p"]]]]]])

(def pair-proj-loop-decl
  [:core/func "pair-proj-loop"
   @[[ :bind "x" nat-type ]]
   nat-type
   nil
    @[
      [:core/clause @[[:pat/var "x"]]
       [:app [:var "pair-proj-loop"] [:fst [:pair [:var "x"] [:var "x"]]]]]]])

(def shadowed-f-decl
  [:core/func "shadowed-f"
   @[[ :bind "f" [:var "Nat->Nat"] ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/var "f"]]
      [:app [:var "f"] [:var "zero"]]]]])

(def header-left-decl
  [:core/func "header-left"
   @[]
   [:var "header-right"]
   [:var "header-right"]
   @[
     [:core/clause @[] [:var "zero"]]]])

(def header-right-decl
  [:core/func "header-right"
   @[]
   [:var "header-left"]
   [:var "header-left"]
   @[
      [:core/clause @[] [:var "zero"]]]])

(def self-header-decl
  [:core/func "self-header"
   @[]
   [:var "self-header"]
   [:var "self-header"]
   @[
     [:core/clause @[] [:var "zero"]]]])

(def complex-header-left-decl
  [:core/func "complex-header-left"
   @[]
   [:t-pi [:var "Nat"] (fn [x] [:var "complex-header-right"])]
   [:t-pi [:var "Nat"] (fn [x] [:var "complex-header-right"])]
   @[
     [:core/clause @[] [:var "zero"]]]])

(def complex-header-right-decl
  [:core/func "complex-header-right"
   @[]
   [:t-sigma [:var "Nat"] (fn [x] [:var "complex-header-left"])]
   [:t-sigma [:var "Nat"] (fn [x] [:var "complex-header-left"])]
    @[
      [:core/clause @[] [:var "zero"]]]])

(def header-clause-left-decl
  [:core/func "header-clause-left"
   @[[ :bind "x" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "x"]]]]
      [:app [:var "header-clause-right"] [:var "x"]]]]])

(def header-clause-right-decl
  [:core/func "header-clause-right"
   @[[ :bind "y" nat-type ]]
   [:app [:var "header-clause-left"] [:var "y"]]
   nil
   @[
     [:core/clause @[[:pat/var "y"]]
      [:var "zero"]]]])

(def swap-loop-decl
  [:core/func "swap-loop"
   @[[ :bind "x" nat-type ]
     [ :bind "y" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]] [:pat/var "y"]]
      [:var "y"]]
     [:core/clause @[[:pat/var "x"] [:pat/con "zero" @[]]]
      [:var "x"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "x"]]]
                     [:pat/con "succ" @[[:pat/var "y"]]]]
      [:app [:app [:var "swap-loop"] [:var "y"]] [:var "x"]]]]])

(def closure-a-decl
  [:core/func "closure-a"
   @[[ :bind "x" nat-type ]
     [ :bind "y" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/var "x"] [:pat/con "succ" @[[:pat/con "succ" @[[:pat/var "y"]]]]]]
      [:app [:app [:var "closure-a"] [:var "zero"]] [:var "y"]]]]])

(def closure-b-decl
  [:core/func "closure-b"
   @[[ :bind "x" nat-type ]
     [ :bind "y" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/var "x"] [:pat/con "succ" @[[:pat/var "y"]]]]
      [:app [:app [:var "closure-b"] [:var "y"]] [:var "x"]]]]])

(def tri-a-decl
  [:core/func "tri-a"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "tri-b"] [:var "n"]]]]])

(def tri-b-decl
  [:core/func "tri-b"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "tri-c"] [:var "n"]]]]])

(def tri-c-decl
  [:core/func "tri-c"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "tri-a"] [:var "n"]]]]])

(def bad-tri-a-decl
  [:core/func "bad-tri-a"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "bad-tri-b"] [:app [:var "succ"] [:var "n"]]]]]])

(def bad-tri-b-decl
  [:core/func "bad-tri-b"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "bad-tri-c"] [:app [:var "succ"] [:var "n"]]]]]])

(def bad-tri-c-decl
  [:core/func "bad-tri-c"
   @[[ :bind "n" nat-type ]]
   nat-type
   nil
   @[
     [:core/clause @[[:pat/con "zero" @[]]]
      [:var "zero"]]
     [:core/clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
      [:app [:var "bad-tri-a"] [:app [:var "succ"] [:var "n"]]]]]])

(test/assert suite
  ((term/sct plus-decl) :ok)
  "Primitive recursion on a constructor argument passes SCT")

(let [result (term/sct loop-decl)]
  (test/assert suite
    (and (not (result :ok))
         (= (length (result :problems)) 1)
         (= (((result :problems) 0) :name) "loop"))
    "Self recursion without size decrease fails SCT"))

(test/assert suite
  ((term/sct* @[even-decl odd-decl]) :ok)
  "Mutual recursion with constructor descent passes SCT")

(let [result (term/sct* @[ping-decl pong-decl])]
  (test/assert suite
    (and (not (result :ok))
         (= (length (result :problems)) 2)
         (all |(= (length ($ :component)) 2) (result :problems)))
    "Mutual recursion without any decrease fails SCT"))

(test/assert suite
  ((term/sct* @[shrink-left-decl one-arg-decl]) :ok)
  "SCT composes non-square call matrices across mutual recursion")

(let [result (term/sct apply-loop-decl)]
  (test/assert suite
    (and (not (result :ok))
         (= (length (result :problems)) 1)
         (= (((result :problems) 0) :name) "apply-loop"))
    "SCT does not treat higher-order applications as structural descent"))

(test/assert suite
  ((term/sct proj-loop-decl) :ok)
  "SCT still recognizes projection subterms as decreasing")

(let [result (term/sct pair-proj-loop-decl)]
  (test/assert suite
    (and (not (result :ok))
         (= (length (result :problems)) 1)
         (= (((result :problems) 0) :name) "pair-proj-loop"))
    "SCT does not treat projections of concrete pairs as decreasing by default"))

(test/assert suite
  ((term/sct shadowed-f-decl) :ok)
  "SCT ignores shadowed local names when looking for recursive calls")

(let [result (term/sct* @[header-left-decl header-right-decl])]
  (test/assert suite
    (and (not (result :ok))
         (= (length (result :problems)) 2)
         (not (nil? (string/find "header-left:type" (term/sc/problem-report (result :problems)))))
         (not (nil? (string/find "diag=[]" (term/sc/problem-report (result :problems))))))
    "SCT rejects recursive cycles appearing in function headers"))

(let [result (term/sct self-header-decl)]
  (test/assert suite
    (and (not (result :ok))
         (= (length (result :problems)) 1)
         (= (((result :problems) 0) :name) "self-header")
         (not (nil? (string/find "self-header:type" (term/sc/problem-report (result :problems))))))
    "SCT rejects direct self-recursion in function headers"))

(let [result (term/sct* @[complex-header-left-decl complex-header-right-decl])]
  (test/assert suite
    (and (not (result :ok))
         (= (length (result :problems)) 2)
         (not (nil? (string/find "complex-header-left:type" (term/sc/problem-report (result :problems)))))
          (not (nil? (string/find "complex-header-right:type" (term/sc/problem-report (result :problems))))))
    "SCT rejects recursive cycles found under dependent header terms"))

(test/assert suite
  ((term/sct* @[header-clause-left-decl header-clause-right-decl]) :ok)
  "SCT handles recursive header edges with the caller arity preserved")

(test/assert suite
  ((term/sct swap-loop-decl) :ok)
  "SCT accepts non-idempotent self calls whose closure gains a diagonal decrease")

(test/assert suite
  ((term/sct* @[closure-a-decl closure-b-decl]) :ok)
  "SCT iterates closure until newly discovered summaries stabilize")

(test/assert suite
  ((term/sct* @[tri-a-decl tri-b-decl tri-c-decl]) :ok)
  "SCT closes decreasing three-function cycles")

(let [result (term/sct* @[bad-tri-a-decl bad-tri-b-decl bad-tri-c-decl])]
  (test/assert suite
    (and (not (result :ok))
         (= (length (result :problems)) 3)
         (all |(= (length ($ :component)) 3) (result :problems)))
    "SCT rejects non-decreasing three-function cycles"))

(test/assert suite
  (not (nil? (string/find "loop" (term/sc/problem-report ((term/sct loop-decl) :problems)))))
  "Problem reports include offending function names")

(test/assert suite
  (let [report (term/sc/problem-report ((term/sct* @[ping-decl pong-decl]) :problems))]
    (and (not (nil? (string/find "ping[2]" report)))
         (not (nil? (string/find "pong" report)))))
  "Problem reports include call-path information")

(test/end-suite suite)
