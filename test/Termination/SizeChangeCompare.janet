#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/termination :as term)

(def suite (test/start-suite "Termination Size Change Compare"))

(defn wrap [matrix]
  {:from "f" :to "f" :matrix matrix :proof [:sc/base-proof "p" "f"]})

(defn mk-matrix [rows cols entries]
  (let [m (term/sc/matrix rows cols)]
    (each [row col rel] entries
      (term/sc/matrix-set m row col rel))
    m))

(test/assert suite
  (= :eq (term/sc/compare [:var "x"] [:pat/var "x"]))
  "Variables compare equal to the same pattern variable")

(test/assert suite
  (= :unknown (term/sc/compare [:var "y"] [:pat/var "x"]))
  "Different variables do not compare as decreasing")

(test/assert suite
  (= :lt (term/sc/compare [:fst [:var "p"]] [:pat/var "p"]))
  "First projections count as structural descent")

(test/assert suite
  (= :lt (term/sc/compare [:snd [:var "p"]] [:pat/var "p"]))
  "Second projections count as structural descent")

(test/assert suite
  (= :unknown (term/sc/compare [:pair [:var "x"] [:var "y"]] [:pat/var "x"]))
  "Pair construction alone does not count as structural descent")

(test/assert suite
  (= :eq (term/sc/compare [:fst [:pair [:var "x"] [:var "y"]]] [:pat/var "x"]))
  "Projecting a concrete pair preserves the exact component comparison")

(test/assert suite
  (= :unknown (term/sc/compare [:app [:var "f"] [:var "x"]] [:pat/var "f"]))
  "Higher-order applications are not mistaken for descent on the head")

(test/assert suite
  (= :eq (term/sc/compare [:app [:var "succ"] [:var "n"]]
                          [:pat/con "succ" @[[:pat/var "n"]]]))
  "Matching constructor applications compare componentwise")

(test/assert suite
  (= :eq (term/sc/compare [:app [:var "succ"] [:var "zero"]]
                          [:pat/con "succ" @[[:pat/con "zero" @[]]]]))
  "Nested constructor patterns compare exactly when heads and arguments match")

(test/assert suite
  (= :unknown (term/sc/compare [:app [:var "zero"] [:var "n"]]
                               [:pat/con "succ" @[[:pat/var "n"]]]))
  "Different constructor heads do not compare spuriously")

(test/assert suite
  (= :unknown (term/sc/compare [:var "x"] [:pat/var "_"]))
  "Wildcard patterns do not produce size information")

(test/assert suite
  (let [unknown (wrap (mk-matrix 1 1 @[]))
        equal (wrap (mk-matrix 1 1 @[[0 0 :eq]]))
        strong (wrap (mk-matrix 1 1 @[[0 0 :lt]]))
        filtered1 (term/sc/filter-incomparable @[unknown] equal)
        filtered2 (term/sc/filter-incomparable filtered1 strong)]
    (and (= 1 (length filtered1))
         (= :eq (term/sc/matrix-get ((filtered1 0) :matrix) 0 0))
         (= 1 (length filtered2))
         (= :lt (term/sc/matrix-get ((filtered2 0) :matrix) 0 0))))
  "Antichain filtering replaces weaker comparable matrices")

(test/assert suite
  (let [m1 (wrap (mk-matrix 2 2 @[[0 0 :lt]]))
        m2 (wrap (mk-matrix 2 2 @[[1 1 :lt]]))
        filtered (term/sc/filter-incomparable @[m1] m2)]
    (= 2 (length filtered)))
  "Antichain filtering keeps incomparable matrices")

(test/assert suite
  (let [calls (term/sc/find-calls @{"loop" 1}
                                  @[[:pat/var "x"]]
                                  [:lam (fn [y] [:app [:var "loop"] [:var "x"]])])]
    (and (= 1 (length calls))
         (= "loop" ((calls 0) 0))
         (= :eq (term/sc/matrix-get ((calls 0) 1) 0 0))))
  "Call discovery sees recursive calls under lambdas")

(test/assert suite
  (let [calls (term/sc/find-calls @{"loop" 1}
                                  @[[:pat/var "x"]]
                                  [:t-pi [:var "Nat"] (fn [y] [:app [:var "loop"] [:var "x"]])])]
    (and (= 1 (length calls))
         (= "loop" ((calls 0) 0))
         (= :eq (term/sc/matrix-get ((calls 0) 1) 0 0))))
  "Call discovery sees recursive calls under dependent pis")

(test/assert suite
  (let [calls (term/sc/find-calls @{"loop" 1}
                                  @[[:pat/var "x"]]
                                  [:t-sigma [:var "Nat"] (fn [y] [:app [:var "loop"] [:var "x"]])])]
    (and (= 1 (length calls))
         (= "loop" ((calls 0) 0))
         (= :eq (term/sc/matrix-get ((calls 0) 1) 0 0))))
  "Call discovery sees recursive calls under dependent sigmas")

(test/assert suite
  (let [calls (term/sc/find-calls @{"loop" 1}
                                  @[[:pat/var "x"]]
                                  [:t-id [:var "Nat"] [:var "x"] [:app [:var "loop"] [:var "x"]]])]
    (and (= 1 (length calls))
         (= "loop" ((calls 0) 0))
         (= :eq (term/sc/matrix-get ((calls 0) 1) 0 0))))
  "Call discovery sees recursive calls inside identity types")

(test/assert suite
  (let [calls (term/sc/find-calls @{"loop" 1}
                                  @[[:pat/var "x"]]
                                  [:t-J [:var "Nat"]
                                        [:var "x"]
                                        [:lam (fn [y] [:app [:var "loop"] [:var "x"]])]
                                        [:var "zero"]
                                        [:var "x"]
                                        [:t-refl [:var "x"]]])]
    (and (= 1 (length calls))
         (= "loop" ((calls 0) 0))
         (= :eq (term/sc/matrix-get ((calls 0) 1) 0 0))))
  "Call discovery sees recursive calls inside J motives")

(test/assert suite
  (let [calls (term/sc/find-calls @{"loop" 1}
                                  @[[:pat/var "p"]]
                                  [:fst [:app [:var "loop"] [:fst [:var "p"]]]])]
    (and (= 1 (length calls))
         (= "loop" ((calls 0) 0))
         (= :lt (term/sc/matrix-get ((calls 0) 1) 0 0))))
  "Call discovery preserves projection-based descent in discovered calls")

(test/assert suite
  (let [calls (term/sc/find-calls @{"loop" 1}
                                  @[[:pat/var "f"]]
                                  [:app [:var "f"] [:app [:var "loop"] [:var "f"]]])]
    (and (= 1 (length calls))
         (= "loop" ((calls 0) 0))
         (= :eq (term/sc/matrix-get ((calls 0) 1) 0 0))))
  "Call discovery records recursive calls inside non-recursive applications only once")

(test/assert suite
  (zero? (length (term/sc/find-calls @{"f" 1}
                                     @[[:pat/var "f"]]
                                     [:app [:var "f"] [:var "zero"]])))
  "Call discovery ignores locally bound variables that shadow function names")

(test/end-suite suite)
