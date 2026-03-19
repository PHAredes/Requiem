#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/termination :as term)

(def suite (test/start-suite "Termination Size Change Graph"))

(defn mk-matrix [rows cols entries]
  (let [m (term/sc/matrix rows cols)]
    (each [row col rel] entries
      (term/sc/matrix-set m row col rel))
    m))

(defn rel->string [rel]
  (case rel
    :lt "<"
    :eq "="
    "?"))

(defn mk-self-call [name rel label]
  (term/sc/call name name
                (if (= rel :unknown)
                  (mk-matrix 1 1 @[])
                  (mk-matrix 1 1 @[[0 0 rel]]))
                [:sc/base-proof label name]))

(defn mk-edge [from to rel label]
  (term/sc/call from to
                (if (= rel :unknown)
                  (mk-matrix 1 1 @[])
                  (mk-matrix 1 1 @[[0 0 rel]]))
                [:sc/base-proof label to]))

(defn wrap [matrix]
  {:from "f" :to "f" :matrix matrix :proof [:sc/base-proof "p" "f"]})

(defn ref-rel-mul [r1 r2]
  (match [r1 r2]
    [:lt :lt] :lt
    [:lt :eq] :lt
    [:eq :lt] :lt
    [:eq :eq] :eq
    _ :unknown))

(defn ref-rel-rank [rel]
  (case rel
    :lt 2
    :eq 1
    0))

(defn ref-rel-max [r1 r2]
  (if (> (ref-rel-rank r1) (ref-rel-rank r2)) r1 r2))

(defn ref-check-1x1 [nodes edges]
  (let [best @{}]
    (each from nodes
      (let [row @{}]
        (each to nodes
          (put row to :unknown))
        (put best from row)))
    (each [from to rel] edges
      (put (best from) to (ref-rel-max ((best from) to) rel)))
    (var changed true)
    (while changed
      (set changed false)
      (each mid nodes
        (each from nodes
          (each to nodes
            (let [candidate (ref-rel-mul ((best from) mid) ((best mid) to))
                  current ((best from) to)]
              (when (> (ref-rel-rank candidate) (ref-rel-rank current))
                (put (best from) to candidate)
                (set changed true)))))))
    (all (fn [node]
           (= ((best node) node) :lt))
         nodes)))

(test/assert suite
  (let [left (mk-matrix 1 2 @[[0 0 :eq] [0 1 :lt]])
        right (mk-matrix 2 1 @[[0 0 :lt] [1 0 :eq]])
        composed (term/sc/compose left right)]
    (and (= "< < | = <" (term/sc/matrix->string composed))
         (term/sc/matrix-diagonal-has-lt? composed)))
  "Matrix composition keeps strongest relation across paths")

(test/assert suite
  (let [strong (mk-matrix 2 2 @[[0 0 :lt] [1 1 :eq]])
        weak (mk-matrix 2 2 @[[1 1 :eq]])]
    (and (term/sc/matrix-dominates? strong weak)
         (not (term/sc/matrix-dominates? weak strong))))
  "Matrix dominance orders precise matrices above weaker ones")

(test/assert suite
  (= "[< ? =]" (term/sc/diagonal->string (mk-matrix 3 3 @[[0 0 :lt] [2 2 :eq]])))
  "Diagonal rendering exposes decreasing evidence")

(test/assert suite
  (let [ack-calls @[
          (term/sc/call "ack" "ack"
                        (mk-matrix 2 2 @[[0 0 :lt]])
                        [:sc/base-proof "ack-1" "ack"])
          (term/sc/call "ack" "ack"
                        (mk-matrix 2 2 @[[0 0 :eq] [1 1 :lt]])
                        [:sc/base-proof "ack-2" "ack"])]
        result (term/sc/check-graph* @{"ack" 2} ack-calls)]
    (result :ok))
  "Arend-style mixed decreasing self-call matrices pass SCT closure")

(let [result (term/sc/check-graph*
               @{"f" 4}
               @[
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :lt]])
                               [:sc/base-proof "f-1" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :eq] [1 1 :lt]])
                               [:sc/base-proof "f-2" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :eq] [1 1 :eq] [2 2 :lt]])
                               [:sc/base-proof "f-3" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :eq] [1 1 :eq] [2 2 :eq] [3 3 :lt]])
                               [:sc/base-proof "f-4" "f"])])]
  (test/assert suite
    (result :ok)
    "Arend artificial decreasing chain closes successfully"))

(let [result (term/sc/check-graph*
               @{"f" 4}
               @[
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :lt]])
                               [:sc/base-proof "f-1" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :eq] [1 1 :lt]])
                               [:sc/base-proof "f-2" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :eq] [1 1 :eq] [2 2 :lt]])
                               [:sc/base-proof "f-3" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :eq] [1 1 :eq] [2 2 :eq] [3 3 :eq]])
                               [:sc/base-proof "f-4" "f"])])]
  (test/assert suite
    (not (result :ok))
    "Arend artificial non-decreasing chain is rejected"))

(let [result (term/sc/check-graph*
               @{"f" 4}
               @[
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[1 1 :lt] [3 3 :eq]])
                               [:sc/base-proof "f-2" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[1 1 :eq] [2 2 :lt] [3 3 :eq]])
                               [:sc/base-proof "f-3" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[3 3 :lt]])
                               [:sc/base-proof "f-1" "f"])
                 (term/sc/call "f" "f"
                               (mk-matrix 4 4 @[[0 0 :lt] [1 1 :eq] [2 2 :eq] [3 3 :eq]])
                               [:sc/base-proof "f-4" "f"])])]
  (test/assert suite
    (result :ok)
    "Arend artificial incomparable matrices still yield a decreasing cycle"))

(let [result (term/sc/check-graph*
               @{"h" 2 "f" 2 "g" 2}
               @[
                 (term/sc/call "h" "h"
                               (mk-matrix 2 2 @[[0 0 :lt] [1 1 :eq]])
                               [:sc/base-proof "h-h-1" "h"])
                 (term/sc/call "h" "h"
                               (mk-matrix 2 2 @[[0 0 :eq] [1 1 :lt]])
                               [:sc/base-proof "h-h-2" "h"])
                 (term/sc/call "f" "f"
                               (mk-matrix 2 2 @[[0 1 :lt]])
                               [:sc/base-proof "f-f" "f"])
                 (term/sc/call "f" "h"
                               (mk-matrix 2 2 @[])
                               [:sc/base-proof "f-h" "h"])
                 (term/sc/call "f" "g"
                               (mk-matrix 2 2 @[[0 0 :lt] [1 1 :eq]])
                               [:sc/base-proof "f-g" "g"])
                 (term/sc/call "g" "f"
                               (mk-matrix 2 2 @[[0 0 :eq] [1 1 :eq]])
                               [:sc/base-proof "g-f" "f"])
                 (term/sc/call "g" "g"
                               (mk-matrix 2 2 @[[0 0 :lt]])
                               [:sc/base-proof "g-g" "g"])
                 (term/sc/call "g" "h"
                               (mk-matrix 2 2 @[])
                               [:sc/base-proof "g-h" "h"])])]
  (test/assert suite
    (not (result :ok))
    "Arend mixed graph counterexample is rejected"))

(let [result (term/sc/check-graph*
               @{"v" 1}
               @[
                 (term/sc/call "v" "v"
                               (mk-matrix 1 1 @[])
                               [:sc/base-proof "unknown" "v"])
                 (term/sc/call "v" "v"
                               (mk-matrix 1 1 @[[0 0 :eq]])
                               [:sc/base-proof "equal" "v"])
                 (term/sc/call "v" "v"
                               (mk-matrix 1 1 @[[0 0 :lt]])
                               [:sc/base-proof "lt" "v"])])]
  (test/assert suite
    (and (result :ok)
         (zero? (length (result :problems))))
    "Dominating matrices do not interfere with a decreasing witness"))

(let [triples @[
        @[:unknown :unknown :unknown]
        @[:unknown :unknown :eq]
        @[:unknown :eq :eq]
        @[:eq :eq :eq]
        @[:lt :unknown :unknown]
        @[:unknown :lt :eq]
        @[:eq :eq :lt]
        @[:lt :lt :lt]]]
  (each triple triples
    (let [r1 (triple 0)
          r2 (triple 1)
          r3 (triple 2)
          result (term/sc/check-graph*
                   @{"f" 1}
                   @[(mk-self-call "f" r1 "r1")
                     (mk-self-call "f" r2 "r2")
                     (mk-self-call "f" r3 "r3")])
          expect (or (= r1 :lt) (= r2 :lt) (= r3 :lt))]
      (test/assertf suite
                    (= expect (result :ok))
                    "Generated single-node 1x1 SCT cases match diagonal intuition"
                    (string "rels=" (rel->string r1) "," (rel->string r2) "," (rel->string r3)
                            " got=" (if (result :ok) "ok" "fail"))))))

(let [pairs @[
        @[:unknown :unknown]
        @[:unknown :eq]
        @[:eq :eq]
        @[:lt :unknown]
        @[:unknown :lt]
        @[:eq :lt]
        @[:lt :eq]
        @[:lt :lt]]]
  (each pair pairs
    (let [r1 (pair 0)
          r2 (pair 1)
          result (term/sc/check-graph*
                   @{"f" 1 "g" 1}
                   @[(mk-edge "f" "g" r1 "f-g")
                     (mk-edge "g" "f" r2 "g-f")])
          expect (and (not= r1 :unknown)
                      (not= r2 :unknown)
                      (or (= r1 :lt) (= r2 :lt)))]
      (test/assertf suite
                    (= expect (result :ok))
                    "Generated two-node 1x1 cycles match composed diagonal intuition"
                    (string "cycle=" (rel->string r1) "," (rel->string r2)
                            " got=" (if (result :ok) "ok" "fail"))))))

(let [m00 (wrap (mk-matrix 2 2 @[[0 0 :lt]]))
      m11 (wrap (mk-matrix 2 2 @[[1 1 :lt]]))
      meq (wrap (mk-matrix 2 2 @[[0 0 :eq] [1 1 :eq]]))
      mboth (wrap (mk-matrix 2 2 @[[0 0 :lt] [1 1 :lt]]))
      kept1 (term/sc/filter-incomparable @[m00] m11)
      kept2 (term/sc/filter-incomparable kept1 meq)
      kept3 (term/sc/filter-incomparable kept2 mboth)]
  (test/assertf suite
                (and (= 2 (length kept1))
                     (= 3 (length kept2))
                     (= 1 (length kept3))
                     (= "< ? | ? <" (term/sc/matrix->string ((kept3 0) :matrix))))
                "2x2 antichain filtering keeps incomparable matrices then collapses to stronger witness"
                (string "after1=" (length kept1) " after2=" (length kept2) " after3=" (length kept3)
                        " final=" (term/sc/matrix->string ((kept3 0) :matrix)))) )

(let [left (mk-matrix 2 2 @[[0 0 :eq] [1 1 :lt]])
      right (mk-matrix 2 2 @[[0 0 :lt] [1 1 :eq]])
      composed (term/sc/compose left right)]
  (test/assertf suite
                (and (= "< ? | ? <" (term/sc/matrix->string composed))
                     (term/sc/matrix-diagonal-has-lt? composed))
                "2x2 composition preserves decreases on distinct coordinates"
                (term/sc/matrix->string composed)))

(test/assert suite
  (let [swap (term/sc/call "swap" "swap"
                           (mk-matrix 2 2 @[[0 1 :lt] [1 0 :lt]])
                           [:sc/base-proof "swap" "swap"])
        result (term/sc/check-graph* @{"swap" 2} @[swap])]
    (result :ok))
  "Non-idempotent self-call matrices are not reported as SCT failures")

(let [cases @[
        {:label "self-unknown"
         :nodes @["f"]
         :edges @[["f" "f" :unknown]]
         :calls @[(mk-self-call "f" :unknown "u")]}
        {:label "self-eq"
         :nodes @["f"]
         :edges @[["f" "f" :eq]]
         :calls @[(mk-self-call "f" :eq "e")]}
        {:label "self-lt"
         :nodes @["f"]
         :edges @[["f" "f" :lt]]
         :calls @[(mk-self-call "f" :lt "l")]}
        {:label "mutual-eq-eq"
         :nodes @["f" "g"]
         :edges @[["f" "g" :eq] ["g" "f" :eq]]
         :calls @[(mk-edge "f" "g" :eq "fg") (mk-edge "g" "f" :eq "gf")]}
        {:label "mutual-lt-eq"
         :nodes @["f" "g"]
         :edges @[["f" "g" :lt] ["g" "f" :eq]]
         :calls @[(mk-edge "f" "g" :lt "fg") (mk-edge "g" "f" :eq "gf")]}
        {:label "mutual-lt-unknown"
         :nodes @["f" "g"]
         :edges @[["f" "g" :lt] ["g" "f" :unknown]]
         :calls @[(mk-edge "f" "g" :lt "fg") (mk-edge "g" "f" :unknown "gf")]}
        {:label "mixed-self-and-mutual"
         :nodes @["f" "g"]
         :edges @[["f" "f" :eq] ["f" "g" :lt] ["g" "f" :eq]]
         :calls @[(mk-self-call "f" :eq "ff") (mk-edge "f" "g" :lt "fg") (mk-edge "g" "f" :eq "gf")]}
        {:label "both-self-lt"
         :nodes @["f" "g"]
         :edges @[["f" "f" :lt] ["g" "g" :lt]]
         :calls @[(mk-self-call "f" :lt "ff") (mk-self-call "g" :lt "gg")]}]]
  (each specimen cases
    (let [arities @{}
          _ (each node (specimen :nodes)
              (put arities node 1))
          reference (ref-check-1x1 (specimen :nodes) (specimen :edges))
          actual ((term/sc/check-graph* arities (specimen :calls)) :ok)]
      (test/assertf suite
                    (= reference actual)
                    "Reference 1x1 closure agrees with SCT on fixed small graphs"
                    (string (specimen :label) " ref=" reference " actual=" actual)))))

(test/end-suite suite)
