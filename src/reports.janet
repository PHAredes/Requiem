#!/usr/bin/env janet

(import ./constraints :as c)
(import ./goals :as g)
(import ./unify :as u)

(defn report/type-holes [prog collect/decl-type-holes]
  (let [out @[]]
    (each decl (prog 1)
      (collect/decl-type-holes decl out))
    out))

(defn report/append-goal-hints [hints start end default-hint]
  (let [out (array/slice hints)]
    (loop [_ :range [start end]]
      (array/push out default-hint))
    out))

(defn report/current-goals! [goals hints start end default-hint]
  (let [hints (report/append-goal-hints hints start end default-hint)]
    {:goals (slice goals start end)
     :hints (slice hints start end)}))

(defn report/check-name-hints [decls term/lambda-names]
  (reduce (fn [acc decl]
            (match decl
              [:decl/check tm _]
              (do (array/push acc (term/lambda-names tm)) acc)
              _ acc))
          @[]
          decls))

(defn report/from-state [constraints goals displayed-goals]
  (let [constraints (c/constraint/merge-goals constraints goals)]
    (u/unify/solve constraints)
    (let [name-map (c/constraint/name-map constraints)
         reportable-constraints (c/constraints/without-name-set constraints displayed-goals)
         solved-goal-names (c/constraint/solved-name-set constraints)
         pending-goals (g/goals/without-name-set goals solved-goal-names)]
      {:name-map name-map
       :constraints reportable-constraints
       :pending-goals pending-goals})))

(def exports
  {:report/append-goal-hints report/append-goal-hints
   :report/current-goals! report/current-goals!
   :report/type-holes report/type-holes
   :report/check-name-hints report/check-name-hints
   :report/from-state report/from-state})
