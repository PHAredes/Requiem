#!/usr/bin/env janet

(import /build/hamt :as h)

(defn goal/make [kind name expected ctx]
  {:kind kind
    :name name
    :expected expected
    :ctx ctx})

(defn- ctx/from-hamt [Γ lookup]
  (map (fn [k] [k (lookup Γ k)]) (h/keys Γ)))

(defn goal/term [name expected Γ lookup]
  (goal/make :term name expected (ctx/from-hamt Γ lookup)))

(defn goal/type [name ctx]
  (goal/make :type name nil ctx))

(defn- ctx/partition [ctx names]
  (reduce (fn [[local global] entry]
            (if (get names (entry 0))
              [local [;global entry]]
              [[;local entry] global]))
          [@[] @[]]
          ctx))

(defn- goal/split-ctx [goal local-names]
  (ctx/partition (goal :ctx) local-names))

(defn goal/local-ctx [goal local-names]
  ((goal/split-ctx goal local-names) 0))

(defn goal/global-ctx [goal local-names]
  ((goal/split-ctx goal local-names) 1))

(defn goals/name-set [goals]
  (reduce (fn [acc goal]
            (if-let [name (goal :name)]
              (put acc name true)
              acc))
          @{}
          goals))

(defn goals/without-name-set [goals hidden-names]
  (reduce (fn [acc goal]
            (if (get hidden-names (goal :name))
              acc
              [;acc goal]))
          @[]
          goals))

(def exports
  {:goal/make goal/make
   :goal/term goal/term
   :goal/type goal/type
   :goal/local-ctx goal/local-ctx
   :goal/global-ctx goal/global-ctx
   :goals/name-set goals/name-set
   :goals/without-name-set goals/without-name-set})
