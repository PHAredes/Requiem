#!/usr/bin/env janet

(defn- ctx/entry-type [entry]
  (case (length entry)
    0 nil
    1 nil
    2 (entry 1)
    (entry 2)))

(defn- ctx/entry-name [entry]
  (entry 0))

(defn constraint/make [mv &opt name expected solution ctx origin dependencies level-constraints]
  @{:mv mv
    :name name
    :expected expected
    :solution solution
    :ctx (or ctx @[])
    :origin (or origin :unknown)
    :dependencies (or dependencies @[])
    :level-constraints (or level-constraints @[])})

(defn ctx/from-env [env]
  (let [seen @{}
        out @[]]
    (loop [i :down-to [(- (length env) 1) 0]]
      (let [entry (env i)
            name (ctx/entry-name entry)]
        (unless (get seen name)
          (put seen name true)
          (array/push out [name (ctx/entry-type entry)]))))
    (reverse out)))

(defn constraint/hole [mv name env &opt origin]
  (constraint/make mv name nil nil (ctx/from-env env) (or origin :elab/hole)))

(defn constraint/dependent [mv name env expected dependencies &opt origin]
  "Create a dependent constraint that depends on other metavariables"
  (constraint/make mv name expected nil (ctx/from-env env) (or origin :elab/dependent) dependencies))

(defn constraint/level [mv name env level-expr &opt origin]
  "Create a level constraint for universe level inference"
  (constraint/make mv name nil nil (ctx/from-env env) (or origin :elab/level) @[] @[level-expr]))

(defn constraint/implicit [mv name env expected dependencies &opt origin]
  "Create an implicit argument constraint"
  (constraint/make mv name expected nil (ctx/from-env env) (or origin :elab/implicit) dependencies))

(defn constraints/from-goals [goals]
  (reduce (fn [acc i]
            (let [goal (goals i)
                  mv (symbol (string "?goal" (+ i 1)))]
              (array/push acc
                          (constraint/make mv
                                           (goal :name)
                                           (goal :expected)
                                           nil
                                           (goal :ctx)
                                           :meta/goal))
              acc))
          @[]
          (range (length goals))))

(defn- goals/expected-map [goals]
  (reduce (fn [acc goal]
            (if (goal :name)
              (put acc (goal :name) (goal :expected))
              acc))
          @{}
          goals))

(defn constraint/merge-goals [constraints goals]
  (let [expected-by-name (goals/expected-map goals)]
    (map (fn [c]
           (if (or (c :expected) (nil? (c :name)))
             c
             (if-let [expected (get expected-by-name (c :name))]
               (put (table/clone c) :expected expected)
               c)))
         constraints)))

(defn constraints/without-mvs [constraints hidden-mvs]
  (reduce (fn [acc c]
            (when (not (get hidden-mvs (c :mv)))
              (array/push acc c))
            acc)
          @[]
          constraints))

(defn constraints/without-name-set [constraints hidden-names]
  (reduce (fn [acc c]
            (when (not (and (c :name) (get hidden-names (c :name))))
              (array/push acc c))
            acc)
          @[]
          constraints))

(defn constraint/mv-set [constraints]
  (reduce (fn [acc c]
            (put acc (c :mv) true))
          @{}
          constraints))

(defn constraint/name-map [constraints]
  (reduce (fn [acc c]
            (if (c :name)
              (put acc (c :mv) (c :name))
              acc))
           @{}
           constraints))

(defn constraint/name-set [constraints]
  (reduce (fn [acc c]
            (if (c :name)
              (put acc (c :name) true)
              acc))
          @{}
          constraints))

(defn constraint/solved-name-set [constraints]
  (reduce (fn [acc c]
            (if (and (c :name) (c :solution))
              (put acc (c :name) true)
              acc))
          @{}
          constraints))

(defn constraint/dependencies [constraints]
  "Get all dependencies across all constraints"
  (reduce (fn [acc c]
            (reduce (fn [acc2 dep]
                      (put acc2 dep true))
                    acc
                    (c :dependencies)))
          @{}
          constraints))

(defn constraint/level-constraints [constraints]
  "Extract all level constraints from constraints"
  (reduce (fn [acc c]
            (array/concat acc (c :level-constraints)))
          @[]
          constraints))

(defn constraint/with-dependencies [constraints dependencies]
  "Add dependencies to all constraints"
  (map (fn [c]
         (put (table/clone c) :dependencies (array/concat (c :dependencies) dependencies)))
       constraints))

(def exports
  {:constraint/make constraint/make
   :ctx/from-env ctx/from-env
   :constraint/hole constraint/hole
   :constraint/dependent constraint/dependent
   :constraint/level constraint/level
   :constraint/implicit constraint/implicit
   :constraints/from-goals constraints/from-goals
   :constraint/merge-goals constraint/merge-goals
   :constraint/mv-set constraint/mv-set
   :constraint/name-map constraint/name-map
   :constraint/name-set constraint/name-set
   :constraint/solved-name-set constraint/solved-name-set
   :constraint/dependencies constraint/dependencies
   :constraint/level-constraints constraint/level-constraints
   :constraint/with-dependencies constraint/with-dependencies
   :constraints/without-name-set constraints/without-name-set
   :constraints/without-mvs constraints/without-mvs})
