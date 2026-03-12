#!/usr/bin/env janet

(defn- ctx/entry-type [entry]
  (case (length entry)
    0 nil
    1 nil
    2 (entry 1)
    (entry 2)))

(defn- ctx/entry-name [entry]
  (entry 0))

(defn constraint/make [mv &opt name expected solution ctx origin]
  @{:mv mv
    :name name
    :expected expected
    :solution solution
    :ctx (or ctx @[])
    :origin (or origin :unknown)})

(defn ctx/from-env [env]
  (let [latest
        (reduce (fn [acc i]
                  (put acc (ctx/entry-name (env i)) i))
                @{}
                (range (length env)))]
    (reduce (fn [acc i]
              (let [entry (env i)
                    name (ctx/entry-name entry)]
                (if (= (get latest name) i)
                  [;acc [name (ctx/entry-type entry)]]
                  acc)))
            @[]
            (range (length env)))))

(defn constraint/hole [mv name env &opt origin]
  (constraint/make mv name nil nil (ctx/from-env env) (or origin :elab/hole)))

(defn- goals/expected-map [goals]
  (reduce (fn [acc goal]
            (if (goal :name)
              (put acc (goal :name) (goal :expected))
              acc))
          @{}
          goals))

(defn constraint/merge-goals! [constraints goals]
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
            (if (get hidden-mvs (c :mv))
              acc
              [;acc c]))
          @[]
          constraints))

(defn constraints/without-name-set [constraints hidden-names]
  (reduce (fn [acc c]
            (if (and (c :name)
                     (get hidden-names (c :name)))
              acc
              [;acc c]))
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

(def exports
  {:constraint/make constraint/make
   :ctx/from-env ctx/from-env
   :constraint/hole constraint/hole
   :constraint/merge-goals! constraint/merge-goals!
   :constraint/mv-set constraint/mv-set
   :constraint/name-map constraint/name-map
   :constraint/name-set constraint/name-set
   :constraint/solved-name-set constraint/solved-name-set
   :constraints/without-name-set constraints/without-name-set
   :constraints/without-mvs constraints/without-mvs})
