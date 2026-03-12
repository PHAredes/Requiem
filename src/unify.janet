#!/usr/bin/env janet

(defn- unify/assign! [solved mv value]
  (if (has-key? solved mv)
    (when (not= (get solved mv) value)
      (errorf "conflicting solutions for %v" mv))
    (put solved mv value)))

(defn- unify/value-kind [c]
  (cond
    (c :solution) :solution
    (c :expected) :expected
    true nil))

(defn- unify/value [c]
  (or (c :solution) (c :expected)))

(defn- unify/merge-named! [named name value kind]
  (when value
    (if-let [entry (get named name)]
      (let [other (entry :value)
            other-kind (entry :kind)]
        (cond
          (not= other value)
          (errorf "named hole ?%v has inconsistent constraints" name)

          (and (= kind :solution) (= other-kind :expected))
          (put named name {:value value :kind kind})

          true
          nil))
      (put named name {:value value :kind kind}))))

(defn unify/solve [constraints]
  (let [solved @{}
        named  @{}]

    (each c constraints
      (let [mv    (c :mv)
            value (unify/value c)
            kind  (unify/value-kind c)
            name  (c :name)]
        (when value
          (unify/assign! solved mv value)
          (put c :solution value))
        (when name
          (unify/merge-named! named name value kind))))

    (each c constraints
      (when (and (c :name) (nil? (c :solution)))
        (when-let [entry (get named (c :name))]
          (let [v (entry :value)]
            (put c :solution v)
            (unify/assign! solved (c :mv) v)))))

    (each c constraints
      (when (and (c :name) (nil? (c :solution)))
        (errorf "unsolved named hole ?%v" (c :name))))

    solved))

(def exports
  {:unify/solve unify/solve})
