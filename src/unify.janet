#!/usr/bin/env janet

(defn- unify/assign! [solved mv value]
  (if (has-key? solved mv)
    (when (not= (get solved mv) value)
      (errorf "conflicting solutions for %v" mv))
    (put solved mv value)))

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

(defn- unify/fill-named! [constraints solved named]
  (reduce (fn [changed c]
            (if-not (and (c :name) (nil? (c :solution)))
              changed
              (if-let [entry (get named (c :name))]
                (do (put c :solution (entry :value))
                    (unify/assign! solved (c :mv) (entry :value))
                    true)
                changed)))
          false
          constraints))

(defn unify/solve [constraints]
  (let [solved @{}
        named  @{}]
    (each c constraints
      (let [mv    (c :mv)
            value (or (c :solution) (c :expected))
            kind  (if (c :solution) :solution :expected)
            name  (c :name)]
        (when value
          (unify/assign! solved mv value)
          (put c :solution value))
        (when name
          (unify/merge-named! named name value kind))))

    (while (unify/fill-named! constraints solved named))

    (each c constraints
      (when (and (c :name) (nil? (c :solution)))
        (errorf "unsolved named hole ?%v" (c :name))))

    solved))

(def exports
  {:unify/solve unify/solve})
