#!/usr/bin/env janet

(defn- unify/assign! [solved mv value]
  (if (has-key? solved mv)
    (when (not= (get solved mv) value)
      (errorf "conflicting solutions for %v" mv))
    (put solved mv value)))

(defn- unify/merge-named! [c solved named name value mv]
  (if (not (has-key? named name))
    (put named name value)
    (let [other (get named name)]
      (cond
        (and value other (not= value other))
        (errorf "named hole ?%v has inconsistent constraints" name)

        (and value (nil? other))
        (put named name value)

        (and (nil? value) other)
        (do (put c :solution other)
            (unify/assign! solved mv other))))))

(defn unify/solve [constraints]
  (let [solved @{}
        named  @{}]

    (each c constraints
      (let [mv    (c :mv)
            value (or (c :solution) (c :expected))
            name  (c :name)]
        (when value
          (unify/assign! solved mv value)
          (put c :solution value))
        (when name
          (unify/merge-named! c solved named name value mv))))

    (each c constraints
      (when (and (c :name) (nil? (c :solution)))
        (when-let [v (get named (c :name))]
          (put c :solution v)
          (unify/assign! solved (c :mv) v))))

    (each c constraints
      (when (and (c :name) (nil? (c :solution)))
        (errorf "unsolved named hole ?%v" (c :name))))

    solved))

(def exports
  {:unify/solve unify/solve})
