#!/usr/bin/env janet

(defn- unify/assign! [solved mv value]
  (if (has-key? solved mv)
    (when (not= (get solved mv) value)
      (errorf "conflicting solutions for %v" mv))
    (put solved mv value)))

(defn unify/solve [constraints]
  (let [solved @{}
        named @{}]
    (each c constraints
      (let [mv (c :mv)
            value (or (c :solution) (c :expected))
            name (c :name)]
        (when value
          (unify/assign! solved mv value)
          (put c :solution value))
        (when name
          (if (has-key? named name)
            (let [other (get named name)]
              (when (and value other (not= value other))
                (errorf "named hole ?%v has inconsistent constraints" name))
              (when (and value (nil? other))
                (put named name value))
              (when (and (nil? value) other)
                (put c :solution other)
                (unify/assign! solved mv other)))
            (put named name value)))))

    (each c constraints
      (when (and (c :name) (nil? (c :solution)))
        (errorf "unsolved named hole ?%v" (c :name))))

    solved))

(def exports
  {:unify/solve unify/solve})
