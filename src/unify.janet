#!/usr/bin/env janet

(import ./levels :as lvl)

(defn- unify/record! [solved mv value]
  (if (has-key? solved mv)
    (when (not= (get solved mv) value)
      (errorf "conflicting solutions for %v" mv))
    (put solved mv value)))

(defn- unify/named-evidence [c]
  (or (c :solution)
      (and (c :name) (c :expected))))

(defn- unify/merge-named! [named c]
  (when-let [name (c :name)]
    (when-let [value (unify/named-evidence c)]
      (if-let [other (get named name)]
        (when (not= other value)
          (errorf "named hole ?%v has inconsistent constraints" name))
        (put named name value)))))

(defn- unify/fill-named! [constraints solved named]
  (each c constraints
    (when (and (c :name) (nil? (c :solution)))
      (if-let [value (get named (c :name))]
        (do
          (put c :solution value)
          (unify/record! solved (c :mv) value))
        (when (nil? (c :expected))
          (errorf "unsolved named hole ?%v" (c :name)))))))

(defn- unify/check-levels! [constraints]
  (defn ground-level [l]
    (let [norm (lvl/closed l)]
      (if (int? norm) norm nil)))
  (each c constraints
    (each constraint (c :level-constraints)
      (match constraint
        [:eq l1 l2]
        (let [g1 (ground-level l1)
              g2 (ground-level l2)]
          (when (and (not (nil? g1)) (not (nil? g2)))
            (when (not= g1 g2)
              (errorf "level constraint violation: %v != %v" l1 l2))))

        [:leq l1 l2]
        (let [g1 (ground-level l1)
              g2 (ground-level l2)]
          (when (and (not (nil? g1)) (not (nil? g2)))
            (when (> g1 g2)
              (errorf "level constraint violation: %v > %v" l1 l2))))

        _ nil))))

(defn unify/solve [constraints]
  "Reconcile named-hole evidence and validate level constraints.

  This is intentionally not a higher-order unifier. The only live semantics
  today are:
  - explicit `:solution` values remain authoritative
  - named constraints may use their `:expected` type as report-time evidence
  - that evidence propagates to other constraints with the same name
  - level constraints are validated when they are ground"
  (let [solved @{}
        named @{}]
    (each c constraints
      (when-let [value (c :solution)]
        (unify/record! solved (c :mv) value))
      (unify/merge-named! named c))

    (unify/fill-named! constraints solved named)
    (unify/check-levels! constraints)

    (each c constraints
      (when-let [value (c :solution)]
        (unify/record! solved (c :mv) value)))

    solved))

(def exports
  {:unify/solve unify/solve})
