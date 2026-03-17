#!/usr/bin/env janet

(import ./levels :as lvl)

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

(defn- unify/pattern-unify [term1 term2]
  "Pattern unification for dependent types"
  (match [term1 term2]
    [[:var x] [:var y]] (if (= x y) @{} nil)
    [[:app f1 a1] [:app f2 a2]]
    (let [f-sol (unify/pattern-unify f1 f2)
          a-sol (unify/pattern-unify a1 a2)]
      (when (and f-sol a-sol)
        (merge f-sol a-sol)))
    [[:lam body1] [:lam body2]]
    (let [fresh (gensym)]
      (unify/pattern-unify (body1 fresh) (body2 fresh)))
    _ nil))

(defn- unify/higher-order-step [constraints solved changed]
  "Perform one step of higher-order unification"
  (reduce (fn [changed c]
            (if (c :solution)
              changed
              (if-let [expected (c :expected)]
                (let [dependencies (c :dependencies)
                      all-deps-solved? (all |(get solved $) dependencies)]
                  (when all-deps-solved?
                    (let [solution (unify/pattern-unify [:var (c :mv)] expected)]
                      (when solution
                        (unify/assign! solved (c :mv) solution)
                        (put c :solution solution)
                        true))))
                changed)))
          changed
          constraints))

(defn- unify/solve-level-constraints [level-constraints]
  "Solve universe level constraints"
  (let [solutions @{}
        constraints (array/slice level-constraints)]
    # Simple level constraint solver - can be extended later
    (each constraint constraints
      (match constraint
        [:eq l1 l2]
        (when (and (lvl/const? l1) (lvl/const? l2))
          (when (not= (l1 1) (l2 1))
            (errorf "level constraint violation: %v != %v" l1 l2)))
        [:leq l1 l2]
        (when (and (lvl/const? l1) (lvl/const? l2))
          (when (> (l1 1) (l2 1))
            (errorf "level constraint violation: %v > %v" l1 l2)))
        _ nil))
    solutions))

(defn unify/solve [constraints]
  (let [solved @{}
        named  @{}]
    # First pass: solve simple constraints
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

    # Solve level constraints
    (let [level-constraints (reduce (fn [acc c]
                                      (array/concat acc (c :level-constraints)))
                                    @[]
                                    constraints)]
      (unify/solve-level-constraints level-constraints))

    # Higher-order unification for dependent constraints
    (var changed true)
    (var iterations 0)
    (while (and changed (< iterations 100))
      (set changed (unify/higher-order-step constraints solved false))
      (++ iterations))

    (each c constraints
      (when (and (c :name) (nil? (c :solution)))
        (errorf "unsolved named hole ?%v" (c :name))))

    solved))

(def exports
  {:unify/solve unify/solve})
