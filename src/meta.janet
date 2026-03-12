#!/usr/bin/env janet

(import /build/hamt :as h)

(defn make [deps]
  (let [goals @[]
        named-goals @{}
        ctx/lookup (deps :ctx/lookup)
        goal-ty (deps :goal-ty)
        goal-term (deps :goal-term)
        print/sem (deps :print/sem)
        sem-eq (deps :sem-eq)]
    (var collect? false)

    (defn expected/placeholder? [expected]
      (= expected goal-ty))

    (defn expected/merge [name current next]
      (cond
        (nil? current) next
        (nil? next) current
        (and (expected/placeholder? current)
             (not (expected/placeholder? next)))
        next
        (and (not (expected/placeholder? current))
             (expected/placeholder? next))
        current
        (not (sem-eq goal-ty current next))
        (errorf "named hole ?%v has inconsistent expected types: %s vs %s"
                name
                (print/sem current)
                (print/sem next))
        true
        current))

    (defn context-vars [Γ]
      (h/keys Γ))

    (defn report [name expected Γ]
      (let [ctx      (map (fn [k] [k (ctx/lookup Γ k)]) (h/keys Γ))
            expected (or expected goal-ty)]
        (if-let [goal (and name (get named-goals name))]
          (do
            (put goal :expected (expected/merge name (goal :expected) expected))
            (when (> (length ctx) (length (goal :ctx)))
              (put goal :ctx ctx))
            goal)
          (let [goal @{:name name :expected expected :ctx ctx}]
            (when name (put named-goals name goal))
            (array/push goals goal)
            goal))))

    (defn set-collect! [enabled]
      (set collect? enabled)
      collect?)

    (defn collecting? []
      collect?)

    (defn error-infer [name Γ]
      (if collect?
        (do
          (report name goal-ty Γ)
          goal-term)
        (errorf "unsolved goal ?%v during inference\nNo expected type is available in inference mode.\nContext variables: %v"
                name
                (context-vars Γ))))

    (defn error-check [name expected Γ]
      (if collect?
        (do
          (report name expected Γ)
          true)
        (errorf "unsolved goal ?%v during checking\nContext variables: %v"
                name
                (context-vars Γ))))

    {:goals goals
     :context-vars context-vars
     :report report
     :set-collect! set-collect!
     :collect? collecting?
     :error-infer error-infer
     :error-check error-check}))

(def exports {:make make})
