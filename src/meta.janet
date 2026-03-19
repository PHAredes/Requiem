#!/usr/bin/env janet

(import /build/hamt :as h)

(defn make [deps]
  (let [goals @[]
        ctx/lookup (deps :ctx/lookup)
        T/Meta (deps :T/Meta)
        goal-ty (deps :goal-ty)
        print/sem (deps :print/sem)
        sem-eq (deps :sem-eq)]
    (var named-goals @{})
    (var named-metas @{})
    (var solutions @{})
    (var next-id 0)
    (var collect? false)

    (defn goal/name [name]
      (if (or (nil? name)
              (= name "_")
              (= name "?"))
        nil
        name))

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

    (defn fresh-id []
      (let [id (string "mv" (+ next-id 1))]
        (++ next-id)
        id))

    (defn meta/id [name]
      (if name
        (or (get named-metas name)
            (let [id name]
              (put named-metas name id)
              id))
        (fresh-id)))

    (defn meta/value [name]
      (let [id (meta/id (goal/name name))]
        (or (get solutions id)
            [T/Meta id])))

    (defn solve! [name value]
      (let [id (meta/id (goal/name name))]
        (put solutions id value)
        value))

    (defn snapshot []
      {:goals (array/slice goals)
       :named-goals (table/clone named-goals)
       :named-metas (table/clone named-metas)
       :solutions (table/clone solutions)
       :next-id next-id
       :collect? collect?})

    (defn restore! [state]
      (array/clear goals)
      (each goal (state :goals)
        (array/push goals goal))
      (set named-goals (table/clone (state :named-goals)))
      (set named-metas (table/clone (state :named-metas)))
      (set solutions (table/clone (state :solutions)))
      (set next-id (state :next-id))
      (set collect? (state :collect?))
      true)

    (defn report [name expected Γ]
      (let [ctx      (map (fn [k] [k (ctx/lookup Γ k)]) (h/keys Γ))
            name     (goal/name name)
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

    (defn reset! []
      (array/clear goals)
      (set named-goals @{})
      (set named-metas @{})
      (set solutions @{})
      (set next-id 0)
      true)

    (defn set-collect! [enabled]
      (set collect? enabled)
      collect?)

    (defn collecting? []
      collect?)

    (defn error-infer [name Γ]
      (if collect?
        (do
          (report name goal-ty Γ)
          (meta/value name))
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
     :reset! reset!
     :snapshot snapshot
     :restore! restore!
     :meta/value meta/value
     :solve! solve!
     :set-collect! set-collect!
     :collect? collecting?
     :error-infer error-infer
     :error-check error-check}))

(def exports {:make make})
