#!/usr/bin/env janet

(import /build/hamt :as h)

(defn make [deps]
  (let [goals @[]
        ty/type (deps :ty/type)
        ctx/lookup (deps :ctx/lookup)
        goal-ty (ty/type 100)]
    (var collect? false)

    (defn context-vars [Γ]
      (map keyword (h/keys Γ)))

    (defn report [name expected Γ]
      (let [goal {:name name
                  :expected expected
                  :ctx (map (fn [k] [k (ctx/lookup Γ k)]) (h/keys Γ))}]
        (array/push goals goal)))

    (defn set-collect! [enabled]
      (set collect? enabled)
      collect?)

    (defn error-infer [name Γ]
      (if collect?
        (do
          (report name goal-ty Γ)
          [:type 100])
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
     :error-infer error-infer
     :error-check error-check}))

(def exports {:make make})
