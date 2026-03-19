#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../build/hamt :as h)
(import ../../src/meta :as meta)

(def suite (test/start-suite "Core Meta"))

(defn ctx [entries]
  (reduce (fn [acc [name ty]]
            (h/put acc name ty))
          (h/new)
          entries))

(defn make-state []
  (meta/make {:ctx/lookup h/get
              :goal-ty [:type 100]
              :goal-term [:type 100]
              :print/sem string}))

(test/assert suite
  (let [state (make-state)]
    ((state :set-collect!) true)
    (array/clear (state :goals))
    ((state :error-infer) "named" (ctx @[["x" [:type 0]]]))
    ((state :error-check) "named" [:type 0] (ctx @[["x" [:type 0]] ["y" [:type 1]]]))
    (let [goals (state :goals)]
      (and (= (length goals) 1)
           (= ((goals 0) :name) "named")
           (= ((goals 0) :expected) [:type 0])
           (= (length ((goals 0) :ctx)) 2))))
  "Named goals are deduplicated and upgraded with checked expectations")

(test/assert-error suite
  (fn []
    (let [state (make-state)]
      ((state :set-collect!) true)
      (array/clear (state :goals))
      ((state :error-check) "named" [:type 0] (ctx @[]))
      ((state :error-check) "named" [:type 1] (ctx @[]))))
  "Named goals reject inconsistent expected types")

(test/assert suite
  (let [state (make-state)]
    ((state :set-collect!) true)
    ((state :reset!))
    ((state :error-check) "_" [:type 0] (ctx @[]))
    ((state :error-check) "_" [:type 1] (ctx @[]))
    (let [goals (state :goals)]
      (and (= (length goals) 2)
           (nil? ((goals 0) :name))
           (nil? ((goals 1) :name)))))
  "Underscore holes stay anonymous across goal collection")

(test/assert suite
  (let [state (make-state)]
    ((state :set-collect!) true)
    ((state :error-check) "named" [:type 0] (ctx @[]))
    ((state :reset!))
    (= (length (state :goals)) 0))
  "Meta state reset clears collected goals")

(test/end-suite suite)
