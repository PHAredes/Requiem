(import ../src/coreTT :as c)
(import ../build/timer :as timer)

(defn stats [d]
  (def n (length d))
  (def s (sort (reverse d)))
  {:mean (/ (sum d) n) :median (s (div n 2)) :min (first s)})

(defn bench [name thunk iters trials]
  (def res @[])
  (repeat trials
    (gccollect)
    (let [start (timer/now)]
      (repeat iters (thunk))
      (array/push res (/ (- (timer/now) start) iters))))
  (let [s (stats res)]
    (printf "%-30s | %15.6f | %15.6f | %15.6f" name (* 1000 (s :mean)) (* 1000 (s :median)) (* 1000 (s :min)))))

(defn main [&]
  (let [ctx (c/ctx/empty)
        # A complex term that takes time to evaluate
        complex-term (do
                       (var t [:type 0])
                       (loop [_ :range [0 100]]
                         (set t [:t-pi t (fn [_] t)]))
                       t)
        # A term that uses the complex term twice
        pair-term [:pair complex-term complex-term]]

    (print "Caching Benchmarks:")
    (printf "%-30s | %15s | %15s | %15s" "Type" "Mean (ms)" "Median (ms)" "Min (ms)")
    (print (string/repeat "-" 80))

    (bench "No Cache (Standard)" (fn [] (c/eval ctx pair-term)) 100 5)

    # Simple manual cache for testing
    (var cache @{})
    (defn eval-cached [ctx tm]
      (let [k [ctx tm]]
        (if-let [v (get cache k)]
          v
          (let [res (c/eval ctx tm)]
            (put cache k res)
            res))))

    (bench "Manual Table Cache" (fn [] (set cache @{}) (eval-cached ctx pair-term)) 100 5)

    # Fiber-local cache
    (defn eval-fiber-cached [ctx tm]
      (let [env (fiber/getenv (fiber/current))
            cache (get env :eval-cache)]
        (let [k [ctx tm]]
          (if-let [v (get cache k)]
            v
            (let [res (c/eval ctx tm)]
              (put cache k res)
              res)))))

    (fiber/setenv (fiber/current) @{:eval-cache @{}})
    (bench "Fiber-local Table Cache" (fn [] (put (fiber/getenv (fiber/current)) :eval-cache @{}) (eval-fiber-cached ctx pair-term)) 100 5)))

(main)
