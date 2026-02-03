(import ../src/coreTT :as current)
(import ../legacy/coreTT_v1 :as legacy)
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
    [name (* 1000 (s :mean)) (* 1000 (s :median)) (* 1000 (s :min))]))

(defn run-suite [label eval-fn ctx-empty-fn]
  (let [ctx (ctx-empty-fn)
        A [:type 0]
        x [:type 0]
        motive-term (do
                      (var t [:type 0])
                      (loop [_ :range [0 100]]
                        (set t [:t-pi t (fn [_] t)]))
                      t)
        id-fn [:lam (fn [t] [:var t])]
        y-term (do
                 (var t [:type 0])
                 (loop [_ :range [0 100]]
                   (set t [:t-pi t (fn [_] t)]))
                 t)
        p-refl [:t-refl [:type 0]]
        p-neut [:neutral [:nvar "p"]]
        results @[]]

    (array/push results (bench "var lookup" (fn [] (eval-fn ctx [:var "x"])) 10000 5))
    (array/push results (bench "J success (refl)" (fn [] (eval-fn ctx [:t-J A x motive-term id-fn y-term p-refl])) 100 5))
    (array/push results (bench "J stuck (neutral)" (fn [] (eval-fn ctx [:t-J A x motive-term id-fn y-term p-neut])) 100 5))

    (printf "\nResults for: %s" label)
    (printf "%-20s | %15s | %15s | %15s" "Benchmark" "Mean (ms)" "Median (ms)" "Min (ms)")
    (printf "--------------------------------------------------------------------------------")
    (each r results
      (printf "%-20s | %15.6f | %15.6f | %15.6f" (r 0) (r 1) (r 2) (r 3)))))

(defn main [&]
  (print "Starting comparison benchmark...")
  (run-suite "Legacy V1 (Single Eval)" legacy/eval legacy/ctx/empty)
  (run-suite "Current (Split)" current/eval current/ctx/empty))

(main)
