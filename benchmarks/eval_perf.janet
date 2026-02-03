(import ../src/coreTT :as c)
(import ../build/timer :as timer)

(defn stats [d]
  (def n (length d))
  (def s (sort (reverse d)))
  {:mean (/ (sum d) n) :median (s (div n 2)) :min (first s)})

(defn bench [name thunk iters trials]
  (print name "...")
  (def res @[])
  (repeat trials
    (gccollect)
    (let [start (timer/now)]
      (repeat iters (thunk))
      (array/push res (/ (- (timer/now) start) iters))))
  (let [s (stats res)]
    (printf "  %10.6f ms [med: %10.6f, min: %10.6f]" (* 1000 (s :mean)) (* 1000 (s :median)) (* 1000 (s :min)))))

(defn main [&]
  (let [Γ (c/ctx/empty)
        A [:type 0]
        x [:type 0]
        # Motive: a very complex TERM
        motive-term (do
                      (var t [:type 0])
                      (loop [i :range [0 500]]
                        (set t [:t-pi t (fn [_] t)]))
                      t)

        id-fn [:lam (fn [t] [:var t])]
        # y: another complex TERM
        y-term (do
                 (var t [:type 0])
                 (loop [i :range [0 500]]
                   (set t [:t-pi t (fn [_] t)]))
                 t)
        p-refl [:t-refl [:type 0]]
        p-neut [:neutral [:nvar "p"]]

        # J term with refl proof
        term-refl [:t-J A x motive-term id-fn y-term p-refl]
        # J term with neutral proof
        term-neut [:t-J A x motive-term id-fn y-term p-neut]]

    (print "Benchmarking eval of J with complex motive/y...")
    (bench "J with refl (success)" (fn [] (c/eval Γ term-refl)) 100 5)
    (bench "J with neutral (stuck)" (fn [] (c/eval Γ term-neut)) 100 5)))

(main)
