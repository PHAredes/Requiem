(import ../src/parser :as p)
(import ../build/timer :as timer)

(def samples
  @[
    "(data Nat: Type ((zero Nat) (succ (forall (n: Nat). Nat))))"
    "(data (Nat: Type) (zero Nat succ (Nat → Nat)))"
    "(def sum: (forall (n: Nat). (forall (m: Nat). Nat)) (match m: (case zero: m) (case (succ m'): (succ (sum n m')))))"
  ])

(defn stats [d]
  (def n (length d))
  (def srt (sort (reverse d)))
  {:mean (/ (sum d) n)
   :median (srt (div n 2))
   :min (first srt)})

(defn bench [name thunk iters trials]
  (print name "...")
  (def res @[])
  (repeat trials
    (gccollect)
    (let [start (timer/now)]
      (repeat iters (thunk))
      (array/push res (/ (- (timer/now) start) iters))))
  (let [s (stats res)]
    (printf "  %10.6f us [med: %10.6f, min: %10.6f]"
            (/ (s :mean) 1000)
            (/ (s :median) 1000)
            (/ (s :min) 1000))))

(defn run-all [f]
  (each src samples
    (f src)))

(defn main [&]
  (print "Benchmarking parser")
  (bench "peg compiled: parse" (fn [] (run-all p/parse/text)) 500 7)
  (bench "peg source: parse" (fn [] (run-all p/parse/text-raw)) 500 7))
