(import ../build/timer :as timer)
(import ../build/hamt :as hamt)

(def SEED 12345)
(def rng (math/rng SEED))
(defn rand-str [len]
  (def b @"")
  (loop [_ :range [0 len]] (buffer/push-byte b (+ 97 (math/rng-int rng 26))))
  (string b))

(defn stats [d]
  (def n (length d))
  (def s (sort (reverse d)))
  {:mean (/ (sum d) n) :median (s (div n 2)) :min (first s)})

(defn bench [name thunk iters trials n]
  (print name "...")
  (def res @[])
  (repeat trials
    (gccollect)
    (let [start (timer/now)]
      (repeat iters (thunk))
      (array/push res (/ (- (timer/now) start) (* iters n)))))
  (let [s (stats res)]
    (printf "  %10.2f [med: %10.2f, min: %10.2f]" (s :mean) (s :median) (s :min))))

(defn main [&]
  (def DEPTH 100000)
  (def TRIALS 10)
  (print "timer: " (timer/type))
  (print "scale: " DEPTH)

  (def ks (map (fn [_] (rand-str 12)) (range DEPTH)))
  (def tk (ks (div DEPTH 2)))

  (print "\n[CONSTRUCTION]")
  (bench "complex" (fn [] (def h (hamt/new-mut)) (loop [k :in ks] (hamt/put-mut h k @[]))) 1 TRIALS DEPTH)
  (bench "soo" (fn [] (def h (hamt/new-mut)) (loop [k :in ks] (hamt/put-mut h k true))) 1 TRIALS DEPTH)

  (let [hmut (hamt/new-mut)
        hsoo (hamt/new-mut)]
    (loop [k :in ks] (hamt/put-mut hmut k @[]))
    (loop [k :in ks] (hamt/put-mut hsoo k true))

    (print "\n[LOOKUP]")
    (bench "complex" (fn [] (hamt/get-mut hmut tk)) 500000 TRIALS 1)
    (bench "soo" (fn [] (hamt/get-mut hsoo tk)) 500000 TRIALS 1))
  (print "\ndone.\n"))

(main)
