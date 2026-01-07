(import ../build/timer :as timer)

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

(defn ctx1/add [Γ x A] (put (table/clone Γ) x A))
(defn ctx1/lookup [Γ x] (get Γ x))

(defn ctx2/add [Γ x A] (table/setproto @{x A} Γ))
(defn ctx2/lookup [Γ x] (get Γ x))

(def CHUNK_SIZE 50)
(defn ctx4/add [Γ x A]
  (def c (get Γ :count 0))
  (if (< c CHUNK_SIZE)
    (let [n (table/clone Γ)] (put n x A) (put n :count (inc c)) n)
    (let [n @{x A :count 1}] (table/setproto n Γ) n)))
(defn ctx4/lookup [Γ x] (get Γ x))

(defn main [&]
  (def DEPTH 100000)
  (def TRIALS 5)
  (print "timer: " (timer/type))

  (def ks (map (fn [_] (rand-str 12)) (range DEPTH)))
  (def tk (last ks))

  (print "\n[CONSTRUCTION]")
  (bench "table/clone" (fn [] (var g @{}) (loop [k :in ks] (set g (ctx1/add g k 1)))) 1 TRIALS DEPTH)
  (bench "prototypes" (fn [] (var g @{}) (loop [k :in ks] (set g (ctx2/add g k 1)))) 1 TRIALS DEPTH)
  (bench "chunking" (fn [] (var g @{:count 0}) (loop [k :in ks] (set g (ctx4/add g k 1)))) 1 TRIALS DEPTH)

  (print "\n[LOOKUP]")
  (var g1 @{}) (loop [k :in ks] (set g1 (ctx1/add g1 k 1)))
  (var g2 @{}) (loop [k :in ks] (set g2 (ctx2/add g2 k 1)))
  (var g4 @{:count 0}) (loop [k :in ks] (set g4 (ctx4/add g4 k 1)))

  (bench "table/clone" (fn [] (ctx1/lookup g1 tk)) 10000 TRIALS 1)
  (bench "prototypes" (fn [] (ctx2/lookup g2 tk)) 1000 TRIALS 1)
  (bench "chunking" (fn [] (ctx4/lookup g4 tk)) 10000 TRIALS 1))

(main)
