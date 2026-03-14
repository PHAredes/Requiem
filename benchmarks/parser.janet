(import ../src/frontend/surface/parser :as s)
(import ../build/timer :as timer)

(def program-samples
  @[
    "Nat:\n  zero\n  succ Nat\n"
    "Vec(A: Type, n: Nat):\n  zero = vnil\n  A, (succ n) = vcons (x: A) (xs: Vec A n)\n"
    "sum(n, m: Nat): Nat\n  n zero = n\n  n (succ m') = succ (sum n m')\n"
  ])

(def expr-samples
  @[
    "f x y"
    "\\ x . x"
    "J Type1 Type0 (\\ y . \\ p . Id Type1 Type0 y) (refl Type0) Type0 (refl Type0)"
  ])

(def type-samples
  @[
    "A -> B -> C"
    "Pi(A: Type). A -> A"
    "Type(max(1, u + 2, v))"
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
  (let [s (stats res)
        mean-us (/ (s :mean) 1000.0)
        median-us (/ (s :median) 1000.0)
        min-us (/ (s :min) 1000.0)]
    (print "  " mean-us " us [med: " median-us ", min: " min-us "]")))

(defn run-all [f]
  (each src program-samples
    (f src)))

(defn run-all-exprs [f]
  (each src expr-samples
    (f src)))

(defn run-all-types [f]
  (each src type-samples
    (f src)))

(defn main [&]
  (print "Benchmarking parser")
  (bench "surface: program" (fn [] (run-all s/parse/program)) 500 7)
  (bench "surface: expr" (fn [] (run-all-exprs s/parse/expr-text)) 500 7)
  (bench "surface: type" (fn [] (run-all-types s/parse/type-text)) 500 7))
