(import ../src/coreTT :as c)
(import ../build/timer :as timer)

(defn main [&]
  (print "Running massive test (deep terms)...")

  (let [depth 5000
        ctx (c/ctx/empty)]

    (print "Creating a term of depth " depth "...")
    # This creates a term (λx. x) applied to itself many times
    # Without memoization, evaluating this could be O(2^n) depending on structure
    # Here we create a simple deep nest: (((... (id id) ...)))
    (var id [:lam (fn [x] [:var x])])
    (var deep id)
    (loop [_ :range [0 depth]]
      (set deep [:app id deep]))

    (print "Evaluating deep term (this tests stack size and memoization)...")
    (try
      (let [res (c/eval/session (fn [] (c/eval ctx deep)))]
        (print "Success! Result head: " (first res)))
      ([err]
        (print "Failed: " err)
        (os/exit 1))))

  (print "\nTesting shared sub-structure (exponential without memoization)...")
  (let [depth 30
        ctx (c/ctx/empty)]
    # (pair t t) where t is also a pair... O(2^depth) without memoization
    (var t [:type 0])
    (loop [_ :range [0 depth]]
      (set t [:pair t t]))

    (print "Evaluating highly shared term...")
    (let [start (os/clock)]
      (c/eval/session (fn [] (c/eval ctx t)))
      (printf "Success! Evaluated in %.4f seconds" (- (os/clock) start))))

  (print "\ndone."))

(main)
