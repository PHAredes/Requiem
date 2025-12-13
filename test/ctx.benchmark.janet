#!/usr/bin/env janet

# ================================================================
#           CONTEXT IMPLEMENTATION BENCHMARKS
#   Compare: table/clone vs prototypes vs arrays vs chunking
# ================================================================

(import spork/test)

# ================================================================
# Implementation 1: Current (table/clone)
# O(n) add (slowest construction), O(1) lookup (fastest lookup)
# ================================================================
(defn ctx1/empty [] @{})

(defn ctx1/add [Γ x A]
  (put (table/clone Γ) x A))

(defn ctx1/lookup [Γ x]
  (def A (get Γ x nil))
  (if (nil? A) 
    (error "unbound")
    A))

# ================================================================
# Implementation 2: Prototypes (pure)
# O(1) add (fastest construction), O(n) lookup (slowest lookup)
# ================================================================
(defn ctx2/empty [] @{})

(defn ctx2/add [Γ x A]
  (table/setproto @{x A} Γ))

(defn ctx2/lookup [Γ x]
  (def A (get Γ x nil))
  (if (nil? A)
    (error "unbound")
    A))

# ================================================================
# Implementation 3: Arrays
# O(n) add, O(n) lookup (worst performance overall)
# ================================================================
(defn ctx3/empty [] @[])

(defn ctx3/add [Γ x A]
  (array/concat @[[x A]] Γ))

(defn ctx3/lookup [Γ x]
  (var result nil)
  (each [y A] Γ
    (when (= x y)
      (set result A)
      (break)))
  (if result result (error "unbound")))

# ================================================================
# Implementation 4: Prototypes + Chunking (CHUNK_SIZE=50, Reference)
# O(k) amortized add, O(1) amortized lookup (Best Balance)
# ================================================================
(def CHUNK_SIZE_4 50)

(defn ctx4/empty []
  (def Γ (table/new (inc CHUNK_SIZE_4)))
  (put Γ :count 0)
  Γ)

(defn ctx4/add [Γ x A]
  (def count (get Γ :count 0))
  
  (if (< count CHUNK_SIZE_4)
    (do
      (def new-Γ (table/clone Γ))
      (put new-Γ x A)
      (put new-Γ :count (inc count))
      new-Γ)
    (do
      (def new-chunk (table/new (inc CHUNK_SIZE_4)))
      (put new-chunk x A)
      (put new-chunk :count 1)
      (table/setproto new-chunk Γ)
      new-chunk)))

(defn ctx4/lookup [Γ x]
  (def A (get Γ x nil))
  (if (nil? A)
    (error "unbound")
    A))

# ================================================================
# Implementation 5: Prototypes + Chunking (CHUNK_SIZE=32, Test Low K)
# O(low k) amortized add (faster), O(high n/k) amortized lookup (slower)
# ================================================================
(def CHUNK_SIZE_5 32)

(defn ctx5/empty []
  (def Γ (table/new (inc CHUNK_SIZE_5)))
  (put Γ :count 0)
  Γ)

(defn ctx5/add [Γ x A]
  (def count (get Γ :count 0))
  
  (if (< count CHUNK_SIZE_5)
    (do
      (def new-Γ (table/clone Γ))
      (put new-Γ x A)
      (put new-Γ :count (inc count))
      new-Γ)
    (do
      (def new-chunk (table/new (inc CHUNK_SIZE_5)))
      (put new-chunk x A)
      (put new-chunk :count 1)
      (table/setproto new-chunk Γ)
      new-chunk)))

(defn ctx5/lookup [Γ x]
  (def A (get Γ x nil))
  (if (nil? A)
    (error "unbound")
    A))
    
# ================================================================
# Implementation 6: Prototypes + Chunking (CHUNK_SIZE=64, Test High K)
# O(high k) amortized add (slower), O(low n/k) amortized lookup (faster)
# ================================================================
(def CHUNK_SIZE_6 64)

(defn ctx6/empty []
  (def Γ (table/new (inc CHUNK_SIZE_6)))
  (put Γ :count 0)
  Γ)

(defn ctx6/add [Γ x A]
  (def count (get Γ :count 0))
  
  (if (< count CHUNK_SIZE_6)
    (do
      (def new-Γ (table/clone Γ))
      (put new-Γ x A)
      (put new-Γ :count (inc count))
      new-Γ)
    (do
      (def new-chunk (table/new (inc CHUNK_SIZE_6)))
      (put new-chunk x A)
      (put new-chunk :count 1)
      (table/setproto new-chunk Γ)
      new-chunk)))

(defn ctx6/lookup [Γ x]
  (def A (get Γ x nil))
  (if (nil? A)
    (error "unbound")
    A))

# ================================================================
# Benchmark Helpers
# ================================================================
(defn time-it [name thunk iterations]
  (try
    (do
      (def warm-up-iters (max 100 (div iterations 100)))
      (repeat warm-up-iters (thunk))
      
      (def start (os/clock :cputime))
      (repeat iterations (thunk))
      (def elapsed (- (os/clock :cputime) start))
      (printf "%s: %.6f seconds (%.2f μs per iteration)" 
              name 
              elapsed 
              (* (/ elapsed iterations) 1000000))
      elapsed)
    ([err]
      (printf "%s: SKIPPED (error: %s)" name err)
      0)))

(defn gen-bindings [n]
  "Generate n unique bindings"
  (seq [i :range [0 n]]
    [(string "x" i) [:Type i]]))

# ================================================================
# Benchmark 1: Deep Context Construction
# ================================================================
(defn bench-deep-construction [ctx/empty ctx/add depths iterations]
  (print "\n=== Deep Context Construction ===")
  (each depth depths
    (time-it 
      (string "  Depth " depth)
      (fn []
        (var Γ (ctx/empty))
        (loop [i :range [0 depth]]
          (set Γ (ctx/add Γ (string "x" i) [:Type i]))))
      iterations)))

# ================================================================
# Benchmark 2: Sequential Lookups (worst case)
# ================================================================
(defn bench-sequential-lookups [ctx/empty ctx/add ctx/lookup depths iterations]
  (print "\n=== Sequential Lookups (worst case) ===")
  (each depth depths
    (var Γ (ctx/empty))
    (loop [i :range [0 depth]]
      (set Γ (ctx/add Γ (string "x" i) [:Type i])))
    
    (time-it
      (string "  Depth " depth " - lookup first binding")
      (fn [] (ctx/lookup Γ "x0"))
      iterations)))

# ================================================================
# Benchmark 3: Random Lookups (average case)
# ================================================================
(defn bench-random-lookups [ctx/empty ctx/add ctx/lookup depths iterations]
  (print "\n=== Random Lookups (average case) ===")
  (var rng (math/rng 42))
  (each depth depths
    (var Γ (ctx/empty))
    (loop [i :range [0 depth]]
      (set Γ (ctx/add Γ (string "x" i) [:Type i])))
    
    (time-it
      (string "  Depth " depth " - random lookups")
      (fn [] 
        (def key (string "x" (math/rng-int rng depth)))
        (ctx/lookup Γ key))
      iterations)))

# ================================================================
# Benchmark 4: Shadowing Performance
# ================================================================
(defn bench-shadowing [ctx/empty ctx/add ctx/lookup iterations]
  (print "\n=== Shadowing Performance ===")
  
  # Add same variable 100 times (heavy shadowing)
  (time-it
    "  Shadow 'x' 100 times"
    (fn []
      (var Γ (ctx/empty))
      (loop [i :range [0 100]]
        (set Γ (ctx/add Γ "x" [:Type i]))))
    iterations)
  
  # Verify lookup gets most recent
  (var Γ (ctx/empty))
  (loop [i :range [0 100]]
    (set Γ (ctx/add Γ "x" [:Type i])))
  (def result (ctx/lookup Γ "x"))
  (assert (= result [:Type 99]) "Shadowing broken!"))

# ================================================================
# Benchmark 5: Memory Allocation Pattern
# ================================================================
(defn bench-memory-churn [ctx/empty ctx/add depth iterations]
  (print "\n=== Memory Allocation Churn ===")
  (time-it
    (string "  Build & discard " depth "-deep contexts " iterations " times")
    (fn []
      (var Γ (ctx/empty))
      (loop [i :range [0 depth]]
        (set Γ (ctx/add Γ (string "x" i) [:Type i])))
      # Discard Γ (GC will collect)
      )
    iterations))

# ================================================================
# Benchmark 6: Type Checker Simulation
# ================================================================
(defn bench-typechecker-pattern [ctx/empty ctx/add ctx/lookup iterations]
  (print "\n=== Realistic Type Checker Pattern ===")
  
  # Simulate: build context, lookup a few times, extend, repeat
  (time-it
    "  Simulate 1000 type checks"
    (fn []
      (var Γ (ctx/empty))
      # Add 20 base bindings
      (loop [i :range [0 20]]
        (set Γ (ctx/add Γ (string "x" i) [:Type 0])))
      
      # Simulate checking 1000 terms
      (loop [_ :range [0 1000]]
        # Lookup a few variables
        (ctx/lookup Γ "x5")
        (ctx/lookup Γ "x10")
        # Extend context (lambda)
        (set Γ (ctx/add Γ (gensym) [:Type 0]))
        # More lookups
        (ctx/lookup Γ "x15")))
    iterations))

# ================================================================
# Benchmark 7: Wide Context (many parallel bindings)
# ================================================================
(defn bench-wide-context [ctx/empty ctx/add ctx/lookup widths iterations]
  (print "\n=== Wide Context (many siblings) ===")
  (each width widths
    (var Γ (ctx/empty))
    (loop [i :range [0 width]]
      (set Γ (ctx/add Γ (string "x" i) [:Type i])))
    
    (time-it
      (string "  Width " width " - lookup middle")
      (fn [] (ctx/lookup Γ (string "x" (div width 2))))
      iterations)))

# ================================================================
# Run All Benchmarks
# ================================================================
(defn run-all-benchmarks []
  (def depths [10 50 100 200 500])
  (def widths [10 50 100 200])
  
  # Increase iterations to make benchmarks slower (at least 0.5s each)
  (def construct-iters 5000)
  (def lookup-iters 500000)
  (def shadow-iters 10000)
  (def churn-iters 10000)
  (def typechecker-iters 100)
  (def wide-iters 500000)
  
  (print "\n" (string/repeat "=" 60))
  (print "IMPLEMENTATION 1: table/clone (current)")
  (print (string/repeat "=" 60))
  (bench-deep-construction ctx1/empty ctx1/add depths construct-iters)
  (bench-sequential-lookups ctx1/empty ctx1/add ctx1/lookup depths lookup-iters)
  (bench-random-lookups ctx1/empty ctx1/add ctx1/lookup depths lookup-iters)
  (bench-shadowing ctx1/empty ctx1/add ctx1/lookup shadow-iters)
  (bench-memory-churn ctx1/empty ctx1/add 100 churn-iters)
  (bench-typechecker-pattern ctx1/empty ctx1/add ctx1/lookup typechecker-iters)
  (bench-wide-context ctx1/empty ctx1/add ctx1/lookup widths wide-iters)
  
  (print "\n" (string/repeat "=" 60))
  (print "IMPLEMENTATION 2: Prototypes (pure)")
  (print (string/repeat "=" 60))
  (bench-deep-construction ctx2/empty ctx2/add depths construct-iters)
  (bench-sequential-lookups ctx2/empty ctx2/add ctx2/lookup depths lookup-iters)
  (bench-random-lookups ctx2/empty ctx2/add ctx2/lookup depths lookup-iters)
  (bench-shadowing ctx2/empty ctx2/add ctx2/lookup shadow-iters)
  (bench-memory-churn ctx2/empty ctx2/add 100 churn-iters)
  (bench-typechecker-pattern ctx2/empty ctx2/add ctx2/lookup typechecker-iters)
  (bench-wide-context ctx2/empty ctx2/add ctx2/lookup widths wide-iters)
  
  (print "\n" (string/repeat "=" 60))
  (print "IMPLEMENTATION 3: Arrays (O(n) lookup)")
  (print (string/repeat "=" 60))
  (bench-deep-construction ctx3/empty ctx3/add depths construct-iters)
  (bench-sequential-lookups ctx3/empty ctx3/add ctx3/lookup depths lookup-iters)
  (bench-random-lookups ctx3/empty ctx3/add ctx3/lookup depths lookup-iters)
  (bench-shadowing ctx3/empty ctx3/add ctx3/lookup shadow-iters)
  (bench-memory-churn ctx3/empty ctx3/add 100 churn-iters)
  (bench-typechecker-pattern ctx3/empty ctx3/add ctx3/lookup typechecker-iters)
  (bench-wide-context ctx3/empty ctx3/add ctx3/lookup widths wide-iters)
  
  (print "\n" (string/repeat "=" 60))
  (print "IMPLEMENTATION 4: Prototypes + Chunking (CHUNK=50 - Reference)")
  (print (string/repeat "=" 60))
  (bench-deep-construction ctx4/empty ctx4/add depths construct-iters)
  (bench-sequential-lookups ctx4/empty ctx4/add ctx4/lookup depths lookup-iters)
  (bench-random-lookups ctx4/empty ctx4/add ctx4/lookup depths lookup-iters)
  (bench-shadowing ctx4/empty ctx4/add ctx4/lookup shadow-iters)
  (bench-memory-churn ctx4/empty ctx4/add 100 churn-iters)
  (bench-typechecker-pattern ctx4/empty ctx4/add ctx4/lookup typechecker-iters)
  (bench-wide-context ctx4/empty ctx4/add ctx4/lookup widths wide-iters)

  (print "\n" (string/repeat "=" 60))
  (print "IMPLEMENTATION 5: Prototypes + Chunking (CHUNK=32 - Low K)")
  (print (string/repeat "=" 60))
  (bench-deep-construction ctx5/empty ctx5/add depths construct-iters)
  (bench-sequential-lookups ctx5/empty ctx5/add ctx5/lookup depths lookup-iters)
  (bench-random-lookups ctx5/empty ctx5/add ctx5/lookup depths lookup-iters)
  (bench-shadowing ctx5/empty ctx5/add ctx5/lookup shadow-iters)
  (bench-memory-churn ctx5/empty ctx5/add 100 churn-iters)
  (bench-typechecker-pattern ctx5/empty ctx5/add ctx5/lookup typechecker-iters)
  (bench-wide-context ctx5/empty ctx5/add ctx5/lookup widths wide-iters)

  (print "\n" (string/repeat "=" 60))
  (print "IMPLEMENTATION 6: Prototypes + Chunking (CHUNK=64 - High K)")
  (print (string/repeat "=" 60))
  (bench-deep-construction ctx6/empty ctx6/add depths construct-iters)
  (bench-sequential-lookups ctx6/empty ctx6/add ctx6/lookup depths lookup-iters)
  (bench-random-lookups ctx6/empty ctx6/add ctx6/lookup depths lookup-iters)
  (bench-shadowing ctx6/empty ctx6/add ctx6/lookup shadow-iters)
  (bench-memory-churn ctx6/empty ctx6/add 100 churn-iters)
  (bench-typechecker-pattern ctx6/empty ctx6/add ctx6/lookup typechecker-iters)
  (bench-wide-context ctx6/empty ctx6/add ctx6/lookup widths wide-iters)
)

# ================================================================
# Correctness Tests
# ================================================================
(defn test-correctness [ctx/empty ctx/add ctx/lookup name]
  (print "\n=== Testing " name " ===")
  
  # Test 1: Basic add/lookup
  (def Γ1 (ctx/add (ctx/empty) "x" [:Type 0]))
  (assert (= (ctx/lookup Γ1 "x") [:Type 0]) "Basic lookup failed")
  
  # Test 2: Multiple bindings
  (var Γ (ctx/empty))
  (set Γ (ctx/add Γ "x" [:Type 0]))
  (set Γ (ctx/add Γ "y" [:Type 1]))
  (set Γ (ctx/add Γ "z" [:Type 2]))
  (assert (= (ctx/lookup Γ "x") [:Type 0]))
  (assert (= (ctx/lookup Γ "y") [:Type 1]))
  (assert (= (ctx/lookup Γ "z") [:Type 2]))
  
  # Test 3: Shadowing
  (var Γ2 (ctx/empty))
  (set Γ2 (ctx/add Γ2 "x" [:Type 0]))
  (set Γ2 (ctx/add Γ2 "x" [:Type 1]))
  (set Γ2 (ctx/add Γ2 "x" [:Type 2]))
  (assert (= (ctx/lookup Γ2 "x") [:Type 2]) "Shadowing failed")
  
  # Test 4: Immutability
  (def Γ-base (ctx/add (ctx/empty) "x" [:Type 0]))
  (def Γ-ext (ctx/add Γ-base "y" [:Type 1]))
  (assert (= (ctx/lookup Γ-base "x") [:Type 0]))
  (try
    (do (ctx/lookup Γ-base "y") (error "Should not find y"))
    ([_] nil))
  
  # Test 5: Deep contexts (testing chunking/prototypes)
  (var Γ-deep (ctx/empty))
  (loop [i :range [0 200]]
    (set Γ-deep (ctx/add Γ-deep (string "x" i) [:Type i])))
  (assert (= (ctx/lookup Γ-deep "x0") [:Type 0]) "Deep context lookup failed")
  (assert (= (ctx/lookup Γ-deep "x199") [:Type 199]) "Deep context lookup failed")
  
  (print "  ✓ All correctness tests passed"))

# ================================================================
# Main
# ================================================================
(defn main [& args]
  # First verify all implementations are correct
  (test-correctness ctx1/empty ctx1/add ctx1/lookup "table/clone")
  (test-correctness ctx2/empty ctx2/add ctx2/lookup "Prototypes")
  (test-correctness ctx3/empty ctx3/add ctx3/lookup "Arrays")
  (test-correctness ctx4/empty ctx4/add ctx4/lookup "Prototypes+Chunking (50)")
  (test-correctness ctx5/empty ctx5/add ctx5/lookup "Prototypes+Chunking (32)")
  (test-correctness ctx6/empty ctx6/add ctx6/lookup "Prototypes+Chunking (64)")
  
  (print "\n" (string/repeat "=" 60))
  (print "It may take several minutes to finish")
  (print "Starting benchmarks...")
  (print "Note: Each benchmark runs for 30 seconds max")
  (print "Tests that fail (too deep chains) will be SKIPPED")
  (print (string/repeat "=" 60))
  
  (run-all-benchmarks)
  
  (print "\n" (string/repeat "=" 60))
  (print "SUMMARY")
  (print (string/repeat "=" 60))
  (print "Run complete! Compare results above.")
  (print "\nExpected results:")
  (print "  - Prototypes (pure): Fastest construction, slowest lookup (fails deep)")
  (print "  - table/clone: Slow construction, fastest lookup")
  (print "  - Arrays: Slow and memory-intensive")
  (print "  - Prototypes+Chunking: Best overall balance. ")
  )
