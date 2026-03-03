#!/usr/bin/env janet

# Benchmark: Context-aware cache vs no cache
(import ../src/coreTT :as c)
(import ../build/timer :as timer)

# Test with reused context (cache helps)
(defn test-cached []
  (print "\n--- REUSED CONTEXT (cache helps) ---")
  
  # Create context once
  (var ctx (c/ctx/empty))
  (for i 0 50
    (set ctx (c/ctx/add ctx (string "var" i) (c/ty/type i))))
  
  # Warmup cache
  (for i 0 50
    (c/ctx/lookup ctx (string "var" i)))
  
  # Benchmark lookups
  (def start (os/clock))
  (for i 0 10000
    (c/ctx/lookup ctx "var25"))
  (def elapsed (- (os/clock) start))
  
  (def st (c/ctx/cache-stats))
  (printf "  10,000 lookups: %.4fs" elapsed)
  (printf "  Cache stats: hits=%d misses=%d" (st :hits) (st :misses))
  (printf "  Hit rate: %.1f%%" (* (st :hit-rate) 100)))

# Test with fresh contexts each time (no cache benefit)
(defn test-uncached []
  (print "\n--- FRESH CONTEXT each time (no cache) ---")
  
  (def start (os/clock))
  (for trial 0 100
    # Create fresh context each iteration
    (var ctx (c/ctx/empty))
    (for i 0 50
      (set ctx (c/ctx/add ctx (string "var" i) (c/ty/type i))))
    # Single lookup
    (c/ctx/lookup ctx "var25"))
  (def elapsed (- (os/clock) start))
  
  (printf "  100 lookups (fresh ctx each): %.4fs" elapsed))

# Test cache survives context creation
(defn test-cache-survival []
  (print "\n--- CACHE SURVIVES CONTEXT CREATION ---")
  
  # Create original context
  (var ctx (c/ctx/empty))
  (for i 0 50
    (set ctx (c/ctx/add ctx (string "v" i) (c/ty/type i))))
  
  # Warmup
  (for i 0 50
    (c/ctx/lookup ctx (string "v" i)))
  
  # Create NEW context by adding
  (def ctx2 (c/ctx/add ctx "new" (c/ty/type 99)))
  
  # Lookup in original ctx (should still be cached)
  (def t1 (os/clock))
  (for i 0 1000
    (c/ctx/lookup ctx "v25"))
  (def time1 (- (os/clock) t1))
  
  # Lookup in new ctx (no cache for this)
  (def t2 (os/clock))
  (for i 0 1000
    (c/ctx/lookup ctx2 "new"))
  (def time2 (- (os/clock) t2))
  
  (printf "  1000 lookups in original ctx (cached): %.4fs" time1)
  (printf "  1000 lookups in new ctx (uncached):   %.4fs" time2)
  (printf "  Cache speedup: %.1fx" (/ time2 time1)))

(defn main []
  (print "=== Context Lookup Cache Benchmark ===")
  
  (test-cached)
  (test-uncached)
  (test-cache-survival)
  
  (print "\n✓ Done!"))

(main)