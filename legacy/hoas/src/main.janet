#!/usr/bin/env janet

# HOAS Main - Interactive interpreter with step-by-step evaluation

(import spork/test)
(import "../src/core" :as h)
(import "../src/parser" :as p)

# Helper function to evaluate with gas limit for fixed points
(defn evaluate-with-gas [input gas-limit]
  "Parse and evaluate expression with gas limit to prevent infinite loops"
  (try
    (let [term (p/parse input)]
      (set h/eval-gas gas-limit)
      (let [result (h/eval term)]
        (set h/eval-gas 1000)  # Reset gas
        result))
    ([err] 
      (set h/eval-gas 1000)  # Reset gas on error
      :error)))

# Evaluate with tracing enabled (with gas limit)
(defn evaluate-with-trace [input]
  "Parse and evaluate expression, showing steps"
  (try
    (let [term (p/parse input)]
      (print "\nInput: " input)
      (print "Parsed: " (p/pretty-term term))
      (print "\n=== Evaluation Trace ===")
      (set h/eval-trace true)
      (set h/eval-gas 100)  # Limited gas for tracing
      (let [result (h/eval term)]
        (set h/eval-trace false)
        (set h/eval-gas 1000)  # Reset gas
        (print "\nFinal result: " (h/pretty-result result))
        result))
    ([err]
      (set h/eval-trace false)
      (set h/eval-gas 1000)  # Reset gas on error
      (print "Error: " err)
      :error)))

# Command line interface
(defn evaluate-args []
  "Handle command line arguments"
  (let [args (dyn :args)]
    (if (<= (length args) 1)
      (repl)
      (do
        (print "Evaluating: " ((slice args 1) 0))
        (evaluate-with-trace ((slice args 1) 0))))))

# Export functions
(def exports {
  :evaluate evaluate-with-trace
  :evaluate-args evaluate-args
})

# Run if this file is executed directly
(when (get (dyn :args) 0)
  (evaluate-args))
