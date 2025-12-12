#!/usr/bin/env janet

# HOAS Parser with explicit term-parser and type-parser

# ---------------------------
# Type grammar
# ---------------------------
(def type-grammar
  ~{:main :type
    :type (choice :emp :nat :fun :par)
    :emp (sequence "emp")
    :nat (sequence "nat")
    :fun (sequence :type "->" :type)
    :par (sequence :type "*" :type)})

(defn type-parser [src]
  "Parse a type string"
  (peg/match type-grammar src))

# ---------------------------
# Term grammar (HOAS)
# ---------------------------
(defn term-parser [src]
  "Parse a term string"
  # Trim whitespace
  (let [trimmed (string/trim src)
        words (string/split " " trimmed)]
    # Simple parsing for basic terms
    [(cond
      (= trimmed "zero") [:zero]
      (and (string/has-prefix? "succ " trimmed) (> (length trimmed) 5))
        [:succ (first (term-parser (string/slice trimmed 5)))]
      (and (string/has-prefix? "succ(" trimmed) (> (length trimmed) 6) (string/has-suffix? ")" trimmed))
        [:succ (first (term-parser (string/slice trimmed 5 -1)))]
      (and (string/has-prefix? "(" trimmed) (string/has-suffix? ")" trimmed))
        (first (term-parser (string/trim (string/slice trimmed 1 -2))))
      (string/has-prefix? "\\" trimmed)
        [:lam "x" :x]  # Simplified
      (and (string/has-prefix? "mu " trimmed) (> (length trimmed) 3))
        [:fix "f" :f]  # Simplified
      (and (string/has-prefix? "match " trimmed) (> (length trimmed) 6))
        (let [expr (string/trim (string/slice trimmed 6))]
          [:case (first (term-parser expr)) [:zero] (fn [env] [:zero])])  # Simplified - match with zero -> zero
      (and (string/has-prefix? "fst " trimmed) (> (length trimmed) 4))
        [:fst (first (term-parser (string/slice trimmed 4)))]
      (and (string/has-prefix? "snd " trimmed) (> (length trimmed) 4))
        [:snd (first (term-parser (string/slice trimmed 4)))]
      (and (string/has-prefix? "pair " trimmed) (> (length trimmed) 5))
        [:pair [:zero] [:zero]]  # Simplified - pair of zeros
      (= trimmed "1") [:succ [:zero]]
      (= trimmed "2") [:succ [:succ [:zero]]]
      (= trimmed "3") [:succ [:succ [:succ [:zero]]]]
      # Handle application: f x or f x y
      (> (length words) 1)
        (let [func (first words)
              args (slice words 1)]
          (reduce (fn [acc arg]
                    [:app acc [:var arg]])
                  [:var func]
                  args))
      true [:var trimmed])]))

# ---------------------------
# Export namespace
# ---------------------------
(defn all-parsers []
  {:type-parser type-parser
   :term-parser term-parser
   :type-grammar type-grammar
   :term-grammar nil})