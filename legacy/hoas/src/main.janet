#!/usr/bin/env janet

# Import the core module and parser
(import "./core" :as core)
(import "./parser" :as parser)

# Parse a term string into a core term
(defn parse-term-to-core [parsed]
  "Convert parser output to core term representation"
  (match parsed
    [:zero] (core/tm/zero)
    [:succ n] (core/tm/succ (parse-term-to-core n))
    [:lam x body] (core/tm/lam (fn [env] (parse-term-to-core body)))
    [:app f x] (core/tm/app (parse-term-to-core f) (parse-term-to-core x))
    [:fix f] (core/tm/fix (fn [env] (parse-term-to-core f)))
    [:case s z sc] (core/tm/case (parse-term-to-core s) (parse-term-to-core z) 
                           (fn [env] (parse-term-to-core sc)))
    [:pair l r] (core/tm/pair (parse-term-to-core l) (parse-term-to-core r))
    [:fst p] (core/tm/fst (parse-term-to-core p))
    [:snd p] (core/tm/snd (parse-term-to-core p))
    :var (core/tm/var parsed)
    x (if (string? x) (core/tm/var x) x)))

# Enhanced term-to-string function - handles all normalized term types
(defn term-to-string [term]
  "Convert a normalized term back to a readable string representation"
  (cond
    (nil? term) ""
    
    # Natural numbers
    (and (tuple? term) (= (length term) 2) (= (get term 0) :nnat))
      (let [n (get term 1)]
        (if (= n 0)
          "zero"
          (let [result @[]]
            (for i 0 n 
              (array/push result "succ"))
            (array/push result "zero")
            (string/join result " "))))
    
    # Lambda functions
    (and (tuple? term) (= (length term) 2) (= (get term 0) :nlam))
      "<lambda>"
    
    # Raw lambda functions (not normalized)
    (and (tuple? term) (= (length term) 2) (= (get term 0) :lam))
      "<lambda>"
    
    # Pairs
    (and (tuple? term) (= (length term) 3) (= (get term 0) :npair))
      (let [l (get term 1) r (get term 2)]
        (string "(pair " (term-to-string l) " " (term-to-string r) ")"))
    
    # Applications
    (and (tuple? term) (= (length term) 3) (= (get term 0) :app))
      (let [f (get term 1) x (get term 2)]
        (string "(" (term-to-string f) " " (term-to-string x) ")"))
    
    # Neutral terms (variables, applications, etc.)
    (and (tuple? term) (= (length term) 2) (= (get term 0) :nneut))
      (let [ne (get term 1)]
        (cond
          # Variables
          (and (tuple? ne) (= (length ne) 2) (= (get ne 0) :nvar))
            (get ne 1)
          
          # Applications
          (and (tuple? ne) (= (length ne) 3) (= (get ne 0) :napp))
            (let [f (get ne 1) x (get ne 2)]
              (string "(" (term-to-string [:nneut f]) " " (term-to-string [:nneut x]) ")"))
          
          # Successor
          (and (tuple? ne) (= (length ne) 2) (= (get ne 0) :nsucc))
            (let [n (get ne 1)]
              (string "succ " (term-to-string [:nneut n])))
          
          # Case expressions
          (and (tuple? ne) (= (length ne) 4) (= (get ne 0) :ncase))
            (let [s (get ne 1) z (get ne 2) sc (get ne 3)]
              (string "(case " (term-to-string [:nneut s]) " " (term-to-string z) " " "<function>)"))
          
          # Pairs in neutral form
          (and (tuple? ne) (= (length ne) 3) (= (get ne 0) :nepair))
            (let [l (get ne 1) r (get ne 2)]
              (string "(pair " (term-to-string [:nneut l]) " " (term-to-string [:nneut r]) ")"))
          
          # First projection
          (and (tuple? ne) (= (length ne) 2) (= (get ne 0) :nfst))
            (let [p (get ne 1)]
              (string "(fst " (term-to-string [:nneut p]) ")"))
          
          # Second projection
          (and (tuple? ne) (= (length ne) 2) (= (get ne 0) :nsnd))
            (let [p (get ne 1)]
              (string "(snd " (term-to-string [:nneut p]) ")"))
          
          # Fallback
          true (string/format "%q" term)))
    
    # String values
    (string? term) term
    
    # Variables
    (and (tuple? term) (= (length term) 2) (= (get term 0) :var))
      (get term 1)
    
    # Functions
    (function? term) "<function>"
    
    # Numbers
    (number? term) (string term)
    
    # Other tuples
    (tuple? term) (string/format "%q" term)
    
    # Fallback
    (true "")))

(defn evaluate [input]
  "Parse and evaluate a term expression, returning the result"
  (if-let [parsed (parser/term-parser input)]
    (try
      (let [core-term (parse-term-to-core (get parsed 0))
            # Determine the appropriate type for normalization
            result (match core-term
                # Natural numbers
                [:zero] (core/nf (core/ty/nat) core-term)
                [:succ _] (core/nf (core/ty/nat) core-term)
                [:case _ _ _] (core/nf (core/ty/nat) core-term)
                
                # Pairs
                [:pair _ _] (core/nf (core/ty/par (core/ty/nat) (core/ty/nat)) core-term)
                [:fst _] (core/nf (core/ty/nat) core-term)
                [:snd _] (core/nf (core/ty/nat) core-term)
                
                # Functions
                [:lam _] core-term
                [:app _ _] core-term
                
                # Fixed points
                [:fix _] core-term
                
                # Variables
                [:var _] core-term
                
                # Default to nat
                _ (core/nf (core/ty/nat) core-term))]
        result)
      ([err]
        :error))
    :error))

# Command-line interface
(def args (dyn :args))

(when (and args (> (length args) 1))
  (let [expression (get args 1)
        result (evaluate expression)]
    (if (= result :error)
      (print "Error: Invalid expression")
      (print (term-to-string result)))))

# Export evaluate for testing