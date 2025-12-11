#!/usr/bin/env janet

# HOAS (Higher-Order Abstract Syntax) Interpreter
# Based on NbE (Normalization by Evaluation)

# Type definitions
(defn ty/emp [] :emp)
(defn ty/nat [] :nat)
(defn ty/fun [a b] [:fun a b])
(defn ty/par [a b] [:par a b])

# Term constructors
(defn tm/var [x] [:var x])
(defn tm/app [f x] [:app f x])
(defn tm/lam [body] [:lam body])  # body is a Janet function
(defn tm/zero [] [:zero])
(defn tm/succ [n] [:succ n])
(defn tm/case [s z sc] [:case s z sc])  # sc is a function
(defn tm/fix [f] [:fix f])  # f is a function
(defn tm/pair [l r] [:pair l r])
(defn tm/fst [p] [:fst p])
(defn tm/snd [p] [:snd p])

# Neutral terms
(defn ne/var [x] [:nvar x])
(defn ne/app [f x] [:napp f x])
(defn ne/succ [n] [:nsucc n])
(defn ne/case [s z sc] [:ncase s z sc])
(defn ne/pair [l r] [:nepair l r])
(defn ne/fst [p] [:nfst p])
(defn ne/snd [p] [:nsnd p])

# Normal forms
(defn nf/neut [ne] [:nneut ne])
(defn nf/lam [body] [:nlam body])
(defn nf/nat [n] [:nnat n])
(defn nf/pair [l r] [:npair l r])

# Raise and Lower: mutually recursive conversion functions
(var raise nil)
(var lower nil)

# Raise: converts neutral terms to semantic values
(set raise
  (fn [ty ne]
    (match ty
      :emp (nf/neut ne)
      :nat (nf/neut ne)
      [:fun a b] (fn [x] (raise b (ne/app ne (lower a x))))
      [:par a b] [(raise a (ne/fst ne)) (raise b (ne/snd ne))])))

# Lower: converts semantic values to normal forms
(set lower
  (fn [ty sem]
    (match ty
      :emp sem
      :nat sem
      [:fun a b] (nf/lam (fn [x] (lower b (sem (raise a (ne/var x))))))
      [:par a b] (let [[x y] sem]
                   (nf/pair (lower a x) (lower b y))))))

# Evaluation
(defn eval [tm]
  (match tm
    [:var x] x
    [:app f t] ((eval f) (eval t))
    [:lam body] (fn [x] (eval (body x)))
    [:zero] (nf/nat 0)
    [:succ t] (let [v (eval t)]
                (match v
                  [:nnat n] (nf/nat (+ n 1))
                  [:nneut ne] (nf/neut (ne/succ ne))))
    [:case s z sc]
    (let [v (eval s)]
      (match v
        [:nnat 0] (eval z)
        [:nnat n] (eval (sc (nf/nat (- n 1))))
        [:nneut ne] (raise (ty/nat)
                           (ne/case ne
                                   (lower (ty/nat) (eval z))
                                   (fn [x] (lower (ty/nat)
                                                 (eval (sc (raise (ty/nat)
                                                                 (ne/var x))))))))))
    [:fix f] (eval (f (eval [:fix f])))
    [:pair l r] [(eval l) (eval r)]
    [:fst p] (let [[l _] (eval p)] l)
    [:snd p] (let [[_ r] (eval p)] r)))

# Normalization
(defn nf [ty tm]
  (lower ty (eval tm)))

# Helper: convert Janet number to HOAS nat term
(defn nat->tm [n]
  (if (zero? n)
    (tm/zero)
    (tm/succ (nat->tm (- n 1)))))

# Helper: extract number from semantic value
(defn sem->nat [sem]
  (match sem
    [:nnat n] n
    _ 0))  # Neutral - shouldn't happen for closed terms

# === PEG Parser for .hoas files ===

(def hoas-grammar
  ~{:main (sequence (any :ws) :expr (any :ws))
    
    # Whitespace and comments
    :ws (choice (set " \t\n\r") :comment)
    :comment (sequence "#" (any (if-not (set "\n") 1)))
    
    # Identifiers
    :ident (<- (sequence (choice (range "az" "AZ") "_")
                        (any (choice (range "az" "AZ" "09") "_" "-" "?" "!"))))
    
    # Numbers
    :number (number (<- (some (range "09"))))
    
    # Expressions
    :expr (choice :lam :fix :case :app-or-atom)
    
    # Lambda: \x => body or λx => body
    :lam (group (sequence (choice "\\" "λ")
                         (any :ws)
                         (constant :lam)
                         :ident
                         (any :ws)
                         "=>"
                         (any :ws)
                         :expr))
    
    # Fixed point: µx => body or mu x => body
    :fix (group (sequence (choice "µ" "mu")
                         (some :ws)
                         (constant :fix)
                         :ident
                         (any :ws)
                         "=>"
                         (any :ws)
                         :expr))
    
    # Case expression: match s { zero => z | succ x => sc }
    :case (group (sequence "match"
                          (some :ws)
                          (constant :case)
                          :expr
                          (any :ws)
                          "{"
                          (any :ws)
                          "zero"
                          (any :ws)
                          "=>"
                          (any :ws)
                          :expr
                          (any :ws)
                          "|"
                          (any :ws)
                          "succ"
                          (some :ws)
                          :ident
                          (any :ws)
                          "=>"
                          (any :ws)
                          :expr
                          (any :ws)
                          "}"))
    
    # Application and atoms
    :app-or-atom (choice :app :atom)
    
    :app (group (sequence (constant :app)
                         :atom
                         (some (sequence (some :ws) :atom))))
    
    :atom (choice :paren
                  :pair
                  :fst
                  :snd
                  :zero
                  :succ-atom
                  :number-lit
                  :var)
    
    # Parenthesized expression
    :paren (sequence "(" (any :ws) :expr (any :ws) ")")
    
    # Pair: (a, b)
    :pair (group (sequence "("
                          (any :ws)
                          (constant :pair)
                          :expr
                          (any :ws)
                          ","
                          (any :ws)
                          :expr
                          (any :ws)
                          ")"))
    
    # Projections
    :fst (group (sequence "fst" (some :ws) (constant :fst) :atom))
    :snd (group (sequence "snd" (some :ws) (constant :snd) :atom))
    
    # Zero
    :zero (group (sequence "zero" (constant :zero)))
    
    # Succ as prefix: succ n
    :succ-atom (group (sequence "succ" (some :ws) (constant :succ) :atom))
    
    # Number literal (syntactic sugar for nested succs)
    :number-lit :number
    
    # Variable
    :var (group (sequence (constant :var) :ident))})

# Parse a string into an AST
(defn parse [src]
  (try
    (peg/match hoas-grammar src)
    ([err]
      (do
        (print "PEG error: " err)
        (print "Input was: " src)
        nil))))

# Convert parsed AST to HOAS terms with environment
(defn ast->hoas [ast env]
  (match ast
    [:var id] (get env id (error (string "Unbound variable: " id)))
    
    [:lam id body]
    (tm/lam (fn [x] (ast->hoas body (merge env {id x}))))
    
    [:fix id body]
    (tm/fix (fn [x] (ast->hoas body (merge env {id x}))))
    
    [:app & atoms]
    (reduce (fn [f x] (tm/app f (ast->hoas x env)))
            (ast->hoas (first atoms) env)
            (slice atoms 1))
    
    [:zero] (tm/zero)
    
    [:succ n] (tm/succ (ast->hoas n env))
    
    [:case s z id sc]
    (tm/case (ast->hoas s env)
             (ast->hoas z env)
             (fn [x] (ast->hoas sc (merge env {id x}))))
    
    [:pair l r] (tm/pair (ast->hoas l env) (ast->hoas r env))
    
    [:fst p] (tm/fst (ast->hoas p env))
    
    [:snd p] (tm/snd (ast->hoas p env))
    
    n (if (number? n) (nat->tm n) (error (string "Unknown AST: " ast)))))

# === REPL and File Execution ===

(defn eval-hoas [src]
  (let [parsed (parse src)]
    (if parsed
      (do
        (print "Parsed AST: " (first parsed))
        (let [ast (first parsed)
              term (ast->hoas ast @{})]
          (print "Evaluating...")
          (eval term)))
      (do
        (print "Parse failed for: " src)
        (error "Parse error")))))

(defn eval-hoas-nat [src]
  (sem->nat (eval-hoas src)))

(defn load-hoas-file [path]
  (let [src (slurp path)]
    (eval-hoas src)))

(defn repl []
  (print "HOAS Interpreter REPL")
  (print "Enter expressions or :quit to exit")
  (print "Example: \\x => \\y => x")
  (print "Example: µf => \\n => match n { zero => zero | succ n' => succ (f n') }")
  (forever
    (prin "> ")
    (flush)
    (def input (getline))
    (if (or (not input) (= input ":quit"))
      (break)
      (try
        (let [result (eval-hoas input)]
          (pp result))
        ([err]
         (print "Error: " err))))))

# Main
(defn main [& args]
  (cond
    (empty? args)
    (repl)
    
    (= (first args) "repl")
    (repl)
    
    (string/has-suffix? ".hoas" (first args))
    (try
      (let [result (load-hoas-file (first args))]
        (pp result))
      ([err]
       (print "Error loading file: " err)))
    
    :else
    (when (not (string/has-suffix? ".janet" (first args)))
      (do
        (print "Evaluating expression: " (first args))
        (try
          (let [result (eval-hoas (first args))]
            (pp result))
          ([err]
           (print "Error: " err)))))))

(when (= (dyn :current-file) (dyn :source))
  (let [all-args (dyn :args)
        # Filter out the script name and .janet files
        args (filter |(not (string/has-suffix? ".janet" $)) (slice all-args 1))]
    (if (empty? args)
      (main)
      (main ;args))))
