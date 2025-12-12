#!/usr/bin/env janet

# HOAS Parser with user-friendly syntax

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
    
    # Atom expressions - reorganized to prioritize specific patterns
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

# Export for compatibility with existing code
(def grammar hoas-grammar)

(defn all-parsers []
  {:grammar hoas-grammar
   :parse parse})
