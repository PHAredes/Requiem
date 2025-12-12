#!/usr/bin/env janet

# Main interface for HOAS interpreter
# Integrates parser and core interpreter

(import "./core")
(import "./parser")

# Helper functions to convert parsed data to core terms
(defn parse-type-to-core [parsed]
  "Convert parsed type data to core type representation"
  (match parsed
    ["emp"] (core/ty/emp)
    ["nat"] (core/ty/nat)
    ["fun" a "->" b] (core/ty/fun (parse-type-to-core a) (parse-type-to-core b))
    ["par" a "*" b] (core/ty/par (parse-type-to-core a) (parse-type-to-core b))
    _ (error "Invalid type parsed")))

(defn parse-term-to-core
  "Convert parsed term data to core term representation"
  [parsed]
  (print "parse-term-to-core called with:" parsed)
  (match parsed
    ["succ" & rest] (core/tm/succ (parse-term-to-core rest))
    ["app" f x] (core/tm/app (parse-term-to-core [f]) (parse-term-to-core [x]))
    ["lam" x "." body] (core/tm/lam (fn [_] (parse-term-to-core [body])))
    ["case" s z sc] (core/tm/case (parse-term-to-core (if (string? s) [s] s)) 
                                 (parse-term-to-core (if (string? z) [z] z))
                                 (fn [_] (parse-term-to-core (if (string? sc) [sc] sc))))
    ["case" & args] 
    (let [[s & rest] args]
      (if (= (get rest 0) "case")
        # Handle nested case: (case x (case y z w) z) -> ["case" "x" "case" "y" "z" "w" "z"]
        (let [[_ z2 sc2 & more] rest]
          (core/tm/case (parse-term-to-core [s])
                       (parse-term-to-core ["case" z2 sc2])
                       (fn [_] (parse-term-to-core (if (= 1 (length more)) [(get more 0)] more)))))
        # Handle regular case with more arguments
        (let [[z sc & more] rest]
          (core/tm/case (parse-term-to-core [s])
                       (parse-term-to-core [z])
                       (fn [_] (parse-term-to-core (if (= 1 (length more)) [(get more 0)] more)))))))
    ["fix" f] (core/tm/fix (fn [_] (parse-term-to-core [f])))
    ["pair" l r] (core/tm/pair (parse-term-to-core [l]) (parse-term-to-core [r]))
    ["pair" & args] 
    (let [[l & rest] args]
      (print "Pair with l:" l "rest:" rest)
      (if (and (> (length rest) 0) (= (get rest 0) "pair"))
        # Handle nested pair: (pair l (pair r (succ zero))) -> ["pair" "l" "pair" "r" "succ" "zero"]
        (let [[_ r & more] rest]
          (core/tm/pair (parse-term-to-core [l])
                       (parse-term-to-core (if (empty? more) ["pair" r] (tuple "pair" r ;more)))))
        # Handle regular pair with single argument: (pair l r)
        (if (= (length rest) 1)
          (let [result (core/tm/pair (parse-term-to-core [l])
                                    (parse-term-to-core rest))]
            (print "Single argument pair result:" result)
            result)
          # Handle flattened nested expression: (pair l (succ zero)) -> ["pair" "l" "succ" "zero"]
          (let [result (core/tm/pair (parse-term-to-core [l])
                                    (parse-term-to-core rest))]
            (print "Multiple arguments pair result:" result)
            result)))))
    ["fst" p] (core/tm/fst (parse-term-to-core [p]))
    ["snd" p] (core/tm/snd (parse-term-to-core [p]))
    [x] (when (string? x) 
          (match x
            "zero" (core/tm/zero)
            x (core/tm/var x)))
    _ (error (string "Invalid term parsed: " (string/format "%j" parsed)))))

(defn parse [input kind]
  "Parse input string and return core representation"
  (let [parser (case kind
                 :type parser/type-parser
                 :term parser/term-parser
                 (error "Invalid kind: must be :type or :term"))]
    (when-let [parsed (peg/match parser input)]
      (case kind
        :type (parse-type-to-core parsed)
        :term (parse-term-to-core parsed)))))

(defn term-to-string [term]
  "Convert a normalized term back to a readable string representation"
  (cond
    (nil? term) ""
    (number? term) (string term)
    (= term [:nnat 0]) "zero"
    (and (tuple? term) (= (length term) 2) (= (get term 0) :nnat)) 
      (string (get term 1))
    (string? term) term
    (and (tuple? term) (= (length term) 2) (= (get term 0) :nneut))
      (let [[_ ne] term]
        (match ne
          [:nvar x] x
          [:napp f x] (string "(app " (term-to-string [:nneut f]) " " (term-to-string [:nneut x]) ")")
          #[:nsucc n] (string "(succ " (term-to-string [:nneut n]) ")")
[:ncase s z sc] (string "(case " (term-to-string [:nneut s]) " " (term-to-string z) " " "<function>") ")")
          #[:nepair l r] (string "(pair " (term-to-string [:nneut l]) " " (term-to-string [:nneut r]) ")")
          #[:nfst p] (string "(fst " (term-to-string [:nneut p]) ")")
          #[:nsnd p] (string "(snd " (term-to-string [:nneut p]) ")")
          _ (string/format "%q" term)))
    (and (tuple? term) (= (length term) 2))
      (string "(pair " (term-to-string (get term 0)) " " (term-to-string (get term 1)) ")")
    (function? term) "<function>"
    (tuple? term) "<tuple>"
    ""))

(defn evaluate [input]
  "Parse and evaluate a term expression, returning the result"
  (print "Evaluating input:" input)
  (if-let [parsed (peg/match parser/term-parser input)]
    (do
      (print "Parsed:" parsed)
      (try
        (let [term (parse-term-to-core parsed)]
          (print "Core term:" term)
          (core/nf (core/ty/nat) term))
        ([err] 
          (print "Error in evaluation:" err)
          (print "Error type:" (type err))
          :error)))
    (do
      (print "Failed to parse input:" input)
      :error)))

# Command-line interface
(def args (dyn :args))
(when (and args (> (length args) 1))
  (let [expression (get args 1)
        result (evaluate expression)]
    (if (= result :error)
      (print "Error: Invalid expression")
      (print (term-to-string result)))))
