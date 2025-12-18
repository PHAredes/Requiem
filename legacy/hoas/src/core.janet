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

# Evaluation with optional tracing and gas limit
(var eval-trace nil)
(var eval-gas 1000)  # Default gas limit

(defn eval [tm]
  (when eval-gas
    (when (<= eval-gas 0)
      (error "Out of gas - evaluation limit exceeded")))
  (when eval-trace 
    (print "EVAL: " tm " (gas: " eval-gas ")"))
  (when eval-gas
    (set eval-gas (- eval-gas 1)))
  (let [result (match tm
    [:var x] x
    [:app f t] 
    (let [fv (eval f)
          tv (eval t)]
      (if (function? fv)
        (fv tv)
        (nf/neut (ne/app (if (string? fv) (ne/var fv) fv)
                         (if (string? tv) (ne/var tv) tv)))))
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
                                                                 (ne/var x))))))))
        (string? v) (nf/neut (ne/case (ne/var v) 
                                      (lower (ty/nat) (eval z))
                                      (fn [x] (lower (ty/nat)
                                                    (eval (sc (raise (ty/nat)
                                                                    (ne/var x))))))))))
    [:fix f] (eval (f (eval [:fix f])))  # ⚠️  Fixed point - can cause infinite loops!
    [:pair l r] [(eval l) (eval r)]
    [:fst p] (let [[l _] (eval p)] l)
    [:snd p] (let [[_ r] (eval p)] r))]
    (when eval-trace 
      (print "RESULT: " result))
    result))

# Normalization
(defn nf [ty tm]
  (lower ty (eval tm)))

# Pretty printer for terms (helper for tracing)
(defn pretty-term [term]
  "Convert term back to string representation"
  (match term
    [:var x] x
    [:zero] "zero"
    [:succ n] (string "(succ " (pretty-term n) ")")
    [:lam body] "(λx.body)"  # Simplified for HOAS
    [:app f x] (string "(" (pretty-term f) " " (pretty-term x) ")")
    [:case s z sc] (string "(case " (pretty-term s) " " (pretty-term z) " sc)")
    [:fix f] (string "(fix " (pretty-term f) ")")
    [:pair l r] (string "(pair " (pretty-term l) " " (pretty-term r) ")")
    [:fst p] (string "(fst " (pretty-term p) ")")
    [:snd p] (string "(snd " (pretty-term p) ")")
    [:nnat n] (string n)
    [:nneut ne] (string "neutral:" (pretty-term ne))
    [:nvar x] (string "nvar:" x)
    [:napp f x] (string "(" (pretty-term f) " " (pretty-term x) ")")
    _ (string term)))

# Pretty printer for evaluation results
(defn pretty-result [result]
  "Convert evaluation result to readable string"
  (match result
    [:nnat n] (string n)
    [:nneut ne] (string "neutral:" ne)
    [:nlam body] "(lam x . body)"  # HOAS functions can't be printed
    [:npair l r] (string "(" (pretty-result l) ", " (pretty-result r) ")")
    array (string "(" (pretty-result (result 0)) ", " (pretty-result (result 1)) ")")  # Pairs evaluate to arrays
    function "(lam x . body)"  # HOAS function
    string result
    number (string result)  # Handle raw numbers
    _ (string result)))

# Export functions
(def exports {
  :ty/emp ty/emp
  :ty/nat ty/nat
  :ty/fun ty/fun
  :ty/par ty/par
  :tm/var tm/var
  :tm/app tm/app
  :tm/lam tm/lam
  :tm/zero tm/zero
  :tm/succ tm/succ
  :tm/case tm/case
  :tm/fix tm/fix
  :tm/pair tm/pair
  :tm/fst tm/fst
  :tm/snd tm/snd
  :ne/var ne/var
  :ne/app ne/app
  :ne/succ ne/succ
  :ne/case ne/case
  :ne/pair ne/pair
  :ne/fst ne/fst
  :ne/snd ne/snd
  :nf/neut nf/neut
  :nf/lam nf/lam
  :nf/nat nf/nat
  :nf/pair nf/pair
  :eval eval
  :nf nf
  :eval-trace eval-trace
  :pretty-term pretty-term
  :pretty-result pretty-result
})

