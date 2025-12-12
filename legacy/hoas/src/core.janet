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
    [:fix f] (eval (f (eval [:fix f])))
    [:pair l r] [(eval l) (eval r)]
    [:fst p] (let [[l _] (eval p)] l)
    [:snd p] (let [[_ r] (eval p)] r)))

# Normalization
(defn nf [ty tm]
  (lower ty (eval tm)))

