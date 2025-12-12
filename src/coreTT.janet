#!/usr/bin/env janet

# ================================================================
#                       CORETT (Janet) - Improved
#   HOAS kernel with proper semantic domain, NbE with eta-equality,
#   bidirectional type checker with better context handling
# ================================================================

# ---------------------
# Semantic Domain (separate from syntax!)
# ---------------------
# Semantic values:
#   [:Type l]           - universes
#   function            - Pi types (HOAS)
#   [v1 v2]             - Sigma types (pairs)
#   [:neutral ne]       - stuck terms

# Normal forms:
#   [:nlam body]        - lambda abstraction
#   [:npair l r]        - pair
#   [:nType l]          - type universe
#   [:nPi A B]          - Pi type
#   [:nSigma A B]       - Sigma type
#   [:nneut ne]         - neutral term

# Neutral terms:
#   [:nvar x]           - variable
#   [:napp f x]         - application
#   [:nfst p]           - first projection
#   [:nsnd p]           - second projection

# ---------------------
# Type constructors
# ---------------------
(defn ty/type [lvl] [:Type lvl])
(defn ty/pi [A B] [:Pi A B])
(defn ty/sigma [A B] [:Sigma A B])

(defn univ-lvl [ty] 
  (match ty 
    [:Type l] l
    _ (errorf "not a universe: %v" ty)))

# ---------------------
# Term constructors (HOAS syntax)
# ---------------------
(defn tm/var [x] [:var x])
(defn tm/lam [body] [:lam body])
(defn tm/app [f x] [:app f x])
(defn tm/type [l] [:type l])
(defn tm/pi [A B] [:t-pi A B])
(defn tm/sigma [A B] [:t-sigma A B])
(defn tm/pair [l r] [:pair l r])
(defn tm/fst [p] [:fst p])
(defn tm/snd [p] [:snd p])

# ---------------------
# Neutral / normal form constructors
# ---------------------
(defn ne/var [x] [:nvar x])
(defn ne/app [f x] [:napp f x])
(defn ne/fst [p] [:nfst p])
(defn ne/snd [p] [:nsnd p])

(defn nf/neut [ne] [:nneut ne])
(defn nf/lam [body] [:nlam body])
(defn nf/pi [A B] [:nPi A B])
(defn nf/sigma [A B] [:nSigma A B])
(defn nf/type [l] [:nType l])
(defn nf/pair [l r] [:npair l r])

# ---------------------
# Context with proper shadowing
# ---------------------
# Context is a list of [name type] tuples
# This preserves shadowing: newer bindings shadow older ones
(defn ctx/empty [] @[])

(defn ctx/add [Γ x A]
  (array/concat @[x A] Γ))

(defn ctx/lookup [Γ x]
  (var found nil)
  (var i 0)
  (while (and (< i (length Γ)) (nil? found))
    (if (= (get Γ i) x)
      (set found (get Γ (+ i 1)))
      (+= i 2)))
  (if (nil? found)
    (errorf "unbound variable: %v" x)
    found))

# ---------------------
# NbE: raise / lower with eta-equality
# ---------------------
(var raise nil)
(var lower nil)

(set raise
  (fn [ty ne]
    (match ty
      [:Type l] [:neutral ne]
      
      [:Pi A B]
      (fn [x]
        (let [nfx (lower A x)]
          (raise (B x) (ne/app ne nfx))))
      
      [:Sigma A B]
      (let [v1 (raise A (ne/fst ne))
            v2 (raise (B v1) (ne/snd ne))]
        [v1 v2]))))

(set lower
  (fn [ty sem]
    (match ty
      [:Type l] 
      (match sem
        [:neutral ne] (nf/neut ne)
        _ sem)  # pass through [:Type l] unchanged
      
      [:Pi A B]
      (match sem
        # Eta-equality for functions: λx. f x ≡ f
        [:neutral ne]
        (nf/lam
          (fn [fresh]
            (let [arg-sem (raise A (ne/var fresh))]
              (lower (B arg-sem)
                     (raise (B arg-sem) (ne/app ne (lower A arg-sem)))))))
        
        # Normal function
        _
        (nf/lam
          (fn [fresh]
            (let [arg-sem (raise A (ne/var fresh))]
              (lower (B arg-sem) (sem arg-sem))))))
      
      [:Sigma A B]
      (match sem
        # Eta-equality for pairs: (fst p, snd p) ≡ p
        [:neutral ne]
        (let [v1 (raise A (ne/fst ne))
              v2 (raise (B v1) (ne/snd ne))]
          (nf/pair (lower A v1) (lower (B v1) v2)))
        
        # Normal pair
        [v1 v2]
        (nf/pair (lower A v1) (lower (B v1) v2))))))

# ---------------------
# Evaluator (returns semantic values)
# ---------------------
(defn eval [Γ tm]
  "Evaluate a term in context Γ to a semantic value"
  (match tm
    # String variable - look up in context
    [:var x]
    (if (string? x)
      [:neutral (ne/var x)]
      x)  # Already a semantic value
    
    [:lam body] 
    (fn [x] (eval Γ (body x)))
    
    [:app f x]
    (let [fv (eval Γ f)
          xv (eval Γ x)]
      (match fv
        [:neutral ne] [:neutral (ne/app ne (lower [:Type 0] xv))]
        _ (fv xv)))  # apply function
    
    [:type l] (ty/type l)
    
    [:t-pi A B] 
    (ty/pi (eval Γ A) (fn [x] (eval Γ (B x))))
    
    [:t-sigma A B] 
    (ty/sigma (eval Γ A) (fn [x] (eval Γ (B x))))
    
    [:pair a b] [(eval Γ a) (eval Γ b)]
    
    [:fst p]
    (let [v (eval Γ p)]
      (match v
        [l r] l
        [:neutral ne] [:neutral (ne/fst ne)]))
    
    [:snd p]
    (let [v (eval Γ p)]
      (match v
        [l r] r
        [:neutral ne] [:neutral (ne/snd ne)]))))

(defn nf [ty tm]
  (lower ty (eval (ctx/empty) tm)))

# ---------------------
# Definitional equality with eta
# ---------------------
(defn sem-eq [ty v1 v2]
  "Check if two semantic values are equal at given type (with eta)"
  (match ty
    [:Type l] (= v1 v2)
    
    [:Pi A B]
    (let [fresh (gensym)
          arg (raise A (ne/var fresh))]
      (match [v1 v2]
        [[:neutral ne1] [:neutral ne2]] (= ne1 ne2)
        _ (sem-eq (B arg) (v1 arg) (v2 arg))))
    
    [:Sigma A B]
    (match [v1 v2]
      [[l1 r1] [l2 r2]]
      (and (sem-eq A l1 l2)
           (sem-eq (B l1) r1 r2))
      
      [[:neutral ne1] [:neutral ne2]] (= ne1 ne2)
      _ false)))

(defn type-eq [Γ A B]
  "Check if two types are equal"
  (= (eval Γ A) (eval Γ B)))

(defn term-eq [Γ A t u]
  "Check if two terms are equal at type A"
  (sem-eq (eval Γ A) (eval Γ t) (eval Γ u)))

# ---------------------
# Bidirectional checker (returns semantic type)
# ---------------------
(var infer nil)
(var check nil)

(defn check-univ [Γ A]
  "Check that A is a universe and return its level"
  (let [UA (infer Γ A)]
    (match UA
      [:Type l] l
      _ (errorf "expected a Type, got: %v" UA))))

(set infer
  (fn [Γ t]
    "Infer the type of term t in context Γ (returns semantic type)"
    (match t
      [:var x] 
      (if (string? x)
        (ctx/lookup Γ x)
        (errorf "var must be a string, got: %v" x))
      
      [:type l] (ty/type (+ l 1))
      
      [:lam _] (error "cannot infer type of lambda; requires annotation")
      
      [:app f x]
      (let [fA (infer Γ f)]
        (match fA
          [:Pi A B]
          (do (check Γ x A)
              (B (eval Γ x)))
          _ (errorf "application of non-Pi: %v" fA)))
      
      [:t-pi A B]
      (let [lvlA (check-univ Γ A)
            fresh (gensym)
            A-sem (eval Γ A)
            Γ2 (ctx/add Γ fresh A-sem)
            lvlB (check-univ Γ2 (B fresh))]
        (ty/type (max lvlA lvlB)))
      
      [:t-sigma A B]
      (let [lvlA (check-univ Γ A)
            fresh (gensym)
            A-sem (eval Γ A)
            Γ2 (ctx/add Γ fresh A-sem)
            lvlB (check-univ Γ2 (B fresh))]
        (ty/type (max lvlA lvlB)))
      
      [:fst p]
      (let [pA (infer Γ p)]
        (match pA
          [:Sigma A B] A
          _ (error "fst expects Sigma")))
      
      [:snd p]
      (let [pA (infer Γ p)]
        (match pA
          [:Sigma A B] (B (eval Γ [:fst p]))
          _ (error "snd expects Sigma")))
      
      [:pair _ _]
      (error "cannot infer type of pair; expected Sigma annotation")
      
      _ (errorf "infer: unknown term %v" t))))

(set check
  (fn [Γ t A]
    "Check that term t has type A in context Γ"
    (match t
      [:lam body]
      (match A
        [:Pi dom cod]
        (let [fresh (gensym)
              arg-sem (raise dom (ne/var fresh))]
          (check (ctx/add Γ fresh dom)
                 (body fresh)
                 (cod arg-sem)))
        _ (error "lambda expected Pi type"))
      
      [:pair l r]
      (match A
        [:Sigma A1 B1]
        (do (check Γ l A1)
            (check Γ r (B1 (eval Γ l))))
        _ (error "pair expects Sigma type"))
      
      _
      (let [A1 (infer Γ t)]
        (if (sem-eq (ty/type 100) A A1)
          true
          (errorf "type mismatch: expected %v got %v" A A1))))))

# ---------------------
# Top-level helpers
# ---------------------
(defn check-top [t expected]
  (let [Γ (ctx/empty)]
    (check Γ t expected)
    true))

(defn infer-top [t]
  (let [Γ (ctx/empty)]
    (infer Γ t)))

# Export public API
(def exports
  {:ty/type ty/type
   :ty/pi ty/pi
   :ty/sigma ty/sigma
   :tm/var tm/var
   :tm/lam tm/lam
   :tm/app tm/app
   :tm/type tm/type
   :tm/pi tm/pi
   :tm/sigma tm/sigma
   :tm/pair tm/pair
   :tm/fst tm/fst
   :tm/snd tm/snd
   :ne/var ne/var
   :ne/app ne/app
   :ne/fst ne/fst
   :ne/snd ne/snd
   :nf/neut nf/neut
   :nf/lam nf/lam
   :nf/pi nf/pi
   :nf/sigma nf/sigma
   :nf/type nf/type
   :nf/pair nf/pair
   :eval eval
   :nf nf
   :lower lower
   :raise raise
   :sem-eq sem-eq
   :type-eq type-eq
   :term-eq term-eq
   :check check
   :infer infer
   :check-top check-top
   :infer-top infer-top
   :ctx/empty ctx/empty
   :ctx/add ctx/add
   :ctx/lookup ctx/lookup})
