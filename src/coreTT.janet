#!/usr/bin/env janet

# ================================================================
#                       CORETT (Janet)
#   HOAS kernel with proper semantic domain, NbE with eta-equality,
#   bidirectional type checker, J and ID
# ================================================================
# ---------------------
# Semantic Domain
# ---------------------
# Semantic values:
#   [:Type l]           - universes
#   function            - Pi types (HOAS)
#   [v1 v2]             - Sigma types (pairs)
#   [:Id A x y]         - Identity type
#   [:refl x]           - Reflexivity proof
#   [:neutral ne]       - stuck terms

# Normal forms:
#   [:nlam body]        - lambda abstraction
#   [:npair l r]        - pair
#   [:nType l]          - type universe
#   [:nPi A B]          - Pi type
#   [:nSigma A B]       - Sigma type
#   [:nId A x y]        - Identity type
#   [:nrefl x]          - Reflexivity
#   [:nneut ne]         - neutral term

# Neutral terms:
#   [:nvar x]           - variable
#   [:napp f x]         - application
#   [:nfst p]           - first projection
#   [:nsnd p]           - second projection
#   [:nJ A x P d y p]   - J eliminator (stuck)

# ---------------------
# Type constructors
# ---------------------
(defn ty/type [lvl] [:Type lvl])
(defn ty/pi [A B] [:Pi A B])
(defn ty/sigma [A B] [:Sigma A B])
(defn ty/id [A x y] [:Id A x y])

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
(defn tm/id [A x y] [:t-id A x y])
(defn tm/refl [x] [:t-refl x])
(defn tm/J [A x P d y p] [:t-J A x P d y p])

# ---------------------
# Neutral / normal form constructors
# ---------------------
(defn ne/var [x] [:nvar x])
(defn ne/app [f x] [:napp f x])
(defn ne/fst [p] [:nfst p])
(defn ne/snd [p] [:nsnd p])
(defn ne/J [A x P d y p] [:nJ A x P d y p])

(defn nf/neut [ne] [:nneut ne])
(defn nf/lam [body] [:nlam body])
(defn nf/pi [A B] [:nPi A B])
(defn nf/sigma [A B] [:nSigma A B])
(defn nf/type [l] [:nType l])
(defn nf/pair [l r] [:npair l r])
(defn nf/id [A x y] [:nId A x y])
(defn nf/refl [x] [:nrefl x])

# ---------------------
# Context (HAMT-backed)
# ---------------------
(import /build/hamt :as h)

(defn ctx/empty []
  (h/new))

(defn ctx/add [Γ x A]
  (h/put Γ (string x) A))

(defn ctx/lookup [Γ x]
  (def v (h/get Γ (string x)))
  (if (nil? v)
    (errorf "unbound variable: %v" x)
    v))

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
           [v1 v2])
         [:Id A x y] [:neutral ne]
         [:neutral _] [:neutral ne])))

(set lower
     (fn [ty sem]
       (match ty
         [:Type l]
         (match sem
           [:neutral ne] (nf/neut ne)
           _ sem)

         [:Pi A B]
         (match sem
           [:neutral ne]
           (nf/lam
             (fn [fresh]
               (let [arg-sem (raise A (ne/var fresh))]
                 (lower (B arg-sem)
                        (raise (B arg-sem) (ne/app ne (lower A arg-sem)))))))

           _
           (nf/lam
             (fn [fresh]
               (let [arg-sem (raise A (ne/var fresh))]
                 (lower (B arg-sem) (sem arg-sem))))))

         [:Sigma A B]
         (match sem
           [:neutral ne]
           (let [v1 (raise A (ne/fst ne))
                 v2 (raise (B v1) (ne/snd ne))]
             (nf/pair (lower A v1) (lower (B v1) v2)))

           [v1 v2]
           (nf/pair (lower A v1) (lower (B v1) v2)))

         [:Id A x y]
         (match sem
           [:refl v] (nf/refl (lower A v))
           [:neutral ne] (nf/neut ne)
           _ sem)
         [:neutral _]
         (match sem
           [:neutral ne] (nf/neut ne)
           _ sem))))

# ---------------------
# Definitional equality with eta
# ---------------------
(defn sem-eq [ty v1 v2]
  "Check if two semantic values are equal at given type (with eta)"
  (match ty
    [:Type l]
    (match [v1 v2]
      # Both are Pi types - check structural equality
      [[:Pi A1 B1] [:Pi A2 B2]]
      (and (sem-eq [:Type l] A1 A2)
           (let [fresh (gensym)
                 arg-sem (raise A1 (ne/var fresh))]
             (sem-eq [:Type l] (B1 arg-sem) (B2 arg-sem))))

      # Both are Sigma types
      [[:Sigma A1 B1] [:Sigma A2 B2]]
      (and (sem-eq [:Type l] A1 A2)
           (let [fresh (gensym)
                 arg-sem (raise A1 (ne/var fresh))]
             (sem-eq [:Type l] (B1 arg-sem) (B2 arg-sem))))

      # Both are Id types
      [[:Id A1 x1 y1] [:Id A2 x2 y2]]
      (and (sem-eq [:Type l] A1 A2)
           (sem-eq A1 x1 x2)
           (sem-eq A1 y1 y2))

      # Otherwise structural equality
      _ (= v1 v2))

    [:Pi A B]
    (let [fresh (gensym)
          arg-sem (raise A (ne/var fresh))]
      (match [v1 v2]
        [[:neutral ne1] [:neutral ne2]] (= ne1 ne2)
        [[:neutral ne1] _]
        (sem-eq (B arg-sem)
                (raise (B arg-sem) (ne/app ne1 (lower A arg-sem)))
                (v2 arg-sem))
        [_ [:neutral ne2]]
        (sem-eq (B arg-sem)
                (v1 arg-sem)
                (raise (B arg-sem) (ne/app ne2 (lower A arg-sem))))
        _ (sem-eq (B arg-sem) (v1 arg-sem) (v2 arg-sem))))

    [:Sigma A B]
    (match [v1 v2]
      [[l1 r1] [l2 r2]]
      (and (sem-eq A l1 l2)
           (sem-eq (B l1) r1 r2))

      [[:neutral ne1] [:neutral ne2]] (= ne1 ne2)
      _ false)

    [:Id A x y]
    (match [v1 v2]
      [[:refl a] [:refl b]] (sem-eq A a b)
      [[:neutral ne1] [:neutral ne2]] (= ne1 ne2)
      _ false)))

# ---------------------
# Evaluator (returns semantic values)
# ---------------------
(var eval nil)

(defn- eval/var [Γ x]
  (if (or (string? x) (symbol? x))
    [:neutral (ne/var x)]
    x))

(defn- eval/lam [Γ body]
  (fn [x] (eval Γ (body x))))

(defn- eval/app [Γ f x]
  (let [fv (eval Γ f)
        xv (eval Γ x)]
    (match fv
      [:neutral ne] [:neutral (ne/app ne (lower [:Type 0] xv))]
      _ (fv xv))))

(defn- eval/t-pi [Γ A B]
  (ty/pi (eval Γ A) (fn [x] (eval Γ (B x)))))

(defn- eval/t-sigma [Γ A B]
  (ty/sigma (eval Γ A) (fn [x] (eval Γ (B x)))))

(defn- eval/pair [Γ a b]
  [(eval Γ a) (eval Γ b)])

(defn- eval/fst [Γ p]
  (let [v (eval Γ p)]
    (match v
      [l r] l
      [:neutral ne] [:neutral (ne/fst ne)])))

(defn- eval/snd [Γ p]
  (let [v (eval Γ p)]
    (match v
      [l r] r
      [:neutral ne] [:neutral (ne/snd ne)])))

(defn- eval/t-id [Γ A x y]
  (ty/id (eval Γ A) (eval Γ x) (eval Γ y)))

(defn- eval/t-refl [Γ x]
  [:refl (eval Γ x)])

(defn- eval/t-J [Γ A x P d y p]
  (let [pv (eval Γ p)
        Av (delay (eval Γ A))
        xv (delay (eval Γ x))
        Pv (delay (eval Γ P))
        dv (delay (eval Γ d))
        yv (delay (eval Γ y))]
    (match pv
      # Computation rule: J A x P d x (refl x) ≡ d
      [:refl zv]
      (if (sem-eq (Av) zv (xv)) (dv)
        [:neutral (ne/J (Av) (xv) (Pv) (dv) (yv) pv)])
      [:neutral ne]
      [:neutral (ne/J (Av) (xv) (Pv) (dv) (yv) pv)]
      _ (errorf "J applied to non-proof: %v" pv))))

(defn- get-eval-cache []
  (if-let [env (fiber/getenv (fiber/current))]
    (get env :eval-cache)))

(set eval
     (fn [Γ tm]
       "Evaluate a term in context Γ to a semantic value"
       (if-let [cache (get-eval-cache)]
         (let [k [Γ tm]]
           (if (has-key? cache k)
             (get cache k)
             (let [res (match tm
                         [:Type l] [:Type l]
                         [:Pi A B] [:Pi A B]
                         [:Sigma A B] [:Sigma A B]
                         [:Id A x y] [:Id A x y]
                         [:refl x] [:refl x]
                         [:neutral ne] [:neutral ne]
                         [:var x] (eval/var Γ x)
                         [:lam body] (eval/lam Γ body)
                         [:app f x] (eval/app Γ f x)
                         [:type l] (ty/type l)
                         [:t-pi A B] (eval/t-pi Γ A B)
                         [:t-sigma A B] (eval/t-sigma Γ A B)
                         [:pair a b] (eval/pair Γ a b)
                         [:fst p] (eval/fst Γ p)
                         [:snd p] (eval/snd Γ p)
                         # Identity type
                         [:t-id A x y] (eval/t-id Γ A x y)
                         [:t-refl x] (eval/t-refl Γ x)
                         # J eliminator
                         [:t-J A x P d y p] (eval/t-J Γ A x P d y p)
                         _ (if (function? tm) tm tm))]
               (put cache k res)
               res)))
         # No cache, fall back to standard execution
         (match tm
           [:Type l] [:Type l]
           [:Pi A B] [:Pi A B]
           [:Sigma A B] [:Sigma A B]
           [:Id A x y] [:Id A x y]
           [:refl x] [:refl x]
           [:neutral ne] [:neutral ne]
           [:var x] (eval/var Γ x)
           [:lam body] (eval/lam Γ body)
           [:app f x] (eval/app Γ f x)
           [:type l] (ty/type l)
           [:t-pi A B] (eval/t-pi Γ A B)
           [:t-sigma A B] (eval/t-sigma Γ A B)
           [:pair a b] (eval/pair Γ a b)
           [:fst p] (eval/fst Γ p)
           [:snd p] (eval/snd Γ p)
           # Identity type
           [:t-id A x y] (eval/t-id Γ A x y)
           [:t-refl x] (eval/t-refl Γ x)
           # J eliminator
           [:t-J A x P d y p] (eval/t-J Γ A x P d y p)
           _ (if (function? tm) tm tm)))))

(defn eval/session [f]
  "Run a computation in a fresh evaluation session with memoization and deep stack"
  (let [fib (fiber/new f :p)]
    (fiber/setmaxstack fib 1000000)
    (fiber/setenv fib (table/setproto @{:eval-cache @{}} (fiber/getenv (fiber/current))))
    (let [res (resume fib)]
      (if (= (fiber/status fib) :error)
        (error res)
        res))))

(defn nf [ty tm]
  (eval/session (fn [] (lower ty (eval (ctx/empty) tm)))))

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
         (if (or (string? x) (symbol? x))
           (ctx/lookup Γ x)
           (errorf "var must be a string or symbol, got: %v" x))

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
               lvlB (check-univ Γ2 (B [:var fresh]))]
           (ty/type (max lvlA lvlB)))

         [:t-sigma A B]
         (let [lvlA (check-univ Γ A)
               fresh (gensym)
               A-sem (eval Γ A)
               Γ2 (ctx/add Γ fresh A-sem)
               lvlB (check-univ Γ2 (B [:var fresh]))]
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

         # Identity type: Id A x y : Type_l where A : Type_l
         [:t-id A x y]
         (let [A-ty (infer Γ A)
               A-sem (eval Γ A)]
           (match A-ty
             [:Type l]
             (do (check Γ x A-sem)
               (check Γ y A-sem)
               (ty/type l))
             _ (errorf "Id type expects A to be a Type, got: %v" A-ty)))

         # Reflexivity: refl x : Id A x x
         [:t-refl x]
         (let [A (infer Γ x)
               xv (eval Γ x)]
           (ty/id A xv xv))

         # J eliminator
         [:t-J A x P d y p]
         (let [lvlA (check-univ Γ A)
               A-sem (eval Γ A)]
           (check Γ x A-sem)

           # P : (y : A) → Id A x y → Type_l
           (let [fresh-y (gensym)
                 fresh-p (gensym)
                 xv (eval Γ x)
                 Γ-y (ctx/add Γ fresh-y A-sem)
                 id-ty (ty/id A-sem xv [:var fresh-y])
                 Γ-yp (ctx/add Γ-y fresh-p id-ty)]
             (check-univ Γ-yp (P [:var fresh-y] [:var fresh-p]))

             # d : P x (refl x)
             (let [P-refl (eval Γ (P xv [:refl xv]))]
               (check Γ d P-refl))

             # y : A
             (check Γ y A-sem)
             (let [yv (eval Γ y)]

               # p : Id A x y
               (check Γ p (ty/id A-sem xv yv))

               # Result type: P y p
               (let [pv (eval Γ p)]
                 (eval Γ (P yv pv))))))

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
                    (body [:var fresh])
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
(defn type-eq [Γ A B]
  "Check if two types are equal"
  (= (eval Γ A) (eval Γ B)))

(defn term-eq [Γ A t u]
  "Check if two terms are equal at type A"
  (or
    (= t u)
    (sem-eq (eval Γ A) (eval Γ t) (eval Γ u))))

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
   :ty/id ty/id
   :tm/var tm/var
   :tm/lam tm/lam
   :tm/app tm/app
   :tm/type tm/type
   :tm/pi tm/pi
   :tm/sigma tm/sigma
   :tm/pair tm/pair
   :tm/fst tm/fst
   :tm/snd tm/snd
   :tm/id tm/id
   :tm/refl tm/refl
   :tm/J tm/J
   :ne/var ne/var
   :ne/app ne/app
   :ne/fst ne/fst
   :ne/snd ne/snd
   :ne/J ne/J
   :nf/neut nf/neut
   :nf/lam nf/lam
   :nf/pi nf/pi
   :nf/sigma nf/sigma
   :nf/type nf/type
   :nf/pair nf/pair
   :nf/id nf/id
   :nf/refl nf/refl
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
   :ctx/lookup ctx/lookup
   :eval/session eval/session})
