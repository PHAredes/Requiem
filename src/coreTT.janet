#!/usr/bin/env janet


# Requiem CoreTT
# NbE kernel with HOAS, bidirectional type checking, and J-eliminator
# ---------------------
# Semantic Domain
# ---------------------
# Tags
(def T/Type 0x01)
(def T/Pi 0x02)
(def T/Sigma 0x04)
(def T/Id 0x08)
(def T/Refl 0x10)
(def T/Neutral 0x20)
(def T/Pair 0x40)

# Normal Form Tags
(def NF/Neut 0x100)
(def NF/Lam 0x200)
(def NF/Pi 0x400)
(def NF/Sigma 0x800)
(def NF/Type 0x1000)
(def NF/Pair 0x2000)
(def NF/Id 0x4000)
(def NF/Refl 0x8000)

# Semantic values:
#   [T/Type l]           - universes
#   function            - Pi types (HOAS)
#   [v1 v2]             - Sigma types (pairs)
#   [T/Id A x y]        - Identity type
#   [T/Refl x]          - Reflexivity proof
#   [T/Neutral ne]      - stuck terms

# Normal forms:
#   [NF/Lam body]        - lambda abstraction
#   [NF/Pair l r]        - pair
#   [NF/Type l]          - type universe
#   [NF/Pi A B]          - Pi type
#   [NF/Sigma A B]       - Sigma type
#   [NF/Id A x y]        - Identity type
#   [NF/Refl x]          - Reflexivity
#   [NF/Neut ne]         - neutral term

# Neutral terms:
#   [:nvar x]           - variable
#   [:napp f x]         - application
#   [:nfst p]           - first projection
#   [:nsnd p]           - second projection
#   [:nJ A x P d y p]   - J eliminator (stuck)
# (Keywords kept for AST readability)

# ---------------------
# Type constructors
# ---------------------
(defn ty/type [lvl] [T/Type lvl])
(defn ty/pi [A B] [T/Pi A B])
(defn ty/sigma [A B] [T/Sigma A B])
(defn ty/id [A x y] [T/Id A x y])
(defn ty/pair [v1 v2] [T/Pair v1 v2])

# ---------------------
# Term constructors (HOAS syntax) - Unchanged (AST)
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

(defn nf/neut [ne] [NF/Neut ne])
(defn nf/lam [body] [NF/Lam body])
(defn nf/pi [A B] [NF/Pi A B])
(defn nf/sigma [A B] [NF/Sigma A B])
(defn nf/type [l] [NF/Type l])
(defn nf/pair [l r] [NF/Pair l r])
(defn nf/id [A x y] [NF/Id A x y])
(defn nf/refl [x] [NF/Refl x])

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

(defn- raise/pi [A B ne]
  (fn [x]
    (let [nfx (lower A x)]
      (raise (B x) (ne/app ne nfx)))))

(defn- raise/sigma [A B ne]
  (let [v1 (raise A (ne/fst ne))
        v2 (raise (B v1) (ne/snd ne))]
    [T/Pair v1 v2]))

(set raise
     (fn [ty ne]
       (let [tag (if (tuple? ty) (get ty 0) 0)]
         (cond
           (= tag T/Pi)
           (let [[_ A B] ty] (raise/pi A B ne))
           (= tag T/Sigma)
           (let [[_ A B] ty] (raise/sigma A B ne))
           true [T/Neutral ne]))))

(defn- lower/type [sem]
  (let [tag (if (tuple? sem) (get sem 0) 0)]
    (cond
      (= tag T/Neutral) (nf/neut (get sem 1))
      (= tag T/Type) (nf/type (get sem 1))
      (= tag T/Pi) (let [[_ A B] sem]
                     (nf/pi (lower/type A)
                            (let [fresh (gensym)
                                  arg (raise A (ne/var fresh))]
                              (lower (ty/type 100) (B arg))))) # Use a high-level universe for lower/type recursion
      (= tag T/Sigma) (let [[_ A B] sem]
                        (nf/sigma (lower/type A)
                                  (let [fresh (gensym)
                                        arg (raise A (ne/var fresh))]
                                    (lower (ty/type 100) (B arg)))))
      (= tag T/Id) (let [[_ A x y] sem]
                     (nf/id (lower/type A) (lower A x) (lower A y)))
      true sem)))

(defn- lower/pi [A B sem]
  (let [stag (if (tuple? sem) (get sem 0) 0)]
    (if (= stag T/Neutral)
      (let [ne (get sem 1)]
        (nf/lam
          (fn [fresh]
            (let [arg-sem (raise A (ne/var fresh))]
              (lower (B arg-sem)
                     (raise (B arg-sem) (ne/app ne (lower A arg-sem))))))))
      (nf/lam
        (fn [fresh]
          (let [arg-sem (raise A (ne/var fresh))]
            (lower (B arg-sem) (sem arg-sem))))))))

(defn- lower/sigma [A B sem]
  (let [stag (if (tuple? sem) (get sem 0) 0)]
    (if (= stag T/Neutral)
      (let [ne (get sem 1)
            v1 (raise A (ne/fst ne))
            v2 (raise (B v1) (ne/snd ne))]
        (nf/pair (lower A v1) (lower (B v1) v2)))
      (let [[_ v1 v2] sem]
        (nf/pair (lower A v1) (lower (B v1) v2))))))

(defn- lower/id [ty sem]
  (let [stag (if (tuple? sem) (get sem 0) 0)]
    (cond
      (= stag T/Refl) (nf/refl (lower (get ty 1) (get sem 1)))
      (= stag T/Neutral) (nf/neut (get sem 1))
      true sem)))

(defn- lower/neutral [sem]
  (let [stag (if (tuple? sem) (get sem 0) 0)]
    (if (= stag T/Neutral)
      (nf/neut (get sem 1))
      sem)))

(set lower
     (fn [ty sem]
       (let [tag (if (tuple? ty) (get ty 0) 0)]
         (cond
           (= tag T/Type) (lower/type sem)
           (= tag T/Pi) (let [[_ A B] ty] (lower/pi A B sem))
           (= tag T/Sigma) (let [[_ A B] ty] (lower/sigma A B sem))
           (= tag T/Id) (lower/id ty sem)
           (= tag T/Neutral) (lower/neutral sem)
           true sem))))

# ---------------------
# Definitional equality with eta
# ---------------------
(var sem-eq nil)

(defn- sem-eq/type [ty v1 v2]
  (let [t1 (if (tuple? v1) (get v1 0) 0)
        t2 (if (tuple? v2) (get v2 0) 0)]
    (cond
      (and (= t1 T/Pi) (= t2 T/Pi))
      (let [[_ A1 B1] v1 [_ A2 B2] v2]
        (and (sem-eq ty A1 A2)
             (let [fresh (gensym)
                   arg-sem (raise A1 (ne/var fresh))]
               (sem-eq ty (B1 arg-sem) (B2 arg-sem)))))

      (and (= t1 T/Sigma) (= t2 T/Sigma))
      (let [[_ A1 B1] v1 [_ A2 B2] v2]
        (and (sem-eq ty A1 A2)
             (let [fresh (gensym)
                   arg-sem (raise A1 (ne/var fresh))]
               (sem-eq ty (B1 arg-sem) (B2 arg-sem)))))

      (and (= t1 T/Id) (= t2 T/Id))
      (let [[_ A1 x1 y1] v1 [_ A2 x2 y2] v2]
        (and (sem-eq ty A1 A2) (sem-eq A1 x1 x2) (sem-eq A1 y1 y2)))

      true (= v1 v2))))

(defn- sem-eq/pi [A B v1 v2]
  (let [fresh (gensym)
        arg-sem (raise A (ne/var fresh))
        t1 (if (tuple? v1) (get v1 0) 0)
        t2 (if (tuple? v2) (get v2 0) 0)]
    (cond
      (and (= t1 T/Neutral) (= t2 T/Neutral))
      (= (get v1 1) (get v2 1))

      (= t1 T/Neutral)
      (sem-eq (B arg-sem)
              (raise (B arg-sem) (ne/app (get v1 1) (lower A arg-sem)))
              (v2 arg-sem))

      (= t2 T/Neutral)
      (sem-eq (B arg-sem)
              (v1 arg-sem)
              (raise (B arg-sem) (ne/app (get v2 1) (lower A arg-sem))))

      true
      (sem-eq (B arg-sem) (v1 arg-sem) (v2 arg-sem)))))

(defn- sem-eq/sigma [A B v1 v2]
  (let [t1 (if (tuple? v1) (get v1 0) 0)
        t2 (if (tuple? v2) (get v2 0) 0)]
    (cond
      (and (= t1 T/Neutral) (= t2 T/Neutral))
      (= (get v1 1) (get v2 1))

      (= t1 T/Neutral)
      (let [[_ l2 r2] v2
            ne1 (get v1 1)
            p1-fst [T/Neutral (ne/fst ne1)]
            p1-snd [T/Neutral (ne/snd ne1)]]
        (and (sem-eq A p1-fst l2)
             (sem-eq (B p1-fst) p1-snd r2)))

      (= t2 T/Neutral)
      (let [[_ l1 r1] v1
            ne2 (get v2 1)
            p2-fst [T/Neutral (ne/fst ne2)]
            p2-snd [T/Neutral (ne/snd ne2)]]
        (and (sem-eq A l1 p2-fst)
             (sem-eq (B l1) r1 p2-snd)))

      true
      (let [[_ l1 r1] v1 [_ l2 r2] v2]
        (and (sem-eq A l1 l2)
             (sem-eq (B l1) r1 r2))))))

(defn- sem-eq/id [A x y v1 v2]
  (let [t1 (if (tuple? v1) (get v1 0) 0)
        t2 (if (tuple? v2) (get v2 0) 0)]
    (cond
      (and (= t1 T/Refl) (= t2 T/Refl))
      (sem-eq A (get v1 1) (get v2 1))

      (and (= t1 T/Neutral) (= t2 T/Neutral))
      (= (get v1 1) (get v2 1))

      true false)))

(set sem-eq
     (fn [ty v1 v2]
       "Check if two semantic values are equal at given type (with eta)"
       (let [tag (if (tuple? ty) (get ty 0) 0)]
         (cond
           (= tag T/Type) (sem-eq/type ty v1 v2)
           (= tag T/Pi) (let [[_ A B] ty] (sem-eq/pi A B v1 v2))
           (= tag T/Sigma) (let [[_ A B] ty] (sem-eq/sigma A B v1 v2))
           (= tag T/Id) (let [[_ A x y] ty] (sem-eq/id A x y v1 v2))
           true (= v1 v2)))))

# ---------------------
# Evaluator (returns semantic values)
# ---------------------
(var eval nil)

(defn- eval/var [Γ x]
  (if (or (string? x) (symbol? x))
    [T/Neutral (ne/var x)]
    x))

(defn- eval/lam [Γ body]
  (fn [x] (eval Γ (body x))))

(defn- eval/app [Γ f x]
  (let [fv (eval Γ f)
        xv (eval Γ x)]
    (let [tag (if (tuple? fv) (get fv 0) 0)]
      (if (= tag T/Neutral)
        [T/Neutral (ne/app (get fv 1) (lower [T/Type 0] xv))]
        (fv xv)))))

(defn- eval/t-pi [Γ A B]
  (ty/pi (eval Γ A) (fn [x] (eval Γ (B x)))))

(defn- eval/t-sigma [Γ A B]
  (ty/sigma (eval Γ A) (fn [x] (eval Γ (B x)))))

(defn- eval/pair [Γ a b]
  [T/Pair (eval Γ a) (eval Γ b)])

(defn- eval/fst [Γ p]
  (let [v (eval Γ p)
        tag (if (tuple? v) (get v 0) 0)]
    (cond
      (= tag T/Pair) (get v 1)
      (= tag T/Neutral) [T/Neutral (ne/fst (get v 1))]
      true (error "fst expects pair"))))

(defn- eval/snd [Γ p]
  (let [v (eval Γ p)
        tag (if (tuple? v) (get v 0) 0)]
    (cond
      (= tag T/Pair) (get v 2)
      (= tag T/Neutral) [T/Neutral (ne/snd (get v 1))]
      true (error "snd expects pair"))))

(defn- eval/t-id [Γ A x y]
  (ty/id (eval Γ A) (eval Γ x) (eval Γ y)))

(defn- eval/t-refl [Γ x]
  [T/Refl (eval Γ x)])

(defn- eval/t-J [Γ A x P d y p]
  (let [pv (eval Γ p)
        Av (eval Γ A)
        xv (eval Γ x)
        Pv (eval Γ P)
        dv (eval Γ d)
        yv (eval Γ y)
        tag (if (tuple? pv) (get pv 0) 0)]
    (cond
      (= tag T/Refl)
      (let [zv (get pv 1)]
        (if (sem-eq Av zv xv) dv
          [T/Neutral (ne/J Av xv Pv dv yv pv)]))

      (= tag T/Neutral)
      [T/Neutral (ne/J Av xv Pv dv yv pv)]

      true (errorf "J applied to non-proof: %v" pv))))

(defn- get-eval-cache []
  (if-let [env (fiber/getenv (fiber/current))]
    (get env :eval-cache)))

(defn- eval-impl [Γ tm]
  (match tm
    [:Type l] [T/Type l]
    [:Pi A B] [T/Pi A B]
    [:Sigma A B] [T/Sigma A B]
    [:Id A x y] [T/Id A x y]
    [:refl x] [T/Refl x]
    [:neutral ne] [T/Neutral ne]
    [:var x] (eval/var Γ x)
    [:lam body] (eval/lam Γ body)
    [:app f x] (eval/app Γ f x)
    [:type l] (ty/type l)
    [:t-pi A B] (eval/t-pi Γ A B)
    [:t-sigma A B] (eval/t-sigma Γ A B)
    [:pair a b] (eval/pair Γ a b)
    [:fst p] (eval/fst Γ p)
    [:snd p] (eval/snd Γ p)
    [:t-id A x y] (eval/t-id Γ A x y)
    [:t-refl x] (eval/t-refl Γ x)
    [:t-J A x P d y p] (eval/t-J Γ A x P d y p)
    _ (if (function? tm) tm tm)))

(set eval
     (fn [Γ tm]
       "Evaluate a term in context Γ to a semantic value"
       (if-let [cache (get-eval-cache)]
         (let [k [Γ tm]]
           (if (has-key? cache k)
             (get cache k)
             (let [res (eval-impl Γ tm)]
               (put cache k res)
               res)))
         (eval-impl Γ tm))))

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
# Bidirectional checker
# ---------------------
(var infer nil)
(var check nil)

(defn check-univ [Γ A]
  "Check that A is a universe and return its level"
  (let [UA (infer Γ A)
        tag (if (tuple? UA) (get UA 0) 0)]
    (if (= tag T/Type)
      (get UA 1)
      (errorf "expected a Type, got: %v" UA))))

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
         (let [fA (infer Γ f)
               tag (if (tuple? fA) (get fA 0) 0)]
           (if (= tag T/Pi)
             (let [[_ A B] fA]
               (do (check Γ x A)
                 (B (eval Γ x))))
             (errorf "application of non-Pi: %v" fA)))

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
         (let [pA (infer Γ p)
               tag (if (tuple? pA) (get pA 0) 0)]
           (if (= tag T/Sigma)
             (get pA 1) # A from [T/Sigma A B]
             (error "fst expects Sigma")))

         [:snd p]
         (let [pA (infer Γ p)
               tag (if (tuple? pA) (get pA 0) 0)]
           (if (= tag T/Sigma)
             (let [[_ A B] pA]
               (B (eval Γ [:fst p])))
             (error "snd expects Sigma")))

         [:pair _ _]
         (error "cannot infer type of pair; expected Sigma annotation")

         # Identity type: Id A x y : Type_l where A : Type_l
         [:t-id A x y]
         (let [A-ty (infer Γ A)
               A-sem (eval Γ A)
               tag (if (tuple? A-ty) (get A-ty 0) 0)]
           (if (= tag T/Type)
             (do (check Γ x A-sem)
               (check Γ y A-sem)
               (ty/type (get A-ty 1)))
             (errorf "Id type expects A to be a Type, got: %v" A-ty)))

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
         (let [tag (if (tuple? A) (get A 0) 0)]
           (if (= tag T/Pi)
             (let [[_ dom cod] A
                   fresh (gensym)
                   arg-sem (raise dom (ne/var fresh))]
               (check (ctx/add Γ fresh dom)
                      (body [:var fresh])
                      (cod arg-sem)))
             (error "lambda expected Pi type")))

         [:pair l r]
         (let [tag (if (tuple? A) (get A 0) 0)]
           (if (= tag T/Sigma)
             (let [[_ A1 B1] A]
               (do (check Γ l A1)
                 (check Γ r (B1 (eval Γ l)))))
             (error "pair expects Sigma type")))

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

# Public API
(def exports
  {:T/Type T/Type
   :T/Pi T/Pi
   :T/Sigma T/Sigma
   :T/Id T/Id
   :T/Refl T/Refl
   :T/Neutral T/Neutral
   :T/Pair T/Pair
   :NF/Neut NF/Neut
   :NF/Lam NF/Lam
   :NF/Pi NF/Pi
   :NF/Sigma NF/Sigma
   :NF/Type NF/Type
   :NF/Pair NF/Pair
   :NF/Id NF/Id
   :NF/Refl NF/Refl
   :ty/type ty/type
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
