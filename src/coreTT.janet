#!/usr/bin/env janet

# Requiem CoreTT
# NbE kernel with HOAS, bidirectional type checking, and J-eliminator

(import ./levels :as lvl)
(import ./meta :as meta)
(import ./checker :as checker)
(import ./print :as printer)

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

# ---------------------
# Type constructors
# ---------------------
(defn ty/type [lvl*] [T/Type (lvl/value lvl*)])
(defn ty/pi [A B] [T/Pi A B])
(defn ty/sigma [A B] [T/Sigma A B])
(defn ty/id [A x y] [T/Id A x y])
(defn ty/pair [v1 v2] [T/Pair v1 v2])

(def T/Type0 [T/Type 0])
(def T/Type100 (ty/type 100))
(def T/TypeOmega T/Type100)

# Term constructors
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
(defn tm/hole [name] [:hole name])

# Neutrals / normal forms
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

# Context
(import /build/hamt :as h)

# Simple context operations - no cache (direct HAMT is faster)
# Keys are converted to strings for HAMT compatibility
(defn ctx/empty []
  (h/new))

(defn ctx/add [Γ x A]
  (h/put Γ (string x) A))

(defn ctx/lookup [Γ x]
  (let [v (h/get Γ (string x))]
    (if (nil? v)
      (errorf "unbound variable '%v' - not found in context.\nAvailable variables: %v" x (map keyword (h/keys Γ)))
      v)))

# NbE: raise / lower
(var raise nil)
(var lower nil)
(var infer nil)
(var eval nil)
(var sem-eq nil)

(defn- tag-of [x]
  (if (tuple? x) (get x 0) 0))

(defn- sem/value? [x]
  (let [tag (tag-of x)]
    (or (function? x)
        (= tag T/Type)
        (= tag T/Pi)
        (= tag T/Sigma)
        (= tag T/Id)
        (= tag T/Refl)
        (= tag T/Neutral)
        (= tag T/Pair))))

(defn- sem/neutral [ne]
  [T/Neutral ne])

(defn- named-neutral [A fresh]
  (raise A (ne/var fresh)))

(defn- with-fresh-neutral [A f]
  (let [fresh (gensym)
        arg-sem (named-neutral A fresh)]
    (f fresh arg-sem)))

(defn- sem/apply [f-ty f-sem arg-sem]
  (let [tag (tag-of f-ty)]
    (if (= tag T/Pi)
      (let [[_ A B] f-ty
            stag (tag-of f-sem)]
        (cond
          (= stag T/Neutral) (raise (B arg-sem) (ne/app (get f-sem 1) (lower A arg-sem)))
          (function? f-sem) (f-sem arg-sem)
          true (errorf "expected function semantics, got: %v" f-sem)))
      (errorf "expected Pi type for semantic application, got: %v" f-ty))))

(defn- j-motive-type [A x]
  (ty/pi A (fn [y] (ty/pi (ty/id A x y) (fn [_] T/Type100)))))

(defn- sem/normalize [x]
  (if (sem/value? x) x (eval (ctx/empty) x)))

(defn- j-motive-store [P]
  (if (function? P)
    [:motive/hoas P]
    [:motive/sem P]))

(defn- j-motive-result-raw [A x P y p]
  (match P
    [:motive/hoas f] (f y p)
    [:motive/sem f]
    (let [P-ty (j-motive-type A x)
          Py-ty ((get P-ty 2) y)
          Py (sem/apply P-ty f y)
          result (sem/apply Py-ty Py p)]
      result)
    _ (errorf "unknown stored J motive: %v" P)))

(defn- j-motive-result [A x P y p]
  (sem/normalize (j-motive-result-raw A x P y p)))

(defn- j-motive-result-eq [A x P1 P2 y p]
  (sem-eq T/TypeOmega
          (j-motive-result A x P1 y p)
          (j-motive-result A x P2 y p)))

(defn- j-motive-eq [A x P1 P2]
  (with-fresh-neutral A
    (fn [_ y-sem]
      (let [id-ty (ty/id A x y-sem)]
        (with-fresh-neutral id-ty
          (fn [_ p-sem]
            (j-motive-result-eq A x P1 P2 y-sem p-sem)))))))

(defn- ne-eq/J [ne1 ne2]
  (let [[_ A1 x1 P1 d1 y1 p1] ne1
        [_ A2 x2 P2 d2 y2 p2] ne2
        refl1 [T/Refl x1]
        refl2 [T/Refl x2]
        dA1 (j-motive-result A1 x1 P1 x1 refl1)
        dA2 (j-motive-result A2 x2 P2 x2 refl2)]
    (and (sem-eq T/TypeOmega A1 A2)
         (sem-eq A1 x1 x2)
         (j-motive-eq A1 x1 P1 P2)
         (sem-eq T/TypeOmega dA1 dA2)
         (sem-eq dA1 d1 d2)
         (sem-eq A1 y1 y2)
         (sem-eq (ty/id A1 x1 y1) p1 p2))))

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
       (let [tag (tag-of ty)]
         (cond
            (= tag T/Pi)
            (let [[_ A B] ty] (raise/pi A B ne))
            (= tag T/Sigma)
            (let [[_ A B] ty] (raise/sigma A B ne))
            true (sem/neutral ne)))))

(defn- lower/type [sem]
  (let [tag (tag-of sem)]
    (cond
      (= tag T/Neutral) (nf/neut (get sem 1))
      (= tag T/Type) (nf/type (get sem 1))
      (= tag T/Pi) (let [[_ A B] sem]
                     (nf/pi (lower/type A)
                             (fn [fresh]
                              (let [arg (named-neutral A fresh)]
                                (lower T/Type100 (B arg))))))
      (= tag T/Sigma) (let [[_ A B] sem]
                        (nf/sigma (lower/type A)
                                   (fn [fresh]
                                    (let [arg (named-neutral A fresh)]
                                       (lower T/Type100 (B arg))))))
      (= tag T/Id) (let [[_ A x y] sem]
                     (nf/id (lower/type A) (lower A x) (lower A y)))
      true sem)))

(defn- lower/pi [A B sem]
  (let [stag (tag-of sem)]
    (if (= stag T/Neutral)
      (let [ne (get sem 1)]
        (nf/lam
          (fn [fresh]
            (let [arg-sem (named-neutral A fresh)]
              (lower (B arg-sem)
                     (raise (B arg-sem) (ne/app ne (lower A arg-sem))))))))
      (nf/lam
        (fn [fresh]
          (let [arg-sem (named-neutral A fresh)]
            (lower (B arg-sem) (sem arg-sem))))))))

(defn- lower/sigma [A B sem]
  (let [stag (tag-of sem)]
    (if (= stag T/Neutral)
      (let [ne (get sem 1)
            v1 (raise A (ne/fst ne))
            v2 (raise (B v1) (ne/snd ne))]
        (nf/pair (lower A v1) (lower (B v1) v2)))
      (let [[_ v1 v2] sem]
        (nf/pair (lower A v1) (lower (B v1) v2))))))

(defn- lower/id [ty sem]
  (let [stag (tag-of sem)]
    (cond
      (= stag T/Refl) (nf/refl (lower (get ty 1) (get sem 1)))
      (= stag T/Neutral) (nf/neut (get sem 1))
      true sem)))

(defn- lower/neutral [sem]
  (let [stag (tag-of sem)]
    (if (= stag T/Neutral)
      (nf/neut (get sem 1))
      sem)))

(set lower
     (fn [ty sem]
       (let [tag (tag-of ty)]
         (cond
            (= tag T/Type) (lower/type sem)
            (= tag T/Pi) (let [[_ A B] ty] (lower/pi A B sem))
           (= tag T/Sigma) (let [[_ A B] ty] (lower/sigma A B sem))
           (= tag T/Id) (lower/id ty sem)
           (= tag T/Neutral) (lower/neutral sem)
           true sem))))

(def pp
  (printer/make {:T/Type T/Type
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
                 :lower lower
                 :lvl/value lvl/value}))

(def print/sem (pp :print/sem))
(def print/ne (pp :print/ne))
(def print/nf (pp :print/nf))
(def print/tm (pp :print/tm))

# Structural equality for NbE artifacts
(var nf-eq nil)
(var ne-eq nil)

(set nf-eq
     (fn [v1 v2]
       (cond
         (= v1 v2) true
         (not (and (tuple? v1) (tuple? v2))) (= v1 v2)
         (not= (get v1 0) (get v2 0)) false
         (= (get v1 0) NF/Neut) (ne-eq (get v1 1) (get v2 1))
         (= (get v1 0) NF/Type) (= (get v1 1) (get v2 1))
         (= (get v1 0) NF/Lam)
         (let [fresh (gensym)
               b1 (get v1 1)
               b2 (get v2 1)]
           (nf-eq (b1 fresh) (b2 fresh)))
         (= (get v1 0) NF/Pi)
         (let [fresh (gensym)
               a1 (get v1 1)
               a2 (get v2 1)
               b1 (get v1 2)
               b2 (get v2 2)]
           (and (nf-eq a1 a2)
                (nf-eq (b1 fresh) (b2 fresh))))
         (= (get v1 0) NF/Sigma)
         (let [fresh (gensym)
               a1 (get v1 1)
               a2 (get v2 1)
               b1 (get v1 2)
               b2 (get v2 2)]
           (and (nf-eq a1 a2)
                (nf-eq (b1 fresh) (b2 fresh))))
         (= (get v1 0) NF/Pair)
         (and (nf-eq (get v1 1) (get v2 1))
              (nf-eq (get v1 2) (get v2 2)))
         (= (get v1 0) NF/Id)
         (and (nf-eq (get v1 1) (get v2 1))
              (nf-eq (get v1 2) (get v2 2))
              (nf-eq (get v1 3) (get v2 3)))
         (= (get v1 0) NF/Refl)
         (nf-eq (get v1 1) (get v2 1))
         true false)))

(set ne-eq
     (fn [ne1 ne2]
       (cond
         (= ne1 ne2) true
         (not (and (tuple? ne1) (tuple? ne2))) (= ne1 ne2)
         (not= (get ne1 0) (get ne2 0)) false
         (= (get ne1 0) :nvar) (= (get ne1 1) (get ne2 1))
         (= (get ne1 0) :napp)
         (and (ne-eq (get ne1 1) (get ne2 1))
              (nf-eq (get ne1 2) (get ne2 2)))
         (or (= (get ne1 0) :nfst) (= (get ne1 0) :nsnd))
         (ne-eq (get ne1 1) (get ne2 1))
         (= (get ne1 0) :nJ)
         (ne-eq/J ne1 ne2)
         true (= ne1 ne2))))

# Definitional equality

(defn- sem-eq/type [ty v1 v2]
  (let [t1 (tag-of v1)
        t2 (tag-of v2)]
    (cond
      (and (= t1 T/Type) (= t2 T/Type))
      (lvl/eq? (get v1 1) (get v2 1))

      (and (= t1 T/Pi) (= t2 T/Pi))
      (let [[_ A1 B1] v1 [_ A2 B2] v2]
        (and (sem-eq ty A1 A2)
             (with-fresh-neutral A1
               (fn [_ arg-sem]
                 (sem-eq ty (B1 arg-sem) (B2 arg-sem))))))

      (and (= t1 T/Sigma) (= t2 T/Sigma))
      (let [[_ A1 B1] v1 [_ A2 B2] v2]
        (and (sem-eq ty A1 A2)
             (with-fresh-neutral A1
               (fn [_ arg-sem]
                 (sem-eq ty (B1 arg-sem) (B2 arg-sem))))))

      (and (= t1 T/Id) (= t2 T/Id))
      (let [[_ A1 x1 y1] v1 [_ A2 x2 y2] v2]
        (and (sem-eq ty A1 A2) (sem-eq A1 x1 x2) (sem-eq A1 y1 y2)))

      (and (= t1 T/Neutral) (= t2 T/Neutral))
      (ne-eq (get v1 1) (get v2 1))

      true (= v1 v2))))

(defn- sem-eq/pi [A B v1 v2]
  (let [t1 (tag-of v1)
        t2 (tag-of v2)]
    (cond
      (and (= t1 T/Neutral) (= t2 T/Neutral))
      (with-fresh-neutral A
        (fn [_ arg-sem]
          (sem-eq (B arg-sem)
                  (raise (B arg-sem) (ne/app (get v1 1) (lower A arg-sem)))
                  (raise (B arg-sem) (ne/app (get v2 1) (lower A arg-sem))))))

      (= t1 T/Neutral)
      (with-fresh-neutral A
        (fn [_ arg-sem]
          (sem-eq (B arg-sem)
                  (raise (B arg-sem) (ne/app (get v1 1) (lower A arg-sem)))
                  (v2 arg-sem))))

      (= t2 T/Neutral)
      (with-fresh-neutral A
        (fn [_ arg-sem]
          (sem-eq (B arg-sem)
                  (v1 arg-sem)
                  (raise (B arg-sem) (ne/app (get v2 1) (lower A arg-sem))))))

      true
      (with-fresh-neutral A
        (fn [_ arg-sem]
          (sem-eq (B arg-sem) (v1 arg-sem) (v2 arg-sem)))))))

(defn- sem-eq/sigma [A B v1 v2]
  (let [t1 (tag-of v1)
        t2 (tag-of v2)]
    (cond
      (and (= t1 T/Neutral) (= t2 T/Neutral))
      (let [ne1 (get v1 1)
            ne2 (get v2 1)
            p1-fst (sem/neutral (ne/fst ne1))
            p2-fst (sem/neutral (ne/fst ne2))
            p1-snd (sem/neutral (ne/snd ne1))
            p2-snd (sem/neutral (ne/snd ne2))]
        (and (sem-eq A p1-fst p2-fst)
             (sem-eq (B p1-fst) p1-snd p2-snd)))

      (= t1 T/Neutral)
      (let [[_ l2 r2] v2
             ne1 (get v1 1)
             p1-fst (sem/neutral (ne/fst ne1))
             p1-snd (sem/neutral (ne/snd ne1))]
        (and (sem-eq A p1-fst l2)
             (sem-eq (B p1-fst) p1-snd r2)))

      (= t2 T/Neutral)
      (let [[_ l1 r1] v1
            ne2 (get v2 1)
            p2-fst (sem/neutral (ne/fst ne2))
            p2-snd (sem/neutral (ne/snd ne2))]
        (and (sem-eq A l1 p2-fst)
             (sem-eq (B l1) r1 p2-snd)))

      true
      (let [[_ l1 r1] v1 [_ l2 r2] v2]
        (and (sem-eq A l1 l2)
             (sem-eq (B l1) r1 r2))))))

(defn- sem-eq/id [A v1 v2]
  (let [t1 (tag-of v1)
        t2 (tag-of v2)]
    (cond
      (and (= t1 T/Refl) (= t2 T/Refl))
      (sem-eq A (get v1 1) (get v2 1))

      (and (= t1 T/Neutral) (= t2 T/Neutral))
      (ne-eq (get v1 1) (get v2 1))

      true false)))

(set sem-eq
     (fn [ty v1 v2]
        "Check if two semantic values are equal at given type (with eta)"
       (if (= v1 v2)
         true
         (let [tag (tag-of ty)]
           (cond
             (= tag T/Type) (sem-eq/type ty v1 v2)
             (= tag T/Pi) (let [[_ A B] ty] (sem-eq/pi A B v1 v2))
             (= tag T/Sigma) (let [[_ A B] ty] (sem-eq/sigma A B v1 v2))
             (= tag T/Id) (let [[_ A _ _] ty] (sem-eq/id A v1 v2))
             true false)))))

(defn- eval/var [Γ x]
  (if (or (string? x) (symbol? x))
    [T/Neutral (ne/var x)]
    x))

(defn- eval/lam [Γ body]
  (fn [x] (eval Γ (body x))))

(defn- eval/app [Γ f x]
  (let [fv (eval Γ f)
         xv (eval Γ x)
         tag (tag-of fv)]
      (if (= tag T/Neutral)
        (let [fA (infer Γ f)
              ftag (tag-of fA)]
          (if (= ftag T/Pi)
            (let [[_ A _] fA]
              (sem/neutral (ne/app (get fv 1) (lower A xv))))
            (errorf "cannot apply neutral term with non-function type: %s"
                    (print/sem fA))))
        (fv xv))))

(defn- eval/t-pi [Γ A B]
  (ty/pi (eval Γ A) (fn [x] (eval Γ (B x)))))

(defn- eval/t-sigma [Γ A B]
  (ty/sigma (eval Γ A) (fn [x] (eval Γ (B x)))))

(defn- eval/pair [Γ a b]
  [T/Pair (eval Γ a) (eval Γ b)])

(defn- eval/fst [Γ p]
  (let [v (eval Γ p)
        tag (tag-of v)]
    (cond
      (= tag T/Pair) (get v 1)
      (= tag T/Neutral) (sem/neutral (ne/fst (get v 1)))
      true (errorf "fst expects a pair value (Σ type), but got: %s"
                   (print/sem v)))))

(defn- eval/snd [Γ p]
  (let [v (eval Γ p)
        tag (tag-of v)]
    (cond
      (= tag T/Pair) (get v 2)
      (= tag T/Neutral) (sem/neutral (ne/snd (get v 1)))
      true (errorf "snd expects a pair value (Σ type), but got: %s"
                   (print/sem v)))))

(defn- eval/t-id [Γ A x y]
  (ty/id (eval Γ A) (eval Γ x) (eval Γ y)))

(defn- eval/t-refl [Γ x]
  [T/Refl (eval Γ x)])

(defn- eval/t-J [Γ A x P d y p]
  (let [pv (eval Γ p)
        Av (eval Γ A)
        xv (eval Γ x)
        Pv (j-motive-store (eval Γ P))
        dv (eval Γ d)
        yv (eval Γ y)
        tag (tag-of pv)]
    (cond
      (= tag T/Refl)
      (let [zv (get pv 1)]
        (if (sem-eq Av zv xv) dv
          (sem/neutral (ne/J Av xv Pv dv yv pv))))

      (= tag T/Neutral)
      (sem/neutral (ne/J Av xv Pv dv yv pv))

      true (errorf "J eliminator requires a proof of identity (Id A x y), but got: %s"
                   (print/sem pv)))))

(set eval
     (fn [Γ tm]
        "Evaluate a term in context Γ to a semantic value"
        (if (sem/value? tm)
          tm
          (match tm
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
            _ tm))))

(defn eval/session [f]
  "Run a computation in a fresh evaluation session with deep stack"
  (let [fib (fiber/new f :p)]
    (fiber/setmaxstack fib 1000000)
    (resume fib)))

(defn nf [ty tm]
  (eval/session (fn [] (lower ty (eval (ctx/empty) tm)))))

# Bidirectional checker / metas are installed later.
(def meta-state
  (meta/make {:ty/type ty/type
              :lower lower
              :ctx/lookup ctx/lookup
              :goal-ty T/Type100
              :goal-term (tm/type 100)
              :print/sem print/sem
              :sem-eq sem-eq}))

(def checker-state
  (checker/make {:T/Type T/Type
                 :T/Pi T/Pi
                 :T/Sigma T/Sigma
                 :T/Refl T/Refl
                 :T/Pair T/Pair
                 :T/Neutral T/Neutral
                 :ty/type ty/type
                 :ty/pi ty/pi
                 :eq-type T/Type100
                 :ty/id ty/id
                 :lvl/<= lvl/<=
                 :lvl/max lvl/max
                 :lvl/succ lvl/succ
                 :sem-eq sem-eq
                 :eval eval
                 :lower lower
                 :raise raise
                 :ctx/add ctx/add
                 :ctx/lookup ctx/lookup
                 :ne/app ne/app
                 :ne/var ne/var
                 :ne/fst ne/fst
                 :print/sem print/sem
                 :print/tm print/tm
                 :meta meta-state}))

(def goals (meta-state :goals))
(def goals/set-collect! (meta-state :set-collect!))
(def goals/collect? (meta-state :collect?))
(set infer (checker-state :infer))
(def check (checker-state :check))
(def subtype (checker-state :subtype))

(defn type-eq [Γ A B]
  (sem-eq T/Type100 (eval Γ A) (eval Γ B)))

(defn term-eq [Γ A t u]
  (or (= t u)
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
   :tm/hole tm/hole
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
   :subtype subtype
   :infer infer
   :check-top check-top
   :infer-top infer-top
   :ctx/empty ctx/empty
   :ctx/add ctx/add
   :ctx/lookup ctx/lookup
   :eval/session eval/session
   :goals goals
   :goals/set-collect! goals/set-collect!
   :goals/collect? goals/collect?})
