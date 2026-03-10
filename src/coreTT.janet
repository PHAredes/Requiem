#!/usr/bin/env janet

# Requiem CoreTT
# NbE kernel with HOAS, bidirectional type checking, and J-eliminator

(import ./levels :as lvl)
(import ./meta :as meta)
(import ./checker :as checker)

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
  (def v (h/get Γ (string x)))
  (if (nil? v)
    (errorf "unbound variable '%v' - not found in context.\nAvailable variables: %v" x (map keyword (h/keys Γ)))
    v))

(var print/sem nil)
(var print/ne nil)
(var print/nf nil)
(var print/tm nil)
(var ne/print* nil)
(var nf/print* nil)
(var print/tm* nil)
(var print/name-map nil)
(var print/used-names nil)
(var print/fresh-id 0)
(var goals nil)
(var goals/set-collect! nil)

# NbE: raise / lower
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
                            (fn [fresh]
                              (let [arg (raise A (ne/var fresh))]
                                (lower (ty/type 100) (B arg))))))
      (= tag T/Sigma) (let [[_ A B] sem]
                        (nf/sigma (lower/type A)
                                  (fn [fresh]
                                    (let [arg (raise A (ne/var fresh))]
                                      (lower (ty/type 100) (B arg))))))
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

# Definitional equality
(var sem-eq nil)

(defn- sem-eq/type [ty v1 v2]
  (let [t1 (if (tuple? v1) (get v1 0) 0)
        t2 (if (tuple? v2) (get v2 0) 0)]
    (cond
      (and (= t1 T/Type) (= t2 T/Type))
      (lvl/eq? (get v1 1) (get v2 1))

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

# Evaluator
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
      true (errorf "fst expects a pair value (Σ type), but got: %s"
                   (print/sem v)))))

(defn- eval/snd [Γ p]
  (let [v (eval Γ p)
        tag (if (tuple? v) (get v 0) 0)]
    (cond
      (= tag T/Pair) (get v 2)
      (= tag T/Neutral) [T/Neutral (ne/snd (get v 1))]
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

      true (errorf "J eliminator requires a proof of identity (Id A x y), but got: %s"
                   (print/sem pv)))))

(set eval
     (fn [Γ tm]
       "Evaluate a term in context Γ to a semantic value"
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
         _ (if (function? tm) tm tm))))

(defn eval/session [f]
  "Run a computation in a fresh evaluation session with deep stack"
  (let [fib (fiber/new f :p)]
    (fiber/setmaxstack fib 1000000)
    (resume fib)))

(defn nf [ty tm]
  (eval/session (fn [] (lower ty (eval (ctx/empty) tm)))))

# Bidirectional checker / metas are installed later.
(var infer nil)
(var check nil)
(var subtype nil)


(defn- print/reset-state! []
  (set print/fresh-id 0)
  (set print/name-map @{})
  (set print/used-names @{}))

(defn- print/mark-used! [name]
  (put print/used-names name true)
  name)

(defn- print/used? [name]
  (get print/used-names name))

(defn- print/internal-name? [x]
  (let [s (string x)]
    (and (> (length s) 0)
         (= (s 0) (chr "_")))))

(defn- print/alpha-name [n]
  (let [letters "abcdefghijklmnopqrstuvwxyz"]
    (defn recur [k]
      (let [q (div k 26)
            r (% k 26)
            ch (string/slice letters r (+ r 1))]
        (if (= q 0)
          ch
          (string (recur (- q 1)) ch))))
    (recur n)))

(defn- print/fresh-name []
  (var out nil)
  (while (nil? out)
    (let [candidate (print/alpha-name print/fresh-id)]
      (++ print/fresh-id)
      (when (not (print/used? candidate))
        (set out (print/mark-used! candidate)))))
  out)

(defn- print/disambiguate [preferred]
  (if (not (print/used? preferred))
    (print/mark-used! preferred)
    (do
      (var out nil)
      (var n 1)
      (while (nil? out)
        (let [candidate (string preferred n)]
          (if (print/used? candidate)
            (++ n)
            (set out (print/mark-used! candidate)))))
      out)))

(defn- print/name [x]
  (or (get print/name-map x)
      (let [preferred (string x)
            out (if (print/internal-name? x)
                  (print/fresh-name)
                  (print/disambiguate preferred))]
        (put print/name-map x out)
        out)))

(defn- print/wrap [s]
  (string "(" s ")"))

(defn- print/atomic-nf? [nf]
  (match nf
    [NF/Type _] true
    [NF/Neut [:nvar _]] true
    _ false))

(defn- print/atomic-ne? [ne]
  (match ne
    [:nvar _] true
    _ false))

(defn- print/nf-arg [nf]
  (let [rendered (nf/print* nf)]
    (if (print/atomic-nf? nf) rendered (print/wrap rendered))))

(defn- print/ne-arg [ne]
  (let [rendered (ne/print* ne)]
    (if (print/atomic-ne? ne) rendered (print/wrap rendered))))

(defn- print/atomic-tm? [tm]
  (match tm
    [:var _] true
    [:type _] true
    [:hole _] true
    _ false))

(defn- print/tm-arg [tm]
  (let [rendered (print/tm* tm)]
    (if (print/atomic-tm? tm) rendered (print/wrap rendered))))

(set ne/print* (fn [ne]
  (match ne
    [:nvar x] (print/name x)
    [:napp f x] (string (print/ne-arg f) " " (print/nf-arg x))
    [:nfst p] (string "fst " (print/ne-arg p))
    [:nsnd p] (string "snd " (print/ne-arg p))
    [:nJ A x P d y p]
    (string "J "
            (print/nf-arg A) " "
            (print/nf-arg x) " "
            (print/nf-arg P) " "
            (print/nf-arg d) " "
            (print/nf-arg y) " "
            (print/ne-arg p))
    _ (string/format "%v" ne))))

(set nf/print* (fn [nf]
  (match nf
    [NF/Type l]
    (string "Type" (if (or (int? l) (tuple? l)) (lvl/value l) (string/format "%v" l)))

    [NF/Pi A B]
    (let [x (print/fresh-name)]
      (string "Pi(" x " : " (nf/print* A) "). " (nf/print* (B x))))

    [NF/Sigma A B]
    (let [x (print/fresh-name)]
      (string "Sigma(" x " : " (nf/print* A) "). " (nf/print* (B x))))

    [NF/Id A x y]
    (string "Id " (print/nf-arg A) " " (print/nf-arg x) " " (print/nf-arg y))

    [NF/Refl x]
    (string "refl " (print/nf-arg x))

    [NF/Pair l r]
    (string "(" (nf/print* l) ", " (nf/print* r) ")")

    [NF/Lam body]
    (let [x (print/fresh-name)]
      (string "λ" x ". " (nf/print* (body x))))

    [NF/Neut ne]
    (ne/print* ne)

    _
    (string/format "%v" nf))))

(set print/tm* (fn [tm]
  (match tm
    [:var x]
    (print/name x)

    [:app f x]
    (string (print/tm-arg f) " " (print/tm-arg x))

    [:type l]
    (string "Type" l)

    [:lam body]
    (let [x (print/fresh-name)]
      (string "λ" x ". " (print/tm* (body [:var x]))))

    [:t-pi A B]
    (let [x (print/fresh-name)]
      (string "Pi(" x " : " (print/tm* A) "). " (print/tm* (B [:var x]))))

    [:t-sigma A B]
    (let [x (print/fresh-name)]
      (string "Sigma(" x " : " (print/tm* A) "). " (print/tm* (B [:var x]))))

    [:pair l r]
    (string "(" (print/tm* l) ", " (print/tm* r) ")")

    [:fst p]
    (string "fst " (print/tm-arg p))

    [:snd p]
    (string "snd " (print/tm-arg p))

    [:t-id A x y]
    (string "Id " (print/tm-arg A) " " (print/tm-arg x) " " (print/tm-arg y))

    [:t-refl x]
    (string "refl " (print/tm-arg x))

    [:t-J A x P d y p]
    (string "J "
            (print/tm-arg A) " "
            (print/tm-arg x) " "
            (print/tm-arg P) " "
            (print/tm-arg d) " "
            (print/tm-arg y) " "
            (print/tm-arg p))

    [:hole name]
    (if name (string "?" name) "?")

    _
    (string/format "%v" tm))))

(set print/ne (fn [ne]
  (let [saved-id print/fresh-id
        saved-map print/name-map
        saved-used print/used-names]
    (print/reset-state!)
    (def out (ne/print* ne))
    (set print/fresh-id saved-id)
    (set print/name-map saved-map)
    (set print/used-names saved-used)
    out)))

(set print/nf (fn [nf]
  (let [saved-id print/fresh-id
        saved-map print/name-map
        saved-used print/used-names]
    (print/reset-state!)
    (def out (nf/print* nf))
    (set print/fresh-id saved-id)
    (set print/name-map saved-map)
    (set print/used-names saved-used)
    out)))

(set print/tm (fn [tm]
  (let [saved-id print/fresh-id
        saved-map print/name-map
        saved-used print/used-names]
    (print/reset-state!)
    (def out (print/tm* tm))
    (set print/fresh-id saved-id)
    (set print/name-map saved-map)
    (set print/used-names saved-used)
    out)))

(set print/sem
     (fn [sem]
       (let [tag (if (tuple? sem) (get sem 0) 0)]
         (cond
           (= tag T/Neutral) (print/ne (get sem 1))
           (= tag T/Type) (print/nf (lower/type sem))
           (= tag T/Pi) (print/nf (lower/type sem))
           (= tag T/Sigma) (print/nf (lower/type sem))
           (= tag T/Id) (print/nf (lower/type sem))
           (= tag T/Refl) (string "refl " (print/sem (get sem 1)))
           (= tag T/Pair) (string "(" (print/sem (get sem 1)) ", " (print/sem (get sem 2)) ")")
           true (string/format "%v" sem)))))

(let [meta-state (meta/make {:ty/type ty/type
                             :lower lower
                             :ctx/lookup ctx/lookup
                             :print/sem print/sem})
      checker-state (checker/make {:T/Type T/Type
                                   :T/Pi T/Pi
                                   :T/Sigma T/Sigma
                                   :ty/type ty/type
                                   :ty/id ty/id
                                   :lvl/<= lvl/leq
                                   :lvl/max (fn [l1 l2] (max (lvl/value l1) (lvl/value l2)))
                                   :lvl/succ (fn [l] (inc (lvl/value l)))
                                   :sem-eq sem-eq
                                   :eval eval
                                   :raise raise
                                   :lower lower
                                   :ctx/empty ctx/empty
                                   :ctx/add ctx/add
                                   :ctx/lookup ctx/lookup
                                   :ne/var ne/var
                                   :print/sem print/sem
                                   :print/tm print/tm
                                   :meta meta-state})]
  (set goals (meta-state :goals))
  (set goals/set-collect! (meta-state :set-collect!))
  (set infer (checker-state :infer))
  (set check (checker-state :check))
  (set subtype (checker-state :subtype)))

(defn type-eq [Γ A B]
  (= (eval Γ A) (eval Γ B)))

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
   :goals/set-collect! goals/set-collect!})
