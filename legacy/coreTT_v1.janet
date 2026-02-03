#!/usr/bin/env janet

# ================================================================
#                       CORETT (Janet) - Legacy V1 (Single Eval)
# ================================================================

(defn ty/type [lvl] [:Type lvl])
(defn ty/pi [A B] [:Pi A B])
(defn ty/sigma [A B] [:Sigma A B])
(defn ty/id [A x y] [:Id A x y])

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

(def CHUNK_SIZE 32)
(defn ctx/empty []
  (def Γ (table/new (inc CHUNK_SIZE)))
  (put Γ :count 0)
  Γ)

(defn ctx/add [Γ x A]
  (def count (get Γ :count 0))
  (if (< count CHUNK_SIZE)
    (do (def new-Γ (table/clone Γ)) (put new-Γ x A) (put new-Γ :count (inc count)) new-Γ)
    (do (def new-chunk (table/new (inc CHUNK_SIZE))) (put new-chunk x A) (put new-chunk :count 1) (table/setproto new-chunk Γ) new-chunk)))

(defn ctx/lookup [Γ x]
  (if (has-key? Γ x) (get Γ x) (errorf "unbound variable: %v" x)))

(var raise nil)
(var lower nil)

(set raise
     (fn [ty ne]
       (match ty
         [:Type l] [:neutral ne]
         [:Pi A B] (fn [x] (let [nfx (lower A x)] (raise (B x) (ne/app ne nfx))))
         [:Sigma A B] (let [v1 (raise A (ne/fst ne)) v2 (raise (B v1) (ne/snd ne))] [v1 v2])
         [:Id A x y] [:neutral ne]
         [:neutral _] [:neutral ne])))

(set lower
     (fn [ty sem]
       (match ty
         [:Type l] (match sem [:neutral ne] (nf/neut ne) _ sem)
         [:Pi A B]
         (match sem
           [:neutral ne]
           (nf/lam (fn [fresh] (let [arg-sem (raise A (ne/var fresh))] (lower (B arg-sem) (raise (B arg-sem) (ne/app ne (lower A arg-sem)))))))
           _ (nf/lam (fn [fresh] (let [arg-sem (raise A (ne/var fresh))] (lower (B arg-sem) (sem arg-sem))))))
         [:Sigma A B]
         (match sem
           [:neutral ne] (let [v1 (raise A (ne/fst ne)) v2 (raise (B v1) (ne/snd ne))] (nf/pair (lower A v1) (lower (B v1) v2)))
           [v1 v2] (nf/pair (lower A v1) (lower (B v1) v2)))
         [:Id A x y] (match sem [:refl v] (nf/refl (lower A v)) [:neutral ne] (nf/neut ne) _ sem)
         [:neutral _] (match sem [:neutral ne] (nf/neut ne) _ sem))))

(defn sem-eq [ty v1 v2]
  (match ty
    [:Type l]
    (match [v1 v2]
      [[:Pi A1 B1] [:Pi A2 B2]] (and (sem-eq [:Type l] A1 A2) (let [fresh (gensym) arg-sem (raise A1 (ne/var fresh))] (sem-eq [:Type l] (B1 arg-sem) (B2 arg-sem))))
      [[:Sigma A1 B1] [:Sigma A2 B2]] (and (sem-eq [:Type l] A1 A2) (let [fresh (gensym) arg-sem (raise A1 (ne/var fresh))] (sem-eq [:Type l] (B1 arg-sem) (B2 arg-sem))))
      [[:Id A1 x1 y1] [:Id A2 x2 y2]] (and (sem-eq [:Type l] A1 A2) (sem-eq A1 x1 x2) (sem-eq A1 y1 y2))
      _ (= v1 v2))
    [:Pi A B] (let [fresh (gensym) arg-sem (raise A (ne/var fresh))]
                (match [v1 v2]
                  [[:neutral ne1] [:neutral ne2]] (= ne1 ne2)
                  [[:neutral ne1] _] (sem-eq (B arg-sem) (raise (B arg-sem) (ne/app ne1 (lower A arg-sem))) (v2 arg-sem))
                  [_ [:neutral ne2]] (sem-eq (B arg-sem) (v1 arg-sem) (raise (B arg-sem) (ne/app ne2 (lower A arg-sem))))
                  _ (sem-eq (B arg-sem) (v1 arg-sem) (v2 arg-sem))))
    [:Sigma A B] (match [v1 v2] [[l1 r1] [l2 r2]] (and (sem-eq A l1 l2) (sem-eq (B l1) r1 r2)) [[:neutral ne1] [:neutral ne2]] (= ne1 ne2) _ false)
    [:Id A x y] (match [v1 v2] [[:refl a] [:refl b]] (sem-eq A a b) [[:neutral ne1] [:neutral ne2]] (= ne1 ne2) _ false)))

(defn eval [Γ tm]
  (match tm
    [:Type l] [:Type l]
    [:Pi A B] [:Pi A B]
    [:Sigma A B] [:Sigma A B]
    [:Id A x y] [:Id A x y]
    [:refl x] [:refl x]
    [:neutral ne] [:neutral ne]
    [:var x] (if (or (string? x) (symbol? x)) [:neutral (ne/var x)] x)
    [:lam body] (fn [x] (eval Γ (body x)))
    [:app f x] (let [fv (eval Γ f) xv (eval Γ x)] (match fv [:neutral ne] [:neutral (ne/app ne (lower [:Type 0] xv))] _ (fv xv)))
    [:type l] (ty/type l)
    [:t-pi A B] (ty/pi (eval Γ A) (fn [x] (eval Γ (B x))))
    [:t-sigma A B] (ty/sigma (eval Γ A) (fn [x] (eval Γ (B x))))
    [:pair a b] [(eval Γ a) (eval Γ b)]
    [:fst p] (let [v (eval Γ p)] (match v [l r] l [:neutral ne] [:neutral (ne/fst ne)]))
    [:snd p] (let [v (eval Γ p)] (match v [l r] r [:neutral ne] [:neutral (ne/snd ne)]))
    [:t-id A x y] (ty/id (eval Γ A) (eval Γ x) (eval Γ y))
    [:t-refl x] [:refl (eval Γ x)]
    [:t-J A x P d y p]
    (let [Av (eval Γ A) xv (eval Γ x) Pv (eval Γ P) dv (eval Γ d) yv (eval Γ y) pv (eval Γ p)]
      (match pv [:refl zv] (if (sem-eq Av zv xv) dv [:neutral (ne/J Av xv Pv dv yv pv)]) [:neutral ne] [:neutral (ne/J Av xv Pv dv yv pv)] _ (errorf "J applied to non-proof: %v" pv)))
    _ (if (function? tm) tm tm)))
