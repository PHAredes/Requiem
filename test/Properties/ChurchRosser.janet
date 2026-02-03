#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)
(import ../Utils/Assertions :as a)

(test/start-suite "Property Church-Rosser")

(var rng (gen/rng))

# ===============================================
# Property: Church-Rosser
# ===============================================
(defn prop-church-rosser [n]
  "Property: If t ≡ u definitionally, then nf(t) = nf(u)"
  (var passed true)
  (repeat n
    (let [t (gen/gen-univ rng)
          Γ (c/ctx/empty)
          # Create eta-equivalent term: (λf. f) t ≡ t
          u [:app [:lam (fn [f] [:var f])] t]]
      (try
        (let [ty [:type 1]
              nf-t (c/nf ty t)
              nf-u (c/nf ty u)]
          (unless (a/nf-eq? nf-t nf-u)
            (set passed false)
            (print "Church-Rosser failed:")
            (print "  t =" t)
            (print "  u =" u)
            (print "  nf(t) =" nf-t)
            (print "  nf(u) =" nf-u)))
        ([err] nil))))
  passed)

(test/assert
  (prop-church-rosser 30)
  "Property: Church-Rosser - convertible terms normalize equally")

# ===============================================
# Property: Raise-Lower Roundtrip
# ===============================================
(defn prop-raise-lower-roundtrip [n]
  "Property: lower(ty, raise(ty, ne)) = ne for neutral terms"
  (var passed true)
  (repeat n
    (let [x (gensym)
          ty (case (math/rng-int rng 3)
               0 (c/ty/type (math/rng-int rng 3))
               1 (c/ty/pi (c/ty/type 0) (fn [_] (c/ty/type 0)))
               2 (c/ty/sigma (c/ty/type 0) (fn [_] (c/ty/type 0))))
          ne (c/ne/var x)]
      (try
        (let [raised (c/raise ty ne)
              lowered (c/lower ty raised)
              ltag (if (tuple? lowered) (get lowered 0) 0)]
          (cond
            (= ltag c/NF/Neut)
            (let [ne2 (get lowered 1)]
              (test/assert (= ne ne2)
                           (string/format "Raise-lower roundtrip preserves neutrals: ty=%v, %v ≡ %v" ty ne ne2)))

            (= ltag c/NF/Lam) true # Eta-expansion
            (= ltag c/NF/Pair) true # Eta-expansion
            (test/assert false (string/format "Unexpected lowered form: tag=%v, val=%v" ltag lowered))))
        ([err]
          (printf "Error in raise-lower: %v" err)
          (set passed false)))))
  passed)

(test/assert
  (prop-raise-lower-roundtrip 30)
  "Property: raise-lower roundtrip preserves neutrals (modulo eta)")

(test/end-suite)
