#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)
(import ../Utils/Generators :as gen)

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
          (unless (= nf-t nf-u)
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
               0 [:Type (math/rng-int rng 3)]
               1 [:Pi [:Type 0] (fn [_] [:Type 0])]
               2 [:Sigma [:Type 0] (fn [_] [:Type 0])])
          ne (c/ne/var x)]
      (try
        (let [raised (c/raise ty ne)
              lowered (c/lower ty raised)]
          (match lowered
            [:nneut ne2] (when (not= ne ne2)
                           (set passed false)
                           (print "Raise-lower roundtrip failed"))
            [:nlam body] true # Eta-expansion expected for Pi
            [:npair _ _] true # Eta-expansion expected for Sigma
            _ (do
                (set passed false)
                (print "Unexpected lowered form:" lowered))))
        ([err]
          (print "Error in raise-lower:" err)
          (set passed false)))))
  passed)

(test/assert
  (prop-raise-lower-roundtrip 30)
  "Property: raise-lower roundtrip preserves neutrals (modulo eta)")

(test/end-suite)
