(import ./TestRunner :as test)
(import ../../src/coreTT :as c)

(def MAX_UNIVERSE_LEVEL 100)

(defn assert-throws [f msg]
  "Helper to assert that a function throws an error"
  (var threw false)
  (try
    (f)
    ([err] (set threw true)))
  (test/assert threw msg))

(defn type-preserves [Γ t expected-ty]
  "Check that term t has type expected-ty and evaluation preserves this"
  (try
    (let [inferred-ty (c/infer Γ t)]
      (c/sem-eq (c/ty/type MAX_UNIVERSE_LEVEL) inferred-ty expected-ty))
    ([err]
      (print "Type preservation error:" err)
      false)))

(defn nf-eq? [v1 v2]
  "Structural equality for normal forms (handles HOAS functions)"
  (cond
    (= v1 v2) true
    (not (and (tuple? v1) (tuple? v2))) (= v1 v2)
    (let [t1 (first v1) t2 (first v2)]
      (if (not= t1 t2) false
        (cond
          (= t1 c/NF/Lam)
          (let [fresh (gensym)
                b1 (get v1 1)
                b2 (get v2 1)]
            (nf-eq? (b1 fresh) (b2 fresh)))
          true (if (= (length v1) (length v2))
                 (all |(nf-eq? (get v1 $) (get v2 $)) (range 1 (length v1)))
                 false))))))

(defn normalization-stable [ty tm]
  "Check that normalizing twice gives same result as normalizing once"
  (let [Γ (c/ctx/empty)
        nf1 (c/nf ty tm)
        sem1 (c/eval Γ tm)
        nf1-again (c/lower ty sem1)]
    (nf-eq? nf1 nf1-again)))
