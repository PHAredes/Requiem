(import ./TestRunner :as test)
(import ../../src/coreTT :as c)

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
      (c/sem-eq (c/ty/type 100) inferred-ty expected-ty))
    ([err]
      (print "Type preservation error:" err)
      false)))

(defn normalization-stable [ty tm]
  "Check that normalizing twice gives same result as normalizing once"
  (let [Γ (c/ctx/empty)
        nf1 (c/nf ty tm)
        sem1 (c/eval Γ tm)
        nf1-again (c/lower ty sem1)]
    (= nf1 nf1-again)))
