(defn rng []
  (math/rng 42))

(defn gen-univ [rng]
  [:type (math/rng-int rng 4)])

(defn gen-nested-term [rng depth]
  "Generate a nested term of given depth"
  (if (<= depth 0)
    [:type (math/rng-int rng 3)]
    (case (math/rng-int rng 4)
      0 [:type (math/rng-int rng 3)]
      1 [:lam (fn [x] (gen-nested-term rng (dec depth)))]
      2 [:app (gen-nested-term rng (dec depth)) (gen-nested-term rng (dec depth))]
      3 [:pair (gen-nested-term rng (dec depth)) (gen-nested-term rng (dec depth))])))
