(defn reducible? [tm]
  (and (tuple? tm)
       (or (and (= :app (tm 0))
                (tuple? (tm 1))
                (= :lam ((tm 1) 0)))
           (and (= :fst (tm 0))
                (tuple? (tm 1))
                (= :pair ((tm 1) 0)))
           (and (= :snd (tm 0))
                (tuple? (tm 1))
                (= :pair ((tm 1) 0))))))

(defn contract [tm]
  (cond
    (and (tuple? tm)
         (= :app (tm 0))
         (tuple? (tm 1))
         (= :lam ((tm 1) 0)))
    (((tm 1) 1) (tm 2))

    (and (tuple? tm)
         (= :fst (tm 0))
         (tuple? (tm 1))
         (= :pair ((tm 1) 0)))
    ((tm 1) 1)

    (and (tuple? tm)
         (= :snd (tm 0))
         (tuple? (tm 1))
         (= :pair ((tm 1) 0)))
    ((tm 1) 2)

    true nil))

(defn step-leftmost [tm]
  (if (reducible? tm)
    (contract tm)
    (if (not (tuple? tm))
      nil
      (case (tm 0)
        :app (let [f-step (step-leftmost (tm 1))]
               (if f-step
                 [:app f-step (tm 2)]
                 (let [x-step (step-leftmost (tm 2))]
                   (if x-step [:app (tm 1) x-step] nil))))
        :fst (let [p-step (step-leftmost (tm 1))]
               (if p-step [:fst p-step] nil))
        :snd (let [p-step (step-leftmost (tm 1))]
               (if p-step [:snd p-step] nil))
        :pair (let [l-step (step-leftmost (tm 1))]
                (if l-step
                  [:pair l-step (tm 2)]
                  (let [r-step (step-leftmost (tm 2))]
                    (if r-step [:pair (tm 1) r-step] nil))))
        nil))))

(defn step-rightmost [tm]
  (if (not (tuple? tm))
    nil
    (case (tm 0)
      :app (let [x-step (step-rightmost (tm 2))]
             (if x-step
               [:app (tm 1) x-step]
               (let [f-step (step-rightmost (tm 1))]
                 (if f-step
                   [:app f-step (tm 2)]
                   (if (reducible? tm) (contract tm) nil)))))
      :fst (let [p-step (step-rightmost (tm 1))]
             (if p-step
               [:fst p-step]
               (if (reducible? tm) (contract tm) nil)))
      :snd (let [p-step (step-rightmost (tm 1))]
             (if p-step
               [:snd p-step]
               (if (reducible? tm) (contract tm) nil)))
      :pair (let [r-step (step-rightmost (tm 2))]
              (if r-step
                [:pair (tm 1) r-step]
                (let [l-step (step-rightmost (tm 1))]
                  (if l-step [:pair l-step (tm 2)] nil))))
      (if (reducible? tm) (contract tm) nil))))

(defn normalize-path [tm step-fn]
  (var out @[tm])
  (var current tm)
  (var next (step-fn current))
  (while next
    (array/push out next)
    (set current next)
    (set next (step-fn current)))
  out)

(defn step-reduce [tm]
  (step-leftmost tm))

(defn reduce-path [tm steps &opt strategy]
  (let [step-fn (if (= strategy :rightmost) step-rightmost step-leftmost)]
    (var current tm)
    (var i 0)
    (while (< i steps)
      (let [next (step-fn current)]
        (if next
          (set current next)
          (break)))
      (++ i))
    current))

(defn get-reduction-paths [tm]
  @[(normalize-path tm step-leftmost)
    (normalize-path tm step-rightmost)])
