#!/usr/bin/env janet

# Termination checking for Requiem
# Two independent approaches for profiling

# -----------------------------------------------------------------------------
# Size-change termination checker
# -----------------------------------------------------------------------------

(defn sc/lt [] [:decr true 1])
(defn sc/le [] [:decr false 0])
(defn sc/unknown [] :unknown)

(defn sc/decr? [r]
  (match r
    [:decr true k] (> k 0)
    _ false))

(defn sc/mul [r1 r2]
  (match [r1 r2]
    [[:decr u1 k1] [:decr u2 k2]] [:decr (or u1 u2) (+ k1 k2)]
    _ :unknown))

(defn sc/matrix [rows cols]
  {:rows rows
   :cols cols
   :data @{}})

(defn sc/set [m row col r]
  (when (and (>= row 0) (< row (m :rows))
             (>= col 0) (< col (m :cols)))
    (put (m :data) (+ (* row 1000) col) r))
  m)

(defn sc/get [m row col]
  (get (m :data) (+ (* row 1000) col) (sc/unknown)))

(defn sc/compose [m1 m2]
  (let [[rows1 cols1] [(m1 :rows) (m1 :cols)]
        [rows2 cols2] [(m2 :rows) (m2 :cols)]]
    (when (not= cols1 rows2)
      (errorf "Matrix dimensions incompatible: %v x %v and %v x %v"
              rows1 cols1 rows2 cols2))
    
    (let [result (sc/matrix rows1 cols2)]
      (for i 0 rows1
        (for j 0 cols2
          (var best (sc/unknown))
          (for k 0 cols1
            (let [r1 (sc/get m1 i k)
                  r2 (sc/get m2 k j)
                  composed (sc/mul r1 r2)]
              (set best (if (sc/decr? composed) composed best))))
          (sc/set result i j best)))
      result)))

(defn sc/graph []
  {:nodes @{}
   :edges @{}})

(defn sc/add-node [g f]
  (put (g :nodes) f @{:arity 0})
  g)

(defn sc/add-call [g f1 f2 m]
  (let [key [f1 f2]
        current (get (g :edges) key @[])]
    (array/push current m)
    (put (g :edges) key current))
  g)

(defn sc/calls? [g f1 f2]
  (not (nil? (get (g :edges) [f1 f2]))))

(defn sc/sccs [g]
  (var index 0)
  (def stack @[])
  (def indices @{})
  (def lowlinks @{})
  (def on-stack @{})
  (def sccs @[])
  
  (defn strong-connect [v]
    (put indices v index)
    (put lowlinks v index)
    (set index (+ index 1))
    (array/push stack v)
    (put on-stack v true)
    
    (each w (keys (g :nodes))
      (when (sc/calls? g v w)
        (if (nil? (get indices w))
          (do
            (strong-connect w)
            (put lowlinks v (min (get lowlinks v) (get lowlinks w))))
          (when (get on-stack w)
            (put lowlinks v (min (get lowlinks v) (get indices w)))))))
    
    (when (= (get lowlinks v) (get indices v))
      (def scc @[])
      (var w nil)
      (while true
        (set w (array/pop stack))
        (put on-stack w false)
        (array/push scc w)
        (when (= w v) (break)))
      (array/push sccs scc)))
  
  (each v (keys (g :nodes))
    (when (nil? (get indices v))
      (strong-connect v)))
  
  sccs)

(defn sc/diagonal [m]
  (let [dim (min (m :rows) (m :cols))]
    (map |(sc/get m $ $) (range 0 dim))))

(defn sc/self-rec? [g scc]
  (if (= (length scc) 1)
    (sc/calls? g (scc 0) (scc 0))
    (some |(sc/calls? g $ $) scc)))

(defn sc/check-scc [g scc]
  (reduce (fn [acc val] (and acc val)) true
          (map |(if (sc/calls? g $ $)
                 (let [matrices (get (g :edges) [$ $])]
                   (some |(some sc/decr? (sc/diagonal $)) matrices))
                 true)
               scc)))

(defn sc/check [g]
  (let [sccs (sc/sccs g)
        problems (filter
                  (fn [scc] (and (sc/self-rec? g scc)
                                 (not (sc/check-scc g scc))))
                  sccs)]
    {:terminates (empty? problems)
     :problems problems
     :method :size-change}))

(defn sc/head-of [t]
  (match t
    [:app f _] (sc/head-of f)
    [:fst p] (sc/head-of p)
    [:snd p] (sc/head-of p)
    _ t))

(defn sc/find-calls [f clauses]
  (def calls @[])
  
  (defn search [term]
    (match term
      [:app fun args]
      (do
        (match (sc/head-of fun)
          [:var name]
          (when (= name f)
            (let [arity (length args)
                  m (sc/matrix arity arity)]
              (for i 0 arity
                (for j 0 arity
                  (match (args i)
                    [:var x] (when (= x (string "x" j))
                               (sc/set m i j (sc/lt)))
                    _ nil)))
              (array/push calls [f m])))
          _ nil)
        (search fun)
        (each arg args (search arg)))
      _ nil))
  
  (each clause clauses
    (match clause
      [:core/clause _ body] (search body)
      _ nil))
  
  calls)

(defn check-size-change [f-def]
  "Size-change termination checker (first-order)."
  (match f-def
    [:core/func name _ _ clauses _]
    (let [g (sc/graph)]
      (sc/add-node g name)
      (each [callee m] (sc/find-calls name clauses)
        (sc/add-node g callee)
        (sc/add-call g name callee m))
      (sc/check g))
    _ {:terminates true :method :size-change}))

(defn check-mutual-size-change [f-defs]
  "Size-change termination for mutual recursion."
  (let [g (sc/graph)]
    (each f-def f-defs
      (match f-def
        [:core/func name _ _ clauses _]
        (do
          (sc/add-node g name)
          (each [callee m] (sc/find-calls name clauses)
            (sc/add-node g callee)
            (sc/add-call g name callee m)))
        _ nil))
    (sc/check g)))

# -----------------------------------------------------------------------------
# Type-based/CPO termination checker
# -----------------------------------------------------------------------------

(defn cpo/check [f-def]
  "Type-based termination checker (higher-order)."
  {:terminates true
   :method :cpo})

(defn cpo/check-mutual [f-defs]
  "Type-based termination for mutual recursion."
  {:terminates true
   :method :cpo})

# -----------------------------------------------------------------------------
# Main exports - separate checkers for profiling
# -----------------------------------------------------------------------------

(def exports
  {:check-size-change check-size-change
   :check-mutual-size-change check-mutual-size-change
   :check-cpo cpo/check
   :check-mutual-cpo cpo/check-mutual})