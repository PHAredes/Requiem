#!/usr/bin/env janet

# Universe levels and displacement algebra.

(def L/Const 0x01)
(def L/Shift 0x02)
(def L/Var 0x04)
(def L/Plus 0x08)
(def L/Max 0x10)

(defn- check-nat [n who]
  (when (or (not (int? n)) (< n 0))
    (errorf "%v expects a non-negative integer, got: %v" who n))
  n)

(defn- check-name [x who]
  (when (nil? x)
    (errorf "%v expects a universe variable name, got nil" who))
  x)

(defn- nat<= [a b]
  (<= a b))

(defn- atom<= [basis1 offset1 basis2 offset2]
  (cond
    (and (= basis1 :const) (= basis2 :const)) (nat<= offset1 offset2)
    (and (= basis1 :const) (not= basis2 :const)) (nat<= offset1 offset2)
    (= basis1 basis2) (nat<= offset1 offset2)
    true false))

(defn const [n]
  [L/Const (check-nat n "lvl/const")])

(defn shift [n]
  [L/Shift (check-nat n "lvl/shift")])

(defn level-var [x]
  [L/Var (check-name x "lvl/var")])

(def uvar level-var)

(def id (shift 0))

(defn const? [l]
  (and (tuple? l) (= (get l 0) L/Const)))

(defn shift? [l]
  (and (tuple? l) (= (get l 0) L/Shift)))

(defn var? [l]
  (and (tuple? l) (= (get l 0) L/Var)))

(defn plus? [l]
  (and (tuple? l) (= (get l 0) L/Plus)))

(defn max? [l]
  (and (tuple? l) (= (get l 0) L/Max)))

(defn- order-key [basis]
  (if (= basis :const)
    ""
    (string basis)))

(defn- terms/add! [terms basis offset]
  (let [current (get terms basis)]
    (when (or (nil? current) (> offset current))
      (put terms basis offset)))
  terms)

(defn- terms/shift [terms n]
  (reduce (fn [acc entry]
            (terms/add! acc (entry 0) (+ n (entry 1))))
          @{}
          (pairs terms)))

(defn- terms/merge [left right]
  (reduce (fn [acc entry]
            (terms/add! acc (entry 0) (entry 1)))
          (table/clone left)
          (pairs right)))

(defn- terms/of-level [l]
  (cond
    (int? l)
    (let [terms @{}]
      (terms/add! terms :const (check-nat l "lvl/level")))

    (const? l)
    (let [terms @{}]
      (terms/add! terms :const (check-nat (get l 1) "lvl/level")))

    (var? l)
    (let [terms @{}]
      (terms/add! terms (check-name (get l 1) "lvl/level") 0))

    (plus? l)
    (let [terms @{}]
      (terms/add! terms
                  (check-name (get l 1) "lvl/level")
                  (check-nat (get l 2) "lvl/level")))

    (max? l)
    (reduce (fn [acc child]
              (terms/merge acc (terms/of-level child)))
            @{}
            (slice l 1))

    (shift? l)
    (errorf "lvl/level: shift is a displacement operator, not a level: %v" l)

    true
    (errorf "invalid level expression: %v" l)))

(defn- atom/of-entry [basis offset]
  (if (= basis :const)
    (const offset)
    (if (zero? offset)
      (level-var basis)
      [L/Plus basis offset])))

(defn- terms/entries [terms]
  (sort
    (map (fn [entry]
           [(order-key (entry 0)) (entry 0) (entry 1)])
         (pairs terms))))

(defn- reify [terms]
  (let [entries (terms/entries terms)]
    (when (zero? (length entries))
      (error "cannot reify empty level expression"))
    (if (= (length entries) 1)
      (let [entry (entries 0)]
        (atom/of-entry (entry 1) (entry 2)))
      (let [atoms (map (fn [entry]
                         (atom/of-entry (entry 1) (entry 2)))
                       entries)]
        (apply tuple (array/concat @[L/Max] atoms))))))

(defn leq [l1 l2]
  (let [t1 (terms/entries (terms/of-level l1))
        t2 (terms/entries (terms/of-level l2))]
    (all (fn [entry]
           (not (nil? (find (fn [rhs]
                              (atom<= (entry 1) (entry 2)
                                       (rhs 1) (rhs 2)))
                            t2))))
         t1)))

(def <= leq)

(defn lt [l1 l2]
  (and (leq l1 l2) (not (leq l2 l1))))

(defn eq? [l1 l2]
  (and (leq l1 l2) (leq l2 l1)))

(defn max* [l1 l2]
  (reify (terms/merge (terms/of-level l1) (terms/of-level l2))))

(def max max*)

(defn apply-shift [shift-val l]
  (when (not (shift? shift-val))
    (errorf "lvl/apply-shift expects a shift, got: %v" shift-val))
  (reify (terms/shift (terms/of-level l) (get shift-val 1))))

(defn normalize [l]
  (if (shift? l)
    (apply-shift l (const 0))
    (reify (terms/of-level l))))

(defn value [l]
  "Read back a closed level expression to a concrete natural number."
  (let [norm (normalize l)]
    (cond
      (int? norm) (check-nat norm "lvl/value")
      (const? norm) (check-nat (get norm 1) "lvl/value")
      true (errorf "lvl/value: level is not closed: %v" l))))

(defn succ [l]
  (apply-shift (shift 1) l))

(defn compose [s1 s2]
  (when (not (shift? s1))
    (errorf "lvl/compose expects a shift as first argument, got: %v" s1))
  (when (not (shift? s2))
    (errorf "lvl/compose expects a shift as second argument, got: %v" s2))
  (shift (+ (get s1 1) (get s2 1))))

(defn closed [l]
  (let [norm (normalize l)]
    (if (const? norm) (get norm 1) norm)))

(defn str [l]
  (let [norm (normalize l)]
    (cond
      (int? norm) (string norm)
      (const? norm) (string (get norm 1))
      (var? norm) (string (get norm 1))
      (plus? norm) (string (get norm 1) " + " (get norm 2))
      (max? norm) (string/join (map str (slice norm 1)) " \\/ ")
      true (string/format "%v" norm))))

(def exports
  {:L/Const L/Const
   :L/Shift L/Shift
   :L/Var L/Var
   :L/Plus L/Plus
   :L/Max L/Max
   :const const
   :shift shift
   :var level-var
   :uvar uvar
   :id id
   :const? const?
   :shift? shift?
   :var? var?
   :plus? plus?
   :max? max?
   :value value
   :normalize normalize
   :closed closed
   :leq leq
   :<= <=
   :lt lt
   :eq? eq?
   :succ succ
   :max max*
   :max* max*
   :apply-shift apply-shift
   :compose compose
   :str str})
