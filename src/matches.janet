#!/usr/bin/env janet

(def YES :yes)
(def NO :no)
(def STUCK :stuck)

(defn outcome/yes [subst] [YES subst])
(defn outcome/no [] [NO])
(defn outcome/stuck [] [STUCK])

(defn outcome/yes? [r] (and (tuple? r) (= (r 0) YES)))
(defn outcome/no? [r] (and (tuple? r) (= (r 0) NO)))
(defn outcome/stuck? [r] (and (tuple? r) (= (r 0) STUCK)))

(defn outcome/subst [r]
  (if (outcome/yes? r)
    (r 1)
    (errorf "outcome/subst called on non-yes result: %v" r)))

(defn subst/empty [] @{})

(defn subst/lookup [sigma x] (get sigma x))

(defn subst/extend [sigma x u]
  (let [s2 (table ;(kvs sigma))]
    (put s2 x u)
    s2))

(defn subst/merge [left right]
  (let [out (table ;(kvs left))]
    (var ok true)
    (eachp [k v] right
      (if-let [existing (get out k)]
        (when (not= existing v)
          (set ok false))
        (put out k v)))
    (if ok out nil)))

(defn term/head-args [u]
  (match u
    [:atom name] [name @[]]
    [:var name] [name @[]]
    [:list xs]
    (if (and (> (length xs) 0)
             (tuple? (xs 0))
             (or (= ((xs 0) 0) :atom)
                 (= ((xs 0) 0) :var)))
      [((xs 0) 1) (slice xs 1)]
      [nil @[]])
    [:app f x]
    (match (term/head-args f)
      [nil _] [nil @[]]
      [head args] [head [;args x]])
    [:napp _ _] [nil @[]]
    [:nvar x] [x @[]]
    _ [nil @[]]))

(defn term/neutral? [u]
  (match u
    [:nvar _] true
    [:napp _ _] true
    [:nfst _] true
    [:nsnd _] true
    true false))

(defn pat/var? [p] (and (tuple? p) (= (p 0) :pat/var)))
(defn pat/con? [p] (and (tuple? p) (= (p 0) :pat/con)))
(defn pat/hole? [p] (and (tuple? p) (= (p 0) :hole)))

(defn pat/var-name [p] (p 1))
(defn pat/con-name [p] (p 1))
(defn pat/con-args [p] (p 2))

(defn pat/vars [p]
  (match p
    [:pat/var x] (if (= x "_") @[] @[x])
    [:hole name] (if (nil? name) @[] @[name])
    [:pat/con _ args] (reduce (fn [acc a] [;acc ;(pat/vars a)]) @[] args)
    [:pat/impossible] @[]
    _ @[]))

(defn pat/to-term [p]
  (match p
    [:pat/var x] [:var x]
    [:hole name] [:var (or name "_")]
    [:pat/con c args]
    (if (zero? (length args))
      [:atom c]
      (reduce (fn [acc a] [:app acc (pat/to-term a)])
              [:atom c]
              args))
    [:pat/impossible]
    (errorf "pat/to-term: impossible pattern has no term representation")
    _
    (errorf "pat/to-term: unknown pattern %v" p)))

(var matches nil)
(var matches* nil)

(set matches
     (fn [u p ctor-name-set]
       (cond
         (and (tuple? p) (= (p 0) :pat/var) (= (p 1) "_"))
         (outcome/yes (subst/empty))

         (and (tuple? p) (= (p 0) :hole) (nil? (p 1)))
         (outcome/yes (subst/empty))

         (and (tuple? p) (= (p 0) :hole) (not (nil? (p 1))))
         (outcome/yes (subst/extend (subst/empty) (p 1) u))

         (pat/var? p)
         (let [x (pat/var-name p)]
           (if (= x "_")
             (outcome/yes (subst/empty))
             (outcome/yes (subst/extend (subst/empty) x u))))

         (pat/con? p)
         (let [ctor (pat/con-name p)
               pats (pat/con-args p)
               [head args] (term/head-args u)]
           (cond
             (term/neutral? u) (outcome/stuck)
             (nil? head) (outcome/stuck)
             (not (has-key? ctor-name-set head)) (outcome/stuck)
             (not= head ctor) (outcome/no)
             (not= (length args) (length pats)) (outcome/no)
             true (matches* args pats ctor-name-set (subst/empty))))

         (and (tuple? p) (= (p 0) :pat/impossible))
         (outcome/no)

         true
         (errorf "matches: unknown pattern form %v" p))))

(set matches*
     (fn [us ps ctor-name-set &opt initial-subst]
       (if (not= (length us) (length ps))
         (outcome/no)
         (do
           (var status YES)
           (var sigma (or initial-subst (subst/empty)))
           (var i 0)
           (while (and (< i (length us)) (= status YES))
             (let [r (matches (us i) (ps i) ctor-name-set)]
               (match r
                 [:yes s2]
                 (if-let [merged (subst/merge sigma s2)]
                   (set sigma merged)
                   (set status NO))
                 [:no]
                 (set status NO)
                 [:stuck]
                 (set status STUCK)))
             (++ i))
           (match status
             :yes (outcome/yes sigma)
             :no (outcome/no)
             :stuck (outcome/stuck))))))

(defn ctor/available? [type-args ctor ctor-name-set]
  (let [patterns (ctor :patterns)]
    (if (zero? (length patterns))
      (outcome/yes (subst/empty))
      (matches* type-args patterns ctor-name-set (subst/empty)))))

(defn ctors/available [type-args ctors ctor-name-set]
  (let [out @[]]
    (each ctor ctors
      (let [r (ctor/available? type-args ctor ctor-name-set)]
        (match r
          [:yes sigma] (array/push out {:ctor ctor :subst sigma})
          [:no] nil
          [:stuck]
          (errorf "constructor %v availability is stuck on indices %v"
                  (ctor :name)
                  type-args))))
    out))

(def exports
  {:YES YES
   :NO NO
   :STUCK STUCK
   :outcome/yes outcome/yes
   :outcome/no outcome/no
   :outcome/stuck outcome/stuck
   :outcome/yes? outcome/yes?
   :outcome/no? outcome/no?
   :outcome/stuck? outcome/stuck?
   :outcome/subst outcome/subst
   :subst/empty subst/empty
   :subst/lookup subst/lookup
   :subst/extend subst/extend
   :subst/merge subst/merge
   :pat/vars pat/vars
   :pat/to-term pat/to-term
   :matches matches
   :matches* matches*
   :ctor/available? ctor/available?
   :ctors/available ctors/available})
