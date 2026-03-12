#!/usr/bin/env janet

(import ./ast :as a)

(defn starts-with-at? [s i pref]
  (string/has-prefix? pref (string/slice s i)))

(defn- is-byte-between? [c lo hi]
  (and (>= c lo) (<= c hi)))

(defn- is-digit-byte? [c]
  (is-byte-between? c (chr "0") (chr "9")))

(defn- digits-only? [text &opt start]
  (let [from (or start 0)]
    (and (>= (length text) from)
         (reduce (fn [ok i]
                   (and ok (is-digit-byte? (text i))))
                 true
                 (range from (length text))))))

(defn- is-upper-byte? [c]
  (is-byte-between? c (chr "A") (chr "Z")))

(defn name/is-upper? [name]
  (and (> (length name) 0)
       (is-upper-byte? (name 0))))

(defn name/is-universe? [name]
  (and (> (length name) 1)
       (= (name 0) (chr "U"))
       (digits-only? name 1)))

(defn name/is-type-universe? [name]
  (and (string/has-prefix? "Type" name)
       (let [suffix (string/slice name 4)]
         (digits-only? suffix))))

(defn- syntax/find-literal [sx lit]
  (find |(= ($ :lit) lit) (sx :literals)))

(defn syntax/default []
  @{:literals @[
      {:lit "->" :k :op :v "->"}
      {:lit "→" :k :op :v "->"}
      {:lit "\\" :k :lambda :v :lambda}
      {:lit "λ" :k :lambda :v :lambda}
      {:lit "Pi" :k :quant :v :pi}
      {:lit "Π" :k :quant :v :pi}
      {:lit "forall" :k :quant :v :pi}
      {:lit "∀" :k :quant :v :pi}
      {:lit "Sigma" :k :quant :v :sigma}
      {:lit "Σ" :k :quant :v :sigma}
      {:lit "∃" :k :quant :v :sigma}
    ]
    :type/quant-builders @{
      :pi a/ty/pi
      :sigma a/ty/sigma
    }
    :type/ident-resolvers @[
      (fn [name sp]
        (if (name/is-type-universe? name)
          (let [suffix (string/slice name 4)]
            (a/ty/universe (if (= suffix "") 0 (scan-number suffix)) sp))
          nil))
      (fn [name sp]
        (if (name/is-universe? name)
          (a/ty/universe (scan-number (string/slice name 1)) sp)
          nil))
      (fn [name sp]
        (if (name/is-upper? name)
          (a/ty/name name sp)
          nil))
      (fn [name sp]
        (a/ty/var name sp))
    ]
    :operators @{"->" {:fixity :infixr :level 20}}})

(defn syntax/clone [sx]
  @{:literals (array/slice (sx :literals))
    :type/quant-builders (table/clone (sx :type/quant-builders))
    :type/ident-resolvers (array/slice (sx :type/ident-resolvers))
    :operators (table/clone (sx :operators))})

(defn syntax/add-literal! [sx lit kind val]
  (array/push (sx :literals) {:lit lit :k kind :v val})
  sx)

(defn syntax/add-operator! [sx op fixity level]
  (put (sx :operators) op {:fixity fixity :level level})
  (when (nil? (syntax/find-literal sx op))
    (syntax/add-literal! sx op :op op))
  sx)

(defn syntax/add-alias! [sx new-lit target-lit]
  (if-let [found (syntax/find-literal sx target-lit)]
    (syntax/add-literal! sx new-lit (found :k) (found :v))
    (match target-lit
      "forall" (syntax/add-literal! sx new-lit :quant :pi)
      "sigma" (syntax/add-literal! sx new-lit :quant :sigma)
      "pi" (syntax/add-literal! sx new-lit :quant :pi)
      (if (or (= target-lit "Type")
              (name/is-type-universe? target-lit)
              (name/is-universe? target-lit))
        (syntax/add-literal! sx new-lit :ident target-lit)
        (errorf "cannot alias unknown literal or keyword: %v" target-lit))))
  sx)

(defn syntax/add-quant-alias! [sx new-lit kind]
  (syntax/add-literal! sx new-lit :quant kind)
  sx)

(defn syntax/add-type-ident-resolver! [sx resolver]
  (array/push (sx :type/ident-resolvers) resolver)
  sx)

(defn- is-ident-byte-c? [c]
  (or (is-byte-between? c (chr "a") (chr "z"))
      (is-byte-between? c (chr "A") (chr "Z"))
      (is-digit-byte? c)
      (= c (chr "-"))
      (= c (chr "_"))
      (= c (chr "'"))))

(defn syntax/match-literal [sx text i]
  (var best nil)
  (each entry (sx :literals)
    (let [lit (entry :lit)]
      (when (starts-with-at? text i lit)
        # Prevent partial matches for alpha keywords
        (let [last-c (lit (- (length lit) 1))
              next-i (+ i (length lit))]
          (when (or (not (is-ident-byte-c? last-c))
                    (>= next-i (length text))
                    (not (is-ident-byte-c? (text next-i))))
            (if (or (nil? best)
                    (> (length lit) (length (best :lit))))
              (set best entry)))))))
  best)

(def exports
  {:starts-with-at? starts-with-at?
   :name/is-upper? name/is-upper?
   :name/is-universe? name/is-universe?
   :name/is-type-universe? name/is-type-universe?
   :syntax/default syntax/default
   :syntax/clone syntax/clone
   :syntax/add-literal! syntax/add-literal!
   :syntax/add-alias! syntax/add-alias!
   :syntax/add-quant-alias! syntax/add-quant-alias!
   :syntax/add-type-ident-resolver! syntax/add-type-ident-resolver!
   :syntax/match-literal syntax/match-literal
   :syntax/add-operator! syntax/add-operator!})
