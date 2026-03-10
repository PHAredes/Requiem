#!/usr/bin/env janet

(import ./ast :as a)

(defn starts-with-at? [s i pref]
  (string/has-prefix? pref (string/slice s i)))

(defn- is-byte-between? [c lo hi]
  (and (>= c lo) (<= c hi)))

(defn- is-digit-byte? [c]
  (is-byte-between? c (chr "0") (chr "9")))

(defn- is-upper-byte? [c]
  (is-byte-between? c (chr "A") (chr "Z")))

(defn name/is-upper? [name]
  (and (> (length name) 0)
       (is-upper-byte? (name 0))))

(defn name/is-universe? [name]
  (and (> (length name) 1)
       (= (name 0) (chr "U"))
       (do
         (var ok true)
         (for i 1 (length name)
           (when (not (is-digit-byte? (name i)))
             (set ok false)))
         ok)))

(defn syntax/default []
  @{:literals @[
      {:lit "->" :k :arrow :v :arrow}
      {:lit "=>" :k :fat-arrow :v :fat-arrow}
      {:lit "\\" :k :lambda :v :lambda}
      {:lit "λ" :k :lambda :v :lambda}
      {:lit "Π" :k :quant :v :pi}
      {:lit "∀" :k :quant :v :pi}
      {:lit "Σ" :k :quant :v :sigma}
      {:lit "∃" :k :quant :v :sigma}
    ]
    :type/quant-builders @{
      :pi a/ty/pi
      :sigma a/ty/sigma
    }
    :type/ident-resolvers @[
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
    ]})

(defn syntax/clone [sx]
  @{:literals (array/slice (sx :literals))
    :type/quant-builders (table/clone (sx :type/quant-builders))
    :type/ident-resolvers (array/slice (sx :type/ident-resolvers))})

(defn syntax/add-literal! [sx lit kind value]
  (array/push (sx :literals) {:lit lit :k kind :v value})
  sx)

(defn syntax/add-quant-alias! [sx alias quant-kind]
  (syntax/add-literal! sx alias :quant quant-kind)
  sx)

(defn syntax/add-type-ident-resolver! [sx resolver]
  (array/push (sx :type/ident-resolvers) resolver)
  sx)

(defn syntax/match-literal [sx text i]
  (var best nil)
  (each entry (sx :literals)
    (let [lit (entry :lit)]
      (when (starts-with-at? text i lit)
        (if (or (nil? best)
                (> (length lit) (length (best :lit))))
          (set best entry)))))
  best)

(def exports
  {:starts-with-at? starts-with-at?
   :name/is-upper? name/is-upper?
   :name/is-universe? name/is-universe?
   :syntax/default syntax/default
   :syntax/clone syntax/clone
   :syntax/add-literal! syntax/add-literal!
   :syntax/add-quant-alias! syntax/add-quant-alias!
   :syntax/add-type-ident-resolver! syntax/add-type-ident-resolver!
   :syntax/match-literal syntax/match-literal})
