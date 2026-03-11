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

(defn name/is-type-universe? [name]
  (and (string/has-prefix? "Type" name)
       (let [suffix (string/slice name 4)]
         (or (= suffix "")
             (do
               (var ok true)
               (for i 0 (length suffix)
                 (when (not (is-digit-byte? (suffix i)))
                   (set ok false)))
               ok)))))

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
  # Ensure the operator is also in literals so the lexer can see it
  (var found-lit false)
  (each entry (sx :literals)
    (when (= (entry :lit) op)
      (set found-lit true)
      (break)))
  (when (not found-lit)
    (syntax/add-literal! sx op :op op))
  sx)

(defn syntax/add-alias! [sx new-lit target-lit]
  (var found nil)
  (each entry (sx :literals)
    (when (= (entry :lit) target-lit)
      (set found entry)
      (break)))
  (if found
    (syntax/add-literal! sx new-lit (found :k) (found :v))
    # If not a literal, maybe it's a known quantifier keyword?
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
