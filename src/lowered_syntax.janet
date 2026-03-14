#!/usr/bin/env janet

(defn node/atom? [node]
  (and (tuple? node) (= (node 0) :atom)))

(defn node/list? [node]
  (and (tuple? node) (= (node 0) :list)))

(defn node/atom [node]
  (if (node/atom? node)
    (node 1)
    (errorf "expected atom node, but got %v" node)))

(defn node/list-items [node]
  (if (node/list? node)
    (node 1)
    (errorf "expected list node, but got %v" node)))

(defn node/atom= [node tok]
  (and (node/atom? node) (= (node 1) tok)))

(defn norm/layout [node]
  (match node
    [:atom _] node
    [:list xs] [:list (map norm/layout xs)]
    [:brackets xs] [:list (map norm/layout xs)]
    _ node))

(defn token/colon? [tok]
  (let [n (length tok)]
    (and (> n 0)
         (= ":" (string/slice tok (- n 1) n)))))

(defn token/strip-colon [tok]
  (let [n (length tok)]
    (if (token/colon? tok)
      (string/slice tok 0 (- n 1))
      tok)))

(defn bind/single-spec? [node]
  (and (node/list? node)
       (let [xs (node/list-items node)]
         (or
           (and (= (length xs) 2)
                (node/atom? (xs 0))
                (token/colon? (node/atom (xs 0))))
           (and (= (length xs) 3)
                (node/atom= (xs 0) ":")
                (node/atom? (xs 1)))))))

(defn bind/from-node [node]
  (let [xs (node/list-items node)]
    (cond
      (and (= (length xs) 2)
           (node/atom? (xs 0))
           (token/colon? (node/atom (xs 0))))
      [:bind (token/strip-colon (node/atom (xs 0))) (xs 1)]

      (and (= (length xs) 3)
           (node/atom= (xs 0) ":")
           (node/atom? (xs 1)))
      [:bind (node/atom (xs 1)) (xs 2)]

      true
      (errorf "invalid binder syntax: %v" node))))

(defn binders/from-spec [spec]
  (if (bind/single-spec? spec)
    @[(bind/from-node spec)]
    (if (node/list? spec)
      (map bind/from-node (node/list-items spec))
      (errorf "invalid binder specification: %v" spec))))

(defn term/forall? [node]
  (and (node/list? node)
       (let [xs (node/list-items node)]
         (and (> (length xs) 0)
              (node/atom? (xs 0))
              (let [head (node/atom (xs 0))]
                (or (= head "forall") (= head "∀")))))))

(defn term/arrow? [node]
  (and (node/list? node)
       (let [xs (node/list-items node)]
         (and (= (length xs) 3)
              (node/atom? (xs 1))
              (let [mid (node/atom (xs 1))]
                (or (= mid "->") (= mid "→")))))))

(defn term/unpack-arrow [node]
  (let [xs (node/list-items node)]
    [(xs 0) (xs 2)]))

(defn term/unpack-forall [node]
  (let [xs (node/list-items node)
        n (length xs)]
    (when (< n 3)
      (errorf "forall form is too short: %v" node))
    (let [binder-spec (xs 1)
          dot-index (find-index |(node/atom= $ ".") (slice xs 2 n))]
      (let [body
            (if dot-index
              (let [actual-index (+ dot-index 2)]
                (if (= actual-index (- n 2))
                  (xs (- n 1))
                  [:list (slice xs (+ actual-index 1) n)]))
              (if (= n 3)
                (xs 2)
                [:list (slice xs 2 n)]))]
        [(binders/from-spec binder-spec) body]))))

(defn term/split-pi [node]
  (defn split-loop [cur index binders]
    (cond
      (term/forall? cur)
      (let [[bs body] (term/unpack-forall cur)]
        (split-loop body index (tuple/join binders bs)))

      (term/arrow? cur)
      (let [[dom cod] (term/unpack-arrow cur)
            name (string "_arg" index)]
        (split-loop cod (+ index 1) [;binders [:bind name dom]]))

      true
      [binders cur]))
  (split-loop node 0 @[]))

(defn term/build-forall [binders body]
  (defn fold-binders [acc binder]
    (let [name (if (>= (length binder) 2) (binder 1) "_")
          ty (if (>= (length binder) 3) (binder 2) [:atom "Type"])
          binder-node [:list @[[ :atom (string name ":") ] ty]]]
      [:list @[[ :atom "forall" ] binder-node [ :atom "." ] acc]]))
  (reduce fold-binders body (reverse binders)))

(def exports
  {:node/atom? node/atom?
   :node/list? node/list?
   :node/atom node/atom
   :node/list-items node/list-items
   :node/atom= node/atom=
   :norm/layout norm/layout
   :token/colon? token/colon?
   :token/strip-colon token/strip-colon
   :bind/single-spec? bind/single-spec?
   :bind/from-node bind/from-node
   :binders/from-spec binders/from-spec
   :term/forall? term/forall?
   :term/arrow? term/arrow?
   :term/unpack-forall term/unpack-forall
   :term/split-pi term/split-pi
   :term/build-forall term/build-forall})
