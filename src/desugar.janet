#!/usr/bin/env janet

(import ./parser :as p)

(defn node/atom? [node]
  (and (tuple? node) (= (node 0) :atom)))

(defn node/list? [node]
  (and (tuple? node) (= (node 0) :list)))

(defn node/atom [node]
  (if (node/atom? node)
    (node 1)
    (errorf "expected atom node, but got %v\nExpected format: [:atom value]\nThis is an internal desugaring error" node)))

(defn node/list-items [node]
  (if (node/list? node)
    (node 1)
    (errorf "expected list node, but got %v\nExpected format: [:list items...]\nThis is an internal desugaring error" node)))

(defn node/atom= [node tok]
  (and (node/atom? node) (= (node 1) tok)))

(defn node/atom/new [tok]
  [:atom tok])

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
      (errorf "invalid binder syntax: %v\nSupported formats:\n  (x: Type) or (x: Type annotation)\n  (: x Type) - alternative syntax\nVariable must have a type annotation" node))))

(defn binders/from-spec [spec]
  (if (bind/single-spec? spec)
    @[(bind/from-node spec)]
    (if (node/list? spec)
      (let [out @[]]
        (each b (node/list-items spec)
          (array/push out (bind/from-node b)))
        out)
      (errorf "invalid forall binder specification: %v\nSupported formats:\n  (x: Type) - single binder\n  (x: Type y: Type) - multiple binders in a list\n  ((x: Type) (y: Type)) - multiple binders as separate specs" spec))))

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
      (errorf "forall form is too short: %v\nMinimum format: (forall (x: A) . B) or (forall (x: A) B)\nYou need at least variable and type annotations" node))
    (let [binder-spec (xs 1)]
      (var dot-index nil)
      (for i 2 n
        (when (and (nil? dot-index) (node/atom= (xs i) "."))
          (set dot-index i)))
      (let [body
            (if dot-index
              (if (= dot-index (- n 2))
                (xs (- n 1))
                [:list (slice xs (+ dot-index 1) n)])
              (if (= n 3)
                (xs 2)
                [:list (slice xs 2 n)]))]
        [(binders/from-spec binder-spec) body]))))

(defn term/split-pi [node]
  (let [binders @[]]
    (var index 0)
    (var cur node)
    (while true
      (if (term/forall? cur)
        (let [[bs body] (term/unpack-forall cur)]
          (each b bs (array/push binders b))
          (set cur body))
        (if (term/arrow? cur)
          (let [[dom cod] (term/unpack-arrow cur)
                name (string "_arg" index)]
            (++ index)
            (array/push binders [:bind name dom])
            (set cur cod))
          (break))))
    [binders cur]))

(defn term/as-head-app [node]
  (cond
    (node/atom? node)
    [(node/atom node) @[]]

    (node/list? node)
    (let [xs (node/list-items node)]
      (if (and (> (length xs) 0) (node/atom? (xs 0)))
        [(node/atom (xs 0)) (slice xs 1 (length xs))]
        [nil @[]]))

    true [nil @[]]))

(defn seq/concat [xs ys]
  (let [out @[]]
    (each x xs (array/push out x))
    (each y ys (array/push out y))
    out))

(defn binders/name->type [binders]
  (let [m @{}]
    (each b binders
      (put m (b 1) (b 2)))
    m))

(defn term/collect-var-order [terms var-types]
  (let [out @[]
        seen @{}]
    (defn walk [node]
      (cond
        (node/atom? node)
        (let [tok (node/atom node)]
          (when (and (has-key? var-types tok)
                     (not (has-key? seen tok)))
            (put seen tok true)
            (array/push out tok)))

        (node/list? node)
        (each x (node/list-items node)
          (walk x))

        true nil))
    (each t terms (walk t))
    out))

(defn pat/from-term [term pat-var-set]
  (match term
    [:atom tok]
    (if (has-key? pat-var-set tok)
      [:pat/var tok]
      [:pat/con tok @[]])

    [:list xs]
    (if (and (> (length xs) 0) (node/atom? (xs 0)))
      (let [head (node/atom (xs 0))
            args @[]]
        (for i 1 (length xs)
          (array/push args (pat/from-term (xs i) pat-var-set)))
        [:pat/con head args])
(errorf "cannot convert term to pattern: %v\nOnly simple patterns are supported:\n  Variables (x, y, etc.)\n  Constructor applications (C pattern1 pattern2)" term))

    _
    (errorf "cannot convert term to pattern: %v\nOnly simple patterns are supported:\n  Variables (x, y, etc.)\n  Constructor applications (C pattern1 pattern2)" term)))

(defn pat/to-term [pat]
  (match pat
    [:pat/var x] [:atom x]
    [:pat/con c args]
    (if (zero? (length args))
      [:atom c]
      (let [xs @[]]
        (array/push xs [:atom c])
        (each a args (array/push xs (pat/to-term a)))
        [:list xs]))
    [:pat/impossible]
    (errorf "cannot convert impossible pattern to term\nThe 'impossible' pattern is internal-only and cannot be converted back to a term")
    _
    (errorf "unknown pattern: %v\nSupported patterns: var, con, and impossible.\nThis is an internal desugaring error" pat)))

(defn term/build-data-app [name args]
  (if (zero? (length args))
    [:atom name]
    (let [xs @[]]
      (array/push xs [:atom name])
      (each a args (array/push xs a))
      [:list xs])))

(defn term/build-forall [binders body]
  (var out body)
  (var i (- (length binders) 1))
  (while (>= i 0)
    (let [b (binders i)
          name (b 1)
          ty (b 2)
          binder-node [:list @[(node/atom/new (string name ":")) ty]]]
      (set out [:list @[(node/atom/new "forall") binder-node (node/atom/new ".") out]]))
    (-- i))
  out)

(defn decl/parse-name-and-ann [nodes]
  (when (zero? (length nodes))
    (errorf "missing declaration name\nExpected format: name: Type = value or name = value"))
  (let [head (nodes 0)]
    (cond
      (and (node/atom? head)
           (token/colon? (node/atom head)))
      (do
        (when (< (length nodes) 2)
          (errorf "missing declaration annotation after %v\nExpected format: name: Type = value\nType annotation is required" (node/atom head)))
        [(token/strip-colon (node/atom head)) (nodes 1) 2])

      (node/list? head)
      (let [xs (node/list-items head)]
        (cond
          (and (= (length xs) 2)
               (node/atom? (xs 0))
               (token/colon? (node/atom (xs 0))))
          [(token/strip-colon (node/atom (xs 0))) (xs 1) 1]

          (and (= (length xs) 3)
               (node/atom= (xs 0) ":")
               (node/atom? (xs 1)))
          [(node/atom (xs 1)) (xs 2) 1]

          true
(errorf "invalid declaration head: %v\nSupported formats:\n  name: Type - annotated binder\n  (x: Type) or (: x Type) - alternative syntax" head)))

      true
      (errorf "invalid declaration head: %v\nDeclaration must start with:\n- A variable name\n- An annotated binder (x: Type)\n- A list declaration" head))))

(defn args/simple-return? [args data-params]
  (and (= (length args) (length data-params))
       (do
         (var ok true)
         (for i 0 (length args)
           (let [a (args i)
                 p (data-params i)]
             (if (and (node/atom? a) (= (node/atom a) (p 1)))
               nil
               (set ok false))))
         ok)))

(defn ctor/desugar [data-name data-params ctor-node]
  (let [xs (node/list-items ctor-node)]
    (when (not= (length xs) 2)
      (errorf "constructor must be (name type), got: %v\nFormat: (ConstructorName : Type)\nConstructor must have a name and a return type" ctor-node))
    (when (not (node/atom? (xs 0)))
      (errorf "constructor name must be an atom (identifier), got: %v\nConstructor names should be simple identifiers like 'Cons', 'Nil', 'Just', 'Nothing'" (xs 0)))
    (let [name (node/atom (xs 0))
          ctor-type (xs 1)
          [ctor-binders ret] (term/split-pi ctor-type)
          [head ret-args] (term/as-head-app ret)]
      (when (not= head data-name)
        (errorf "constructor %v must return %v, but got %v\nConstructors must return their parent data type" name data-name ret))
      (when (not= (length ret-args) (length data-params))
        (errorf "constructor %v returns wrong number of index arguments: %v\nExpected %d arguments to match data type parameters" name ret (length data-params)))
      (if (args/simple-return? ret-args data-params)
        [:ctor name @[] @[] ctor-binders ctor-type]
        (let [var-types (binders/name->type data-params)]
          (each b ctor-binders
            (put var-types (b 1) (b 2)))
          (let [ordered-vars (term/collect-var-order ret-args var-types)
                pat-var-set @{}
                pat-binders @[]]
            (each v ordered-vars
              (do
                (put pat-var-set v true)
                (array/push pat-binders [:bind v (get var-types v)])))
            (let [ctor-params @[]]
              (each b ctor-binders
                (when (not (has-key? pat-var-set (b 1)))
                  (array/push ctor-params b)))
              (let [patterns @[]]
                (each a ret-args
                  (array/push patterns (pat/from-term a pat-var-set)))
                (let [ret-term (term/build-data-app data-name (map pat/to-term patterns))
                      encoded (term/build-forall (seq/concat pat-binders ctor-params) ret-term)]
                  [:ctor name pat-binders patterns ctor-params encoded])))))))))

(defn data/desugar [nodes]
  (let [[name ann consumed] (decl/parse-name-and-ann nodes)
        tail (slice nodes consumed (length nodes))]
    (when (zero? (length tail))
      (errorf "data %v missing constructor block\nExpected format: (data Name: Type) (Constructor1 ...) (Constructor2 ...)" name))
    (let [[params sort] (term/split-pi ann)
          ctor-block (tail 0)]
      (when (not (node/list? ctor-block))
        (errorf "data %v constructors must be grouped in a list\nExpected: (data Name: Type) ((C1 ...) (C2 ...) ...)" name))
      (let [ctors @[]]
        (each c (node/list-items ctor-block)
          (array/push ctors (ctor/desugar name params c)))
        [:decl/data name params sort ctors]))))

(defn pat/from-case [node depth]
  (match node
    [:atom tok]
    (cond
      (= tok "impossible") [:pat/impossible]
      (= tok "_") [:pat/var "_"]
      (> depth 0) [:pat/var tok]
      true [:pat/con tok @[]])

    [:list xs]
    (if (and (> (length xs) 0) (node/atom? (xs 0)))
      (let [head (node/atom (xs 0))
            args @[]]
        (for i 1 (length xs)
          (array/push args (pat/from-case (xs i) (+ depth 1))))
        [:pat/con head args])
(errorf "invalid case pattern: %v\nSupported patterns:\n  Variables: x, y, _ (wildcard)\n  Constructor patterns: (Cons x xs)\n  Impossible: impossible" node))

    _
    (errorf "invalid case pattern: %v\nOnly atom or list patterns are supported in case expressions" node)))

(defn params/default-patterns [params]
  (let [out @[]]
    (each p params
      (array/push out [:pat/var (p 1)]))
    out))

(defn case/split [case-node]
  (let [xs (node/list-items case-node)]
    (when (or (zero? (length xs)) (not (node/atom= (xs 0) "case")))
      (errorf "invalid case clause: %v\nCase clauses must start with 'case' keyword" case-node))
    (let [rest (slice xs 1 (length xs))]
      (when (< (length rest) 2)
        (errorf "case clause is too short: %v\nMinimum format: (case pattern expression)\nYou need at least a pattern and an expression" case-node))
      (if (and (node/atom? (rest 0))
               (token/colon? (node/atom (rest 0))))
        [[:atom (token/strip-colon (node/atom (rest 0)))] (rest 1)]
        (do
          (var colon-index nil)
          (for i 0 (length rest)
            (when (and (nil? colon-index) (node/atom= (rest i) ":"))
              (set colon-index i)))
          (if colon-index
            (let [pat-node
                  (if (= colon-index 1)
                    (rest 0)
                    [:list (slice rest 0 colon-index)])
                  body
                  (if (= colon-index (- (length rest) 2))
                    (rest (- (length rest) 1))
                    [:list (slice rest (+ colon-index 1) (length rest))])]
              [pat-node body])
            [(rest 0) (rest 1)]))))))

(defn case/desugar [case-node params target-index]
  (let [[pat-node body] (case/split case-node)
        pat (pat/from-case pat-node 0)
        all-pats (params/default-patterns params)]
    (put all-pats target-index pat)
    [:clause all-pats body]))

(defn term/match? [node]
  (and (node/list? node)
       (let [xs (node/list-items node)]
         (and (> (length xs) 0)
              (node/atom= (xs 0) "match")))))

(defn match/target-name [node]
  (cond
    (and (node/atom? node) (token/colon? (node/atom node)))
    (token/strip-colon (node/atom node))

    (node/atom? node)
    (node/atom node)

    true (errorf "invalid match target: %v\nMatch target must be a variable or annotated variable like 'x:Type'" node)))

(defn match/param-index [params name]
  (var idx nil)
  (for i 0 (length params)
    (when (and (nil? idx) (= ((params i) 1) name))
      (set idx i)))
  idx)

(defn clauses/from-body [body params]
  (if (term/match? body)
    (let [xs (node/list-items body)]
      (when (< (length xs) 3)
        (errorf "match form is too short: %v\nMinimum format: (match target (case pattern body) ...)\nYou need a target and at least one case" body))
      (let [target (match/target-name (xs 1))
            target-index (match/param-index params target)]
        (when (nil? target-index)
          (errorf "match target %v is not a function parameter\nMatch expressions can only pattern match on parameters of the enclosing function" target))
        (let [clauses @[]]
          (for i 2 (length xs)
            (array/push clauses (case/desugar (xs i) params target-index)))
          clauses)))
    @[[:clause (params/default-patterns params) body]]))

(defn func/desugar [nodes]
  (let [[name ann consumed] (decl/parse-name-and-ann nodes)
        tail (slice nodes consumed (length nodes))]
    (when (zero? (length tail))
      (errorf "def %v missing body\nExpected format: (def name: Type = expression)\nFunction definitions require a body after the type annotation" name))
    (let [body (tail 0)
          [params result] (term/split-pi ann)
          clauses (clauses/from-body body params)]
      [:decl/func name params result clauses])))

(defn decl/desugar [form]
  (let [norm (p/norm/layout form)]
    (if (node/list? norm)
      (let [xs (node/list-items norm)]
        (when (zero? (length xs))
          (errorf "empty top-level form %v\nTop-level forms cannot be empty lists ()" norm))
        (when (not (node/atom? (xs 0)))
          (errorf "top-level form must start with atom (keyword): %v\nTop-level forms should start with 'data' or 'def'" norm))
        (let [head (node/atom (xs 0))
              rest (slice xs 1 (length xs))]
          (match head
            "data" (data/desugar rest)
            "def" (func/desugar rest)
            _ (errorf "unsupported top-level form: %v\nSupported top-level forms:\n  (data ...)\n  (def ...)\n  (import ...)\n  (export ...)" head))))
      (errorf "top-level form must be a list (s-expression): %v\nAll top-level forms must be properly parenthesized" norm))))

(defn desugar/program [forms]
  (map decl/desugar forms))

(def exports
  {:desugar/program desugar/program
   :decl/desugar decl/desugar
   :term/split-pi term/split-pi
   :term/as-head-app term/as-head-app
   :term/build-forall term/build-forall
   :term/build-data-app term/build-data-app
   :term/forall? term/forall?
   :term/arrow? term/arrow?})
