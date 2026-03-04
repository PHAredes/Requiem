#!/usr/bin/env janet

(import ./parser :as p)

(defn node/atom? [node]
  (and (tuple? node) (= (node 0) :atom)))

(defn node/list? [node]
  (and (tuple? node) (= (node 0) :list)))

(defn node/atom [node]
  (if (node/atom? node)
    (node 1)
    (errorf "expected atom node, but got %v\nExpected format: [:atom value]\nThis is an internal lowering error" node)))

(defn node/list-items [node]
  (if (node/list? node)
    (node 1)
    (errorf "expected list node, but got %v\nExpected format: [:list items...]\nThis is an internal lowering error" node)))

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

(defn find-index [pred xs]
  (defn find-iter [i xs]
    (if (empty? xs)
      nil
      (if (pred (first xs))
        i
        (find-iter (+ i 1) (slice xs 1)))))
  (find-iter 0 xs))

(defn term/split-pi [node]
  (defn split-loop [cur index binders]
    (cond
      (term/forall? cur)
      (let [[bs body] (term/unpack-forall cur)]
        (split-loop body index (reduce |(array/push $0 $1) binders bs)))

      (term/arrow? cur)
      (let [[dom cod] (term/unpack-arrow cur)
            name (string "_arg" index)]
        (split-loop cod (+ index 1) (array/push binders [:bind name dom])))

      true
      [binders cur]))
  (split-loop node 0 @[]))

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
    (errorf "unknown pattern: %v\nSupported patterns: var, con, and impossible.\nThis is an internal lowering error" pat)))

(defn term/build-data-app [name args]
  (if (zero? (length args))
    [:atom name]
    (let [xs @[]]
      (array/push xs [:atom name])
      (each a args (array/push xs a))
      [:list xs])))

(defn term/build-forall [binders body]
  (defn fold-binders [acc binder]
    (let [name (if (>= (length binder) 2) (binder 1) "_")
          ty (if (>= (length binder) 3) (binder 2) [:atom "Type"])
          binder-node [:list @[(node/atom/new (string name ":")) ty]]]
      [:list @[(node/atom/new "forall") binder-node (node/atom/new ".") acc]]))
  (reduce fold-binders body (reverse binders)))

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

(defn decl/parse-telescope-head [nodes kind]
  (when (and (> (length nodes) 0)
             (node/atom? (nodes 0))
             (not (token/colon? (node/atom (nodes 0)))))
    (let [name (node/atom (nodes 0))
          n (length nodes)]
      (defn collect-params [i params]
        (cond
          (and (< i n) (bind/single-spec? (nodes i)))
          (collect-params (+ i 1) (array/push params (bind/from-node (nodes i))))
          
          (and (< i n) (node/atom= (nodes i) ":"))
          (do
            (when (>= (+ i 1) n)
              (errorf "%v %v is missing result sort/type after ':'" kind name))
            [name params (nodes (+ i 1)) (+ i 2)])
          
          true nil))
      (collect-params 1 @[]))))

(defn data/parse-head [nodes]
  # Handle the case where first node is "data" keyword (from selector syntax)
  (if (and (> (length nodes) 0) 
           (node/atom? (nodes 0)) 
           (= (node/atom (nodes 0)) "data"))
    (let [[name params sort consumed] (data/parse-head (slice nodes 1 (length nodes)))]
      [name params sort (+ consumed 1)])
    (if-let [tel (decl/parse-telescope-head nodes "data")]
      tel
      (let [[name ann consumed] (decl/parse-name-and-ann nodes)
            [params sort] (term/split-pi ann)]
        [name params sort consumed]))))

(defn func/parse-head [nodes]
  (if-let [tel (decl/parse-telescope-head nodes "def")]
    tel
    (let [[name ann consumed] (decl/parse-name-and-ann nodes)
          [params result] (term/split-pi ann)]
      [name params result consumed])))

(defn clause/pipe? [node]
  (and (node/list? node)
       (let [xs (node/list-items node)]
         (and (> (length xs) 0)
              (node/atom= (xs 0) "|")))))

(defn clause/eq-index [xs start]
  (defn find-eq-iter [i xs]
    (when (not (empty? xs))
      (if (node/atom= (first xs) "=")
        i
        (find-eq-iter (+ i 1) (slice xs 1)))))
  (find-eq-iter start (slice xs start)))

(defn clause/body-from [xs eq-index kind]
  (let [rest (slice xs (+ eq-index 1) (length xs))]
    (when (zero? (length rest))
      (errorf "%v clause is missing a right-hand side after '='" kind))
    (if (= (length rest) 1)
      (rest 0)
      [:list rest])))

(defn params/default-selector-terms [params]
  (let [out @[]]
    (each p params
      (array/push out [:atom (p 1)]))
    out))

(defn ctor/arg->binder [arg i]
  (if (bind/single-spec? arg)
    (bind/from-node arg)
    [:bind (string "_arg" i) arg]))

(defn ctor/args->binders [args]
  (let [out @[]]
    (for i 0 (length args)
      (array/push out (ctor/arg->binder (args i) i)))
    out))

(defn args/simple-return? [args data-params]
  (and (= (length args) (length data-params))
       (let [n (length args)]
         (defn check-index [i]
           (if (= i n)
             true
             (let [a (args i)
                   p (data-params i)]
               (and (node/atom? a)
                    (= (node/atom a) (p 1))
                    (check-index (+ i 1))))))
         (check-index 0))))

(defn ctor/lower-indexed [data-name data-params name ctor-binders ret-args]
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
            [:ctor name pat-binders patterns ctor-params encoded]))))))

(defn ctor/lower [data-name data-params ctor-node]
  (let [xs (node/list-items ctor-node)]
    (when (not= (length xs) 2)
      (errorf "constructor must be (name type), got: %v\nFormat: (ConstructorName : Type)\nConstructor must have a name and a return type" ctor-node))
    (when (not (node/atom? (xs 0)))
      (errorf "constructor name must be an atom (identifier), got: %v\nConstructor names should be simple identifiers like 'Cons', 'Nil', 'Just', 'Nothing'" (xs 0)))
    (let [name (node/atom (xs 0))
          ctor-type (xs 1)
          [ctor-binders ret] (term/split-pi ctor-type)
          [head0 ret-args0] (term/as-head-app ret)
          [head ret-args]
          (if (nil? head0)
            (if (node/atom? ret)
              (let [atom-name (node/atom ret)]
                (if (= atom-name data-name)
                  [data-name @[]]
                  (errorf "constructor %v must return %v, but got %v\nConstructors must return their parent data type" name data-name ret)))
              (errorf "constructor %v has invalid return type structure: %v\nExpected an application of %v, but got malformed type" name ret data-name))
            [head0 ret-args0])]
      (when (not= head data-name)
        (errorf "constructor %v must return %v, but got %v\nConstructors must return their parent data type" name data-name ret))
      (when (not= (length ret-args) (length data-params))
        (errorf "constructor %v returns wrong number of index arguments: %v\nExpected %d arguments to match data type parameters" name ret (length data-params)))
      (if (args/simple-return? ret-args data-params)
        [:ctor name @[] @[] ctor-binders ctor-type]
        (ctor/lower-indexed data-name data-params name ctor-binders ret-args)))))

(defn ctor/lower-selector-clause [data-name data-params clause-node]
  (let [xs (node/list-items clause-node)]
    (when (or (zero? (length xs)) (not (node/atom= (xs 0) "|")))
      (errorf "invalid data constructor clause: %v\nExpected: (| selectors... = C args...) or (| C args...)" clause-node))
    (let [eq-index (clause/eq-index xs 1)
          selectors (if eq-index
                      (slice xs 1 eq-index)
                      (params/default-selector-terms data-params))
          rhs (if eq-index
                (slice xs (+ eq-index 1) (length xs))
                (slice xs 1 (length xs)))]
      (when (not= (length selectors) (length data-params))
        (errorf "constructor selector arity mismatch in %v\nExpected %d selector(s), got %d"
                clause-node
                (length data-params)
                (length selectors)))
      (when (zero? (length rhs))
        (errorf "constructor clause has no constructor on right-hand side: %v" clause-node))
      (when (not (node/atom? (rhs 0)))
        (errorf "constructor name must be an atom in clause: %v" clause-node))
      (let [ctor-name (node/atom (rhs 0))
            ctor-binders (ctor/args->binders (slice rhs 1 (length rhs)))]
        (let [ret-term (term/build-data-app data-name selectors)
              ctor-type (term/build-forall ctor-binders ret-term)
              synthetic [:list @[(node/atom/new ctor-name) ctor-type]]]
          (ctor/lower data-name data-params synthetic))))))

(defn data/lower [nodes]
  (let [[name params sort consumed] (data/parse-head nodes)
        tail-raw (slice nodes consumed (length nodes))
        tail (if (tuple? tail-raw) (array ;tail-raw) tail-raw)]
    (if (zero? (length tail))
      [:decl/data name params sort @[]]
      (if (clause/pipe? (tail 0))
        (let [ctors @[]]
          (each c tail
            (do
              (when (not (clause/pipe? c))
                (errorf "all constructor clauses must use the '|' form in data %v" name))
              (array/push ctors (ctor/lower-selector-clause name params c))))
          [:decl/data name params sort ctors])
        (let [ctor-block (tail 0)]
          (when (not (node/list? ctor-block))
            (errorf "data %v constructors must be grouped in a list\nExpected: (data Name: Type) ((C1 ...) (C2 ...) ...)" name))
          (let [ctors @[]]
            (each c (node/list-items ctor-block)
              (array/push ctors (ctor/lower name params c)))
            [:decl/data name params sort ctors]))))))

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

(defn params/name-set-prefix [params end-exclusive]
  (let [out @{}]
    (for i 0 end-exclusive
      (put out ((params i) 1) true))
    out))

(defn node/binder [name ty]
  [:list @[(node/atom/new (string name ":")) ty]])

(defn term/build-lam [binders body]
  (if (zero? (length binders))
    body
    (let [spec
          (if (= (length binders) 1)
            (node/binder ((binders 0) 1) ((binders 0) 2))
            [:list (map |(node/binder ($ 1) ($ 2)) binders)])]
      [:list @[(node/atom/new "fn") spec body]])))

(defn term/self-call? [node func-name param-names target-index rec-var]
  (let [[head args] (term/as-head-app node)]
    (and (= head func-name)
         (= (length args) (length param-names))
         (let [n (length args)]
           (defn check-index [i]
             (if (= i n)
               true
               (let [arg (args i)
                     expected (if (= i target-index) rec-var (param-names i))]
                 (and (node/atom? arg)
                      (= (node/atom arg) expected)
                      (check-index (+ i 1))))))
           (check-index 0)))))

(defn term/replace-self-call [node func-name param-names target-index rec-var ih-name]
  (if (term/self-call? node func-name param-names target-index rec-var)
    [:atom ih-name]
    (match node
      [:list xs]
      [:list (map |(term/replace-self-call $ func-name param-names target-index rec-var ih-name) xs)]
      _ node)))

(defn type/returns-data? [ty data-name]
  (let [[head _] (term/as-head-app ty)]
    (= head data-name)))

(defn ctor/case-args [pat ctor-name]
  (match pat
    [:pat/con c args] (if (= c ctor-name) args nil)
    _ nil))

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
  (defn find-param-iter [i params]
    (when (not (empty? params))
      (if (= ((first params) 1) name)
        i
        (find-param-iter (+ i 1) (slice params 1)))))
  (find-param-iter 0 params))

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
        (let [colon-index (find-index |(node/atom= $ ":") rest)]
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

(defn match/cases [xs]
  (let [out @[]]
    (for i 2 (length xs)
      (let [[pat-node body] (case/split (xs i))]
        (array/push out [(pat/from-case pat-node 0) body])))
    out))

(defn match/wildcard-body [entries]
  (defn find-wildcard [entries]
    (when (not (empty? entries))
      (let [e (first entries)]
        (if (and (= ((e 0) 0) :pat/var)
                 (= ((e 0) 1) "_"))
          (e 1)
          (find-wildcard (slice entries 1))))))
  (find-wildcard entries))

(defn match/find-ctor-entry [entries ctor-name]
  (defn find-ctor [entries]
    (when (not (empty? entries))
      (let [e (first entries)]
        (if (ctor/case-args (e 0) ctor-name)
          e
          (find-ctor (slice entries 1))))))
  (find-ctor entries))

(def M/Yes :match/yes)
(def M/No :match/no)
(def M/Stuck :match/stuck)

(defn data/ctor-name-set [data-env]
  (let [known @{}]
    (each data-name (keys data-env)
      (if-let [ctors (get data-env data-name)]
        (each ctor ctors
          (put known (ctor 1) true))))
    known))

(defn subst/lookup [subst x]
  (defn scan [i]
    (if (< i 0)
      nil
      (let [entry (subst i)]
        (if (= (entry 0) x)
          (entry 1)
          (scan (- i 1))))))
  (scan (- (length subst) 1)))

(defn subst/extend [subst x term]
  [;subst [x term]])

(defn selector/head-definitely-ctor? [head ctor-name-set var-name-set]
  (and (has-key? ctor-name-set head)
       (not (has-key? var-name-set head))))

(defn selector/mismatch-status [head ctor-name-set var-name-set]
  (if (selector/head-definitely-ctor? head ctor-name-set var-name-set)
    M/No
    M/Stuck))

(defn selector/merge-step [status subst next-status next-subst]
  (cond
    (= next-status M/No) [M/No next-subst]
    (= next-status M/Stuck) [M/Stuck subst]
    true [status next-subst]))

(defn selector/term-eq-status [lhs rhs ctor-name-set var-name-set]
  (if (= lhs rhs)
    M/Yes
    (let [[lhead largs] (term/as-head-app lhs)
          [rhead rargs] (term/as-head-app rhs)]
      (cond
        (or (nil? lhead) (nil? rhead)) M/Stuck
        (or (not (selector/head-definitely-ctor? lhead ctor-name-set var-name-set))
            (not (selector/head-definitely-ctor? rhead ctor-name-set var-name-set)))
        M/Stuck
        (not= lhead rhead) M/No
        (not= (length largs) (length rargs)) M/No
        true
        (let [n (length largs)]
          (defn walk [i]
            (if (= i n)
              M/Yes
              (let [status (selector/term-eq-status (largs i) (rargs i) ctor-name-set var-name-set)]
                (if (= status M/Yes)
                  (walk (+ i 1))
                  status))))
          (walk 0))))))

(defn selector/match-term [term pat ctor-name-set var-name-set subst]
  (match pat
    [:pat/var x]
    (if (= x "_")
      [M/Yes subst]
      (if-let [bound (subst/lookup subst x)]
        (let [eq-status (selector/term-eq-status bound term ctor-name-set var-name-set)]
          (if (= eq-status M/Yes)
            [M/Yes subst]
            (if (= eq-status M/No)
              [M/No subst]
              [M/Stuck subst])))
        [M/Yes (subst/extend subst x term)]))

    [:pat/con ctor pats]
    (let [[head args] (term/as-head-app term)]
      (cond
        (nil? head) [M/Stuck subst]
        (not (selector/head-definitely-ctor? head ctor-name-set var-name-set)) [M/Stuck subst]
        (not= head ctor) [(selector/mismatch-status head ctor-name-set var-name-set) subst]
        (not= (length args) (length pats)) [M/No subst]
        true
        (let [n (length args)]
          (defn walk [i status subst]
            (if (= i n)
              [status subst]
              (let [[next-status next-subst]
                    (selector/match-term (args i) (pats i) ctor-name-set var-name-set subst)
                    [merged-status merged-subst]
                    (selector/merge-step status subst next-status next-subst)]
                (if (= merged-status M/No)
                  [merged-status merged-subst]
                  (walk (+ i 1) merged-status merged-subst)))))
          (walk 0 M/Yes subst))))

    [:pat/impossible] [M/No subst]

    _ (errorf "invalid selector pattern: %v" pat)))

(defn selector/match-target [target-args selector-pats ctor-name-set var-name-set]
  (if (not= (length target-args) (length selector-pats))
    M/No
    (let [n (length target-args)]
      (defn walk [i status subst]
        (if (= i n)
          status
          (let [[next-status next-subst]
                (selector/match-term (target-args i) (selector-pats i) ctor-name-set var-name-set subst)
                [merged-status merged-subst]
                (selector/merge-step status subst next-status next-subst)]
            (if (= merged-status M/No)
              M/No
              (walk (+ i 1) merged-status merged-subst)))))
      (walk 0 M/Yes @[]))))

(defn match/check-selector-availability [target target-ty ctors target-args data-env var-name-set]
  (let [ctor-name-set (data/ctor-name-set data-env)]
    (each ctor ctors
      (let [status (selector/match-target target-args (ctor 3) ctor-name-set var-name-set)]
        (when (= status M/Stuck)
          (errorf "ambiguous selector matching for constructor %v on match target %v: %v\nTarget type: %v\nConstructor selectors: %v\nSelector matching got stuck (neither definitely matches nor definitely mismatches). Refine the target indices before matching."
                  (ctor 1)
                  target
                  target-args
                  target-ty
                  (ctor 3)))))
    true))

(defn type/ctor-name-set [ty data-env]
  (let [[head _] (term/as-head-app ty)
        out @{}]
    (if-let [ctors (get data-env head)]
      (do
        (each c ctors
          (put out (c 1) true))
        out)
      out)))

(defn pat/from-clause [node depth ctor-set]
  (match node
    [:atom tok]
    (cond
      (= tok "impossible") [:pat/impossible]
      (= tok "_") [:pat/var "_"]
      (and (= depth 0) (has-key? ctor-set tok)) [:pat/con tok @[]]
      true [:pat/var tok])

    [:list xs]
    (if (and (> (length xs) 0) (node/atom? (xs 0)))
      (let [head (node/atom (xs 0))
            args @[]]
        (for i 1 (length xs)
          (array/push args (pat/from-clause (xs i) (+ depth 1) ctor-set)))
        [:pat/con head args])
      (errorf "invalid function clause pattern: %v" node))

    _
    (errorf "invalid function clause pattern: %v" node)))

(defn func/lower-selector-clause [clause-node params data-env]
  (let [xs (node/list-items clause-node)]
    (when (or (zero? (length xs)) (not (node/atom= (xs 0) "|")))
      (errorf "invalid function clause: %v\nExpected: (| p1 ... pn = body)" clause-node))
    (if-let [eq-index (clause/eq-index xs 1)]
      (let [pat-nodes (slice xs 1 eq-index)
            body (clause/body-from xs eq-index "function")]
        (when (> (length pat-nodes) (length params))
          (errorf "function clause arity mismatch in %v\nExpected %d pattern(s), got %d"
                  clause-node
                  (length params)
                  (length pat-nodes)))
        (let [patterns @[]
              consumed (length pat-nodes)
              rest-params (slice params consumed (length params))
              wrapped-body (term/build-lam rest-params body)]
          (for i 0 (length pat-nodes)
            (let [expected-ty ((params i) 2)
                  ctor-set (type/ctor-name-set expected-ty data-env)]
              (array/push patterns (pat/from-clause (pat-nodes i) 0 ctor-set))))
          (for i consumed (length params)
            (array/push patterns [:pat/var "_"]))
          [:clause patterns wrapped-body]))
      (errorf "function clause is missing '=': %v" clause-node))))

(defn term/build-elim-branch [data-name ctor func-name param-names target-index result case-entry wildcard-body]
  (let [ctor-name (ctor 1)
        ctor-params (ctor 4)
        pat-args (if case-entry (ctor/case-args (case-entry 0) ctor-name) nil)
        body0 (if case-entry (case-entry 1)
                (if wildcard-body wildcard-body
                  (errorf "missing match case for constructor %v" ctor-name)))]
    (when (and pat-args (not= (length pat-args) (length ctor-params)))
      (errorf "constructor pattern %v has %d arg(s), expected %d"
              ctor-name
              (length pat-args)
              (length ctor-params)))
    (let [branch-binders @[]
          rec-map @{}]
      (for i 0 (length ctor-params)
        (let [b (ctor-params i)
              p (if (and pat-args (< i (length pat-args))) (pat-args i) nil)
              name
              (if (and p (= (p 0) :pat/var) (not= (p 1) "_"))
                (p 1)
                (string (b 1) "_" i))
              ty (b 2)]
          (array/push branch-binders [:bind name ty])
          (when (type/returns-data? ty data-name)
            (let [ih-name (string "ih-" name)]
              (put rec-map name ih-name)
              (array/push branch-binders [:bind ih-name result])))))
      (let [body
            (reduce (fn [acc rec-var]
                      (let [ih-name (get rec-map rec-var)]
                        (term/replace-self-call acc func-name param-names target-index rec-var ih-name)))
                    body0
                    (keys rec-map))]
        (term/build-lam branch-binders body)))))

(defn match/lower-elim [func-name params result body data-env]
  (let [xs (node/list-items body)]
    (when (< (length xs) 3)
      (errorf "match form is too short: %v\nMinimum format: (match target (case pattern body) ...)\nYou need a target and at least one case" body))
    (let [target (match/target-name (xs 1))
          target-index (match/param-index params target)]
      (when (nil? target-index)
        (errorf "match target %v is not a function parameter\nMatch expressions can only pattern match on parameters of the enclosing function" target))
      (let [target-ty ((params target-index) 2)
            [data-name target-args] (term/as-head-app target-ty)]
        (when (nil? data-name)
          (errorf "match target %v must have an inductive type head, got: %v" target target-ty))
        (if-let [ctors (get data-env data-name)]
          (let [param-name-set (params/name-set-prefix params target-index)
                _ (match/check-selector-availability target target-ty ctors target-args data-env param-name-set)
                param-names (map |($ 1) params)
                entries (match/cases xs)
                wildcard-body (match/wildcard-body entries)
                motive (term/build-lam @[[ :bind target target-ty ]] result)
                branches @[]]
            (each ctor ctors
              (array/push branches
                          (term/build-elim-branch data-name
                                                  ctor
                                                  func-name
                                                  param-names
                                                  target-index
                                                  result
                                                  (match/find-ctor-entry entries (ctor 1))
                                                  wildcard-body)))
            (let [app @[(node/atom/new (string data-name "-elim")) motive]]
              (each b branches (array/push app b))
              (array/push app [:atom target])
              [:list app]))
          (errorf "unknown data type %v in match target %v\nEnsure the data declaration appears before this function" data-name target))))))

(defn func/lower [nodes data-env]
  (let [[name params result consumed] (func/parse-head nodes)
        tail (slice nodes consumed (length nodes))]
    (when (zero? (length tail))
      (errorf "def %v missing body\nExpected format: (def name: Type = expression)\nFunction definitions require a body after the type annotation" name))
    (if (clause/pipe? (tail 0))
      (let [clauses @[]]
        (each c tail
          (do
            (when (not (clause/pipe? c))
              (errorf "all clauses in def %v must use the '|' form" name))
            (array/push clauses (func/lower-selector-clause c params data-env))))
        [:decl/func name params result clauses])
      (let [body (tail 0)
            lowered-body (if (term/match? body)
                           (match/lower-elim name params result body data-env)
                           body)
            clauses @[[:clause (params/default-patterns params) lowered-body]]]
        [:decl/func name params result clauses]))))

(defn decl/lower [form data-env]
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
            "data" (data/lower rest)
            "def" (func/lower rest data-env)
            _ (errorf "unsupported top-level form: %v\nSupported top-level forms:\n  (data ...)\n  (def ...)\n  (import ...)\n  (export ...)" head))))
      (errorf "top-level form must be a list (s-expression): %v\nAll top-level forms must be properly parenthesized" norm))))

(defn lower/program [forms]
  (let [decls @[]
        data-env @{}]
    (each form forms
      (let [decl (decl/lower form data-env)]
        (array/push decls decl)
        (when (= (decl 0) :decl/data)
          (put data-env (decl 1) (decl 4)))))
    decls))

(def exports
  {:lower/program lower/program
   :decl/lower decl/lower
   :bind/from-node bind/from-node
   :binders/from-spec binders/from-spec
   :term/split-pi term/split-pi
   :term/as-head-app term/as-head-app
   :term/build-forall term/build-forall
   :term/build-data-app term/build-data-app
   :term/forall? term/forall?
   :term/arrow? term/arrow?})
