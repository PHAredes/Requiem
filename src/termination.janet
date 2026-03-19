#!/usr/bin/env janet

(defn sc/relation-rank [rel]
  (case rel
    :lt 2
    :eq 1
    0))

(defn sc/relation-max [r1 r2]
  (if (> (sc/relation-rank r1) (sc/relation-rank r2)) r1 r2))

(defn sc/relation-dominates? [r1 r2]
  (>= (sc/relation-rank r1) (sc/relation-rank r2)))

(defn sc/relation-mul [r1 r2]
  (match [r1 r2]
    [:lt :lt] :lt
    [:lt :eq] :lt
    [:eq :lt] :lt
    [:eq :eq] :eq
    _ :unknown))

(defn sc/matrix [rows cols]
  (let [m @[]]
    (for i 0 rows
      (let [row @[]]
        (for j 0 cols
          (array/push row :unknown))
        (array/push m row)))
    m))

(defn sc/matrix-rows [m] (length m))

(defn sc/matrix-cols [m]
  (if (zero? (length m)) 0 (length (m 0))))

(defn sc/matrix-set [m row col rel]
  (put (m row) col rel)
  m)

(defn sc/matrix-get [m row col]
  (get-in m [row col] :unknown))

(defn sc/matrix-diagonal-has-lt? [m]
  (let [dim (min (sc/matrix-rows m) (sc/matrix-cols m))]
    (var i 0)
    (var found false)
    (while (< i dim)
      (when (= (sc/matrix-get m i i) :lt)
        (set found true)
        (break))
      (++ i))
    found))

(defn sc/matrix-diagonal [m]
  (let [dim (min (sc/matrix-rows m) (sc/matrix-cols m))
        out @[]]
    (for i 0 dim
      (array/push out (sc/matrix-get m i i)))
    out))

(defn sc/matrix-dominates? [m1 m2]
  (and (= (sc/matrix-rows m1) (sc/matrix-rows m2))
       (= (sc/matrix-cols m1) (sc/matrix-cols m2))
       (let [rows (sc/matrix-rows m1)
             cols (sc/matrix-cols m1)]
         (var ok true)
         (for i 0 rows
           (for j 0 cols
             (when (not (sc/relation-dominates? (sc/matrix-get m1 i j)
                                                (sc/matrix-get m2 i j)))
               (set ok false))))
         ok)))

(defn sc/compose [m1 m2]
  (let [rows1 (sc/matrix-rows m1)
        cols1 (sc/matrix-cols m1)
        rows2 (sc/matrix-rows m2)
        cols2 (sc/matrix-cols m2)]
    (when (not= rows1 cols2)
      (errorf "incompatible call matrices: %d x %d then %d x %d"
              rows1 cols1 rows2 cols2))
    (let [result (sc/matrix rows2 cols1)]
      (for i 0 rows2
        (for j 0 cols1
          (var best :unknown)
          (for k 0 cols2
            (set best
                 (sc/relation-max best
                                  (sc/relation-mul (sc/matrix-get m2 i k)
                                                   (sc/matrix-get m1 k j)))))
          (sc/matrix-set result i j best)))
      result)))

(defn sc/filter-incomparable [matrices matrix]
  (var i 0)
  (var kept @[])
  (while (< i (length matrices))
    (let [existing (matrices i)]
      (cond
        (sc/matrix-dominates? (existing :matrix) (matrix :matrix))
        (do
          (set kept nil)
          (set i (length matrices)))

        (sc/matrix-dominates? (matrix :matrix) (existing :matrix))
        nil

        true
        (array/push kept existing)))
    (++ i))
  (if kept
    (do
      (array/push kept matrix)
      kept)
    matrices))

(defn sc/base-proof [label callee]
  [:sc/base-proof label callee])

(defn sc/compose-proof [p1 p2]
  [:sc/compose-proof p1 p2])

(defn sc/proof->path [proof]
  (match proof
    [:sc/base-proof label callee] @[label callee]
    [:sc/compose-proof p1 p2] (array/concat (sc/proof->path p1) (sc/proof->path p2))
    _ @[]))

(defn sc/call [from to matrix proof]
  {:from from
    :to to
    :matrix matrix
    :proof proof})

(defn sc/call-compose [c1 c2]
  (sc/call (c1 :from)
           (c2 :to)
            (sc/compose (c1 :matrix) (c2 :matrix))
            (sc/compose-proof (c1 :proof) (c2 :proof))))

(defn sc/graph []
  {:arities @{}
   :edges @{}})

(defn sc/register [g name arity]
  (put (g :arities) name arity)
  (when (nil? (get (g :edges) name))
    (put (g :edges) name @{}))
  g)

(defn sc/matrices [g from to]
  (get (get (g :edges) from @{}) to @[]))

(defn sc/add-call [g from to matrix]
  (let [from-edges (get (g :edges) from @{})
        old (get from-edges to @[])
        next (sc/filter-incomparable old matrix)]
    (put from-edges to next)
    (put (g :edges) from from-edges)
    (not= old next)))

(defn sc/edge-targets [g from]
  (keys (get (g :edges) from @{})))

(defn sc/reverse-edges [g]
  (let [rev @{}]
    (eachp [name _] (g :arities)
      (put rev name @[]))
    (eachp [from tos] (g :edges)
      (eachp [to calls] tos
        (when (> (length calls) 0)
          (let [targets (get rev to @[])]
            (array/push targets from)
            (put rev to targets)))))
    rev))

(defn sc/sccs [g]
  (var visited @{})
  (let [order @[]
        rev (sc/reverse-edges g)
        comps @[]]
    (defn visit [node]
      (unless (get visited node)
        (put visited node true)
        (each next (sc/edge-targets g node)
          (visit next))
        (array/push order node)))
    (defn visit-rev [node comp]
      (unless (get visited node)
        (put visited node true)
        (array/push comp node)
        (each next (get rev node @[])
          (visit-rev next comp))))
    (eachp [name _] (g :arities)
      (visit name))
    (set visited @{})
    (while (> (length order) 0)
      (let [node (array/pop order)]
        (unless (get visited node)
          (let [comp @[]]
            (visit-rev node comp)
            (array/push comps comp)))))
    comps))

(defn sc/component-recursive? [g comp]
  (or (> (length comp) 1)
      (and (= (length comp) 1)
           (> (length (sc/matrices g (comp 0) (comp 0))) 0))))

(defn sc/matrix->string [m]
  (string/join
    (map (fn [row]
           (string/join
             (map (fn [rel]
                    (case rel
                      :lt "<"
                      :eq "="
                      "?"))
                  row)
             " "))
         m)
    " | "))

(defn sc/relation->string [rel]
  (case rel
    :lt "<"
    :eq "="
    "?"))

(defn sc/diagonal->string [m]
  (let [diag (sc/matrix-diagonal m)]
    (if (zero? (length diag))
      "[]"
      (string "["
              (string/join (map sc/relation->string diag) " ")
              "]"))))

(defn sc/problem-summary [problem]
  (let [path (string/join (sc/proof->path (problem :proof)) " -> ")]
    (string/format "%s via %s [%s] diag=%s"
                    (problem :name)
                    path
                    (sc/matrix->string (problem :matrix))
                    (sc/diagonal->string (problem :matrix)))))

(defn sc/problem-report [problems]
  (string/join (map sc/problem-summary problems) "; "))

(var sc/compare nil)

(defn sc/immediate-subterms [tm]
  (match tm
    [:pair l r] @[l r]
    [:fst p] @[p]
    [:snd p] @[p]
    [:fst [:pair l _]] @[l]
    [:snd [:pair _ r]] @[r]
    _ @[]))

(defn sc/best-subterm-relation [term pat]
  (let [subs (sc/immediate-subterms term)]
    (reduce (fn [best subterm]
              (let [rel (sc/compare subterm pat)]
                (if (= rel :unknown)
                  best
                  (sc/relation-max best :lt))))
            :unknown
            subs)))

(defn sc/spine [tm]
  (var cur tm)
  (var rev-args @[])
  (while (and (tuple? cur) (= (cur 0) :app))
    (array/push rev-args (cur 2))
    (set cur (cur 1)))
  [cur (reverse rev-args)])

(defn sc/head-of [tm]
  (match tm
    [:app f _] (sc/head-of f)
    [:fst p] (sc/head-of p)
    [:snd p] (sc/head-of p)
    _ tm))

(defn sc/combine-subrelations [rels]
  (reduce sc/relation-mul :eq rels))

(defn sc/compare-con-args [args pats]
  (if (not= (length args) (length pats))
    :unknown
    (let [rels @[]]
      (for i 0 (length args)
        (array/push rels (sc/compare (args i) (pats i))))
      (sc/combine-subrelations rels))))

(set sc/compare
     (fn [term pat]
       (match pat
           [:pat/var x]
           (cond
             (= x "_") :unknown
             (= term [:var x]) :eq
             (not= :unknown (sc/best-subterm-relation term pat))
             :lt
             true :unknown)

         [:pat/con ctor args]
          (let [[head term-args] (sc/spine term)]
            (if (and (tuple? head)
                    (= (head 0) :var)
                    (= (head 1) ctor)
                    (= (length term-args) (length args)))
             (sc/compare-con-args term-args args)
             (reduce (fn [best subpat]
                       (let [subrel (sc/compare term subpat)]
                         (if (= subrel :unknown)
                            best
                            (sc/relation-max best :lt))))
                      :unknown
                      (array/concat args (sc/immediate-subterms term)))))

         _ :unknown)))

(defn sc/call-matrix [caller-patterns call-args callee-arity]
  (let [matrix (sc/matrix callee-arity (length caller-patterns))
        used-args (slice call-args 0 callee-arity)]
    (for i 0 callee-arity
      (for j 0 (length caller-patterns)
        (sc/matrix-set matrix i j (sc/compare (used-args i) (caller-patterns j)))))
    matrix))

(defn sc/call-head [tm target-arities]
  (let [[head args] (sc/spine tm)]
    (match head
      [:var name]
      (if-let [arity (get target-arities name)]
        (when (>= (length args) arity)
          [name (slice args 0 arity)])
        nil)
      _ nil)))

(defn sc/maybe-record-call [calls target-arities caller-patterns tm]
  (when-let [[callee args] (sc/call-head tm target-arities)]
    (array/push calls
                [callee (sc/call-matrix caller-patterns
                                        args
                                        (get target-arities callee))])))

(defn sc/find-calls [target-arities caller-patterns term]
  (let [calls @[]]
    (defn walk [tm]
      (match tm
        [:app f x]
        (do
          (sc/maybe-record-call calls target-arities caller-patterns tm)
          (walk f)
          (walk x))

        [:var _]
        (sc/maybe-record-call calls target-arities caller-patterns tm)

        [:lam body] (walk (body [:var (gensym)]))
        [:t-pi A B] (do (walk A) (walk (B [:var (gensym)])))
        [:t-sigma A B] (do (walk A) (walk (B [:var (gensym)])))
        [:pair l r] (do (walk l) (walk r))
        [:fst p] (do (sc/maybe-record-call calls target-arities caller-patterns tm)
                     (walk p))
        [:snd p] (do (sc/maybe-record-call calls target-arities caller-patterns tm)
                     (walk p))
        [:t-id A x y] (do (walk A) (walk x) (walk y))
        [:t-refl x] (walk x)
        [:t-J A x P d y p] (do (walk A) (walk x) (walk P) (walk d) (walk y) (walk p))
        _ nil))
    (walk term)
    calls))

(defn sc/clause-proof [name clause-index callee]
  (sc/base-proof (string/format "%s[%d]" name (+ clause-index 1)) callee))

(defn sc/header-proof [name section callee]
  (sc/base-proof (string/format "%s:%s" name section) callee))

(defn sc/header-patterns [params]
  (reduce (fn [acc param]
            (match param
              [:bind name _]
              (do
                (array/push acc [:pat/var name])
                acc)
              _
              (do
                (array/push acc [:pat/var "_"])
                acc)))
          @[]
          params))

(defn sc/add-clause-call [g name clause-index callee matrix]
  (sc/add-call g
               name
               callee
               (sc/call name
                        callee
                        matrix
                        (sc/clause-proof name clause-index callee))))

(defn sc/add-header-call [g name section callee matrix]
  (sc/add-call g
               name
               callee
               (sc/call name
                        callee
                        matrix
                        (sc/header-proof name section callee))))

(defn sc/build-graph [defs]
  (let [g (sc/graph)
        target-arities @{}]
    (each def defs
      (match def
        [:core/func name params _ _ _]
        (do
          (put target-arities name (length params))
          (sc/register g name (length params)))
        _ nil))
    (each def defs
      (match def
        [:core/func name params result core-type clauses]
        (let [header-pats (sc/header-patterns params)]
          (each [callee matrix] (sc/find-calls target-arities header-pats core-type)
            (sc/add-header-call g name "type" callee matrix))
          (each [callee matrix] (sc/find-calls target-arities header-pats result)
            (sc/add-header-call g name "result" callee matrix))
          (for clause-index 0 (length clauses)
            (let [clause (clauses clause-index)]
              (match clause
                [:core/clause patterns body]
                (each [callee matrix] (sc/find-calls target-arities patterns body)
                  (sc/add-clause-call g name clause-index callee matrix))
                _ nil))))
        _ nil))
    g))

(defn sc/idempotent-matrix? [m]
  (sc/matrix-dominates? m (sc/compose m m)))

(defn sc/recursive-components [g]
  (reduce (fn [acc comp]
            (if (sc/component-recursive? g comp)
              (do
                (array/push acc comp)
                acc)
              acc))
          @[]
          (sc/sccs g)))

(defn sc/complete-component [g comp]
  (for k 0 (length comp)
    (let [mid (comp k)]
      (for i 0 (length comp)
        (let [from (comp i)
              left (array/slice (sc/matrices g from mid))]
          (when (> (length left) 0)
            (for j 0 (length comp)
              (let [to (comp j)
                    right (array/slice (sc/matrices g mid to))]
                (when (> (length right) 0)
                  (each c1 left
                    (each c2 right
                      (sc/add-call g from to (sc/call-compose c1 c2)))))))))))))

(defn sc/problems [g comps]
  (let [out @[]]
    (each comp comps
      (each name comp
        (each call (sc/matrices g name name)
          (when (and (sc/idempotent-matrix? (call :matrix))
                     (not (sc/matrix-diagonal-has-lt? (call :matrix))))
            (array/push out {:name name
                             :component comp
                             :matrix (call :matrix)
                             :proof (call :proof)})))))
    out))

(defn sc/check* [defs]
  (let [g (sc/build-graph defs)
        comps (sc/recursive-components g)
        _ (each comp comps
            (sc/complete-component g comp))
        problems (sc/problems g comps)]
    {:ok (zero? (length problems))
     :m :sct
     :graph g
     :problems problems}))

(defn sc/check-graph* [arities calls]
  (let [g (sc/graph)]
    (eachp [name arity] arities
      (sc/register g name arity))
    (each call calls
      (sc/add-call g (call :from) (call :to) call))
    (let [comps (sc/recursive-components g)
          _ (each comp comps
              (sc/complete-component g comp))
          problems (sc/problems g comps)]
      {:ok (zero? (length problems))
       :m :sct
       :graph g
       :problems problems})))

(defn sct [f-def]
  (match f-def
    [:core/func _ _ _ _ _] (sc/check* @[f-def])
    _ {:ok true :m :sct :graph (sc/graph) :problems @[]}))

(defn sct* [f-defs]
  (sc/check* f-defs))

(defn cpo [f]
  {:ok true :m :cpo :subject f})

(defn cpo* [fs]
  {:ok true :m :cpo :subject fs})

(def exports
  {:sct sct
   :sct* sct*
   :cpo cpo
   :cpo* cpo*
   :sc/call sc/call
   :sc/check-graph* sc/check-graph*
    :sc/compare sc/compare
    :sc/compose sc/compose
    :sc/diagonal->string sc/diagonal->string
    :sc/find-calls sc/find-calls
    :sc/filter-incomparable sc/filter-incomparable
    :sc/matrix sc/matrix
    :sc/matrix-get sc/matrix-get
    :sc/matrix-diagonal-has-lt? sc/matrix-diagonal-has-lt?
    :sc/matrix-dominates? sc/matrix-dominates?
    :sc/matrix-set sc/matrix-set
    :sc/matrix->string sc/matrix->string
   :sc/problem-report sc/problem-report
   :check-size-change sct
   :check-mutual-size-change sct*
   :check-cpo cpo
   :check-mutual-cpo cpo*})

exports
