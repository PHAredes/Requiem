#!/usr/bin/env janet

(defn make [deps]
  (let [T/Type (deps :T/Type)
        T/Pi (deps :T/Pi)
        T/Sigma (deps :T/Sigma)
        T/Refl (deps :T/Refl)
        T/Pair (deps :T/Pair)
        T/Neutral (deps :T/Neutral)
        ty/type (deps :ty/type)
        ty/pi (deps :ty/pi)
        eq-type (deps :eq-type)
        ty/id (deps :ty/id)
        lvl/<= (deps :lvl/<=)
        lvl/max (deps :lvl/max)
        lvl/succ (deps :lvl/succ)
        sem-eq (deps :sem-eq)
        eval (deps :eval)
        lower (deps :lower)
        raise (deps :raise)
        ctx/add (deps :ctx/add)
        ctx/lookup (deps :ctx/lookup)
        ne/app (deps :ne/app)
        ne/var (deps :ne/var)
        ne/fst (deps :ne/fst)
        print/sem (deps :print/sem)
        print/tm (deps :print/tm)
        meta (deps :meta)
        constraints (deps :constraints)
        unify (deps :unify)
        goals (meta :goals)
        goals/reset! (meta :reset!)
        goals/set-collect! (meta :set-collect!)
        goals/collect? (meta :collect?)]

    (var infer nil)
    (var check nil)
    (var subtype nil)

    (defn with-fresh-sem [A k]
      (let [fresh (gensym)
            arg-sem (raise A (ne/var fresh))]
        (k fresh arg-sem)))

    (defn with-bound [Γ A k]
      (with-fresh-sem A
        (fn [fresh arg-sem]
          (k fresh arg-sem (ctx/add Γ fresh A)))))

    (defn subtype/pi [A1 B1 A2 B2]
      (and (subtype A2 A1)
            (with-fresh-sem A2
              (fn [_fresh arg-sem]
                (subtype (B1 arg-sem) (B2 arg-sem))))))

    (defn subtype/sigma [A1 B1 A2 B2]
      (and (subtype A1 A2)
            (with-fresh-sem A1
              (fn [_fresh arg-sem]
                (subtype (B1 arg-sem) (B2 arg-sem))))))

    (defn tag-of [x]
      (if (tuple? x) (get x 0) 0))

    (defn sem/neutral [ne]
      [T/Neutral ne])

    (defn fst-sem [p-sem]
      (let [tag (tag-of p-sem)]
        (cond
          (= tag T/Pair) (get p-sem 1)
          (= tag T/Neutral) (sem/neutral (ne/fst (get p-sem 1)))
          true (errorf "fst expected pair semantics, got: %s" (print/sem p-sem)))))

    (defn j/motive-app-term [P y p]
      (if (function? P)
        (P y p)
        [:app [:app P y] p]))

    (defn sem/apply [f-ty f-sem arg-sem]
      (let [tag (tag-of f-ty)]
        (if (= tag T/Pi)
          (let [[_tag A B] f-ty
                B-sem (B arg-sem)
                ftag (tag-of f-sem)]
            {:ty B-sem
             :sem (cond
                    (= ftag T/Neutral)
                    (raise B-sem (ne/app (get f-sem 1) (lower A arg-sem)))

                    (function? f-sem)
                    (f-sem arg-sem)

                    true
                    (errorf "expected function semantics for application, got: %v" f-sem))})
          (errorf "expected Pi type for semantic application, got: %s"
                  (print/sem f-ty)))))

    (defn j/motive-app-typed [P-ty P-sem yv pv]
      (let [step1 (sem/apply P-ty P-sem yv)
            step2 (sem/apply (step1 :ty) (step1 :sem) pv)]
        (step2 :sem)))

    (set subtype
         (fn [A B]
            "Semantic subtyping with cumulative universes and Pi/Sigma variance."
            (let [tagA (tag-of A)
                  tagB (tag-of B)]
              (cond
                (and (= tagA T/Type) (= tagB T/Type))
                (lvl/<= (get A 1) (get B 1))

               (and (= tagA T/Pi) (= tagB T/Pi))
               (let [[_tag1 A1 B1] A
                      [_tag2 A2 B2] B]
                 (subtype/pi A1 B1 A2 B2))

               (and (= tagA T/Sigma) (= tagB T/Sigma))
               (let [[_tag1 A1 B1] A
                      [_tag2 A2 B2] B]
                 (subtype/sigma A1 B1 A2 B2))

                true
                (sem-eq eq-type A B)))))

    (defn check-univ [Γ A]
      "Check that A is a universe and return its level"
      (let [UA (infer Γ A)
            tag (tag-of UA)]
        (if (= tag T/Type)
          (get UA 1)
          (errorf "expected a universe Type (Type_l), but got: %s\nTip: Make sure your type expression evaluates to a Type, e.g., Type 0, Type 1, etc."
                  (print/sem UA)))))

    (defn infer-binder [Γ A B]
      (let [lvlA (check-univ Γ A)
            A-sem (eval Γ A)
            lvlB (with-bound Γ A-sem
                   (fn [fresh _arg-sem Γ2]
                     (check-univ Γ2 (B [:var fresh]))))]
        (ty/type (lvl/max lvlA lvlB))))

    (set infer
         (fn [Γ t]
           "Infer the type of term t in context Γ (returns semantic type)"
           (let [tag (if (tuple? t) (get t 0) nil)]
             (cond
               (= tag :var)
               (let [x (get t 1)]
                 (if (or (string? x) (symbol? x))
                   (ctx/lookup Γ x)
                   (errorf "variable must be a string or symbol, but got: %v\nVariable names should be like 'x', 'y', 'myVar', etc." x)))

               (= tag :type)
               (ty/type (lvl/succ (get t 1)))

               (= tag :lam)
               (errorf "cannot infer type of lambda expression %s\nLambda types require annotation because they have principal types.\nSuggestion: Annotate with a Pi type: (λx. body) : (Πx:A. B)"
                       (print/tm t))

               (= tag :hole)
               ((meta :error-infer) (get t 1) Γ)

               (= tag :app)
               (let [f (get t 1)
                     x (get t 2)
                     fA (infer Γ f)
                     ftag (tag-of fA)]
                 (if (= ftag T/Pi)
                   (let [[_tag A B] fA]
                     (do (check Γ x A)
                         (B (eval Γ x))))
                   (errorf "cannot apply function - expected a Pi type (Πx:A. B), but got: %s\nTip: Make sure the function has a proper Pi type annotation or can be inferred as one."
                           (print/sem fA))))

               (= tag :t-pi)
               (infer-binder Γ (get t 1) (get t 2))

               (= tag :t-sigma)
               (infer-binder Γ (get t 1) (get t 2))

               (= tag :fst)
               (let [p (get t 1)
                     pA (infer Γ p)
                     ptag (tag-of pA)]
                 (if (= ptag T/Sigma)
                   (get pA 1)
                   (errorf "fst projection requires a Σ (Sigma) type product, but got: %s\nExpected format: Σx:A. B or a term that evaluates to a Sigma type"
                           (print/sem pA))))

               (= tag :snd)
               (let [p (get t 1)
                     pA (infer Γ p)
                     ptag (tag-of pA)]
                 (if (= ptag T/Sigma)
                   (let [[_tag _fst B] pA
                         p-sem (eval Γ p)]
                     (B (fst-sem p-sem)))
                   (errorf "snd projection requires a Σ (Sigma) type product, but got: %s\nExpected format: Σx:A. B or a term that evaluates to a Sigma type"
                           (print/sem pA))))

               (= tag :pair)
               (errorf "cannot infer type of pair %s\nPairs require explicit Sigma type annotation because they lack principal types.\nSuggestion: (pair a b) : (Σx:A. B)"
                       (print/tm t))

               (= tag :t-id)
               (let [A (get t 1)
                     x (get t 2)
                     y (get t 3)
                     A-ty (infer Γ A)
                     A-sem (eval Γ A)
                     A-tag (tag-of A-ty)]
                 (if (= A-tag T/Type)
                   (do (check Γ x A-sem)
                       (check Γ y A-sem)
                       (ty/type (get A-ty 1)))
                   (errorf "Identity type (Id A x y) expects 'A' to be a universe Type, but got: %s\nThe first argument must evaluate to a Type, e.g., Type 0, Type 1, etc."
                           (print/sem A-ty))))

               (= tag :t-refl)
               (let [x (get t 1)
                     A (infer Γ x)
                     xv (eval Γ x)]
                 (ty/id A xv xv))

               (= tag :t-J)
               (let [A (get t 1)
                     x (get t 2)
                     P (get t 3)
                     d (get t 4)
                     y (get t 5)
                     p (get t 6)
                     A-sem (eval Γ A)]
                 (check-univ Γ A)
                 (check Γ x A-sem)
                 (let [fresh-y (gensym)
                       fresh-p (gensym)
                       xv (eval Γ x)
                       yv-sem (raise A-sem (ne/var fresh-y))
                       Γ-y (ctx/add Γ fresh-y A-sem)
                       id-ty (ty/id A-sem xv yv-sem)
                       pv-sem (raise id-ty (ne/var fresh-p))
                       Γ-yp (ctx/add Γ-y fresh-p id-ty)
                       motive-ty (ty/pi A-sem
                                        (fn [yv]
                                          (ty/pi (ty/id A-sem xv yv)
                                                 (fn [_pv] eq-type))))]
                    (if (function? P)
                     (do
                        (check-univ Γ-yp (j/motive-app-term P [:var fresh-y] [:var fresh-p]))
                        (let [P-refl (eval Γ (j/motive-app-term P x [:t-refl x]))]
                          (check Γ d P-refl))
                        (check Γ y A-sem)
                        (let [yv (eval Γ y)]
                          (check Γ p (ty/id A-sem xv yv))
                          (eval Γ (j/motive-app-term P y p))))
                      (do
                        (check Γ P motive-ty)
                        (let [P-sem (eval Γ P)]
                         (let [P-refl (j/motive-app-typed motive-ty P-sem xv [T/Refl xv])]
                           (check Γ d P-refl))
                         (check Γ y A-sem)
                         (let [yv (eval Γ y)]
                           (check Γ p (ty/id A-sem xv yv))
                           (let [pv (eval Γ p)]
                             (j/motive-app-typed motive-ty P-sem yv pv))))))))

               true
               (errorf "infer: unknown term %s\nThis term is not recognized by the type checker.\nSupported forms: var, type, lambda, application, pi, sigma, pair, fst, snd, id, refl, J"
                       (print/tm t))))))

    (set check
         (fn [Γ t A]
           (let [tag (if (tuple? t) (get t 0) nil)]
             (cond
               (= tag :hole)
               ((meta :error-check) (get t 1) A Γ)

               (= tag :lam)
               (let [A-tag (tag-of A)
                     body (get t 1)]
                 (if (= A-tag T/Pi)
                   (let [[_tag dom cod] A]
                     (with-bound Γ dom
                       (fn [fresh arg-sem Γ2]
                         (check Γ2
                                (body [:var fresh])
                                (cod arg-sem)))))
                   (errorf "lambda checking failed - expected a Pi type (Πx:A. B), but got: %s\nLambda expressions can only be checked against function types."
                           (print/sem A))))

               (= tag :pair)
               (let [A-tag (tag-of A)
                     l (get t 1)
                     r (get t 2)]
                 (if (= A-tag T/Sigma)
                   (let [[_tag A1 B1] A]
                     (do (check Γ l A1)
                         (check Γ r (B1 (eval Γ l)))))
                   (errorf "pair checking failed - expected a Sigma type (Σx:A. B), but got: %s\nPair expressions can only be checked against Sigma product types."
                           (print/sem A))))

               true
               (let [A1 (infer Γ t)]
                 (if (subtype A1 A)
                   true
                   (errorf "type mismatch between expected type and inferred type\nExpected: %s\nInferred: %s\nSuggestion: Check if the terms are actually equal or if there's a type annotation issue."
                           (print/sem A)
                           (print/sem A1))))))))

    (defn constraints/gen [Γ t A]
      "Generate constraints for checking term t against type A"
      (let [cs @[]
            t-tag (if (tuple? t) (get t 0) nil)
            A-tag (tag-of A)]
        (cond
          # Hole constraints - create metavariable for unknown terms
          (= t-tag :hole)
          (match t
            [:hole hole-name]
            (let [mv (meta :fresh-meta)
                  env (constraints :ctx/from-env Γ)]
              (array/push cs (constraints :constraint/hole mv hole-name env :elab/hole)))
            _ (errorf "invalid hole term: %v" t))

          # Lambda constraints - expect Pi type and generate body constraint
          (= t-tag :lam)
          (match t
            [:lam body]
            (if (= A-tag T/Pi)
              (let [[_ dom cod] A
                    mv (meta :fresh-meta)
                    env (constraints :ctx/from-env Γ)]
                (array/push cs (constraints :constraint/dependent mv "lam-body" env (cod (raise dom (ne/var mv))) @[dom] :elab/lambda)))
              (let [mv (meta :fresh-meta)
                    env (constraints :ctx/from-env Γ)]
                (array/push cs (constraints :constraint/dependent mv "lam-pi" env A @[] :elab/lambda))))
            _ (errorf "invalid lambda term: %v" t))

          # Application constraints - expect Pi type for function
          (= t-tag :app)
          (match t
            [:app f x]
            (try
              (let [fA (infer Γ f)
                    ftag (tag-of fA)]
                (unless (= ftag T/Pi)
                  (let [dom-mv (meta :fresh-meta)
                        cod-mv (meta :fresh-meta)
                        env (constraints :ctx/from-env Γ)]
                    (array/push cs (constraints :constraint/dependent dom-mv "app-pi" env (ty/pi [:var dom-mv] (fn [x] [:var cod-mv])) @[fA] :elab/application)))))
              ([e]
                # If inference fails, create a constraint without inferred type
                (let [dom-mv (meta :fresh-meta)
                      cod-mv (meta :fresh-meta)
                      env (constraints :ctx/from-env Γ)]
                  (array/push cs (constraints :constraint/dependent dom-mv "app-pi" env (ty/pi [:var dom-mv] (fn [x] [:var cod-mv])) @[] :elab/application)))))
            _ (errorf "invalid application term: %v" t))

          # Recursive constraint generation for other term forms
          (= t-tag :fst)
          (match t
            [:fst p]
            (let [p-cs (constraints/gen Γ p A)]
              (each c p-cs (array/push cs c)))
            _ (errorf "invalid fst term: %v" t))

          (= t-tag :snd)
          (match t
            [:snd p]
            (let [p-cs (constraints/gen Γ p A)]
              (each c p-cs (array/push cs c)))
            _ (errorf "invalid snd term: %v" t))

          (= t-tag :pair)
          (match t
            [:pair l r]
            (when (= A-tag T/Sigma)
              (let [[_ A1 B1] A
                    l-cs (constraints/gen Γ l A1)
                    r-cs (constraints/gen Γ r (B1 (eval Γ l)))]
                (each c l-cs (array/push cs c))
                (each c r-cs (array/push cs c))))
            _ (errorf "invalid pair term: %v" t))

          # Default case - no constraints for unsupported forms
          true
          cs)))

    (defn collect/goals [thunk]
      (let [saved-collect (goals/collect?)
            saved-goals (array/slice goals)]
        (goals/reset!)
        (goals/set-collect! true)
        (try
          (let [result (thunk)
                fresh-goals (array/slice goals)]
            (goals/reset!)
            (each goal saved-goals
              (array/push goals goal))
            (goals/set-collect! saved-collect)
            {:result result :goals fresh-goals})
          ([err]
           (goals/reset!)
           (each goal saved-goals
             (array/push goals goal))
           (goals/set-collect! saved-collect)
           (error err)))))

    (defn solve-constraints [constraints]
      "Solve a list of constraints using unification"
      ((unify :unify/solve) constraints))

    (defn solve-goals [goals]
      ((constraints :constraints/from-goals) goals))

    (defn infer/c [Γ t]
      "Infer type while collecting live goal constraints"
      (let [collected (collect/goals (fn [] (infer Γ t)))]
        {:result (collected :result)
         :constraints (solve-goals (collected :goals))
         :goals (collected :goals)}))

    (defn infer/constraint [Γ t expected]
      "Constraint-based inference: infer type and solve constraints against expected type"
      (try
        (let [result (collect/goals
                       (fn []
                         (let [inferred (infer Γ t)]
                           (when expected
                             (when (not (subtype inferred expected))
                               (errorf "type mismatch between expected type and inferred type\nExpected: %s\nInferred: %s"
                                       (print/sem expected)
                                       (print/sem inferred))))
                           inferred)))
              solved (solve-goals (result :goals))]
          {:result (result :result)
           :constraints solved
           :goals (result :goals)
           :solved (all |($ :solution) solved)})
        ([e]
          {:error e :solved false})))

    (defn check/c [Γ t A]
      "Check term against type while collecting live goal constraints"
      (try
        (let [result (collect/goals (fn [] (check Γ t A)))
              solved (solve-goals (result :goals))]
          {:result (result :result)
           :constraints solved
           :goals (result :goals)})
        ([e]
          {:error e :constraints @[]})))

    (defn fill-hole [constraints hole-name solution]
      "Fill a named hole in constraints with a solution"
      (var found false)
      (let [updated (map (fn [c]
                           (if (and (c :name) (= (c :name) hole-name))
                             (do (set found true)
                                 (put (table/clone c) :solution solution))
                             c))
                         constraints)]
        (if found
          {:solved (solve-constraints updated) :filled true}
          {:solved constraints :filled false})))

    (defn suggest-solutions [constraints Γ]
      "Suggest possible solutions for unsolved constraints"
      (let [suggestions @[]]
        (each c constraints
          (when (nil? (c :solution))
            (cond
              (= (c :origin) :elab/hole)
              (array/push suggestions {:hole (c :name) :type (c :expected) :context (c :ctx)})

              (= (c :origin) :elab/lambda)
              (array/push suggestions {:constraint "lambda-pi" :expected (c :expected) :context (c :ctx)})

              (= (c :origin) :elab/application)
              (array/push suggestions {:constraint "app-pi" :expected (c :expected) :context (c :ctx)}))))
        suggestions))

    (defn interactive-elab [Γ t A]
      "Interactive elaboration with hole filling suggestions"
      (let [check-result (check/c Γ t A)
            constraints (check-result :constraints)
            suggestions (suggest-solutions constraints Γ)]
        (merge check-result {:suggestions suggestions})))

    (defn constraint-summary [constraints]
      "Generate a user-friendly summary of constraints"
      (let [summary @[]]
        (each c constraints
          (let [status (if (c :solution) "solved" "unsolved")
                name (or (c :name) "anonymous")
                origin (c :origin)]
            (array/push summary {:name name :status status :origin origin :expected (c :expected)})))
        summary))

    (defn refine-type [Γ t partial-type]
      "Refine a partial type using constraint-based inference"
      (let [result (infer/constraint Γ t partial-type)]
        (if (result :solved)
          {:refined-type (result :type) :success true}
          {:refined-type partial-type :constraints (result :constraints) :success false})))

    (defn auto-complete [Γ partial-term expected-type]
      "Suggest auto-completions for partial terms"
      (let [constraints (constraints/gen Γ partial-term expected-type)
            suggestions (suggest-solutions constraints Γ)]
        {:suggestions suggestions :constraints (constraint-summary constraints)}))

    {:infer infer
     :check check
     :subtype subtype
     :check-univ check-univ
     :constraints/gen constraints/gen
     :infer/c infer/c
     :check/c check/c
     :infer/constraint infer/constraint
     :solve-constraints solve-constraints
     :fill-hole fill-hole
     :suggest-solutions suggest-solutions
     :interactive-elab interactive-elab
     :constraint-summary constraint-summary
     :refine-type refine-type
     :auto-complete auto-complete}))

(def exports {:make make})
