#!/usr/bin/env janet

(defn make [deps]
  (let [T/Type (deps :T/Type)
        T/Pi (deps :T/Pi)
        T/Sigma (deps :T/Sigma)
        T/Pair (deps :T/Pair)
        T/Neutral (deps :T/Neutral)
        ty/type (deps :ty/type)
        ty/id (deps :ty/id)
        lvl/<= (deps :lvl/<=)
        lvl/max (deps :lvl/max)
        lvl/succ (deps :lvl/succ)
        sem-eq (deps :sem-eq)
        eval (deps :eval)
        raise (deps :raise)
        ctx/add (deps :ctx/add)
        ctx/lookup (deps :ctx/lookup)
        ne/var (deps :ne/var)
        ne/fst (deps :ne/fst)
        print/sem (deps :print/sem)
        print/tm (deps :print/tm)
        meta (deps :meta)]

    (var infer nil)
    (var check nil)
    (var subtype nil)

    (defn subtype/pi [A1 B1 A2 B2]
      (and (subtype A2 A1)
           (let [fresh (gensym)
                 arg-sem (raise A2 (ne/var fresh))]
             (subtype (B1 arg-sem) (B2 arg-sem)))))

    (defn subtype/sigma [A1 B1 A2 B2]
      (and (subtype A1 A2)
           (let [fresh (gensym)
                 arg-sem (raise A1 (ne/var fresh))]
             (subtype (B1 arg-sem) (B2 arg-sem)))))

    (defn tag-of [x]
      (if (tuple? x) (get x 0) 0))

    (defn fst-sem [p-sem]
      (let [tag (tag-of p-sem)]
        (cond
          (= tag T/Pair) (get p-sem 1)
          (= tag T/Neutral) [T/Neutral (ne/fst (get p-sem 1))]
          true (errorf "fst expected pair semantics, got: %s" (print/sem p-sem)))))

    (set subtype
         (fn [A B]
            "Semantic subtyping with cumulative universes and Pi/Sigma variance."
            (let [tagA (tag-of A)
                  tagB (tag-of B)]
              (cond
                (and (= tagA T/Type) (= tagB T/Type))
                (lvl/<= (get A 1) (get B 1))

               (and (= tagA T/Pi) (= tagB T/Pi))
               (let [[_ A1 B1] A
                     [_ A2 B2] B]
                 (subtype/pi A1 B1 A2 B2))

               (and (= tagA T/Sigma) (= tagB T/Sigma))
               (let [[_ A1 B1] A
                     [_ A2 B2] B]
                 (subtype/sigma A1 B1 A2 B2))

               true
               (sem-eq (ty/type 100) A B)))))

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
            fresh (gensym)
            A-sem (eval Γ A)
            Γ2 (ctx/add Γ fresh A-sem)
            lvlB (check-univ Γ2 (B [:var fresh]))]
        (ty/type (lvl/max lvlA lvlB))))

    (set infer
         (fn [Γ t]
           "Infer the type of term t in context Γ (returns semantic type)"
           (match t
             [:var x]
             (if (or (string? x) (symbol? x))
               (ctx/lookup Γ x)
               (errorf "variable must be a string or symbol, but got: %v\nVariable names should be like 'x', 'y', 'myVar', etc." x))

             [:type l] (ty/type (lvl/succ l))

             [:lam _]
             (errorf "cannot infer type of lambda expression %s\nLambda types require annotation because they have principal types.\nSuggestion: Annotate with a Pi type: (λx. body) : (Πx:A. B)"
                     (print/tm t))

             [:hole name]
              ((meta :error-infer) name Γ)

              [:app f x]
              (let [fA (infer Γ f)
                    tag (tag-of fA)]
                (if (= tag T/Pi)
                  (let [[_ A B] fA]
                    (do (check Γ x A)
                       (B (eval Γ x))))
                 (errorf "cannot apply function - expected a Pi type (Πx:A. B), but got: %s\nTip: Make sure the function has a proper Pi type annotation or can be inferred as one."
                          (print/sem fA))))

              [:t-pi A B]
              (infer-binder Γ A B)

              [:t-sigma A B]
              (infer-binder Γ A B)

              [:fst p]
              (let [pA (infer Γ p)
                    tag (tag-of pA)]
                (if (= tag T/Sigma)
                  (get pA 1)
                  (errorf "fst projection requires a Σ (Sigma) type product, but got: %s\nExpected format: Σx:A. B or a term that evaluates to a Sigma type"
                         (print/sem pA))))

              [:snd p]
              (let [pA (infer Γ p)
                    tag (tag-of pA)]
                (if (= tag T/Sigma)
                  (let [[_ _ B] pA
                        p-sem (eval Γ p)]
                    (B (fst-sem p-sem)))
                  (errorf "snd projection requires a Σ (Sigma) type product, but got: %s\nExpected format: Σx:A. B or a term that evaluates to a Sigma type"
                          (print/sem pA))))

             [:pair _ _]
             (errorf "cannot infer type of pair %s\nPairs require explicit Sigma type annotation because they lack principal types.\nSuggestion: (pair a b) : (Σx:A. B)"
                     (print/tm t))

              [:t-id A x y]
              (let [A-ty (infer Γ A)
                    A-sem (eval Γ A)
                    tag (tag-of A-ty)]
                (if (= tag T/Type)
                  (do (check Γ x A-sem)
                      (check Γ y A-sem)
                     (ty/type (get A-ty 1)))
                 (errorf "Identity type (Id A x y) expects 'A' to be a universe Type, but got: %s\nThe first argument must evaluate to a Type, e.g., Type 0, Type 1, etc."
                         (print/sem A-ty))))

             [:t-refl x]
             (let [A (infer Γ x)
                   xv (eval Γ x)]
               (ty/id A xv xv))

             [:t-J A x P d y p]
             (let [lvlA (check-univ Γ A)
                   A-sem (eval Γ A)]
               (check Γ x A-sem)
               (let [fresh-y (gensym)
                     fresh-p (gensym)
                     xv (eval Γ x)
                     Γ-y (ctx/add Γ fresh-y A-sem)
                     id-ty (ty/id A-sem xv [:var fresh-y])
                     Γ-yp (ctx/add Γ-y fresh-p id-ty)]
                 (check-univ Γ-yp (P [:var fresh-y] [:var fresh-p]))
                 (let [P-refl (eval Γ (P xv [:refl xv]))]
                   (check Γ d P-refl))
                 (check Γ y A-sem)
                 (let [yv (eval Γ y)]
                   (check Γ p (ty/id A-sem xv yv))
                   (let [pv (eval Γ p)]
                     (eval Γ (P yv pv))))))

             _
             (errorf "infer: unknown term %s\nThis term is not recognized by the type checker.\nSupported forms: var, type, lambda, application, pi, sigma, pair, fst, snd, id, refl, J"
                     (print/tm t)))))

    (set check
         (fn [Γ t A]
           (match t
             [:hole name]
             ((meta :error-check) name A Γ)

              [:lam body]
              (let [tag (tag-of A)]
                (if (= tag T/Pi)
                  (let [[_ dom cod] A
                        fresh (gensym)
                       arg-sem (raise dom (ne/var fresh))]
                   (check (ctx/add Γ fresh dom)
                          (body [:var fresh])
                          (cod arg-sem)))
                 (errorf "lambda checking failed - expected a Pi type (Πx:A. B), but got: %s\nLambda expressions can only be checked against function types."
                         (print/sem A))))

              [:pair l r]
              (let [tag (tag-of A)]
                (if (= tag T/Sigma)
                  (let [[_ A1 B1] A]
                    (do (check Γ l A1)
                       (check Γ r (B1 (eval Γ l)))))
                 (errorf "pair checking failed - expected a Sigma type (Σx:A. B), but got: %s\nPair expressions can only be checked against Sigma product types."
                         (print/sem A))))

             _
             (let [A1 (infer Γ t)]
               (if (subtype A1 A)
                 true
                 (errorf "type mismatch between expected type and inferred type\nExpected: %s\nInferred: %s\nSuggestion: Check if the terms are actually equal or if there's a type annotation issue."
                         (print/sem A)
                         (print/sem A1)))))))

    {:infer infer
     :check check
     :subtype subtype
     :check-univ check-univ}))

(def exports {:make make})
