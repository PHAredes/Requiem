#!/usr/bin/env janet

(import ./src/frontend/surface/parser :as sp)
(import ./src/elab :as e)
(import ./src/coreTT :as tt)
(import /build/hamt :as h)
(import /build/timer :as timer)
(import ./src/levels :as lvl)
(import ./src/core_printer :as pp)
(import ./src/matches :as mt)

(defn- print/node [tm]
  (match tm
    [:atom tok] tok
    [:var x] (string x)
    [:type l] (string "Type" l)
    [:hole name] (if name (string "?" name) "?")
    [:list xs]
    (if (and (= (length xs) 3)
             (tuple? (xs 0))
             (= ((xs 0) 0) :atom)
             (= ((xs 0) 1) "fn"))
      (let [binder (xs 1)
            binder-text (match binder
                          [:atom name] name
                          [:list bs] (string/join (map print/node bs) " ")
                          _ (print/node binder))]
        (string "λ" binder-text "." (print/node (xs 2))))
      (string "(" (string/join (map print/node xs) " ") ")"))
    [:app f a] (string "(" (print/node f) " " (print/node a) ")")
    [:t-pi A _] (string "Pi(" (print/node A) ", ...)")
    [:t-sigma A _] (string "Sigma(" (print/node A) ", ...)")
    [:pair l r] (string "(" (print/node l) ", " (print/node r) ")")
    [:fst p] (string "fst " (print/node p))
    [:snd p] (string "snd " (print/node p))
    [:t-id A x y] (string "Id " (print/node A) " " (print/node x) " " (print/node y))
    [:t-refl x] (string "refl " (print/node x))
    [:t-J _ _ _ _ _ _] "J ..."
    _ (string/format "%v" tm)))

(defn- print/param [param]
  (match param
    [:param name ty _]
    (if ty
      (string name ": " (print/node ty))
      name)
    _ (string/format "%v" param)))

(defn- print/ctor [ctor]
  (match ctor
    [:ctor/plain name fields _]
    (if (zero? (length fields))
      name
      (string name
              "(" 
              (string/join (map (fn [f]
                                  (match f
                                    [:field/named fname ty _] (string fname ": " (print/node ty))
                                    [:field/anon ty _] (print/node ty)
                                    _ "..."))
                                fields)
                           ", ")
              ")"))

    [:ctor/indexed indices name fields _]
    (string (string/join (map print/node indices) ", ")
            " = "
            name
            (if (zero? (length fields))
              ""
              (string "(" 
                      (string/join (map (fn [f]
                                          (match f
                                            [:field/named fname ty _] (string fname ": " (print/node ty))
                                            [:field/anon ty _] (print/node ty)
                                            _ "..."))
                                        fields)
                                   ", ")
                      ")")))

    _
    (string/format "%v" ctor)))

(defn- print/binder [binder]
  (match binder
    [:bind name ty]
    (string name
            ": "
               (if (and (tuple? ty)
                      (or (= (ty 0) :atom)
                          (= (ty 0) :list)))
              (print/node ty)
              (pp/print/tm ty)))
    _
    (string/format "%v" binder)))

(defn- print/lowered-ctor [ctor]
  (match ctor
    [:ctor name pat-binders patterns ctor-params _ _]
    (let [indices (if (zero? (length patterns))
                    nil
                    (string/join (map print/node (map mt/pat/to-term patterns)) ", "))
          params (tuple/join pat-binders ctor-params)
          render-param (fn [b]
                         (match b
                           [:bind bname bty]
                           (if (string/has-prefix? "_arg" bname)
                             (print/node bty)
                             (print/binder b))
                           _ (string/format "%v" b)))
          suffix (if (zero? (length params))
                   ""
                   (string "(" (string/join (map render-param params) ", ") ")"))]
      (if indices
        (string indices " = " name suffix)
        (string name suffix)))

    _
    (string/format "%v" ctor)))

(defn- print/header [name params result printer]
  (string name
          (if (zero? (length params))
            ""
            (string "(" (string/join (map print/binder params) ", ") ")"))
          ": "
          (printer result)))

(defn decl/render [decl]
  (let [tag (decl 0)]
    (cond
      (= tag :decl/data)
      (string (decl 1)
              (if (zero? (length (decl 2)))
                ""
                (string "(" (string/join (map print/binder (decl 2)) ", ") ")"))
              ": "
              (print/node (decl 3))
              (if (zero? (length (decl 4)))
                ""
                (string "\n  " (string/join (map print/lowered-ctor (decl 4)) "\n  "))))

      (= tag :decl/func)
      (string (print/header (decl 1) (decl 2) (decl 3) print/node)
              "\n  "
              (length (decl 4))
              " clause(s)")

      (= tag :decl/record)
      (string (decl 1) "\n  " (length (decl 2)) " entry(ies)")

      (= tag :decl/compute)
      (string "compute " (print/node (decl 1)))

      (= tag :decl/check)
      (string "check " (print/node (decl 1)) " : " (print/node (decl 2)))

      (= tag :core/data)
      (string (decl 1)
              (if (zero? (length (decl 2)))
                ""
                (string "(" (string/join (map print/binder (decl 2)) ", ") ")"))
              "\n  "
              (length (decl 4))
              " ctor(s)")

      (= tag :core/func)
      (string (print/header (decl 1) (decl 2) (decl 3) pp/print/tm)
              "\n  "
              (length (decl 5))
              " clause(s)")

      (= tag :core/compute)
      (string "compute " (pp/print/tm (decl 1)))

      (= tag :core/check)
      (string "check " (pp/print/tm (decl 1)) " : " (pp/print/tm (decl 2)))

      true
      (string "unknown declaration: " (string/format "%v" decl)))))

(defn- print/decls [decls]
  (eachp [i decl] decls
    (print (decl/render decl))
    (when (< (+ i 1) (length decls))
      (print ""))))

(var goal-print/names nil)
(var goal-print/next-id 0)

(defn- goal-print/base-name [n]
  (let [names @["x" "y" "z" "w" "u" "v" "a" "b" "c" "d"]
        k (% n (length names))
        q (div n (length names))
        base (names k)]
    (if (= q 0) base (string base q))))

(defn- goal-print/fresh! []
  (let [name (goal-print/base-name goal-print/next-id)]
    (++ goal-print/next-id)
    name))

(defn- goal-print/snapshot []
  [goal-print/names goal-print/next-id])

(defn- goal-print/restore! [snapshot]
  (let [[saved-names saved-next] snapshot]
    (set goal-print/names saved-names)
    (set goal-print/next-id saved-next)))

(var print/goal-ne nil)
(var print/goal-nf nil)
(var print/goal-sem nil)

(defn- goal-print/with-state [names next-id f]
  (let [snapshot (goal-print/snapshot)]
    (set goal-print/names names)
    (set goal-print/next-id next-id)
    (try
      (let [out (f)]
        (goal-print/restore! snapshot)
        out)
      ([err]
       (goal-print/restore! snapshot)
       (error err)))))

(defn- goal-print/nf-binder [label A B]
  (let [actual (gensym)
        shown (goal-print/fresh!)]
    (put goal-print/names actual shown)
    (string label "(" shown ": " (print/goal-nf A) "). " (print/goal-nf (B actual)))))

(defn- goal-print/sem-binder [label A B]
  (let [actual (gensym)
        shown (goal-print/fresh!)]
    (put goal-print/names actual shown)
    (let [arg (tt/raise A (tt/ne/var actual))]
      (string label "(" shown ": " (print/goal-sem A) "). " (print/goal-sem (B arg))))))

(set print/goal-ne
     (fn [ne]
       (cond
         (and (tuple? ne) (= (ne 0) :nvar)) (or (get goal-print/names (ne 1)) (string (ne 1)))
         (and (tuple? ne) (= (ne 0) :napp)) (string "(" (print/goal-ne (ne 1)) " " (print/goal-nf (ne 2)) ")")
         (and (tuple? ne) (= (ne 0) :nfst)) (string "fst " (print/goal-ne (ne 1)))
         (and (tuple? ne) (= (ne 0) :nsnd)) (string "snd " (print/goal-ne (ne 1)))
         (and (tuple? ne) (= (ne 0) :nJ)) "J ..."
         true (string/format "%v" ne))))

(set print/goal-nf
     (fn [nf]
       (let [tag (if (tuple? nf) (nf 0) nil)]
          (cond
          (= tag tt/NF/Type) (string "Type" (lvl/str (nf 1)))
          (= tag tt/NF/Pi)
          (goal-print/nf-binder "Pi" (nf 1) (nf 2))
          (= tag tt/NF/Sigma)
          (goal-print/nf-binder "Sigma" (nf 1) (nf 2))
         (= tag tt/NF/Id)
         (string "Id " (print/goal-nf (nf 1)) " " (print/goal-nf (nf 2)) " " (print/goal-nf (nf 3)))
         (= tag tt/NF/Refl) (string "refl " (print/goal-nf (nf 1)))
         (= tag tt/NF/Pair) (string "(" (print/goal-nf (nf 1)) ", " (print/goal-nf (nf 2)) ")")
         (= tag tt/NF/Neut) (print/goal-ne (nf 1))
         true (string/format "%v" nf)))))

(set print/goal-sem
     (fn [sem]
       (let [tag (if (tuple? sem) (sem 0) nil)]
         (cond
         (= tag tt/T/Type)
         (string "Type" (lvl/str (sem 1)))
          (= tag tt/T/Neutral) (print/goal-ne (sem 1))
          (= tag tt/T/Pi)
          (goal-print/sem-binder "Pi" (sem 1) (sem 2))
          (= tag tt/T/Sigma)
          (goal-print/sem-binder "Sigma" (sem 1) (sem 2))
         (= tag tt/T/Id)
         (let [A (sem 1)
               x (sem 2)
               y (sem 3)]
           (string "Id " (print/goal-sem A) " "
                   (print/goal-nf (tt/lower A x)) " "
                   (print/goal-nf (tt/lower A y))))
         (= tag tt/T/Pair) (string "(" (print/goal-sem (sem 1)) ", " (print/goal-sem (sem 2)) ")")
         (= tag tt/T/Refl) (string "refl " (string/format "%v" (sem 1)))
         true (string/format "%v" sem)))))

(defn- print/goal-type [sem names]
  (let [start-next (reduce (fn [n _] (+ n 1)) 0 names)]
    (goal-print/with-state (table/clone names)
                           start-next
                           (fn [] (print/goal-sem sem)))))

(defn- tt/goals/restore! [saved-goals saved-collect]
  (array/clear tt/goals)
  (each g saved-goals
    (array/push tt/goals g))
  (tt/goals/set-collect! saved-collect))

(defn- partition/goal-ctx [ctx hidden-names]
  (reduce (fn [[local global] entry]
            (if (get hidden-names (entry 0))
              [local [;global entry]]
              [[;local entry] global]))
          [@[] @[]]
          ctx))

(defn- bind-spec/name [node]
  (match node
    [:atom name] name
    [:list xs]
    (cond
      (and (= (length xs) 2)
           (= ((xs 0) 0) :atom)
           (string/has-suffix? ":" ((xs 0) 1)))
      (string/slice ((xs 0) 1) 0 (- (length ((xs 0) 1)) 1))

      (and (= (length xs) 3)
           (= ((xs 0) 0) :atom)
           (= ((xs 0) 1) ":")
           (= ((xs 1) 0) :atom))
      ((xs 1) 1)

      true nil)

    _ nil))

(defn- term/lambda-names [tm]
  (match tm
    [:list xs]
    (if (and (= (length xs) 3)
             (= ((xs 0) 0) :atom)
             (= ((xs 0) 1) "fn"))
      (let [binder (xs 1)
            body (xs 2)
            names (match binder
                    [:atom name] @[name]
                    [:list bs] (reduce (fn [acc b]
                                         (if-let [name (bind-spec/name b)]
                                           [;acc name]
                                           acc))
                                       @[]
                                       bs)
                    _ @[])]
        (tuple/join names (term/lambda-names body)))
      @[])

    _ @[]))

(defn- print/bindings [entries indent names]
  (if (zero? (length entries))
    (printf "%s<empty>" indent)
    (each c entries
      (printf "%s%s : %s"
              indent
              (or (get names (c 0)) (string (c 0)))
              (print/goal-type (c 1) names)))))

(defn- print/goal-block [g hidden-names preferred-names &opt indent]
  (let [indent (or indent "  ")
        [local-ctx global-ctx] (partition/goal-ctx (g :ctx) hidden-names)
        local-names (let [out @{}]
                      (eachp [i entry] local-ctx
                        (put out
                             (entry 0)
                             (if (< i (length preferred-names))
                               (preferred-names i)
                               (goal-print/base-name i))))
                      out)]
    (printf "%sLocal context:" indent)
    (print/bindings local-ctx (string indent "  ") local-names)
    (printf "%sAvailable names:" indent)
    (print/bindings global-ctx (string indent "  ") local-names)
    (printf "%s------------------------------" indent)
    (printf "%s?%s : %s" indent (string (g :name)) (print/goal-type (g :expected) local-names))))

(defn- print/goals [goals hidden-names preferred-name-groups &opt header indent]
  (let [indent (or indent "  ")]
    (when (> (length goals) 0)
      (when header
        (print header))
      (eachp [i g] goals
        (print/goal-block g
                          hidden-names
                          (if (< i (length preferred-name-groups))
                            (preferred-name-groups i)
                            @[])
                          indent)
        (when (< (+ i 1) (length goals))
          (print ""))))))

(defn- global-names [Γ]
  (reduce (fn [acc k]
            (do (put acc k true) acc))
          @{}
          (h/keys Γ)))

(defn- resolve-path [path]
  (let [resolved (if (string/has-prefix? "@examples/" path)
                   (string "examples/" (string/slice path (length "@examples/")))
                   path)]
    (if (os/stat resolved)
      (if (string/has-suffix? ".requiem" resolved)
        resolved
        (errorf "CLI now only accepts `.requiem` source files, got: %q" resolved))
      (if (and (not (string/has-suffix? ".requiem" resolved))
               (os/stat (string resolved ".requiem")))
        (string resolved ".requiem")
        (if (string/has-suffix? ".requiem" resolved)
          resolved
          (errorf "CLI now only accepts `.requiem` source files, got: %q" resolved))))))

(defn- mode/runs-computes? [mode]
  (or (= mode :run) (= mode :compile)))

(defn- requiem-root []
  (or (os/getenv "REQUIEM_ROOT") "."))

(defn- default-prelude-import []
  (string (requiem-root) "/Prelude"))

(defn- with-default-prelude [src]
  (string "import \"" (default-prelude-import) "\"\n\n" src))

(defn- print/help []
  (print "Usage: requiem [mode] <file>")
  (print "")
  (print "Modes:")
  (print "  run      parse, elaborate, and execute compute blocks")
  (print "  check    parse and elaborate without running compute blocks")
  (print "  compile  alias of run")
  (print "  help     show this help")
  (print "")
  (print "Input:")
  (print "  the CLI accepts `.requiem` source files only")
  (print "")
  (print "Examples:")
  (print "  requiem examples/test.requiem")
  (print "  requiem check examples/test.requiem")
  (print "  requiem compile @examples/test.requiem"))

(defn- print/surface-type [ty]
  (match ty
    [:ty/hole _ _] (print/node (sp/lower/type ty))
    [:ty/universe _ _] (print/node (sp/lower/type ty))
    [:ty/name _ _] (print/node (sp/lower/type ty))
    [:ty/var _ _] (print/node (sp/lower/type ty))
    [:ty/app _ _ _] (print/node (sp/lower/type ty))
    [:ty/arrow _ _ _] (print/node (sp/lower/type ty))
    [:ty/pi _ _ _] (print/node (sp/lower/type ty))
    [:ty/sigma _ _ _] (print/node (sp/lower/type ty))
    [:ty/op _ _ _] (print/node (sp/lower/type ty))
    _ (print/node ty)))

(defn- collect/type-holes [ty ctx out]
  (match ty
    [:ty/hole name _]
    (array/push out {:name (or name "_") :expected "Type?" :ctx ctx})

    [:ty/pi binder body _]
    (let [binder-ty (binder 2)
          next-ctx [;ctx [(binder 1) binder-ty]]]
      (collect/type-holes binder-ty ctx out)
      (collect/type-holes body next-ctx out))

    [:ty/sigma binder body _]
    (let [binder-ty (binder 2)
          next-ctx [;ctx [(binder 1) binder-ty]]]
      (collect/type-holes binder-ty ctx out)
      (collect/type-holes body next-ctx out))

    [:ty/arrow dom cod _]
    (do
      (collect/type-holes dom ctx out)
      (collect/type-holes cod ctx out))

    [:ty/app f a _]
    (do
      (collect/type-holes f ctx out)
      (collect/type-holes a ctx out))

    [:ty/op _ args _]
    (each arg args (collect/type-holes arg ctx out))

    _ nil))

(defn- collect/field-type-holes [field ctx out]
  (match field
    [:field/named _ ty _] (collect/type-holes ty ctx out)
    [:field/anon ty _] (collect/type-holes ty ctx out)
    _ nil))

(defn- collect/ctor-type-holes [ctor ctx out]
  (match ctor
    [:ctor/plain _ fields _]
    (each field fields
      (collect/field-type-holes field ctx out))

    [:ctor/indexed _ _ fields _]
    (each field fields
      (collect/field-type-holes field ctx out))

    _ nil))

(defn- collect/decl-type-holes [decl out]
  (match decl
    [:decl/data _ params sort ctors _]
    (let [ctx @[]]
      (each p params
        (when (p 2)
          (collect/type-holes (p 2) ctx out))
        (array/push ctx [(p 1) (or (p 2) [:ty/hole nil nil])]))
      (collect/type-holes sort ctx out)
      (each ctor ctors
        (collect/ctor-type-holes ctor ctx out)))

    [:decl/func _ ty _ _]
    (collect/type-holes ty @[] out)

    [:decl/check _ ty _]
    (collect/type-holes ty @[] out)

    _ nil))

(defn- print/type-hole-goals [goals hidden-names]
  (when (> (length goals) 0)
    (print "Type holes:")
    (each g goals
      (let [[ctx globals] (partition/goal-ctx (g :ctx) hidden-names)]
        (print "  Local context:")
        (if (zero? (length ctx))
          (print "    <empty>")
          (each c ctx
            (printf "    %s : %s" (c 0) (print/surface-type (c 1)))))
        (print "  Available names:")
        (if (zero? (length globals))
          (print "    <empty>")
          (each c globals
            (printf "    %s : %s" (c 0) (print/goal-type (c 1) @{}))))
        (print "  ------------------------------")
        (printf "  ?%s : %s" (g :name) (g :expected))
        (print "")))))

(defn- binders->ctx [params Γ]
  (reduce (fn [acc b]
            (match b
              [:bind name ty-core]
              (tt/ctx/add acc name (tt/eval acc ty-core))
              _ acc))
          Γ
          params))

(defn- binders->pi-sem [Γ params result-core]
  (defn recur [i cur-ctx]
    (if (= i (length params))
      (tt/eval cur-ctx result-core)
      (let [b (params i)
            name (b 1)
            dom (tt/eval cur-ctx (b 2))]
        (tt/ty/pi dom
                  (fn [x]
                    (recur (+ i 1) (tt/ctx/add cur-ctx name x)))))))
  (recur 0 Γ))

(defn- build-global-ctx [core-decls]
  (var Γ (tt/ctx/empty))
  (each decl core-decls
    (match decl
      [:core/data name params sort ctors]
      (do
        (set Γ (tt/ctx/add Γ name (binders->pi-sem Γ params sort)))
        (each ctor ctors
          (let [ctor-name (ctor 1)
                ctor-ty (ctor 5)]
            (set Γ (tt/ctx/add Γ ctor-name (tt/eval Γ ctor-ty))))))

      [:core/func name _ _ core-ty _]
      (set Γ (tt/ctx/add Γ name (tt/eval Γ core-ty)))

      _ nil))
  Γ)

(defn- term/spine [tm]
  (var cur tm)
  (var rev-args @[])
  (while (and (tuple? cur) (= (cur 0) :app))
    (array/push rev-args (cur 2))
    (set cur (cur 1)))
  (if (and (tuple? cur) (= (cur 0) :var))
    [(cur 1) (reverse rev-args)]
    [nil @[]]))

(defn- term/subst [tm sigma]
  (match tm
    [:var x]
    (or (mt/subst/lookup sigma x) tm)

    [:app f a]
    [:app (term/subst f sigma) (term/subst a sigma)]

    [:t-pi A B]
    [:t-pi (term/subst A sigma) B]

    [:t-sigma A B]
    [:t-sigma (term/subst A sigma) B]

    [:pair l r]
    [:pair (term/subst l sigma) (term/subst r sigma)]

    [:fst p]
    [:fst (term/subst p sigma)]

    [:snd p]
    [:snd (term/subst p sigma)]

    [:t-id A x y]
    [:t-id (term/subst A sigma) (term/subst x sigma) (term/subst y sigma)]

    [:t-refl x]
    [:t-refl (term/subst x sigma)]

    [:t-J A x P d y p]
    [:t-J (term/subst A sigma)
          (term/subst x sigma)
          (term/subst P sigma)
          (term/subst d sigma)
          (term/subst y sigma)
          (term/subst p sigma)]

    _ tm))

(defn- pattern/extend-ctx [Γ pat expected-core ctor-env]
  (match pat
    [:pat/var x]
    (if (= x "_")
      Γ
      (tt/ctx/add Γ x (tt/eval Γ expected-core)))

    [:pat/con head args]
    (let [info (get (ctor-env :ctors) head)]
      (if (nil? info)
        Γ
        (let [[exp-head exp-args] (term/spine expected-core)]
          (if (or (nil? exp-head) (not= exp-head (info :data)))
            Γ
            (let [ctor (info :ctor)
                  patterns (ctor 3)
                  result (if (zero? (length patterns))
                           (mt/outcome/yes (mt/subst/empty))
                           (mt/matches* exp-args patterns (ctor-env :ctor-name-set) (mt/subst/empty)))]
              (if (not (mt/outcome/yes? result))
                Γ
                (let [sigma (mt/outcome/subst result)
                      params (ctor 4)]
                  (when (not= (length args) (length params))
                    (errorf "constructor %s expects %d argument(s), got %d"
                            head
                            (length params)
                            (length args)))
                  (var cur-ctx Γ)
                  (for i 0 (length params)
                    (set cur-ctx
                         (pattern/extend-ctx cur-ctx
                                             (args i)
                                             (term/subst ((params i) 2) sigma)
                                             ctor-env)))
                  cur-ctx)))))))

    _ Γ))

(defn- clause/extend-ctx [Γ params clause ctor-env]
  (match clause
    [:core/clause patterns _]
    (reduce (fn [cur-ctx i]
              (if (< i (length params))
                (pattern/extend-ctx cur-ctx
                                    (patterns i)
                                    ((params i) 2)
                                    ctor-env)
                cur-ctx))
            Γ
            (range (length patterns)))

    _ Γ))

(defn- build-ctor-env [core-decls]
  (let [ctors @{}
        ctor-name-set @{}]
    (each decl core-decls
      (match decl
        [:core/data data-name _ _ data-ctors]
        (each ctor data-ctors
          (put ctors (ctor 1) {:data data-name :ctor ctor})
          (put ctor-name-set (ctor 1) true))
        _ nil))
    {:ctors ctors :ctor-name-set ctor-name-set}))

(defn- check/with-ctors [Γ tm expected-core ctor-env]
  (let [expected-sem (tt/eval Γ expected-core)
        [head args] (term/spine tm)
        info (and head (get (ctor-env :ctors) head))]
    (cond
      (nil? info)
      (tt/check Γ tm expected-sem)

      true
      (let [[exp-head exp-args] (term/spine expected-core)]
        (cond
          (or (nil? exp-head) (not= exp-head (info :data)))
          (tt/check Γ tm expected-sem)

          true
          (let [ctor (info :ctor)
                patterns (ctor 3)
                result (if (zero? (length patterns))
                         (mt/outcome/yes (mt/subst/empty))
                         (mt/matches* exp-args patterns (ctor-env :ctor-name-set) (mt/subst/empty)))]
            (if (mt/outcome/yes? result)
              (let [sigma (mt/outcome/subst result)
                    params (ctor 4)]
                (when (not= (length args) (length params))
                  (errorf "constructor %s expects %d argument(s), got %d"
                          head
                          (length params)
                          (length args)))
                (for i 0 (length params)
                  (let [arg (args i)
                        param-ty (term/subst ((params i) 2) sigma)]
                    (check/with-ctors Γ arg param-ty ctor-env)))
                true)
              (tt/check Γ tm expected-sem))))))))

(defn run/file-surface [path mode]
  (def start-ms (timer/ms))
  (def src (with-default-prelude (string (slurp path))))
  (print "Parsing " path "...")
  (def prog (sp/parse/program src))
  (def surface-type-holes @[])
  (each decl (prog 1)
    (collect/decl-type-holes decl surface-type-holes))
  (def lowered (sp/lower/program prog))
  (def lowered-check-names
    (reduce (fn [acc decl]
              (match decl
                [:decl/check tm _]
                [;acc (term/lambda-names tm)]
                _ acc))
            @[]
            lowered))
  (print/decls lowered)
  (def core (e/elab/program lowered))
  (def global-ctx (build-global-ctx core))
  (def global-name-set (global-names global-ctx))
  (print/type-hole-goals surface-type-holes global-name-set)
  (def ctor-env (build-ctor-env core))
  (var check-goal-index 0)
  (def goal-name-hints @[])
  (let [saved-goals (slice tt/goals 0)
        saved-collect (tt/goals/collect?)]
    (tt/goals/set-collect! true)
    (array/clear tt/goals)
    (try
      (do
        (each decl core
          (match decl
            [:core/func name params result ty clauses]
            (do
              (let [Γ (binders->ctx params global-ctx)
                    expected result]
                (each c clauses
                  (check/with-ctors Γ (c 2) expected ctor-env))))

            [:core/compute tm]
            (when (mode/runs-computes? mode)
              (printf "\nCompute: %s" (pp/print/tm tm))
              (let [res (tt/nf (tt/ty/type 100) tm)]
                (printf "  => %s" (pp/print/nf res))))

            [:core/check tm ty]
            (do
              (def preferred-names (if (< check-goal-index (length lowered-check-names))
                                     (lowered-check-names check-goal-index)
                                     @[]))
              (++ check-goal-index)
              (def goal-count-before (length tt/goals))
              (printf "\nCheck: %s : %s" (pp/print/tm tm) (pp/print/tm ty))
              (check/with-ctors global-ctx tm ty ctor-env)
              (print "  => OK")
              (let [goal-count-after (length tt/goals)]
                (when (> goal-count-after goal-count-before)
                  (for _ goal-count-before goal-count-after
                    (array/push goal-name-hints preferred-names))
                  (print "  Current goal:")
                  (print/goals (slice tt/goals goal-count-before goal-count-after)
                               global-name-set
                               (slice goal-name-hints goal-count-before goal-count-after)
                               nil
                               "    "))))
             _ nil))

        (let [pending tt/goals]
          (print/goals pending global-name-set goal-name-hints "\nUnsolved goals:" "  "))

        (print "")
        (def elapsed-ms (- (timer/ms) start-ms))
        (printf "Done. %d declaration(s) in %.3fs" (length lowered) (/ elapsed-ms 1000.0))
        (tt/goals/restore! saved-goals saved-collect))
      ([err]
       (tt/goals/restore! saved-goals saved-collect)
       (error err)))))

(defn run/file [path mode]
  (run/file-surface (resolve-path path) mode))

(defn- parse/cli [args]
  (let [args (if (and (> (length args) 0)
                      (or (string/has-suffix? ".janet" (args 0))
                          (= (args 0) "requiem")))
               (slice args 1)
               args)
        n (length args)]
    (cond
      (= n 1)
      (match (args 0)
        "help" [:help nil]
        "-h" [:help nil]
        "--help" [:help nil]
        _ [:run (args 0)])

      (= n 2)
      (match (args 0)
        "run" [:run (args 1)]
        "check" [:check (args 1)]
        "compile" [:compile (args 1)]
        "help" [:help nil]
        _ nil)

      true
      nil)))

(defn main [& args]
  (if (zero? (length args))
    (print/help)
    (if-let [[mode path] (parse/cli args)]
      (if (= mode :help)
        (print/help)
        (run/file path mode))
      (do
        (print/help)
        (os/exit 1)))))
