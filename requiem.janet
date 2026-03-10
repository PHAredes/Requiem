#!/usr/bin/env janet

(import ./src/frontend/sexpr/parser :as p)
(import ./src/frontend/sexpr/lower :as l)
(import ./src/frontend/surface/parser :as sp)
(import ./src/elab :as e)
(import ./src/coreTT :as tt)
(import ./src/pretty :as pp)
(import ./src/matches :as mt)

(defn- print/node [tm]
  (match tm
    [:atom tok] tok
    [:var x] (string x)
    [:type l] (string "Type" l)
    [:hole name] (if name (string "?" name) "?")
    [:list xs] (string "(" (string/join (map print/node xs) " ") ")")
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
      (string name " : " (print/node ty))
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
            " : "
              (if (and (tuple? ty)
                     (or (= (ty 0) :atom)
                         (= (ty 0) :list)))
              (print/node ty)
              (pp/print/tm ty)))
    _
    (string/format "%v" binder)))

(defn decl/summary [decl]
  (let [tag (decl 0)]
    (cond
      (= tag :decl/data)
      (let [name (decl 1)
            a2 (decl 2)
            a3 (decl 3)
            a4 (decl 4)]
        (if (array? a3)
          (string "data "
                  name
                  (if (zero? (length a2))
                    ""
                    (string "(" (string/join (map print/param a2) ", ") ")"))
                  " ("
                  (length a3)
                  " ctor(s): "
                  (string/join (map print/ctor a3) "; ")
                  ")")
          (string "data "
                  name
                  (if (zero? (length a2))
                    ""
                    (string "(" (string/join (map print/binder a2) ", ") ")"))
                  " : "
                  (print/node a3)
                  " ("
                  (length a4)
                  " ctor(s))")))

      (= tag :decl/func)
      (string "def " (decl 1) " : " (print/node (decl 2)) " (" (length (decl 3)) " clause(s))")

      (= tag :decl/record)
      (string "record " (decl 1) " (" (length (decl 2)) " entry(ies))")

      (= tag :decl/compute)
      (string "compute " (print/node (decl 1)))

      (= tag :decl/check)
      (string "check " (print/node (decl 1)) " : " (print/node (decl 2)))

      (= tag :core/data)
      (string "data "
              (decl 1)
              (if (zero? (length (decl 2)))
                ""
                (string "(" (string/join (map print/binder (decl 2)) ", ") ")"))
              " (core, "
              (length (decl 4))
              " ctor(s))")

      (= tag :core/func)
      (string "def "
              (decl 1)
              (if (zero? (length (decl 2)))
                ""
              (string "(" (string/join (map print/binder (decl 2)) ", ") ")"))
              " : "
              (pp/print/tm (decl 3))
              " (core, "
              (length (decl 5))
              " clause(s))")

      (= tag :core/compute)
      (string "compute " (pp/print/tm (decl 1)))

      (= tag :core/check)
      (string "check " (pp/print/tm (decl 1)) " : " (pp/print/tm (decl 2)))

      true
      (string "unknown declaration: " (string/format "%v" decl)))))

(defn- surface-file? [path]
  (string/has-suffix? ".requiem" path))

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

(defn run/file-surface [path]
  (def start (os/clock))
  (def src (string (slurp path)))
  (print "Parsing (surface) " path "...")
  (def prog (sp/parse/program src))
  (def lowered (sp/lower/program prog))
  (print "Lowered declarations: " (length lowered))
  (each decl lowered
    (print "  - " (decl/summary decl)))
  (def core (e/elab/program lowered))
  (print "Elaborated core declarations: " (length core))
  (def global-ctx (build-global-ctx core))
  (def ctor-env (build-ctor-env core))
  (array/clear tt/goals) # Reset goals
  (tt/goals/set-collect! true)
  (each decl core
    (match decl
      [:core/func name params result ty clauses]
      (do
        (let [Γ (binders->ctx params global-ctx)
              expected result]
          (each c clauses
            (check/with-ctors Γ (c 2) expected ctor-env))))

      [:core/compute tm]
      (do
        (printf "\nCompute: %s" (pp/print/tm tm))
        (let [res (tt/nf (tt/ty/type 100) tm)]
          (printf "  => %s" (pp/print/nf res))))
      [:core/check tm ty]
      (do
        (printf "\nCheck: %s : %s" (pp/print/tm tm) (pp/print/tm ty))
        (check/with-ctors global-ctx tm ty ctor-env)
        (print "  => OK"))
      _ nil))
  (tt/goals/set-collect! false)
  
  (let [pending tt/goals]
    (when (> (length pending) 0)
      (print "\nPending Goals:")
      (each g pending
        (printf "  ?%v : %s" (g :name) (pp/print/nf (g :expected)))
        (each c (g :ctx)
          (printf "    %v : %s" (c 0) (pp/print/nf (c 1)))))))

  (print "")
  (def elapsed (- (os/clock) start))
  (printf "Done. %d declaration(s) in %.3fs" (length lowered) elapsed))

(defn run/file-sexpr [path]
  (def start (os/clock))
  (def src (slurp path))
  (print "Parsing (sexpr) " path "...")
  (def forms (p/parse/text src))
  (def interactions (length forms))
  (print "Parsed " interactions " interaction(s)")
  (def lowered (l/lower/program forms))
  (print "Lowered declarations: " (length lowered))
  (each decl lowered
    (print "  - " (decl/summary decl)))
  (def core (e/elab/program lowered))
  (print "Elaborated core declarations: " (length core))
  (def elapsed (- (os/clock) start))
  (printf "Done. %d interaction(s) in %.3fs" interactions elapsed))

(defn run/file [path]
  (if (surface-file? path)
    (run/file-surface path)
    (run/file-sexpr path)))

(defn main [& args]
  (def n (length args))
  (if (zero? n)
    (do
      (print "Usage: requiem <file.requiem>")
      (os/exit 1))
    (run/file (args (- n 1)))))
