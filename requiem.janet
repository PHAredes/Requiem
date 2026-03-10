#!/usr/bin/env janet

(import ./src/frontend/sexpr/parser :as p)
(import ./src/frontend/sexpr/lower :as l)
(import ./src/frontend/surface/parser :as sp)
(import ./src/elab :as e)
(import ./src/coreTT :as tt)
(import ./src/matches :as mt)

(defn decl/summary [decl]
  (match decl
    [:decl/data name _ _ ctors]
    (string "data " name " (" (length ctors) " constructor(s))")
    [:decl/func name params _ clauses]
    (string "def " name " (" (length params) " param(s), " (length clauses) " clause(s))")
    [:decl/record header entries]
    (string "record " header " (" (length entries) " entry(ies))")
    [:decl/compute tm]
    (string "compute " (string/format "%v" tm))
    [:decl/compute tm _]
    (string "compute " (string/format "%v" tm))
    [:decl/check tm ty]
    (string "check " (string/format "%v" tm) " : " (string/format "%v" ty))
    [:decl/check tm ty _]
    (string "check " (string/format "%v" tm) " : " (string/format "%v" ty))
    [:core/data name params _ _]
    (string "data " name " (core)")
    [:core/func name params _ _ _]
    (string "def " name " (core)")
    [:core/compute tm]
    (string "compute " (string/format "%v" tm))
    [:core/check tm ty]
    (string "check " (string/format "%v" tm) " : " (string/format "%v" ty))
    _
    (string "unknown declaration: " (string/format "%v" decl))))

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
  (if (zero? (length params))
    (tt/eval Γ result-core)
    (let [b (params 0)
          name (b 1)
          dom (tt/eval Γ (b 2))
          rest (slice params 1)]
      (tt/ty/pi dom
                (fn [x]
                  (binders->pi-sem (tt/ctx/add Γ name x) rest result-core))))))

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
  (let [[head args] (term/spine tm)
        info (and head (get (ctor-env :ctors) head))]
    (if (nil? info)
      (tt/check Γ tm (tt/eval Γ expected-core))
      (let [[exp-head exp-args] (term/spine expected-core)]
        (if (or (nil? exp-head) (not= exp-head (info :data)))
          (tt/check Γ tm (tt/eval Γ expected-core))
          (let [ctor (info :ctor)
                patterns (ctor 3)
                result (if (zero? (length patterns))
                         (mt/outcome/yes (mt/subst/empty))
                         (mt/matches* exp-args patterns (ctor-env :ctor-name-set) (mt/subst/empty)))]
            (if (mt/outcome/yes? result)
              (let [sigma (mt/outcome/subst result)
                    params (ctor 4)]
                (when (not= (length args) (length params))
                  (errorf "constructor %v expects %d argument(s), got %d"
                          head
                          (length params)
                          (length args)))
                (for i 0 (length params)
                  (let [arg (args i)
                        param-ty (term/subst ((params i) 2) sigma)]
                    (check/with-ctors Γ arg param-ty ctor-env)))
                true)
              (tt/check Γ tm (tt/eval Γ expected-core)))))))))

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
        (printf "\nCompute: %v" tm)
        (let [res (tt/nf (tt/ty/type 100) tm)]
          (printf "  => %s" (tt/nf/print res))))
      [:core/check tm ty]
      (do
        (printf "\nCheck: %v : %v" tm ty)
        (check/with-ctors global-ctx tm ty ctor-env)
        (print "  => OK"))
      _ nil))
  (tt/goals/set-collect! false)
  
  (let [pending tt/goals]
    (when (> (length pending) 0)
      (print "\nPending Goals:")
      (each g pending
        (printf "  ?%v : %s" (g :name) (tt/nf/print (g :expected)))
        (each c (g :ctx)
          (printf "    %v : %s" (c 0) (tt/nf/print (c 1)))))))

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
