#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/sig :as s)
(import ../../src/elab :as e)
(import ../../src/coreTT :as tt)
(import ../../src/levels :as lvl)

(defn mk-sig []
  (let [sig (s/sig/empty)]
    (s/sig/add-data sig
                    "Nat"
                    @[]
                    (tt/tm/type 0)
                    @[
                      {:name "zero" :patterns @[] :params @[]}
                      {:name "succ"
                       :patterns @[]
                       :params @[{:name "n" :type [:var "Nat"]}]}
                    ])
    (s/sig/add-data sig
                    "Vec"
                    @[{:name "A" :type (tt/tm/type 0)}
                      {:name "n" :type [:var "Nat"]}]
                    (tt/tm/type 0)
                    @[
                      {:name "vnil"
                       :patterns @[[:pat/con "zero" @[]]]
                       :params @[]}
                      {:name "vcons"
                       :patterns @[[:pat/con "succ" @[[:pat/var "k"]]]]
                       :params @[{:name "x" :type [:var "A"]}
                                 {:name "xs" :type [:var "VecTail"]}]}
                    ])
    (s/sig/add-func sig
                    "id"
                    @[{:name "x" :type [:var "Nat"]}]
                    [:var "Nat"]
                    [:t-pi [:var "Nat"] (fn [_] [:var "Nat"])])
    sig))

(def suite (test/start-suite "Elab Bridge"))

(test/assert suite
  (let [state (e/elab/state)
        h1 (e/elab/hole state "a")
        h2 (e/elab/hole state "a")
        h3 (e/elab/hole state nil)]
    (and (= h1 h2)
         (not= h1 h3)
         (= (length (state :constraints)) 2)))
  "Named holes share metavar; anonymous holes are fresh")

(test/assert suite
  (let [sig (mk-sig)
        env {:check-arg (fn [_env _sig arg _ty] arg)}
        result (e/elab/ctor-call env
                                 sig
                                 "Vec"
                                 @[[:var "zero"]]
                                 "vnil"
                                 @[])]
    (= ((result :term) 0) :var))
  "IxCall succeeds for available constructor")

(test/assert-error suite
  (fn []
    (let [sig (mk-sig)
          env {:check-arg (fn [_env _sig arg _ty] arg)}]
      (e/elab/ctor-call env
                        sig
                        "Vec"
                        @[[:var "zero"]]
                        "vcons"
                        @[[:var "x"] [:var "xs"]])))
  "IxCall rejects unavailable constructor")

(test/assert-error suite
  (fn []
    (let [sig (mk-sig)
          env {:check-arg (fn [_env _sig arg _ty] arg)}]
      (e/elab/ctor-call env
                        sig
                        "Vec"
                        @[[:nvar "n"]]
                        "vcons"
                        @[[:var "x"] [:var "xs"]])))
  "IxCall reports stuck availability for neutral indices")

(test/assert suite
  (let [sig (mk-sig)
        ref (e/elab/func-ref sig "id")]
    (= (ref 0) :lam))
  "Function references elaborate to exact-ref")

(test/assert suite
  (let [program (e/elab/program
                  @[
                    [:decl/func "alias-id"
                     @[]
                     [:list @[[:atom "Nat"] [:atom "->"] [:atom "Nat"]]]
                     @[
                       [:clause @[]
                        [:list @[[:atom "lambda"]
                                 [:list @[[:atom "x"]]]
                                 [:atom "x"]]]]
                     ]]
                  ])
        clause-body ((((program 0) 5) 0) 2)]
    (= (clause-body 0) :lam))
  "Dispatch aliases normalize lambda spellings")

(test/assert suite
  (let [program (e/elab/program
                  @[
                    [:decl/func "sig-ty"
                     @[]
                     [:list @[[:atom "exists"]
                              [:list @[[:atom "x:"] [:atom "Nat"]]]
                              [:atom "."]
                              [:atom "Nat"]]
                     ]
                     @[
                       [:clause @[] [:atom "zero"]]
                     ]]
                  ])
        result ((program 0) 3)]
    (= (result 0) :t-sigma))
  "Dispatch aliases normalize sigma spellings")

(test/assert-error suite
  (fn []
    (e/elab/program
      @[
        [:decl/func "loop"
         @[[ :bind "n" [:atom "Nat"] ]]
         [:atom "Nat"]
         @[
           [:clause @[[:pat/con "zero" @[]]] [:atom "zero"]]
           [:clause @[[:pat/con "succ" @[[:pat/var "n"]]]]
            [:list @[[:atom "loop"] [:list @[[:atom "succ"] [:atom "n"]]]]]]
         ]]
      ]))
  "Program elaboration rejects non-terminating recursion"
  "termination check failed: loop")

(test/assert-error suite
  (fn []
    (e/elab/program
      @[
        [:decl/func "header-left"
         @[]
         [:atom "header-right"]
         @[
           [:clause @[] [:atom "zero"]]
         ]]
        [:decl/func "header-right"
         @[]
         [:atom "header-left"]
         @[
           [:clause @[] [:atom "zero"]]
         ]]
      ]))
  "Program elaboration rejects recursive cycles in function headers"
  "termination check failed: header-left")

(test/assert-error suite
  (fn []
    (e/elab/program
      @[
        [:decl/func "self-header"
         @[]
         [:atom "self-header"]
         @[
           [:clause @[] [:atom "zero"]]
         ]]
      ]))
  "Program elaboration rejects direct self-recursion in function headers"
  "termination check failed: self-header")

(test/assert-error suite
  (fn []
    (e/elab/program
      @[
        [:decl/func "header-pi-left"
         @[]
         [:list @[[:atom "Pi"]
                  [:list @[[:atom "Ann"] [:atom "x"] [:atom "Nat"]]]
                  [:atom "header-pi-right"]]]
         @[
           [:clause @[] [:atom "zero"]]
         ]]
        [:decl/func "header-pi-right"
         @[]
         [:list @[[:atom "Sigma"]
                  [:list @[[:atom "x:"] [:atom "Nat"]]]
                  [:atom "."]
                  [:atom "header-pi-left"]]]
         @[
           [:clause @[] [:atom "zero"]]
         ]]
      ]))
  "Program elaboration rejects recursive cycles in dependent headers"
  "termination check failed: header-pi")

(test/assert suite
  (let [program (e/elab/program
                  @[
                    [:decl/func "plus"
                     @[[ :bind "m" [:atom "Nat"] ]
                       [ :bind "n" [:atom "Nat"] ]]
                     [:atom "Nat"]
                     @[
                       [:clause @[[:pat/con "zero" @[]] [:pat/var "n"]] [:atom "n"]]
                       [:clause @[[:pat/con "succ" @[[:pat/var "m"]]] [:pat/var "n"]]
                        [:list @[[:atom "succ"]
                                 [:list @[[:atom "plus"] [:atom "m"] [:atom "n"]]]]]
                       ]]]
                   ])]
    (= ((program 0) 0) :core/func))
  "Program elaboration accepts structurally recursive functions")

(test/assert suite
  (let [motive-body [:list @[[ :atom "Id" ]
                               [:atom "Type1"]
                              [:atom "Type0"]
                              [:atom "y"]]]
        motive-inner [:list @[[ :atom "fn" ]
                               [:list @[[:atom "p"]]]
                               motive-body]]
        motive [:list @[[ :atom "fn" ]
                         [:list @[[:atom "y"]]]
                         motive-inner]]
        node [:list @[[ :atom "J" ]
                       [:atom "Type1"]
                       [:atom "Type0"]
                       motive
                       [:list @[[:atom "refl"] [:atom "Type0"]]]
                       [:atom "Type0"]
                       [:list @[[:atom "refl"] [:atom "Type0"]]]]]
        term ((e/exports :term/elab) @[] node)
        inferred (tt/infer-top term)]
    (and (= (term 0) :t-J)
         (= (get inferred 0) tt/T/Id)))
  "Raw elaboration nodes elaborate J motives end-to-end")

(test/assert suite
  (let [node [:tm/lam @["x"] [:tm/var "x" nil] nil]
        term ((e/exports :term/elab) @[] node)
        body (get term 1)
        fresh "fresh-x"]
    (and (= (term 0) :lam)
         (= (body fresh) fresh)))
  "Direct surface lambdas accept string params")

(test/assert suite
  (let [node [:ty/universe (lvl/uvar 'u) nil]
        term ((e/exports :term/elab) @[] node)
        inferred (tt/infer-top term)]
    (and (= term [:type (lvl/uvar 'u)])
         (= (get inferred 0) tt/T/Type)
         (lvl/eq? (get inferred 1)
                  (lvl/apply-shift (lvl/shift 1) (lvl/uvar 'u)))))
  "Elaboration preserves symbolic universe levels in direct AST input")

(test/assert suite
  (let [decls ((e/exports :record->decls)
               [:decl/record
                "id(A: Type): A -> A"
                @[
                  [:entry "x = x" @[]]
                ]])]
    (and (= (length decls) 1)
         (= ((decls 0) 0) :decl/func)))
  "Record desugaring reuses the surface parser for function-like records")

(test/assert suite
  (let [decls ((e/exports :record->decls)
               [:decl/record
                "Pair(A: Type):"
                @[
                  [:entry "mk"
                   @[
                     [:entry "(fst: A)" @[]]
                     [:entry "(snd: A)" @[]]
                   ]]
                ]])]
    (and (= (length decls) 2)
         (= ((decls 0) 0) :decl/func)
         (= ((decls 1) 0) :decl/func)))
  "Record sigma shorthand desugars into surface declarations without sexpr nodes")

(test/end-suite suite)
