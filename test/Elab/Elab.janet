#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/sig :as s)
(import ../../src/elab :as e)
(import ../../src/coreTT :as tt)
(import ../../src/frontend/sexpr/parser :as p)

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

(test/assert suite
  (let [node (p/parse/one "(J Type1 Type0 (fn (y) (fn (p) (Id Type1 Type0 y))) (refl Type0) Type0 (refl Type0))")
        term ((e/exports :term/elab) @[] node)
        inferred (tt/infer-top term)]
    (and (= (term 0) :t-J)
         (= (get inferred 0) tt/T/Id)))
  "Elaborated J motives typecheck end-to-end")

(test/end-suite suite)
