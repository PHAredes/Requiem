#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/sig :as s)
(import ../../src/coreTT :as tt)

(defn mk-nat-sig []
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
    sig))

(defn mk-vec-sig []
  (let [sig (mk-nat-sig)]
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
                                 {:name "xs" :type [:app [:var "Vec"] [:var "A"] [:var "k"]]}]}
                    ])
    sig))

(def suite (test/start-suite "Elab Signature"))

(test/assert suite
  (let [names (s/sig/ctor-name-set (mk-nat-sig))]
    (and (has-key? names "zero")
         (has-key? names "succ")))
  "Constructor name set contains all constructors")

(test/assert suite
  (let [sig (mk-nat-sig)
        available (s/sig/available-ctors sig "Nat" @[])]
    (= (length available) 2))
  "Unindexed constructors are available")

(test/assert suite
  (let [sig (mk-vec-sig)
        available (s/sig/available-ctors sig
                                         "Vec"
                                         @[[:var "zero"]])]
    (and (= (length available) 1)
         (let [ctor ((available 0) :ctor)]
           (= (ctor :name) "vnil"))))
  "Indexed constructor filtering uses matches")

(test/assert suite
  (let [sig (mk-nat-sig)]
    (do
      (s/sig/add-func sig
                      "id"
                      @[{:name "x" :type [:var "Nat"]}]
                      [:var "Nat"]
                      [:t-pi [:var "Nat"] (fn [_] [:var "Nat"])] )
       (let [ref (s/sig/delta-ref sig "id")]
          (= (ref 0) :lam))) )
  "Delta-ref eta-expands bare function names")

(test/assert suite
  (let [sig (mk-nat-sig)]
    (do
      (s/sig/add-func sig
                      "id"
                      @[{:name "x" :type [:var "Nat"]}]
                      [:var "Nat"]
                      [:t-pi [:var "Nat"] (fn [_] [:var "Nat"])] )
      (let [ref (s/sig/delta-ref sig "id")]
        (= (ref 0) :lam))) )
  "Delta-ref keeps exact application semantics")

(test/assert suite
  (let [sig (mk-nat-sig)]
    (do
      (s/sig/add-func sig
                      "id"
                      @[{:name "x" :type [:var "Nat"]}]
                      [:var "Nat"]
                      [:t-pi [:var "Nat"] (fn [_] [:var "Nat"])] )
      (let [ref (s/sig/delta-ref sig "id")
            body (ref 1)
            arg [:var "n"]
            app (body arg)]
        (= app [:app [:var "id"] [:var "n"]]))))
  "Delta-ref threads lambda binders into the spine")

(test/assert-error suite
  (fn []
    (let [sig (mk-nat-sig)]
      (s/sig/delta-ref sig "Nat")))
  "Delta-ref rejects non-function names")

(test/assert suite
  (let [sig (s/sig/build
              @[
                [:core/data
                 "Nat"
                 @[]
                 (tt/tm/type 0)
                 @[
                   [:core/ctor "zero" @[] @[] @[] [:var "Nat"]]
                   [:core/ctor "succ" @[] @[] @[[:bind "n" [:var "Nat"]]] [:var "Nat"]]
                 ]]
                [:core/func
                 "id"
                 @[[:bind "x" [:var "Nat"]]]
                 [:var "Nat"]
                 [:t-pi [:var "Nat"] (fn [_] [:var "Nat"])]
                 @[]]
              ])]
    (and (= ((s/sig/ctor sig "Nat" "zero") :name) "zero")
         (= (length (s/sig/available-ctors sig "Nat" @[])) 2)
         (= ((s/sig/delta-ref sig "id") 0) :lam)))
  "Signature build normalizes core declarations for lookups")

(test/end-suite suite)
