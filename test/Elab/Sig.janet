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

(test/start-suite "Elab Signature")

(test/assert
  (let [names (s/sig/ctor-name-set (mk-nat-sig))]
    (and (has-key? names "zero")
         (has-key? names "succ")))
  "Constructor name set contains all constructors")

(test/assert
  (let [sig (mk-nat-sig)
        available (s/sig/available-ctors sig "Nat" @[])]
    (= (length available) 2))
  "Unindexed constructors are available")

(test/assert
  (let [sig (mk-vec-sig)
        available (s/sig/available-ctors sig
                                         "Vec"
                                         @[[:var "zero"]])]
    (and (= (length available) 1)
         (let [ctor ((available 0) :ctor)]
           (= (ctor :name) "vnil"))))
  "Indexed constructor filtering uses matches")

(test/assert
  (let [sig (mk-nat-sig)]
    (do
      (s/sig/add-func sig
                      "id"
                      @[{:name "x" :type [:var "Nat"]}]
                      [:var "Nat"]
                      [:t-pi [:var "Nat"] (fn [_] [:var "Nat"])] )
      (let [ref (s/sig/exact-ref sig "id")]
        (= (ref 0) :lam))) )
  "Exact-ref eta-expands bare function names")

(test/assert-error
  (fn []
    (let [sig (mk-nat-sig)]
      (s/sig/exact-ref sig "Nat")))
  "Exact-ref rejects non-function names")

(test/end-suite)
