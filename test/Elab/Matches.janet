#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/matches :as m)

(test/start-suite "Elab Matches")

(def ctor-set @{"zero" true "succ" true "vnil" true "vcons" true})

(test/assert
  (let [result (m/matches [:atom "zero"] [:pat/con "zero" @[]] ctor-set)]
    (and (= (result 0) :yes)
         (= (length (kvs (result 1))) 0)))
  "0-ary constructor matches")

(test/assert
  (let [result (m/matches [:var "zero"] [:pat/con "zero" @[]] ctor-set)]
    (and (= (result 0) :yes)
         (= (length (kvs (result 1))) 0)))
  "Constructor head also matches when represented as :var")

(test/assert
  (= (m/matches [:atom "zero"] [:pat/con "succ" @[]] ctor-set)
     [:no])
  "Different constructors mismatch")

(test/assert
  (= (m/matches [:napp [:nvar "f"] [:var "x"]]
                [:pat/con "zero" @[]]
                ctor-set)
     [:stuck])
  "Neutral selector yields :stuck")

(test/assert
  (= (m/matches [:var "n"] [:pat/con "zero" @[]] ctor-set)
     [:stuck])
  "Non-constructor variable head yields :stuck")

(test/assert
  (let [result (m/matches [:var "zero"] [:pat/var "x"] ctor-set)]
    (and (= (result 0) :yes)
         (= (get (result 1) "x") [:var "zero"])))
  "Variable pattern binds selector")

(test/assert
  (let [result (m/matches* @[[:var "zero"] [:var "zero"]]
                           @[[:pat/var "x"] [:pat/var "x"]]
                           ctor-set)]
    (and (= (result 0) :yes)
         (= (get (result 1) "x") [:var "zero"])))
  "Repeated variable with consistent values succeeds")

(test/assert
  (= (m/matches* @[[:var "zero"] [:app [:var "succ"] [:var "zero"]]]
                 @[[:pat/var "x"] [:pat/var "x"]]
                 ctor-set)
     [:no])
  "Repeated variable with conflicting values fails")

(test/assert
  (= (m/pat/to-term [:pat/con "succ" @[[:pat/con "zero" @[]]]])
     [:app [:atom "succ"] [:atom "zero"]])
  "pat/to-term builds left-associated constructor application")

(test/assert
  (let [p [:pat/con "vcons" @[[:pat/var "x"] [:pat/con "vnil" @[]]]]
        t (m/pat/to-term p)
        result (m/matches t p ctor-set)]
    (and (= (result 0) :yes)
         (= (get (result 1) "x") [:var "x"])))
  "pat/to-term round-trips through matches")

(test/end-suite)
