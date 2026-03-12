#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/matches :as m)

(def suite (test/start-suite "Elab Matches"))

(def ctor-set @{"zero" true "succ" true "vnil" true "vcons" true})

(test/assert suite
  (let [result (m/matches [:atom "zero"] [:pat/con "zero" @[]] ctor-set)]
    (and (= (result 0) :yes)
         (= (length (kvs (result 1))) 0)))
  "0-ary constructor matches")

(test/assert suite
  (let [result (m/matches [:var "zero"] [:pat/con "zero" @[]] ctor-set)]
    (and (= (result 0) :yes)
         (= (length (kvs (result 1))) 0)))
  "Constructor head also matches when represented as :var")

(test/assert suite
  (= (m/matches [:atom "zero"] [:pat/con "succ" @[]] ctor-set)
     [:no])
  "Different constructors mismatch")

(test/assert suite
  (= (m/matches [:napp [:nvar "f"] [:var "x"]]
                [:pat/con "zero" @[]]
                ctor-set)
     [:stuck])
  "Neutral selector yields :stuck")

(test/assert suite
  (= (m/matches [:var "n"] [:pat/con "zero" @[]] ctor-set)
     [:stuck])
  "Non-constructor variable head yields :stuck")

(test/assert suite
  (let [result (m/matches [:var "zero"] [:pat/var "x"] ctor-set)]
    (and (= (result 0) :yes)
         (= (get (result 1) "x") [:var "zero"])))
  "Variable pattern binds selector")

(test/assert suite
  (let [result (m/matches* @[[:var "zero"] [:var "zero"]]
                           @[[:pat/var "x"] [:pat/var "x"]]
                           ctor-set)]
    (and (= (result 0) :yes)
         (= (get (result 1) "x") [:var "zero"])))
  "Repeated variable with consistent values succeeds")

(test/assert suite
  (= (m/matches* @[[:var "zero"] [:app [:var "succ"] [:var "zero"]]]
                 @[[:pat/var "x"] [:pat/var "x"]]
                 ctor-set)
     [:no])
  "Repeated variable with conflicting values fails")

(test/assert suite
  (= (m/pat/to-term [:pat/con "succ" @[[:pat/con "zero" @[]]]])
     [:app [:atom "succ"] [:atom "zero"]])
  "pat/to-term builds left-associated constructor application")

(test/assert suite
  (let [p [:pat/con "vcons" @[[:pat/var "x"] [:pat/con "vnil" @[]]]]
        t (m/pat/to-term p)
        result (m/matches t p ctor-set)]
    (and (= (result 0) :yes)
         (= (get (result 1) "x") [:var "x"])))
  "pat/to-term round-trips through matches")

(test/end-suite suite)
