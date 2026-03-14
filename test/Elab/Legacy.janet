#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/elab_legacy :as el)

(def suite (test/start-suite "Elab Legacy"))

(defn atom [x] [:atom x])
(defn lst [xs] [:list xs])

(def legacy-forms
  @[(lst @[(atom "data")
           (atom "Nat:")
           (atom "Type")
           (lst @[(lst @[(atom "zero") (atom "Nat")])])])
    (lst @[(atom "def")
           (atom "zero-id:")
           (atom "Nat")
           (atom "zero")])])

(test/assert suite
  (let [core ((el/exports :elab/forms) legacy-forms)]
    (and (= (length core) 2)
         (= ((core 0) 0) :core/data)
         (= ((core 1) 0) :core/func)))
  "Legacy elab/forms still elaborates deprecated sexpr programs")

(test/assert suite
  (let [src "(data Nat: Type ((zero Nat)))\n(def zero-id: Nat zero)"
        core ((el/exports :elab/text) src)]
    (and (= (length core) 2)
         (= ((core 0) 0) :core/data)
         (= ((core 1) 0) :core/func)))
  "Legacy elab/text still parses and elaborates deprecated sexpr source")

(test/end-suite suite)
