#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/levels :as lvl)
(import ../../src/print :as printer)

(def suite (test/start-suite "Printer State"))

(def pp
  (printer/make {:T/Type 0x01
                 :T/Pi 0x02
                 :T/Sigma 0x04
                 :T/Id 0x08
                 :T/Refl 0x10
                 :T/Neutral 0x20
                 :T/Pair 0x40
                 :NF/Neut 0x100
                 :NF/Lam 0x200
                 :NF/Pi 0x400
                 :NF/Sigma 0x800
                 :NF/Type 0x1000
                 :NF/Pair 0x2000
                 :NF/Id 0x4000
                 :NF/Refl 0x8000
                 :ty/type (fn [l] [:type l])
                 :lower (fn [_ sem] sem)
                 :lvl/str lvl/str}))

(def print/tm (pp :print/tm))

(test/assert suite
  (= "a"
     (print/tm [:var "_x"]))
  "Printer renders internal names with fresh aliases")

(test/assert suite
  (let [tm [:app [:var "_f"] [:var "_x"]]]
    (= (print/tm tm) (print/tm tm)))
  "Printer state resets between top-level calls")

(test/assert suite
  (let [names (map (fn [i] (string "_x" i)) (range 27))
        tm (reduce (fn [acc x]
                     [:app acc [:var x]])
                   [:var (names 0)]
                   (slice names 1))
        rendered (print/tm tm)]
    (and (not (nil? (string/find "a b" rendered)))
         (not (nil? (string/find "z) aa" rendered)))))
  "Printer alpha names continue past z")

(test/assert-error suite
  (fn []
    (print/tm [:lam (fn [_] (error "boom"))]))
  "Printer surfaces body rendering errors")

(test/assert suite
  (= "a"
     (print/tm [:var "_x"]))
  "Printer restores state after failed render")

(test/assert suite
  (= "Typeu + 2"
     (print/tm [:type (lvl/apply-shift (lvl/shift 2) (lvl/uvar 'u))]))
  "Printer renders symbolic universe levels")

(test/end-suite suite)
