#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/coreTT :as c)

(def suite (test/start-suite "Core Subtyping"))

# Type subtyping laws
(let [U0 (c/ty/type 0)
      U1 (c/ty/type 1)
      U2 (c/ty/type 2)]
  (test/assert suite
    (c/subtype U1 U1)
    "Type subtyping is reflexive")

  (test/assert suite
    (and (c/subtype U0 U1)
         (c/subtype U1 U2)
         (c/subtype U0 U2))
    "Type subtyping is transitive"))

# Pi subtyping laws with dependent codomain
(let [dep-pi2 (c/ty/pi (c/ty/type 2) (fn [A] A))
      dep-pi1 (c/ty/pi (c/ty/type 1) (fn [A] A))
      dep-pi0 (c/ty/pi (c/ty/type 0) (fn [A] A))]
  (test/assert suite
    (c/subtype dep-pi1 dep-pi1)
    "Pi subtyping is reflexive")

  (test/assert suite
    (and (c/subtype dep-pi2 dep-pi1)
         (c/subtype dep-pi1 dep-pi0)
         (c/subtype dep-pi2 dep-pi0))
    "Pi subtyping is transitive")

  (let [Γ (c/ctx/add (c/ctx/empty) "f" dep-pi2)]
    (test/assert suite
      (c/check Γ [:var "f"] dep-pi1)
      "Checker applies Pi subsumption with dependent codomain")))

# Sigma subtyping laws with dependent second component
(let [dep-sig1 (c/ty/sigma (c/ty/type 1) (fn [A] A))
      dep-sig2 (c/ty/sigma (c/ty/type 2) (fn [A] A))
      dep-sig3 (c/ty/sigma (c/ty/type 3) (fn [A] A))]
  (test/assert suite
    (c/subtype dep-sig2 dep-sig2)
    "Sigma subtyping is reflexive")

  (test/assert suite
    (and (c/subtype dep-sig1 dep-sig2)
         (c/subtype dep-sig2 dep-sig3)
         (c/subtype dep-sig1 dep-sig3))
    "Sigma subtyping is transitive")

  (let [Γ (c/ctx/add (c/ctx/empty) "p" dep-sig1)]
    (test/assert suite
      (c/check Γ [:var "p"] dep-sig2)
      "Checker applies Sigma subsumption with dependent codomain")))

(test/end-suite suite)
