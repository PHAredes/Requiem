#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/frontend/surface/ast :as a)

(def suite (test/start-suite "Surface AST"))

(def sp (a/span/none))
(def binder (a/ty/binder "A" (a/ty/universe 0 sp) sp))
(def body (a/ty/name "A" sp))

(test/assert suite
  (= (a/span/none) [:span [:pos 1 1 0] [:pos 1 1 0]])
  "Missing spans use the explicit sentinel")

(test/assert suite
  (= (a/ty/forall binder body sp)
     (a/ty/pi binder body sp))
  "Forall is a direct alias for Pi")

(test/assert suite
  (= (a/ty/exists binder body sp)
     (a/ty/sigma binder body sp))
  "Exists is a direct alias for Sigma")

(test/assert suite
  (and (a/node/type? (a/ty/op "+" @[] sp))
       (a/node/term? (a/tm/op "+" @[] sp))
       (a/node/pat? (a/pat/con "zero" @[] sp))
       (a/node/decl? (a/decl/compute (a/tm/nat 0 sp) sp))
       (a/node/decl? (a/decl/check (a/tm/nat 0 sp) (a/ty/universe 0 sp) sp))
       (not (a/node/decl? (a/program @[] sp))))
  "Node predicates classify each surface family")

(test/assert-error suite
  (fn []
    (a/ast/set-debug-checks! true)
    (a/tm/nat -1 sp))
  "Debug checks reject invalid naturals"
  "tm/nat.value >= 0")

(a/ast/set-debug-checks! false)

(test/end-suite suite)
