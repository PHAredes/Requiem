#!/usr/bin/env janet

(import ../../surface :as s)

(def ast/debug-checks? s/ast/debug-checks?)
(def ast/set-debug-checks! s/ast/set-debug-checks!)

(def pos s/pos)
(def span s/span)
(def span/none s/span/none)

(def ty/hole s/ty/hole)
(def ty/universe s/ty/universe)
(def ty/name s/ty/name)
(def ty/var s/ty/var)
(def ty/app s/ty/app)
(def ty/arrow s/ty/arrow)
(def ty/binder s/ty/binder)
(def ty/pi s/ty/pi)
(def ty/forall s/ty/forall)
(def ty/sigma s/ty/sigma)
(def ty/exists s/ty/exists)
(def ty/op s/ty/op)

(def tm/hole s/tm/hole)
(def tm/var s/tm/var)
(def tm/ref s/tm/ref)
(def tm/nat s/tm/nat)
(def tm/app s/tm/app)
(def tm/lam s/tm/lam)
(def tm/let s/tm/let)
(def tm/op s/tm/op)

(def pat/wild s/pat/wild)
(def pat/hole s/pat/hole)
(def pat/var s/pat/var)
(def pat/con s/pat/con)
(def pat/nat s/pat/nat)

(def decl/param s/decl/param)
(def decl/field-named s/decl/field-named)
(def decl/field-anon s/decl/field-anon)
(def decl/ctor-plain s/decl/ctor-plain)
(def decl/ctor-indexed s/decl/ctor-indexed)
(def decl/clause s/decl/clause)
(def decl/prec s/decl/prec)
(def decl/data s/decl/data)
(def decl/func s/decl/func)

(def program s/program)

(def node/tag s/node/tag)
(def node/span s/node/span)
(def node/type? s/node/type?)
(def node/term? s/node/term?)
(def node/pat? s/node/pat?)
(def node/decl? s/node/decl?)

(def exports
  {:ast/debug-checks? ast/debug-checks?
   :ast/set-debug-checks! ast/set-debug-checks!
   :pos pos
   :span span
   :span/none span/none
   :ty/hole ty/hole
   :ty/universe ty/universe
   :ty/name ty/name
   :ty/var ty/var
   :ty/app ty/app
   :ty/arrow ty/arrow
   :ty/binder ty/binder
   :ty/pi ty/pi
   :ty/forall ty/forall
   :ty/sigma ty/sigma
   :ty/exists ty/exists
   :ty/op ty/op
   :tm/hole tm/hole
   :tm/var tm/var
   :tm/ref tm/ref
   :tm/nat tm/nat
   :tm/app tm/app
   :tm/lam tm/lam
   :tm/let tm/let
   :tm/op tm/op
   :pat/wild pat/wild
   :pat/hole pat/hole
   :pat/var pat/var
   :pat/con pat/con
   :pat/nat pat/nat
   :decl/param decl/param
   :decl/field-named decl/field-named
   :decl/field-anon decl/field-anon
   :decl/ctor-plain decl/ctor-plain
   :decl/ctor-indexed decl/ctor-indexed
   :decl/clause decl/clause
   :decl/prec decl/prec
   :decl/data decl/data
   :decl/func decl/func
   :program program
   :node/tag node/tag
   :node/span node/span
   :node/type? node/type?
   :node/term? node/term?
   :node/pat? node/pat?
   :node/decl? node/decl?})
