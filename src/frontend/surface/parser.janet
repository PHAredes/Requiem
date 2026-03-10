#!/usr/bin/env janet

(import ./ast :as a)
(import ./syntax :as x)
(import ./pratt :as pr)
(import ./patterns :as pat)
(import ./decls :as d)

(def ast/debug-checks? a/ast/debug-checks?)
(def ast/set-debug-checks! a/ast/set-debug-checks!)

(def syntax/default x/syntax/default)
(def syntax/clone x/syntax/clone)
(def syntax/add-literal! x/syntax/add-literal!)
(def syntax/add-quant-alias! x/syntax/add-quant-alias!)
(def syntax/add-type-ident-resolver! x/syntax/add-type-ident-resolver!)

(def pos a/pos)
(def span a/span)
(def span/none a/span/none)

(def ty/hole a/ty/hole)
(def ty/universe a/ty/universe)
(def ty/name a/ty/name)
(def ty/var a/ty/var)
(def ty/app a/ty/app)
(def ty/arrow a/ty/arrow)
(def ty/binder a/ty/binder)
(def ty/pi a/ty/pi)
(def ty/forall a/ty/forall)
(def ty/sigma a/ty/sigma)
(def ty/exists a/ty/exists)
(def ty/op a/ty/op)

(def tm/hole a/tm/hole)
(def tm/var a/tm/var)
(def tm/ref a/tm/ref)
(def tm/nat a/tm/nat)
(def tm/app a/tm/app)
(def tm/lam a/tm/lam)
(def tm/let a/tm/let)
(def tm/op a/tm/op)

(def pat/wild a/pat/wild)
(def pat/hole a/pat/hole)
(def pat/var a/pat/var)
(def pat/con a/pat/con)
(def pat/nat a/pat/nat)

(def decl/param a/decl/param)
(def decl/field-named a/decl/field-named)
(def decl/field-anon a/decl/field-anon)
(def decl/ctor-plain a/decl/ctor-plain)
(def decl/ctor-indexed a/decl/ctor-indexed)
(def decl/clause a/decl/clause)
(def decl/prec a/decl/prec)
(def decl/data a/decl/data)
(def decl/func a/decl/func)

(def program a/program)

(def node/tag a/node/tag)
(def node/span a/node/span)
(def node/type? a/node/type?)
(def node/term? a/node/term?)
(def node/pat? a/node/pat?)
(def node/decl? a/node/decl?)

(def parse/type-text pr/parse/type-text)
(def parse/expr-text pr/parse/expr-text)
(def parse/pat-text pat/parse/pat-text)
(def parse/source d/parse/source)

(defn parse/type [xv &opt prec sx]
  (if (string? xv)
    (parse/type-text xv (or prec @{}) (or sx (x/syntax/default)))
    (do
      (when (and (a/ast/debug-checks?) (not (a/node/type? xv)))
        (errorf "parse/type expected type node, got: %v" xv))
      xv)))

(defn parse/expr [xv &opt prec sx]
  (if (string? xv)
    (parse/expr-text xv (or prec @{}) (or sx (x/syntax/default)))
    (do
      (when (and (a/ast/debug-checks?) (not (a/node/term? xv)))
        (errorf "parse/expr expected term node, got: %v" xv))
      xv)))

(defn parse/pat [xv]
  (if (string? xv)
    (parse/pat-text xv)
    (do
      (when (and (a/ast/debug-checks?) (not (a/node/pat? xv)))
        (errorf "parse/pat expected pattern node, got: %v" xv))
      xv)))

(defn parse/program [xv &opt sx]
  (if (string? xv)
    (parse/source xv (or sx (x/syntax/default)))
    (do
      (when (and (a/ast/debug-checks?) (not= (a/node/tag xv) :program))
        (errorf "parse/program expected :program node, got: %v" xv))
      xv)))

(def exports
  {:ast/debug-checks? a/ast/debug-checks?
   :ast/set-debug-checks! a/ast/set-debug-checks!
   :syntax/default x/syntax/default
   :syntax/clone x/syntax/clone
   :syntax/add-literal! x/syntax/add-literal!
   :syntax/add-quant-alias! x/syntax/add-quant-alias!
   :syntax/add-type-ident-resolver! x/syntax/add-type-ident-resolver!
   :pos a/pos
   :span a/span
   :span/none a/span/none

   :ty/hole a/ty/hole
   :ty/universe a/ty/universe
   :ty/name a/ty/name
   :ty/var a/ty/var
   :ty/app a/ty/app
   :ty/arrow a/ty/arrow
   :ty/binder a/ty/binder
   :ty/pi a/ty/pi
   :ty/forall a/ty/forall
   :ty/sigma a/ty/sigma
   :ty/exists a/ty/exists
   :ty/op a/ty/op

   :tm/hole a/tm/hole
   :tm/var a/tm/var
   :tm/ref a/tm/ref
   :tm/nat a/tm/nat
   :tm/app a/tm/app
   :tm/lam a/tm/lam
   :tm/let a/tm/let
   :tm/op a/tm/op

   :pat/wild a/pat/wild
   :pat/hole a/pat/hole
   :pat/var a/pat/var
   :pat/con a/pat/con
   :pat/nat a/pat/nat

   :decl/param a/decl/param
   :decl/field-named a/decl/field-named
   :decl/field-anon a/decl/field-anon
   :decl/ctor-plain a/decl/ctor-plain
   :decl/ctor-indexed a/decl/ctor-indexed
   :decl/clause a/decl/clause
   :decl/prec a/decl/prec
   :decl/data a/decl/data
   :decl/func a/decl/func
   :program a/program

   :node/tag a/node/tag
   :node/span a/node/span
   :node/type? a/node/type?
   :node/term? a/node/term?
   :node/pat? a/node/pat?
   :node/decl? a/node/decl?

   :parse/type parse/type
   :parse/expr parse/expr
   :parse/pat parse/pat
   :parse/type-text parse/type-text
   :parse/expr-text parse/expr-text
   :parse/pat-text parse/pat-text
   :parse/source parse/source
   :parse/program parse/program})
