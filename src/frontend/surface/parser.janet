#!/usr/bin/env janet

(import ./ast :as a)
(import ./syntax :as x)
(import ./pratt :as pr)
(import ./patterns :as pat)
(import ./decls :as d)

(def parse/type-text pr/parse/type-text)
(def parse/expr-text pr/parse/expr-text)
(def parse/pat-text pat/parse/pat-text)
(def parse/source d/parse/source)

(defn parse/type [xv &opt prec sx]
  (if (string? xv)
    (parse/type-text xv (or prec @{}) (or sx (x/syntax/default)))
    xv))

(defn parse/expr [xv &opt prec sx]
  (if (string? xv)
    (parse/expr-text xv (or prec @{}) (or sx (x/syntax/default)))
    xv))

(defn parse/pat [xv]
  (if (string? xv)
    (parse/pat-text xv)
    xv))

(defn parse/program [xv &opt sx]
  (if (string? xv)
    (parse/source xv (or sx (x/syntax/default)))
    xv))

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
