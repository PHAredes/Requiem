#!/usr/bin/env janet

(import ./ast :as a)
(import ./syntax :as x)
(import ./lexer :as lx)
(import ./pratt :as pr)
(import ./patterns :as pat)
(import ./decls :as d)
(import ./lower :as lo)

# ---------------------------------------------------------------
# Exports
# ---------------------------------------------------------------

# AST Nodes
(def node/tag a/node/tag)
(def node/type? a/node/type?)
(def node/term? a/node/term?)
(def node/pat? a/node/pat?)
(def node/decl? a/node/decl?)

(defn- syntax/with-prec [prec sx]
  (let [syn (or sx (x/syntax/default))]
    (when prec
      (eachp [op spec] prec
        (x/syntax/add-operator! syn op (spec :fixity) (spec :level))))
    syn))

(defn- parse-or-validate [xv pred parse-text label expected prec sx]
  (if (string? xv)
    (parse-text xv nil (syntax/with-prec prec sx))
    (do
      (when (and (a/ast/debug-checks?) (not (pred xv)))
        (errorf "%s expected %s node, got: %v" label expected xv))
      xv)))

(defn parse/type-text [text &opt prec sx]
  (pr/parse/type-text text (syntax/with-prec prec sx)))

(defn parse/expr-text [text &opt prec sx]
  (pr/parse/expr-text text (syntax/with-prec prec sx)))

(def parse/pat-text pat/parse/pat-text)
(def parse/fields d/parse/fields)
(def parse/source d/parse/source)
(def parse/program d/parse/source)

(def syntax/default x/syntax/default)
(def syntax/clone x/syntax/clone)
(def syntax/add-literal! x/syntax/add-literal!)
(def syntax/add-quant-alias! x/syntax/add-quant-alias!)
(def syntax/add-operator! x/syntax/add-operator!)

(def lower/type lo/lower/type)
(def lower/term lo/lower/term)
(def lower/program lo/lower/program)

(defn parse/type [xv &opt prec sx]
  (parse-or-validate xv a/node/type? parse/type-text "parse/type" "type" prec sx))

(defn parse/expr [xv &opt prec sx]
  (parse-or-validate xv a/node/term? parse/expr-text "parse/expr" "term" prec sx))

(defn parse/pat [xv]
  (if (string? xv)
    (parse/pat-text xv)
    (do
      (when (and (a/ast/debug-checks?) (not (a/node/pat? xv)))
        (errorf "parse/pat expected pattern node, got: %v" xv))
      xv)))

(def exports
  {:node/tag node/tag
   :node/type? node/type?
   :node/term? node/term?
   :node/pat? node/pat?
   :node/decl? node/decl?
   
   :parse/type-text parse/type-text
   :parse/expr-text parse/expr-text
   :parse/pat-text parse/pat-text
   :parse/fields parse/fields
   :parse/source parse/source
   
   :lower/type lower/type
   :lower/term lower/term
   :lower/program lower/program
   
   :parse/type parse/type
   :parse/expr parse/expr
   :parse/pat parse/pat})
