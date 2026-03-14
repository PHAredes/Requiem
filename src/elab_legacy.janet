#!/usr/bin/env janet

# Deprecated compatibility bridge for the legacy s-expression frontend.
#
# This is the sole supported legacy entrypoint in `src/`.
# New code should use:
#   surface/parser -> surface/lower -> elab/program

(import ./frontend/sexpr/parser :as p)
(import ./frontend/sexpr/lower :as l)
(import ./frontend/sexpr/deprecated :as dep)
(import ./elab :as e)

(defn- warn! []
  (dep/warn! :elab-legacy-entrypoint
             "`src/elab_legacy.janet` is deprecated; prefer `surface/parser` + `surface/lower` + `elab/program`"))

(defn elab/forms [forms]
  (warn!)
  (e/elab/program (l/lower/program forms)))

(defn elab/text [src]
  (warn!)
  (elab/forms (p/parse/text src)))

(def exports
  {:elab/forms elab/forms
   :elab/text elab/text})
