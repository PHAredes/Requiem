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

(defn elab/forms [forms]
  (dep/warn! :elab-legacy-forms
             "`src/elab_legacy.janet` consumes deprecated s-expression forms; prefer `elab/program` with lowered surface declarations")
  (e/elab/program (l/lower/program forms)))

(defn elab/text [src]
  (dep/warn! :elab-legacy-text
             "`src/elab_legacy.janet` uses the deprecated s-expression frontend; prefer `surface/parser` + `surface/lower` + `elab/program`")
  (elab/forms (p/parse/text src)))

(def exports
  {:elab/forms elab/forms
   :elab/text elab/text})
