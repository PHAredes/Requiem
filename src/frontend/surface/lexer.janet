#!/usr/bin/env janet

(import ../../surface :as s)

(def parse/type-text s/parse/type-text)
(def parse/expr-text s/parse/expr-text)

(def exports
  {:parse/type-text parse/type-text
   :parse/expr-text parse/expr-text})
