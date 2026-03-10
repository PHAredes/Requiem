#!/usr/bin/env janet

(import ../../surface :as s)

(def parse/source s/parse/source)

(def exports
  {:parse/source parse/source})
