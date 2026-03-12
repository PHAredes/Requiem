#!/usr/bin/env janet

# Compatibility wrapper. Prefer importing ./core_printer.

(import ./core_printer :as core-printer)

(def print/tm core-printer/print/tm)
(def print/nf core-printer/print/nf)
(def print/ne core-printer/print/ne)
(def print/sem core-printer/print/sem)

(def exports
  {:print/tm print/tm
   :print/nf print/nf
   :print/ne print/ne
   :print/sem print/sem})
