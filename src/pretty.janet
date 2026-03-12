#!/usr/bin/env janet

(import ./coreTT :as tt)
(import ./levels :as lvl)
(import ./print :as printer)

(def deps
  {:T/Type tt/T/Type
   :T/Pi tt/T/Pi
   :T/Sigma tt/T/Sigma
   :T/Id tt/T/Id
   :T/Refl tt/T/Refl
   :T/Neutral tt/T/Neutral
   :T/Pair tt/T/Pair
   :NF/Neut tt/NF/Neut
   :NF/Lam tt/NF/Lam
   :NF/Pi tt/NF/Pi
   :NF/Sigma tt/NF/Sigma
   :NF/Type tt/NF/Type
   :NF/Pair tt/NF/Pair
   :NF/Id tt/NF/Id
   :NF/Refl tt/NF/Refl
   :ty/type tt/ty/type
   :lower tt/lower
   :lvl/value lvl/value})

(def pp (printer/make deps))

(def print/tm (pp :print/tm))
(def print/nf (pp :print/nf))
(def print/ne (pp :print/ne))
(def print/sem (pp :print/sem))

(def exports
  {:print/tm print/tm
   :print/nf print/nf
   :print/ne print/ne
   :print/sem print/sem})
