#!/usr/bin/env janet

(import ../../surface :as s)

(def syntax/default s/syntax/default)
(def syntax/clone s/syntax/clone)
(def syntax/add-literal! s/syntax/add-literal!)
(def syntax/add-quant-alias! s/syntax/add-quant-alias!)
(def syntax/add-type-ident-resolver! s/syntax/add-type-ident-resolver!)

(def exports
  {:syntax/default syntax/default
   :syntax/clone syntax/clone
   :syntax/add-literal! syntax/add-literal!
   :syntax/add-quant-alias! syntax/add-quant-alias!
   :syntax/add-type-ident-resolver! syntax/add-type-ident-resolver!})
