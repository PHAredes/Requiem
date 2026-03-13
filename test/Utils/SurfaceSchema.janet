#!/usr/bin/env janet

(defn sc/any [] [:sc/any])
(defn sc/string [] [:sc/string])
(defn sc/int [] [:sc/int])
(defn sc/lit [x] [:sc/lit x])
(defn sc/array [item] [:sc/array item])
(defn sc/optional [inner] [:sc/optional inner])
(defn sc/union [members] [:sc/union members])
(defn sc/lazy [thunk] [:sc/lazy thunk])
(defn sc/refine [inner pred label] [:sc/refine inner pred label])
(defn sc/tagged [tag fields] [:sc/tagged tag fields])

(defn- ok [v] [:ok v])
(defn- err [m] [:err m])

(var schema/type nil)
(var schema/term nil)
(var schema/pat nil)
(var schema/decl nil)

(defn- path->str [path]
  (if (zero? (length path)) "<root>" (string/join path ".")))

(defn- resolve [schema]
  (if (= (schema 0) :sc/lazy) ((schema 1)) schema))

(defn sc/validate [schema value path]
  (let [s (resolve schema)
        t (s 0)]
    (match t
      :sc/any (ok value)
      :sc/string (if (string? value)
                   (ok value)
                   (err (string "expected string at " (path->str path) ", got " value)))
      :sc/int (if (int? value)
                (ok value)
                (err (string "expected int at " (path->str path) ", got " value)))
      :sc/lit (if (= value (s 1))
                (ok value)
                (err (string "expected literal " (s 1) " at " (path->str path)
                             ", got " value)))
      :sc/array 
      (if (not (or (array? value) (tuple? value)))
        (err (string "expected array at " (path->str path) ", got " value))
        (do
          (var e nil)
          (for i 0 (length value)
            (when (nil? e)
              (let [r (sc/validate (s 1) (value i) [;path (string "[" i "]")])]
                (when (= (r 0) :err) (set e r)))))
          (if e e (ok value))))
      :sc/optional (if (nil? value) (ok value) (sc/validate (s 1) value path))
      :sc/union 
      (do
        (var pass nil)
        (var last nil)
        (each m (s 1)
          (when (nil? pass)
            (let [r (sc/validate m value path)]
              (if (= (r 0) :ok)
                (set pass r)
                (set last (r 1))))))
        (if pass
          pass
          (err (string "no union matched at " (path->str path)
                       (if last (string ": " last) "")))))
      :sc/refine
      (let [r (sc/validate (s 1) value path)]
        (if (= (r 0) :err)
          r
          (if ((s 2) value)
            (ok value)
            (err (string "refinement failed (" (s 3) ") at " (path->str path)
                         ", got " value)))))
      :sc/tagged
      (if (not (tuple? value))
        (err (string "expected tuple at " (path->str path) ", got " value))
        (if (or (< (length value) 1) (not= (value 0) (s 1)))
          (err (string "expected tag " (s 1) " at " (path->str path) ", got " value))
          (if (not= (length value) (+ 1 (length (s 2))))
            (err (string "wrong tuple arity for " (s 1) " at " (path->str path)
                         ": expected " (+ 1 (length (s 2))) " got " (length value)))
            (do
              (var e nil)
              (for i 0 (length (s 2))
                (when (nil? e)
                  (let [r (sc/validate ((s 2) i)
                                       (value (+ i 1))
                                       [;path (string (s 1) "#" (+ i 1))])]
                    (when (= (r 0) :err) (set e r)))))
              (if e e (ok value))))))
      _ (err (string "unknown schema tag " t " at " (path->str path))))))

(defn sc/check [schema value]
  (sc/validate schema value @[]))

(defn sc/parse [schema value]
  (let [r (sc/check schema value)]
    (if (= (r 0) :ok)
      value
      (error (r 1)))))

(def nonneg-int
  (sc/refine (sc/int) |(>= $ 0) "non-negative integer"))

(def pos-int
  (sc/refine (sc/int) |(> $ 0) "positive integer"))

(def hole-name
  (sc/optional (sc/string)))

(def schema/pos (sc/tagged :pos @[pos-int pos-int nonneg-int]))
(def schema/span (sc/tagged :span @[schema/pos schema/pos]))
(def schema/binder (sc/tagged :binder @[(sc/string) (sc/lazy (fn [] schema/type)) schema/span]))

(set schema/type
     (sc/union @[
       (sc/tagged :ty/hole @[hole-name schema/span])
       (sc/tagged :ty/universe @[nonneg-int schema/span])
       (sc/tagged :ty/name @[(sc/string) schema/span])
       (sc/tagged :ty/var @[(sc/string) schema/span])
       (sc/tagged :ty/app @[(sc/lazy (fn [] schema/type)) (sc/lazy (fn [] schema/type)) schema/span])
       (sc/tagged :ty/arrow @[(sc/lazy (fn [] schema/type)) (sc/lazy (fn [] schema/type)) schema/span])
       (sc/tagged :ty/pi @[schema/binder (sc/lazy (fn [] schema/type)) schema/span])
       (sc/tagged :ty/sigma @[schema/binder (sc/lazy (fn [] schema/type)) schema/span])
       (sc/tagged :ty/op @[(sc/string) (sc/array (sc/lazy (fn [] schema/type))) schema/span])]))

(set schema/term
     (sc/union @[
       (sc/tagged :tm/hole @[hole-name schema/span])
       (sc/tagged :tm/var @[(sc/string) schema/span])
       (sc/tagged :tm/ref @[(sc/string) schema/span])
       (sc/tagged :tm/nat @[nonneg-int schema/span])
       (sc/tagged :tm/app @[(sc/lazy (fn [] schema/term)) (sc/lazy (fn [] schema/term)) schema/span])
       (sc/tagged :tm/lam @[(sc/array (sc/string)) (sc/lazy (fn [] schema/term)) schema/span])
       (sc/tagged :tm/let @[(sc/string) (sc/lazy (fn [] schema/term)) (sc/lazy (fn [] schema/term)) schema/span])
       (sc/tagged :tm/op @[(sc/string) (sc/array (sc/lazy (fn [] schema/term))) schema/span])]))

(set schema/pat
     (sc/union @[
       (sc/tagged :pat/wild @[schema/span])
       (sc/tagged :pat/hole @[hole-name schema/span])
       (sc/tagged :pat/var @[(sc/string) schema/span])
       (sc/tagged :pat/con @[(sc/string) (sc/array (sc/lazy (fn [] schema/pat))) schema/span])
       (sc/tagged :pat/nat @[nonneg-int schema/span])]))

(def schema/param (sc/tagged :param @[(sc/string) (sc/optional (sc/lazy (fn [] schema/type))) schema/span]))
(def schema/field
  (sc/union @[(sc/tagged :field/named @[(sc/string) (sc/lazy (fn [] schema/type)) schema/span])
              (sc/tagged :field/anon @[(sc/lazy (fn [] schema/type)) schema/span])]))
(def schema/ctor
  (sc/union @[(sc/tagged :ctor/plain @[(sc/string) (sc/array schema/field) schema/span])
              (sc/tagged :ctor/indexed @[(sc/array (sc/lazy (fn [] schema/pat))) (sc/string) (sc/array schema/field) schema/span])]))
(def schema/clause (sc/tagged :clause @[(sc/array (sc/lazy (fn [] schema/pat))) (sc/lazy (fn [] schema/term)) schema/span]))
(set schema/decl
     (sc/union @[
       (sc/tagged :decl/prec @[(sc/lit :infixl) nonneg-int (sc/string) schema/span])
       (sc/tagged :decl/prec @[(sc/lit :infixr) nonneg-int (sc/string) schema/span])
       (sc/tagged :decl/prec @[(sc/lit :prefix) nonneg-int (sc/string) schema/span])
       (sc/tagged :decl/prec @[(sc/lit :postfix) nonneg-int (sc/string) schema/span])
       (sc/tagged :decl/data @[(sc/string) (sc/array schema/param) (sc/lazy (fn [] schema/type)) (sc/array schema/ctor) schema/span])
       (sc/tagged :decl/func @[(sc/string) (sc/lazy (fn [] schema/type)) (sc/array schema/clause) schema/span])]))

(def schema/program
  (sc/tagged :program @[(sc/array (sc/lazy (fn [] schema/decl))) schema/span]))

(defn check/type [x] (sc/check schema/type x))
(defn check/term [x] (sc/check schema/term x))
(defn check/pat [x] (sc/check schema/pat x))
(defn check/decl [x] (sc/check schema/decl x))
(defn check/program [x] (sc/check schema/program x))

(defn assert/type [x] (sc/parse schema/type x))
(defn assert/term [x] (sc/parse schema/term x))
(defn assert/pat [x] (sc/parse schema/pat x))
(defn assert/decl [x] (sc/parse schema/decl x))
(defn assert/program [x] (sc/parse schema/program x))

(def exports
  {:sc/any sc/any
   :sc/string sc/string
   :sc/int sc/int
   :sc/lit sc/lit
   :sc/array sc/array
   :sc/optional sc/optional
   :sc/union sc/union
   :sc/lazy sc/lazy
   :sc/refine sc/refine
   :sc/tagged sc/tagged
   :sc/check sc/check
   :sc/parse sc/parse

   :schema/pos schema/pos
   :schema/span schema/span
   :schema/type schema/type
   :schema/term schema/term
   :schema/pat schema/pat
   :schema/decl schema/decl
   :schema/program schema/program

   :check/type check/type
   :check/term check/term
   :check/pat check/pat
   :check/decl check/decl
   :check/program check/program

   :assert/type assert/type
   :assert/term assert/term
   :assert/pat assert/pat
   :assert/decl assert/decl
   :assert/program assert/program})
