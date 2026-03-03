#!/usr/bin/env janet

(import ../Utils/TestRunner :as test)
(import ../../src/parser :as p)
(import ../../src/surface :as s)
(import ../../src/elab :as e)

(defn decl/find-func [decls name]
  (var out nil)
  (each d decls
    (when (and (nil? out)
               (= (d 0) :decl/func)
               (= (d 1) name))
      (set out d)))
  out)

(defn lowered/body [func-decl]
  (let [clauses (func-decl 4)
        clause0 (clauses 0)]
    (clause0 2)))

(defn lowered/clauses [func-decl]
  (func-decl 4))

(defn lowered/first-clause [func-decl]
  ((func-decl 4) 0))

(defn lowered/clause-patterns [clause]
  (clause 1))

(defn node/count-atom [node tok]
  (match node
    [:atom x] (if (= x tok) 1 0)
    [:list xs] (reduce (fn [acc n] (+ acc (node/count-atom n tok))) 0 xs)
    [:brackets xs] (reduce (fn [acc n] (+ acc (node/count-atom n tok))) 0 xs)
    _ 0))

(defn core/find-func [decls name]
  (var out nil)
  (each d decls
    (when (and (nil? out)
               (= (d 0) :core/func)
               (= (d 1) name))
      (set out d)))
  out)

(defn decl/find-data [decls name]
  (var out nil)
  (each d decls
    (when (and (nil? out)
               (= (d 0) :decl/data)
               (= (d 1) name))
      (set out d)))
  out)

(defn data/ctors [data-decl]
  (data-decl 4))

(defn core/first-clause-body [func-decl]
  (let [clauses (func-decl 5)
        c0 (clauses 0)]
    (c0 2)))

(defn core/app-head [tm]
  (if (and (tuple? tm) (= (tm 0) :app))
    (core/app-head (tm 1))
    tm))

(defn mk-sum-src [rec-var]
  (string
    "(data Nat: Type ((zero Nat) (succ (forall (k: Nat). Nat))))"
    " (def sum: (forall (n: Nat). (forall (m: Nat). Nat))"
    "   (match m:"
    "     (case zero: n)"
    "     (case (succ " rec-var "): (succ (sum n " rec-var ")))))"))

(test/start-suite "Property Tesla Encoding")

(let [rng (math/rng 123)]
  (for _ 0 40
    (let [rec-var (string "r" (math/rng-int rng 10000))
          src (mk-sum-src rec-var)
          forms (p/parse/text src)
          lowered (s/lower/program forms)
          sum-decl (decl/find-func lowered "sum")
          body (lowered/body sum-decl)]
      (test/assert (p/has/atom? body "Nat-elim") "match lowers to Nat-elim")
      (test/assert (not (p/has/atom? body "match")) "lowered body has no match atom")
      (test/assert (p/has/atom? body (string "ih-" rec-var)) "recursive branch introduces ih binder")
      (test/assert (not (p/has/atom? body "sum")) "structural branch removes direct recursive call"))))

(let [forms (p/parse/text (slurp "examples/test.requiem"))
      lowered (s/lower/program forms)
      core (e/elab/program lowered)
      sum-decl (decl/find-func lowered "sum")
      not-decl (decl/find-func lowered "not")
      sum-core (core/find-func core "sum")
      not-core (core/find-func core "not")]
  (test/assert (= (length (lowered/clauses sum-decl)) 2) "selector-style sum keeps two clauses")
  (test/assert (= (length (lowered/clauses not-decl)) 2) "selector-style not keeps two clauses")
  (test/assert (= (length (sum-core 5)) 2) "sum elaborates two clauses")
  (test/assert (= (length (not-core 5)) 2) "not elaborates two clauses"))

(let [src (string
            "(data Vec (A: Type) (n: Nat): Type "
            "  (| A zero = vnil)"
            "  (| A (succ n) = vcons (x: A) (xs: (Vec A n))))")
      forms (p/parse/text src)
      lowered (s/lower/program forms)
      vec (decl/find-data lowered "Vec")]
  (test/assert (not (nil? vec)) "selector-style indexed data parses")
  (test/assert (= (length (data/ctors vec)) 2) "selector-style Vec has two constructors"))

(let [src (string
            "data Nat: Type\n"
            "  | = zero\n"
            "  | = succ (n: Nat)\n\n"
            "def add (n: Nat) (m: Nat): Nat\n"
            "  | n zero = n\n"
            "  | n (succ m) = (succ (add n m))")
      forms (p/parse/text src)
      lowered (s/lower/program forms)
      nat (decl/find-data lowered "Nat")
      add (decl/find-func lowered "add")]
  (test/assert (= (length lowered) 2) "sweet syntax parses into two top-level decls")
  (test/assert (= (length (data/ctors nat)) 2) "sweet syntax data clauses lower")
  (test/assert (= (length (lowered/clauses add)) 2) "sweet syntax def clauses lower"))

(let [src (string
            "(data Nat: Type (| = zero) (| = suc (n: Nat)))"
            " (def keep1 (n: Nat) (m: Nat): Nat (| n = n))"
            " (def keep0 (n: Nat) (m: Nat): Nat (| = n))")
      forms (p/parse/text src)
      lowered (s/lower/program forms)
      keep1 (decl/find-func lowered "keep1")
      keep0 (decl/find-func lowered "keep0")
      keep1-clause (lowered/first-clause keep1)
      keep0-clause (lowered/first-clause keep0)
      keep1-body (keep1-clause 2)
      keep0-body (keep0-clause 2)]
  (test/assert (= (length (lowered/clause-patterns keep1-clause)) 2)
               "partial clause expands to full pattern vector")
  (test/assert (= (length (lowered/clause-patterns keep0-clause)) 2)
               "empty selector clause expands to full pattern vector")
  (test/assert (= (node/count-atom keep1-body "fn") 1)
               "one consumed arg leaves one lambda in goal")
  (test/assert (= (node/count-atom keep0-body "fn") 1)
               "zero consumed args leaves lambda goal with remaining binders")
  (test/assert (p/has/atom? keep1-body "m:")
               "remaining parameter type appears in generated lambda")
  (test/assert (p/has/atom? keep0-body "n:")
               "empty selector clause introduces first binder")
  (test/assert (p/has/atom? keep0-body "m:")
               "empty selector clause introduces second binder"))

(let [pi-decls (e/elab/program
                 @[(tuple :decl/func
                          "pi_t"
                          @[]
                          [:atom "Type"]
                          @[(tuple :clause @[] (p/parse/one "(Pi (Ann n Nat) Nat)"))])])
      lam-decls (e/elab/program
                  @[(tuple :decl/func
                           "lam_t"
                           @[]
                           [:atom "Type"]
                           @[(tuple :clause @[] (p/parse/one "(Lam (Ann n Nat) n)"))])])
      ann-decls (e/elab/program
                  @[(tuple :decl/func
                           "ann_t"
                           @[(tuple :bind "n" [:atom "Nat"])]
                           [:atom "Nat"]
                           @[(tuple :clause @[(tuple :pat/var "n")] (p/parse/one "(Ann n Nat)"))])])
      pi-core (core/first-clause-body (pi-decls 0))
      lam-core (core/first-clause-body (lam-decls 0))
      ann-core (core/first-clause-body (ann-decls 0))]
  (test/assert (and (tuple? pi-core) (= (pi-core 0) :t-pi)) "Pi/Ann lowers to core Pi")
  (test/assert (and (tuple? lam-core) (= (lam-core 0) :lam)) "Lam/Ann lowers to core lambda")
  (test/assert (and (tuple? ann-core) (= ann-core [:var "n"])) "Ann term elaborates to annotated term"))

(defn mk-random-data-decl [rng]
  "Generate a random data declaration with 1-3 constructors."
  (let [data-name (string "D" (math/rng-int rng 10000))
        ctor-count (+ 1 (math/rng-int rng 3))
        ctors (reduce (fn [acc c]
                       (let [ctor-name (string "C" c "_" (math/rng-int rng 1000))
                             has-args (< (math/rng-int rng 2) 1)
                             ctor-type (if has-args 
                                        (string "(forall (a: Nat). " data-name ")")
                                        data-name)]
                         (array/push acc (string "(" ctor-name " " ctor-type ")"))
                         acc))
                     @[]
                     (range ctor-count))]
    (tuple data-name (string "(data " data-name ": Type (" (string/join ctors " ") "))"))))

(defn mk-random-match-func [rng data-name]
  "Generate a random function that matches on the given data type."
  (let [func-name (string "f" (math/rng-int rng 10000))
        match-var (string "x" (math/rng-int rng 10000))]
    [func-name
     (string "(def " func-name ": (forall (" match-var ": " data-name "). Nat)"
             " (match " match-var ":"
             " (case _ 0)))")]))

(let [rng (math/rng 456)]
  (loop [_ :range [0 5]]
    (let [[data-name data-src] (mk-random-data-decl rng)
          [func-name func-src] (mk-random-match-func rng data-name)
          full-src (string data-src " " func-src)]
      (let [forms (p/parse/text full-src)
            lowered (s/lower/program forms)
            data-decl (decl/find-data lowered data-name)]
        (let [func-decl (decl/find-func lowered func-name)]
          (test/assert (not (nil? data-decl)) "random data declaration parsed correctly")
          (test/assert (not (nil? func-decl)) "random function declaration parsed correctly")
          (when func-decl
            (let [body (lowered/body func-decl)
                  elim-name (string data-name "-elim")]
              (test/assert (p/has/atom? body elim-name) (string "match lowers to " elim-name " for arbitrary data type"))
              (test/assert (not (p/has/atom? body "match")) "lowered body has no match atom for arbitrary data type"))))))))

(test/end-suite)
