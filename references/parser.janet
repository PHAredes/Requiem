#!/usr/bin/env janet

# parser.janet
# PEG grammar for the language.
#
# The PEG handles lexing + structural parsing.
# Mixfix/precedence resolution is a separate Pratt pass over the CST.
# Indentation is handled via a pre-pass that inserts :indent/:dedent tokens.
#
# METAVARIABLES
# -------------
# A metavariable (hole) is an unknown to be filled by unification.
# Syntax:
#   ?          anonymous hole  — elaborator invents a fresh name
#   ?name      named hole      — can be referenced/constrained elsewhere
#
# Holes are valid in both term and type position:
#   f: ? -> Nat                -- unknown domain, infer it
#   x: Vec ? n                 -- unknown element type
#   head ? n (vcons x _) = x   -- don't care about implicit arg
#   eval ? (lit-n 42)          -- let elaborator fill the Ty index
#
# Named holes with the same name unify across the whole declaration:
#   round-trip: ?a -> ?a       -- both ?a must be the same type
#
# The elaborator collects all holes into a constraint set and
# runs unification. Named holes with the same name are unified.
# Anonymous holes are always fresh and independent.
#
# Holes in coreTT map to tm/hole (already defined in coreTT.janet):
#   (tm/hole name)   where name is a symbol (gensym'd if anonymous)

# ============================================================
# LEXICAL
# ============================================================

(def ws+     '(some (set " \t")))
(def ws*     '(any  (set " \t")))
(def nl      '(+ "\r\n" "\n" "\r"))
(def comment '(* "--" (any (if-not (+ "\n" "\r") 1))))
(def blank   '(* (any (set " \t")) (? comment) nl))

# --------------------
# Name classes
# --------------------
#
# Pascal  = [A-Z][A-Za-z0-9]*
# kebab   = [a-z][a-z0-9-]*   (hyphens between word chars only)
# mixfix  = segments + at least one *
# nat-lit = [0-9]+
# hole    = ?  |  ?kebab-name

(def pascal-name
  '(capture (* (range "AZ")
               (any (range "AZ" "az" "09")))))

(def kebab-name
  '(capture (* (range "az")
               (any (+ (range "az" "09")
                       (* "-" (range "az" "09")))))))

(def mixfix-name
  '(capture (some (+ "*"
                     (some (+ (range "AZ" "az" "09")
                              (set "+-/<>=~^@!?|&%.")))))))

(def hole
  '(+ (* "?" (capture (* (range "az")
                          (any (+ (range "az" "09")
                                  (* "-" (range "az" "09")))))))
      (capture "?")))

(def nat-lit
  '(capture (some (range "09"))))

# ============================================================
# INDENTATION  (pass 1)
# ============================================================
#
# Janet PEG has no mechanism to bind "current indent level" as
# mutable state across a match. Indentation-sensitivity therefore
# lives in a separate tokenisation pass that emits:
#
#   {:kind :indent, :col n, :line n}   -- deeper block opened
#   {:kind :dedent, :col n, :line n}   -- block(s) closed
#   {:kind :line,   :text s, :col n, :line n}
#
# The structural grammar (pass 2) then works on this flat sequence
# rather than raw characters, which keeps every PEG clean and
# single-purpose.

(defn indent/tokenize [src]
  (def lines (string/split "\n" src))
  (def stack @[0])
  (def tokens @[])
  (var lnum 0)

  (each line lines
    (++ lnum)
    (def trimmed (string/trimr line))
    (when (or (= trimmed "")
              (string/has-prefix? "--" (string/triml trimmed)))
      (continue))

    (var col 0)
    (while (and (< col (length trimmed))
                (= (get trimmed col) (chr " ")))
      (++ col))

    (def cur (last stack))

    (cond
      (> col cur)
      (do (array/push stack col)
          (array/push tokens {:kind :indent :col col :line lnum}))

      (< col cur)
      (do
        (while (> (last stack) col)
          (array/pop stack)
          (array/push tokens {:kind :dedent :col (last stack) :line lnum}))))

    (array/push tokens {:kind :line
                        :text (string/slice trimmed col)
                        :col  col
                        :line lnum}))

  (while (> (length stack) 1)
    (array/pop stack)
    (array/push tokens {:kind :dedent :col (last stack) :line (length lines)}))

  tokens)

# ============================================================
# LINE-LEVEL PEG GRAMMARS  (pass 2, per line)
# ============================================================
#
# Each grammar operates on a single line's text string.
# The classify-line function tries them in priority order.
#
# Grammars that need to handle holes include a :hole rule that
# matches both ? and ?name, emitting [:hole nil] or [:hole "name"].
# The assembler lifts these into tm/hole nodes for the elaborator.

# --------------------
# Shared hole rule (inlined into each grammar that needs it)
# --------------------
#
# (group (* (constant :hole) (+ named anon)))
# => [:hole "name"]  or  [:hole nil]

# --------------------
# Type expressions
# --------------------
#
# type-expr =
#   ?  |  ?name                      metavariable
#   Un                               universe level n
#   Pascal { type-atom }             type application
#   var                              type variable
#   (type-expr)                      grouping
#   type-atom -> type-expr           non-dependent function (right-assoc)
#   Π(var: type-expr). type-expr     dependent function  (value binder)
#   ∀(Var: type-expr). type-expr     parametric          (type binder)
#   Σ(var: type-expr). type-expr     dependent pair
#   ∃(var: type-expr). type-expr     existential pair
#   mixfix-type                      left as raw text; Pratt pass resolves

(def type-grammar
  ~{:ws*  (any  (set " \t"))
    :ws+  (some (set " \t"))
    :lower (range "az")
    :upper (range "AZ")
    :alnum (+ (range "AZ" "az" "09"))

    :hole
    (group (* (constant :hole)
              (+ (* "?" (capture (* :lower (any (+ :alnum (* "-" :lower))))))
                 (* "?" (constant nil)))))

    :universe
    (group (* (constant :universe)
              (capture "U")
              (capture (any (range "09")))))

    :type-var
    (capture (* :lower (any (+ :alnum (* "-" :lower)))))

    :type-name
    (capture (* :upper (any :alnum)))

    :binder-arg
    (group (* "(" :ws*
              (capture (* :lower (any (+ :alnum (* "-" :lower)))))
              :ws* ":" :ws*
              :type-expr
              :ws* ")"))

    :type-atom
    (+ :hole
       :universe
       (* "(" :ws* :type-expr :ws* ")")
       (* :type-name (any (* :ws+ :type-atom)))
       :type-var)

    :pi-type    (group (* (constant :pi)     "Π" :binder-arg :ws* "." :ws* :type-expr))
    :forall     (group (* (constant :forall) "∀" :binder-arg :ws* "." :ws* :type-expr))
    :sigma-type (group (* (constant :sigma)  "Σ" :binder-arg :ws* "." :ws* :type-expr))
    :exists     (group (* (constant :exists) "∃" :binder-arg :ws* "." :ws* :type-expr))
    :arrow      (group (* (constant :arrow)  :type-atom :ws* "->" :ws* :type-expr))

    :type-expr  (+ :pi-type :forall :sigma-type :exists :arrow :type-atom)
    :main :type-expr})

# --------------------
# Patterns
# --------------------
#
# pat =
#   ?  |  ?name   metavariable — wildcard that also participates in unification
#   _              wildcard    — no binding, no unification
#   var            name binding
#   ctor pat*      constructor pattern
#   nat-lit
#   (pat)
#
# The distinction between ? and _ matters to the elaborator:
#   _ just discards
#   ? tells the elaborator "I left something here; figure it out"
#   ?name ties the hole to others of the same name in the clause

(def pat-grammar
  ~{:ws*  (any  (set " \t"))
    :ws+  (some (set " \t"))
    :lower (range "az")
    :upper (range "AZ")
    :alnum (+ (range "AZ" "az" "09"))

    :hole
    (group (* (constant :hole)
              (+ (* "?" (capture (* :lower (any (+ :alnum (* "-" :lower))))))
                 (* "?" (constant nil)))))

    :wild   (capture "_")

    :var-pat
    (capture (* :lower (any (+ :alnum (* "-" :lower)))))

    :ctor-name
    (capture (* :lower (any (+ :alnum (* "-" :lower)))))

    :nat-pat (capture (some (range "09")))

    :atom-pat
    (+ :hole
       :wild
       :nat-pat
       (* "(" :ws* :pat :ws* ")")
       (* :ctor-name (any (* :ws+ :atom-pat)))
       :var-pat)

    :pat  :atom-pat
    :main :pat})

# --------------------
# Constructor arms
# --------------------
#
# plain:    ctor-name field*
# indexed:  index-pats = ctor-name field*
#
# index-pats = single-pat { , single-pat }
# (comma separates resource/set index components, as in These)
#
# field = (var : type-expr)  |  type-expr  |  hole
#
# Holes are valid in field types:
#   vcons(x: ?)(xs: Vec ? n)   -- element type left open

(def ctor-grammar
  ~{:ws*  (any  (set " \t"))
    :ws+  (some (set " \t"))
    :lower (range "az")
    :upper (range "AZ")
    :alnum (+ (range "AZ" "az" "09"))

    :hole
    (group (* (constant :hole)
              (+ (* "?" (capture (* :lower (any (+ :alnum (* "-" :lower))))))
                 (* "?" (constant nil)))))

    :type-ref
    (capture (some (if-not (set " \t\n\r(),=") 1)))

    :named-field
    (group (* (constant :named-field)
              "(" :ws*
              (capture (* :lower (any (+ :alnum (* "-" :lower)))))
              :ws* ":" :ws*
              (+ :hole :type-ref)
              :ws* ")"))

    :anon-field  (+ :hole :type-ref)
    :field       (+ :named-field :anon-field)
    :fields      (group (any (* :ws+ :field)))

    :ctor-name (capture (* :lower (any (+ :alnum (* "-" :lower)))))

    :single-pat
    (+ (* "(" :ws*
          (capture (some (if-not (set " \t)") 1)))
          :ws* ")")
       (capture (* (+ :lower :upper (range "09"))
                   (any (+ :alnum (* "-" :lower))))))

    :index-pats
    (group (* :single-pat
              (any (* :ws* "," :ws* :single-pat))))

    :indexed-arm
    (group (* (constant :indexed)
              :index-pats :ws* "=" :ws*
              :ctor-name :fields))

    :plain-arm
    (group (* (constant :plain) :ctor-name :fields))

    :ctor-arm (+ :indexed-arm :plain-arm)
    :main :ctor-arm})

# --------------------
# Function clauses
# --------------------
#
# clause = pat* = expr
#
# Holes in patterns carry through to the elaborator:
#   eval ? (lit-n n) = n        -- ? fills the Ty index
#   head ? n (vcons x _) = x    -- ? fills the implicit A
#   const x ? = x               -- ? is a don't-care with unification
#
# The right-hand side (expr) is captured as raw text.
# The Pratt pass resolves:
#   - mixfix operator structure
#   - function application (left-assoc juxtaposition)
#   - hole positions in expressions (? is a valid expression)

(def clause-grammar
  ~{:ws*  (any  (set " \t"))
    :ws+  (some (set " \t"))
    :lower (range "az")
    :upper (range "AZ")
    :alnum (+ (range "AZ" "az" "09"))

    :hole-pat
    (group (* (constant :hole)
              (+ (* "?" (capture (* :lower (any (+ :alnum (* "-" :lower))))))
                 (* "?" (constant nil)))))

    :pat-atom
    (+ :hole-pat
       (* "(" :ws* (capture (some (if-not (set " \t)") 1))) :ws* ")")
       (capture (* (+ :lower :upper (range "09"))
                   (any (+ :alnum (* "-" :lower))))))

    :pats (group (some (* :ws* :pat-atom)))

    :clause
    (group (* (constant :clause)
              :pats :ws* "=" :ws*
              (capture (thru -1))))

    :main :clause})

# --------------------
# Precedence declarations
# --------------------
#
# infixl n *op*    left-associative, precedence n
# infixr n *op*    right-associative, precedence n
# prefix n *op*    prefix, precedence n
# postfix n *op*   postfix, precedence n
#
# The Pratt pass reads these declarations from the CST before
# parsing any expressions. The table maps op-name -> {fixity, prec}.
# Types and terms share the same precedence table — the role of
# the operator (type former vs term) is determined by casing,
# not by which table it lives in.

(def prec-grammar
  ~{:ws+  (some (set " \t"))
    :lower (range "az")
    :upper (range "AZ")
    :alnum (+ (range "AZ" "az" "09"))

    :fixity (+ (capture "infixl") (capture "infixr")
               (capture "prefix") (capture "postfix"))

    :op-name
    (capture (some (+ "*"
                      (some (+ :alnum (set "+-/<>=~^@!?|&%."))))))

    :prec-decl
    (group (* (constant :prec)
              :fixity :ws+
              (capture (some (range "09")))
              :ws+
              :op-name))

    :main :prec-decl})

# --------------------
# Top-level declaration header
# --------------------
#
# type-decl:   PascalName(params):
# term-decl:   kebab-name: type-sig
# op-decl:     *op*: type-sig
#
# The colon is the one shared sigil. What precedes it determines
# the kind. No keywords. Pascal = type. kebab/mixfix = term/op.

(def header-grammar
  ~{:ws*  (any  (set " \t"))
    :ws+  (some (set " \t"))
    :lower (range "az")
    :upper (range "AZ")
    :alnum (+ (range "AZ" "az" "09"))

    :type-name   (capture (* :upper (any :alnum)))
    :term-name   (capture (* :lower (any (+ :alnum (* "-" :lower)))))
    :op-name     (capture (some (+ "*" (some (+ :alnum (set "+-/<>=~^@!?|&%."))))))

    :param
    (group (* (capture (* (+ :lower :upper) (any (+ :alnum (* "-" :lower)))))
              (? (* :ws* ":" :ws*
                    (capture (some (if-not (set " \t,)") 1)))))))

    :param-list  (group (* :param (any (* :ws* "," :ws* :param))))

    :type-head
    (group (* (constant :type-decl)
              :type-name
              (? (* "(" :ws* :param-list :ws* ")"))
              :ws* ":"))

    :term-head
    (group (* (constant :term-decl)
              (+ :op-name :term-name)
              :ws* ":" :ws*
              (capture (thru -1))))

    :main (+ :type-head :term-head)})

# ============================================================
# CST ASSEMBLER
# ============================================================
#
# Walks the indent-tokenised stream.
# Col = 0 lines are top-level declaration headers.
# Indented lines are body (arms or clauses) of the current decl.

(defn- classify-line [text col]
  (or (peg/match (peg/compile prec-grammar)   text)
      (peg/match (peg/compile header-grammar)  text)
      (peg/match (peg/compile ctor-grammar)    text)
      (peg/match (peg/compile clause-grammar)  text)
      [{:raw text :col col}]))

(defn parse/build-cst [src]
  (def tokens (indent/tokenize src))
  (def decls @[])
  (var current nil)
  (var body @[])
  (var i 0)

  (defn flush []
    (when current
      (array/push decls (merge current {:body (array/slice body)}))
      (set current nil)
      (array/clear body)))

  (while (< i (length tokens))
    (def tok (get tokens i))
    (++ i)
    (match (tok :kind)
      :line
      (let [text (tok :text)
            col  (tok :col)]
        (if (= col 0)
          (do (flush)
              (def parsed (classify-line text col))
              (set current {:header parsed :col col :line (tok :line)}))
          (when current
            (array/push body {:text   text
                              :col    col
                              :line   (tok :line)
                              :parsed (classify-line text col)}))))
      _ nil))

  (flush)
  decls)

# ============================================================
# DEMO
# ============================================================

(defn demo []
  (def src ```
-- plain types
Nat:
  zero
  succ Nat

Bool:
  true
  false

-- indexed type
Vec(A, n: Nat):
  zero   = vnil
  succ n = vcons(x: A)(xs: Vec A n)

-- resource-indexed type (These)
These(A, B: U0):
  A    = this(a: A)
  B    = that(b: B)
  A, B = those(a: A)(b: B)

-- holes in type signatures
mystery: ? -> Nat
  x = zero

-- named holes (same name = same type, unified)
round-trip: ?a -> ?a
  x = x

-- holes in indexed type fields
Sketchy(A, n: Nat):
  succ n = node(x: ?)(xs: Vec ? n)

-- functions
head: Vec A (succ n) -> A
  vcons x _ = x

-- holes in patterns (implicit args)
eval: Term t -> interp t
  ? (lit-n n)   = n
  ? (lit-b b)   = b
  ? (app ? f x) = (eval f) (eval x)

-- anonymous holes in patterns just say "fill this in"
const: A -> B -> A
  x ? = x

-- precedence declarations
infixl 6 *+*
infixr 5 *::*
infixr 4 *->*
infixr 0 if*then*else*

-- operator definitions (mixfix = term, kebab segments)
*+*: Nat -> Nat -> Nat
  n m = add n m

*::*: A -> List A -> List A
  x xs = cons x xs

if*then*else*: Bool -> A -> A -> A
  true  t _ = t
  false _ f = f
```)

  (def cst (parse/build-cst src))
  (print "\n=== CST ===")
  (each decl cst
    (print "\n--- decl ---")
    (pp decl)))

(demo)
