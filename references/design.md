# Language Design & Implementation Guide

---

## 1. Philosophy

The identifier's casing *is* the syntax. No keywords.

| Casing | Role | Judgment | Match on |
|---|---|---|---|
| `Pascal` | type / data | introduction | indices |
| `kebab` | function / term | elimination | values |
| `Pascal*Pascal` / `*op*` | mixfix type or operator | intro or elim | by segment casing |

The type checker enforces semantics. Convention enforces readability.
If you want a linter, write one. It's not the language's job.

---

## 2. ## Binders and Quantifiers

In this system, we use ∀ and Σ as our primary building blocks. All other forms are derived sugars used to clarify the creator's intent. Sugars stay outside of the parser, at a preprocessing stage. It is valid to any and all sugars

### The Core Primitives

* **∀(x: A). B**: The universal binder (Pi). A function where the type of the result B can depend on the input x.
* **Σ(x: A). B**: The dependent pair (Sigma). A bundle containing a witness x and a property B.

---

### Derived Sugars

While these elaborate to the same core nodes, the different syntax tells the reader how to think about the data:

| Surface Form | Core Node | Intent |
| :--- | :--- | :--- |
| **A -> B** | ∀(_: A). B | Non-dependent function; the input value is ignored by the return type. |
| **Π(x: A). B** | ∀(x: A). B | Dependent function; used when the value x specifically shapes B. |
| **∀(A: Type). B** | ∀(A: Type). B | Parametric polymorphism; signals the logic is uniform across types. |
| **∃(x: A). B** | Σ(x: A). B | Existential; the witness is intended to be "forgotten" or hidden after use. |

### Usage Guidelines

* **Σ vs ∃**: Use Σ if you plan to project the witness and compute with it. Use ∃ if the specific witness should be treated as an implementation detail.
*
* **∀ vs Π**: Use ∀ for type binders to show the function is generic. Use Π when the dependency is on a concrete value.
---

## 3. Metavariables (Holes)

```
?          -- anonymous hole, elaborator invents a fresh name
?name      -- named hole, same name = same metavariable
```

- Anonymous `?` are always independent. Two `?` never unify with each other.
- Named `?name` with the same name in the same declaration share one metavariable.
- `_` is pure discard. No constraint is generated.
- `?` says "something is here; figure it out." `_` says "nothing is here; ignore it."

Valid anywhere: type signatures, constructor fields, pattern positions, expressions.

```
mystery: ? -> Nat             -- infer the domain
round-trip: ?a -> ?a          -- both must be the same type
eval ? (lit-n n) = n          -- ? fills the Ty index in pattern position
const x ? = x                 -- don't-care arg with unification
```

---

## 4. BNF

### Lexical

```bnf
<upper>    ::= "A"..."Z"
<lower>    ::= "a"..."z"
<digit>    ::= "0"..."9"
<alnum>    ::= <upper> | <lower> | <digit>

<pascal>   ::= <upper> { <alnum> }
<kebab>    ::= <lower> { <alnum> | "-" <lower> }
<mixfix>   ::= <mix-seg> { <mix-seg> }     -- must contain ≥1 "*"
<mix-seg>  ::= "*" | <alnum>+ | <sym>+
<sym>      ::= "+" | "-" | "/" | "<" | ">" | "=" | "~" | "^"
             | "@" | "!" | "?" | "|" | "&" | "%" | "."

<nat-lit>  ::= <digit>+
<hole>     ::= "?" | "?" <kebab>
<comment>  ::= "--" { any } <newline>
```

### Top-level

```bnf
<program>    ::= { <decl> }
<decl>       ::= <type-decl> | <term-decl> | <prec-decl>
```

### Precedence

```bnf
<prec-decl>  ::= <fixity> <nat-lit> <mixfix>
<fixity>     ::= "infixl" | "infixr" | "prefix" | "postfix"
```

Types and terms share one precedence table.
Operator role (type former vs term) is determined by casing of segments.

### Types

```bnf
<type-decl>  ::= <pascal> [ "(" <param-list> ")" ] ":" NEWLINE
                   INDENT { <ctor-arm> } DEDENT

<param-list> ::= <param> { "," <param> }
<param>      ::= <var> | <var> ":" <type-expr>

<ctor-arm>   ::= <ctor-def>                      -- unindexed
               | <index-pats> "=" <ctor-def>     -- indexed

<index-pats> ::= <pat> { "," <pat> }             -- comma = resource/set index

<ctor-def>   ::= <kebab> { <ctor-field> }
<ctor-field> ::= "(" <var> ":" <type-expr> ")"
               | <type-expr>
               | <hole>
```

### Terms

```bnf
<term-decl>  ::= ( <kebab> | <mixfix> ) ":" <type-expr> NEWLINE
                   INDENT { <clause> } DEDENT

<clause>     ::= <pat> { <pat> } "=" <expr> NEWLINE
```

### Expressions

```bnf
<expr>       ::= <atom> { <atom> }         -- left-assoc application
               | <mixfix-expr>             -- Pratt pass
               | "\" <var> { <var> } "=>" <expr>
               | "let" <var> "=" <expr> "in" <expr>
               | <hole>

<atom>       ::= <var> | <pascal> | <nat-lit> | <hole> | "(" <expr> ")"
```

### Type expressions

```bnf
<type-expr>  ::= <type-atom>
               | <type-atom> "->" <type-expr>
               | "Π" "(" <var> ":" <type-expr> ")" "." <type-expr>
               | "∀" "(" <var> ":" <type-expr> ")" "." <type-expr>
               | "Σ" "(" <var> ":" <type-expr> ")" "." <type-expr>
               | "∃" "(" <var> ":" <type-expr> ")" "." <type-expr>
               | <mixfix-type>
               | <hole>

<type-atom>  ::= <pascal> { <type-atom> }
               | <var>
               | "U" [ <digit>+ ]
               | "(" <type-expr> ")"
               | <hole>
```

### Patterns

```bnf
<pat>        ::= "_"                    -- discard, no unification
               | <hole>                 -- metavariable, unification
               | <var>                  -- binding
               | <kebab> { <pat> }      -- constructor pattern
               | <nat-lit>
               | "(" <pat> ")"
```

---

## 5. Architecture

```
source text
    │
    ▼
indent/tokenize          -- pass 1: :indent/:dedent/:line tokens
    │                       Janet PEG cannot hold mutable indent state.
    │                       Same strategy as Python's tokenizer.
    ▼
classify-line (PEG)      -- pass 2: per-line PEG grammars
    │                       prec / header / ctor-arm / clause
    ▼
parse/build-cst          -- assembler: flat token stream → nested CST
    │
    ▼
Pratt pass               -- mixfix operator trees, application structure
    │                       reads infixl/infixr/prefix/postfix from CST
    │                       handles hole positions in expressions
    │
    ▼  ← YOU ARE HERE: needs to be written
    │
    ▼
sig/build                -- build signature from CST type declarations
    │                       params(Γ, f), typeOf(Γ, f) for every name
    │
    ▼
elab/decl                -- elaborate each declaration (Aya style)
    │   ├─ exact-application: f → lambda(f vars(Δ), Δ)
    │   ├─ ctor IxCall: matches(u,p) → σ, check v : Δ_c·σ
    │   ├─ hole collection: ? → tm/hole(gensym), ?name → shared
    │   └─ unification: solve constraint set
    │
    ▼
coreTT                   -- NbE kernel, bidirectional check/infer
```

### Why PEG + Pratt, not one pass

PEG is ordered choice with no backtracking. It handles structural disambiguation
cleanly: is this line a header, an arm, a clause? One look at the first token decides.

Operator precedence requires *comparing* adjacent operators and deciding
associativity. That comparison is stateful — Pratt parsing is exactly a
precedence-climbing stack. The two tools are complementary: PEG builds the flat
structure, Pratt builds the expression tree.

### Why two-pass indentation

Janet PEG grammars compile to bytecode. There is no way to bind a "current indent
level" variable inside a PEG rule. Same solution as Python's tokenizer: a pre-pass
emits INDENT/DEDENT tokens, after which the main grammar sees a flat stream with
explicit block markers.

---

## 6. The three files to write

### 6.1 `matches.janet` — the load-bearing piece

This is `matches(u, p) → σ | ⊥ | stuck` from the simpler-indexed-types paper.
It is **term-match-pattern**, not term-match-term. That's why it's decidable.

```
matches(u, x)      → [u/x]          -- variable: always succeeds, binds x to u
matches(∅, ∅)      → []             -- empty: trivially succeeds
matches(c u, c p)  → matches(u, p)  -- same ctor: recurse on args
matches(c₁ u, c₂p) → ⊥              -- different ctors: definite failure
matches(u, p)      → ⊥  if u is stuck (neutral) and p is a ctor pattern
```

Three outcomes mirror the paper exactly:
- **Yes** + substitution σ: constructor is available, apply σ to Δ_c
- **No**: constructor is unavailable, skip it in coverage
- **Stuck**: cannot decide (neutral term), pattern matching cannot proceed here

```janet
# Returns one of:
#   [:yes subst]   -- matched, subst maps pattern vars to terms
#   [:no]          -- definite mismatch
#   [:stuck]       -- neutral term, cannot decide

(defn matches [u p ctor-name-set]
  ...)

# Match a list of terms against a list of patterns (the selector case)
(defn matches* [us ps ctor-name-set]
  ...)
```

Key implementation points:
- You need `ctor-name-set` to distinguish constructors from variables.
  A term like `zero` is a constructor; `n` is a variable. Without this set
  you cannot tell them apart when matching.
- Holes `?` and `_` in patterns are both wildcards here — they both succeed
  and bind (hole) or discard (_). The difference is handled upstream by the
  elaborator before matches is called.
- Do NOT attempt higher-order unification. If you encounter a non-constructor
  head, return `:stuck`. This is the entire point of simpler indexed types.

### 6.2 `sig.janet` — signature management

The signature knows about every declared name: its parameters, its type, its
constructors (for data), its clauses (for functions).

```janet
# Build signature entry for a type declaration
# Returns {:kind :data :params [...] :sort ... :ctors [...]}
(defn sig/add-data [sig name params sort ctors] ...)

# Build signature entry for a function declaration
# Returns {:kind :func :params [...] :result ... :type ...}
(defn sig/add-func [sig name params result] ...)

# Exact application: f → lambda(f vars(Δ), Δ)
# This is the FuncRef rule from the elegant-elaboration paper.
# Every function reference elaborates to its fully-applied eta-expansion.
# coreTT then reduces it immediately when arguments arrive.
(defn sig/exact-ref [sig name]
  (let [delta (sig/params sig name)]
    (build-lambda [:app-spine name (vars delta)] delta)))

# Constructor availability: given type args u, which ctors are available?
# Returns list of {:ctor c :subst σ} where matches*(u, c.patterns) = [:yes σ]
(defn sig/available-ctors [sig data-name type-args ctor-name-set]
  ...)
```

The `ctor-name-set` is built once from the signature and passed down. It's the
set of all known constructor names in scope. This is what lets `matches` distinguish
`zero` (constructor) from `n` (variable) when they appear as selector terms.

### 6.3 `elab.janet` — the thin bridge

The elaborator's job is to translate CST → coreTT terms using `sig` and `matches`.
It should be *thin*. All hard decisions delegate.

**IxCall** (constructor with index patterns):
```janet
(defn elab/ctor-call [env sig data-name type-args ctor-name args]
  # 1. get the constructor entry from sig
  (let [ctor (sig/ctor sig data-name ctor-name)
        # 2. run matches on the current type args vs the ctor's selector patterns
        result (matches* type-args (ctor :patterns) (sig/ctor-name-set sig))]
    (match result
      [:yes sigma]
      # 3. apply σ to Δ_c, check args against the result
      (let [delta-c (apply-subst (ctor :params) sigma)]
        (check-args env sig delta-c args))
      [:no]
      (errorf "constructor %v not available at these indices" ctor-name)
      [:stuck]
      (errorf "cannot determine availability of %v: indices are neutral" ctor-name))))
```

**Exact application** (function reference):
```janet
(defn elab/func-ref [sig name]
  # Every bare function reference expands to its eta-normal form.
  # coreTT reduces it as arguments arrive via APP rule.
  (sig/exact-ref sig name))
```

**Hole collection**:
```janet
(defn elab/hole [ctx name]
  # Anonymous hole: fresh gensym, add to constraint set
  # Named hole: look up or create in constraint set, share the metavar
  (let [sym (if (nil? name) (gensym) (or (ctx/hole ctx name) (gensym)))]
    (ctx/add-hole ctx name sym)
    (coreTT/tm/hole sym)))
```

**Unification** (after elaboration):
```janet
# Walk the constraint set.
# For each unsolved hole, attempt to solve from the constraints.
# If a hole remains unsolved after full pass, it's an error.
# Named holes that appear in multiple positions must unify their solutions.
(defn unify/solve [constraints] ...)
```

---

## 7. What coreTT already gives you

`coreTT.janet` already has:
- `tm/hole name` — placeholder node
- `check Γ t A` — bidirectional checking
- `infer Γ t` — bidirectional synthesis
- `eval Γ t` — NbE evaluation
- `sem-eq ty v1 v2` — definitional equality with eta
- `subtype A B` — cumulative universe subtyping

The elaborator never passes holes to `check`/`infer` directly.
It resolves them first. If unification fails, it errors before coreTT sees anything.

---

## 8. What `lower.janet` got right (keep the ideas, not the code)

- `selector/match-term` is `matches(u, p)` — the right idea, wrong embedding
- `ctor/lower-indexed` correctly separates pat-binders from ctor-params
- `params/index-positions` correctly identifies which params are indices vs types
- `M/Yes`, `M/No`, `M/Stuck` — the right three outcomes

Extract those ideas into `matches.janet`. Everything else (S-expr node walking,
match-to-eliminator lowering, record desugaring) does not survive the rewrite.

---

## 9. File map after rewrite

```
src/
  parser.janet     -- PEG pass 1 (indent) + pass 2 (per-line grammars) + CST assembler
  pratt.janet      -- Pratt pass: mixfix trees, application structure
  sig.janet        -- Signature: params, types, ctors, exact-refs
  matches.janet    -- matches(u,p) → yes/no/stuck
  elab.janet       -- CST → coreTT: IxCall, ConCall, exact-app, hole collection
  unify.janet      -- Metavariable constraint solving
  coreTT.janet     -- NbE kernel (keep as-is)
  levels.janet     -- Universe levels (keep as-is)
```

Total elaboration flow per declaration:

```
CST decl
  → sig/build entry
  → elab/decl
      → for each ctor arm: matches* → [:yes σ] → check fields against Δ_c·σ
      → for each clause: elaborate patterns, elaborate body
      → collect holes → constraint set
  → unify/solve constraints
  → coreTT/check final term
```

---

## 10. Style guide (brief)

- Types are `Pascal`. Functions are `kebab`. Operators are `*seg*`.
- Constructor names are `lower`, attached to their type by context.
- Type variables are single lowercase: `A`, `B`, `n`, `m`.
- Prefer total functions. If partial, name it honestly.
- Clauses: most specific first, top to bottom.
- Holes `?` in development; remove before considering code done.
- If you cannot tell from the name whether something is a type or function,
  the name is wrong. Fix the name.
