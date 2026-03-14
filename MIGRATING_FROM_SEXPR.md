# Migrating from the legacy s-expression frontend

`src/frontend/sexpr/` is deprecated.

For source programs, prefer the main surface frontend used by `.requiem` files. The old s-expression parser and lowering code remain only for compatibility with a small amount of internal tooling.

## What changes

- Old source style: parenthesized s-expressions such as `(data ...)` and `(def ...)`
- New source style: surface declarations such as `Nat:` and `sum(n: Nat): Nat`
- Preferred pipeline: `src/frontend/surface/parser.janet` -> `src/frontend/surface/lower.janet` -> `src/elab.janet`

## Common translations

Data declarations:

```lisp
(data Nat: Type ((zero Nat) (succ (forall (n: Nat). Nat))))
```

becomes

```requiem
Nat:
  zero
  succ Nat
```

Functions:

```lisp
(def id: (forall (A: Type). (forall (x: A). A)) x = x)
```

becomes

```requiem
id(A: Type, x: A): A
  x = x
```

Indexed constructors:

```lisp
(data Vec (A: Type) (n: Nat): Type
  (| zero = vnil)
  (| A (succ n) = vcons (x: A) (xs: Vec A n)))
```

becomes

```requiem
Vec(A: Type, n: Nat):
  zero = vnil
  A, (succ n) = vcons (x: A) (xs: Vec A n)
```

Universe levels:

```lisp
Type(u + 2)
U(max(1, u + 2, v))
```

becomes

```requiem
Type(u + 2)
Type(max(1, u + 2, v))
```

`U(...)` is still accepted, but `Type(...)` is the canonical form.

Lambdas and Pi types:

```lisp
(fn (x) x)
(forall (A: Type). A -> A)
```

becomes

```requiem
fn x . x
Pi(A: Type). A -> A
```

## API migration

- Replace `src/frontend/sexpr/parser.janet` with `src/frontend/surface/parser.janet`
- Replace `parse/text` with `parse/program` for source files
- Replace legacy single-form parsing with `parse/expr-text` or `parse/type-text` as appropriate
- Replace `src/frontend/sexpr/lower.janet` with `src/frontend/surface/lower.janet`
- Prefer `elab/program` on lowered surface declarations over the deprecated bridge in `src/elab_legacy.janet`

## What is still legacy-only

- `src/elab_legacy.janet`
- `src/frontend/sexpr/parser.janet`
- `src/frontend/sexpr/lower.janet`

Those paths should be treated as transitional.

## CLI status

The `requiem` CLI no longer falls back to the legacy s-expression frontend for non-`.requiem` files.

- Use `.requiem` source files with `janet requiem.janet path/to/file.requiem`
- Legacy s-expression inputs must go through `src/elab_legacy.janet` or other internal compatibility code only while migration is still in progress
