# Requiem

A minimal dependently-typed language core in Janet, embeddable in C/C++ via Janet's FFI.

## Overview

Requiem implements:

- **NbE (Normalization by Evaluation)** with eta-equality for functions and pairs
- **HOAS** — substitution delegated to the host language
- **Bidirectional type checking** with universe subtyping (`Type₀ <: Type₁ <: ...`)
- **Identity types** with J eliminator
- **Pi, Sigma, Id** as core type formers
- **Frontend pipeline** — PEG parser -> lowering -> core elaboration

The core is ~500 lines of Janet. Zero dependencies beyond Janet itself.

## Build & Run

```bash
jpm build           # compile native extensions (HAMT, timer)
jpm test            # run full test suite
janet requiem.janet examples/test.requiem   # run frontend on a file
```

## Project Structure

```
src/
  coreTT.janet                  # NbE kernel, bidirectional checker, J eliminator
  levels.janet                  # Universe level algebra
  elab.janet                    # Elaboration from lowered terms to core terms
  frontend/
    sexpr/
      parser.janet              # PEG-based s-expression parser
      lower.janet               # Lowering (pattern matching, indexed constructors)
    surface/
      parser.janet              # Surface parser entrypoint
      ast.janet                 # Canonical surface AST constructors
      syntax.janet              # Compositional syntax aliases
      layout.janet              # Delimiter-aware split/layout helpers
      lexer.janet               # Surface tokenization entry helpers
      pratt.janet               # Pratt expression/type parsing entry helpers
      patterns.janet            # Pattern parser entry helpers
      decls.janet               # Top-level declaration parser entry helpers
native/
  hamt.c            # Persistent Hash Array Mapped Trie (C extension)
  timer.c           # High-resolution timer (C extension)
test/               # Property-based, unit, and regression tests
```

## Not Yet Planned

- Implicit arguments — everything is explicit
- Tooling / LSP — REPL + tests are sufficient

## License

MIT
