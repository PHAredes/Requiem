# Requiem

A minimal dependently-typed language core in Janet, embeddable in C/C++ via Janet's FFI.

## Overview

Requiem implements:

- **NbE (Normalization by Evaluation)** with eta-equality for functions and pairs
- **HOAS** — substitution delegated to the host language
- **Bidirectional type checking** with universe subtyping (`Type₀ <: Type₁ <: ...`)
- **Identity types** with J eliminator
- **Pi, Sigma, Id** as core type formers
- **Frontend pipeline** — PEG parser -> surface lowering -> core elaboration

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
  coreTT.janet      # NbE kernel, bidirectional checker, J eliminator
  elab.janet        # Elaboration from lowered surface terms to core terms
  surface.janet     # Surface lowering (pattern matching, indexed constructors)
  parser.janet      # PEG-based s-expression parser
  levels.janet      # Universe level algebra
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
