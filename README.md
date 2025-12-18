# Requiem

A minimal dependently-typed language with a correct-by-construction core, built for personal use and C/C++ embedding via Janet.

## What it is

Requiem is a dependently-typed language in the spirit of Agda, implementing:

- **HOAS (Higher-Order Abstract Syntax)** — delegates substitution to the host language
- **Normalization by Evaluation (NbE)** with eta-equality for functions and pairs
- **Bidirectional type checking** — clean separation between inference and checking
- **Identity types (J eliminator)** — intensional equality à la Martin-Löf
- **Universe hierarchy** — `Type₀ : Type₁ : Type₂ : ...`

The core is ~500 lines of Janet and embeds trivially into C/C++ via Janet's FFI.

## Status: Work in Progress

**What works:**
- ✅ Core type theory (Pi, Sigma, Id types)
- ✅ NbE with eta-equality
- ✅ Mostly property-based tests passing
- ✅ Context with efficient shadowing (benchmark validated)
- ✅ Legacy experiments (`legacy/hoas`, `legacy/phoas`), for documentation

**Currently consolidating:**
- Finalizing the core (`src/coreTT.janet`)
- Fixing "gambiarras"

**Not planned (yet):**
- Parser / surface syntax — write terms directly in Janet s-expressions
- Elaboration / implicit arguments — pass everything explicitly
- Tooling / LSP — REPL + tests are sufficient

## Why

I needed a dependently-typed core I could:
1. Fully understand and modify
2. Embed in C/C++ projects without heavy runtimes
3. Use to build verified DSLs on demand

Requiem solves *my* problem. Not yours. Maybe that's useful to you anyway.

## Running
```bash
# Run tests
janet test/coreTT.janet
janet test/coreTT-id.janet
janet test/coreTT-plus.janet

# Benchmark context operations
janet test/ctx.benchmark.janet
```

## License

MIT
