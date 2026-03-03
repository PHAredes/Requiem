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
**Zero dependencies.**

## New Features

### Tesla-Style Frontend
Requiem now includes a complete frontend pipeline:
- **Parser**: PEG-based parser for Lispy surface syntax
- **Desugar**: Tesla-style desugaring with pattern-based encoding for indexed types
- **Elaborate**: Elaboration to core type theory terms

### Enhanced Error Messages
Type checking errors now provide:
- Available variables in context for unbound variable errors
- Expected vs actual format details for projection errors
- Helpful suggestions for common type checking failures
- Clear explanations with actionable tips

### Universe Subtyping
- Cumulative universe hierarchy: `Type₀ <: Type₁ <: Type₂`
- Semantic subtyping relation for Type, Pi, and Sigma types
- Pi variance (contravariant domain, covariant codomain)
- Sigma covariance
- Checker uses subtyping at check-time for better type inference

## Status: Active Development

**What works:**
- ✅ Core type theory (Pi, Sigma, Id types)
- ✅ NbE with eta-equality
- ✅ Comprehensive property-based test suite (Confluence, Church-Rosser, Normalization)
- ✅ Context with efficient shadowing
- ✅ Universe subtyping with cumulative hierarchy (Type₀ <: Type₁)
- ✅ Tesla-style frontend pipeline (parse → desugar → elaborate)
- ✅ Enhanced error messages with helpful suggestions
- ✅ Legacy experiments (`legacy/hoas`, `legacy/phoas`), for documentation

**Features:**
- **Universe Subtyping**: Semantic subtyping with Type cumulativity, Pi variance, and Sigma covariance
- **Frontend Pipeline**: Lispy PEG-based parser, Tesla-style desugaring, elaboration to core TT
- **Enhanced Error Messages**: Context-aware suggestions, detailed explanations, helpful hints
- **Performance Optimizations**: Cached normalization (111x speedup for repeated evaluations)

**Not planned (yet):**
- Implicit arguments — pass everything explicitly
- Tooling / LSP — REPL + tests are sufficient

## Why

I needed a dependently-typed core I could:
1. Fully understand and modify
2. Embed in C/C++ projects without heavy runtimes
3. Use to build verified DSLs on demand

Requiem solves *my* problem. Not yours. Maybe that's useful to you anyway.

Requiem is a standard Janet project managed by `jpm`.

```bash
# Install dependencies (none!) and build
jpm build

# Install globally (optional)
# jpm install
```

## Running

```bash
# Run the test suite
jpm test

# Run the frontend pipeline on a file
janet requiem.janet examples/test.requiem

# Run context benchmarks
janet benchmarks/Context.janet

# Test enhanced error messages
janet test/ErrorMessages.janet
```

## License

MIT
