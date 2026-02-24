# AGENTS.md

This file provides guidance for AI agents working on the Requiem codebase.

## Build/Test/Development Commands

### Core Commands
```bash
# Build the project (compiles native extensions)
jpm build

# Run the full test suite
jpm test

# Run individual test files
janet test/Core/coreTT-J.janet
janet test/Properties/Confluence.janet
janet test/Integration/Integration.janet

# Run benchmarks
janet benchmarks/Context.janet

# Start REPL for manual testing
janet
```

### Test Categories
- `test/Core/` - Core functionality tests
- `test/Properties/` - Property-based tests (Confluence, Church-Rosser, etc.)
- `test/Equality/` - Equality property tests
- `test/Types/` - Type system tests
- `test/Integration/` - Integration tests
- `test/Regression/` - Regression tests
- `test/Native/` - C extension tests
- `test/Utils/` - Test utilities

## Code Style Guidelines

### Naming Conventions
- **Type constructors**: `ty/` prefix (e.g., `ty/type`, `ty/pi`, `ty/sigma`)
- **Term constructors**: `tm/` prefix (e.g., `tm/var`, `tm/lam`, `tm/app`)
- **Neutral terms**: `ne/` prefix (e.g., `ne/var`, `ne/app`)
- **Normal forms**: `nf/` prefix (e.g., `nf/neut`, `nf/lam`, `nf/pi`)
- **Context operations**: `ctx/` prefix (e.g., `ctx/empty`, `ctx/add`, `ctx/lookup`)
- **Evaluation functions**: `eval/` prefix (e.g., `eval/neutral`, `eval/value`)

### Tag Constants
- Use uppercase with slashes for type tags: `T/Type`, `T/Pi`, `T/Sigma`, `T/Id`, `T/Refl`
- Use uppercase with slashes for normal form tags: `NF/Neut`, `NF/Lam`, `NF/Pi`, `NF/Sigma`
- Hexadecimal values for tags (e.g., `0x01`, `0x02`, `0x100`)

### Data Structure Patterns
1. **Tuples with tagged first element** for all AST nodes:
   ```janet
   [:var x]           # Variable
   [:lam body]        # Lambda
   [:app f x]         # Application
   [:type l]          # Type universe
   [:t-pi A B]        # Pi type (term)
   ```

2. **Tagged vectors for semantic values**:
   ```janet
   [T/Type lvl]       # Universe
   [T/Pi A B]         # Pi type
   [NF/Lam body]      # Normal form lambda
   ```

3. **HOAS for function types**: Use native Janet functions to represent Pi types

### Import Style
- Import native modules at top of file:
  ```janet
  (import /build/hamt :as h)
  ```

### Error Handling
- Use `errorf` for runtime errors:
  ```janet
  (errorf "unbound variable: %v" x)
  ```

### Test Style
- Use the custom test framework from `test/Utils/TestRunner.janet`:
  ```janet
  (start-suite "Suite Name")
  (assert condition "Test description")
  (assert-error function "Expected error test")
  (end-suite)
  ```

## Architecture Guidelines

### Core Structure
- `src/coreTT.janet` contains the main type theory implementation
- Native extensions in `native/` for performance-critical code
- Tests should be comprehensive, including property-based tests where applicable

### Performance Considerations
- The project is optimized for modern hardware performance
- Use HAMT (Hash Array Mapped Trie) for efficient data structures
- Prefer native C extensions for hot paths (timer, hamt)
- Maintain the split evaluator design for better branch prediction

### Type Theory Implementation
- Maintain bidirectional type checking (separate inference and checking)
- Preserve NbE (Normalization by Evaluation) with eta-equality
- Keep identity types implementation correct
- Ensure proper handling of universe hierarchy

## Adding New Features

1. **New Types**: Add tags following the hex pattern, update all relevant constructors
2. **New Operations**: Follow the naming convention with appropriate prefix
3. **Tests**: Always add comprehensive tests, including property-based tests
4. **Documentation**: Update comments and design documents if applicable

## Notes for Agents

- This is a sophisticated mathematical codebase implementing dependent type theory
- The code is intentionally minimal with zero external dependencies
- Focus on correctness and performance when making changes
- The project uses Janet, a Lisp-like language - expect S-expressions
- Test coverage is critical - run `jpm test` after all changes
- No automatic linting/formatting configured - follow existing patterns manually