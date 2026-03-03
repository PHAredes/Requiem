# Requiem Roadmap (Tesla + Cumulative Universes)

This roadmap is ordered for correctness first, then ergonomics.

## M0 - Selector Matching Soundness (in progress)

- [x] Implement 3-way selector matching result (`yes` / `no` / `stuck`) for constructor availability checks.
- [x] Reject `match` lowering when selector matching is `stuck` (ambiguous constructor availability).
- [ ] Use selector result to drive branch obligations (`yes` constructors required, `no` constructors optional/unreachable diagnostics).
- [ ] Add dedicated diagnostics for unreachable constructor clauses under `no`.

## M1 - Coverage and Overlap for Selector Clauses

- [ ] Exhaustiveness checking for function/data selector-style clauses.
- [ ] Redundancy and overlap reporting with source-oriented error messages.
- [ ] Explicit handling of `impossible` branches with validation.

## M2 - Inductive Soundness Gates

- [ ] Strict positivity checks for `data` declarations.
- [ ] Constructor argument sanity checks for recursive occurrences.

## M3 - Termination Discipline

- [ ] Structural recursion checker for `def` bodies.
- [ ] Reject non-structural/self-referential recursion that breaks normalization intent.

## M4 - Universe System Upgrade

- [ ] Move from concrete level arithmetic to level variables + constraints.
- [ ] Constraint solving for `max`/`succ` interactions.
- [ ] Universe-polymorphic declarations and checking.

## M5 - Elimination Policy Clarity

- [ ] Document and enforce elimination constraints across cumulative universes.
- [ ] Add tests for small/large elimination behavior.

## M6 - Metatheory Regression Harness

- [ ] Strengthen preservation/progress-style regression checks.
- [ ] Add canonicity/normalization-oriented property tests tied to recursion/induction features.

## M7 - Usability Layer

- [ ] Module system and namespace rules.
- [ ] Prelude + standard library baseline.
- [ ] Better error spans and actionable diagnostics.
- [ ] Package/build workflow stabilization.
