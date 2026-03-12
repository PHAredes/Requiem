# Property Testing Notes

This test suite now supports QuickCheck-style reproducibility knobs:

- `TEST_SEED=<seed> jpm test`
- `TEST_TRIALS=<n> jpm test`

Examples:

```bash
TEST_SEED=123 jpm test
TEST_SEED=123 TEST_TRIALS=200 janet test/Properties/Confluence.janet
TEST_TRIALS=500 bash scripts/property_stress.sh 101 202 303 404 505
```

Guidelines for new property tests:

1. Generate closed, typable terms whenever possible.
2. Prefer explicit witness pairs or diamonds over tautologies.
3. Compare normal forms with `test/Utils/Assertions.janet` helpers.
4. Print the seed and generated witness on failure.
5. Keep property counts configurable through `test/property-count`.
6. Prefer witnessed inferable judgments when testing weakening/check-infer style metatheory.

Current generator entry points:

- `test/Utils/Generators.janet:seed/current`
- `test/Utils/Generators.janet:trials/current`
- `test/Utils/Generators.janet:gen-canonical-sample`
- `test/Utils/Generators.janet:gen-fragment-sample`
- `test/Utils/Generators.janet:gen-inferable-closed-sample`
- `test/Utils/Generators.janet:gen-convertible-pair`
- `test/Utils/Generators.janet:gen-reduction-diamond`
- `test/Utils/Generators.janet:gen-well-typed-sample`
- `test/Utils/Generators.janet:gen-inferable-judgment`

Stress helper:

- `scripts/property_stress.sh`
- `scripts/property_stress_ci.sh`

Suggested split:

- `gen-canonical-sample` for canonical-form and normalization-value properties
- `gen-fragment-sample` for progress/reduction properties over the tested fragment
- `gen-inferable-closed-sample` for closed inferable terms, including inferable `J` cases
- `gen-inferable-judgment` for weakening/check-infer/preservation style properties in context

Current reduction-path entry points:

- `test/Utils/ReductionPaths.janet:step-leftmost`
- `test/Utils/ReductionPaths.janet:step-rightmost`
- `test/Utils/ReductionPaths.janet:get-reduction-paths`
