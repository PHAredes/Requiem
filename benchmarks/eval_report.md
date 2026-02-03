# Evaluator Implementation Comparison

Benchmark results for the current implementation against the legacy version ([legacy/coreTT_v1.janet](file:///home/user/Repos/Requiem/legacy/coreTT_v1.janet)).

| Implementation | J success (refl) [Med cycles] | J stuck (neutral) [Med cycles] | var lookup [Med cycles] |
| :--- | :--- | :--- | :--- |
| **Current (Split)** | **~13.5 ms** | ~333.9 ms | ~1.8 ms |
| **Legacy V1 (Single Eval)** | ~609.4 ms | ~466.4 ms | ~2.1 ms |

## Key Insights:
1. **Speedup**: The current implementation is significantly faster for successful `J` elimination due to the split evaluator and improved lookup.
2. **Refactoring**: Splitting the evaluator provides a performance gain by reducing branching in the hot path.
3. **Legacy Version**: The original single-function `eval` is preserved in `legacy/coreTT_v1.janet`.

## Verification:
- All 105 tests passed with `jpm test` for all implementations.
- Final implementation: **Split Evaluator**.
