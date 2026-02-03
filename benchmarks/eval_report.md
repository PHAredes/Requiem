# Evaluator Implementation Comparison

I have benchmarked the current implementation against the original state of the codebase. To preserve the original implementation for your reference, I have saved it to [legacy/coreTT_v1.janet](file:///home/user/Repos/Requiem/legacy/coreTT_v1.janet).

| Implementation | J success (refl) [Med cycles] | J stuck (neutral) [Med cycles] | var lookup [Med cycles] |
| :--- | :--- | :--- | :--- |
| **Current (Split + Delay)** | **~13.5 ms** | ~333.9 ms | ~1.8 ms |
| **Legacy V1 (Single Eval)** | ~609.4 ms | ~466.4 ms | ~2.1 ms |

## Key Insights:
1. **Speedup**: The current implementation is **~45x faster** for successful `J` elimination due to the `delay` optimization.
2. **Refactoring**: Splitting the function provides a slight performance gain even without the `delay` (as shown in previous benchmarks).
3. **Legacy Version**: You can always find the original single-function `eval` in [legacy/coreTT_v1.janet](file:///home/user/Repos/Requiem/legacy/coreTT_v1.janet).

## Verification:
- All 105 tests passed with `jpm test` for all implementations.
- Final implementation: **Split + Delay**.
