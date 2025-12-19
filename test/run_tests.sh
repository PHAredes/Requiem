#!/usr/bin/env bash

# Test runner for Requiem test suite
# Usage:
#   ./test/run_tests.janet          # Run all tests (excluding benchmarks)
#   ./test/run_tests.janet Identity # Run only tests matching "Identity"
#   ./test/run_tests.janet --bench  # Include benchmarks

FILTER="${1:-}"
RUN_BENCH=false

if [[ "$FILTER" == "--bench" ]]; then
    RUN_BENCH=true
    FILTER=""
fi

echo "Discovering tests..."

DIRS="test/Core test/Types test/Properties test/Equality test/Regression"

if $RUN_BENCH; then
    DIRS="$DIRS test/Benchmarks"
fi

PASSED=0
FAILED=0

for dir in $DIRS; do
    if [[ -d "$dir" ]]; then
        for f in "$dir"/*.janet; do
            if [[ -f "$f" ]]; then
                if [[ -z "$FILTER" ]] || [[ "$f" == *"$FILTER"* ]]; then
                    echo ""
                    echo "----------------------------------------"
                    echo "Running $f"
                    echo "----------------------------------------"
                    if janet -e "(dofile \"$f\")"; then
                        ((PASSED++))
                    else
                        ((FAILED++))
                        echo "FAILED: $f"
                    fi
                fi
            fi
        done
    fi
done

echo ""
echo "========================================"
echo "SUMMARY: $PASSED suites passed, $FAILED failed"
echo "========================================"

if [[ $FAILED -gt 0 ]]; then
    exit 1
fi
