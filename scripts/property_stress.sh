#!/usr/bin/env bash
set -euo pipefail

TRIALS="${TEST_TRIALS:-500}"
SEEDS=("$@")

if [ ${#SEEDS[@]} -eq 0 ]; then
  SEEDS=(101 202 303 404 505)
fi

SUITES=(
  test/Properties/ChurchRosser.janet
  test/Properties/Confluence.janet
  test/Properties/Consistency.janet
  test/Properties/Decidability.janet
  test/Properties/Normalization.janet
  test/Properties/Preservation.janet
  test/Properties/Soundness.janet
  test/Properties/Substitution.janet
  test/Properties/Weakening.janet
)

for seed in "${SEEDS[@]}"; do
  printf '== seed %s trials %s ==\n' "$seed" "$TRIALS"
  for suite in "${SUITES[@]}"; do
    TEST_SEED="$seed" TEST_TRIALS="$TRIALS" janet "$suite"
  done
done

printf '== full suite seed %s trials %s ==\n' "${SEEDS[0]}" "$TRIALS"
TEST_SEED="${SEEDS[0]}" TEST_TRIALS="$TRIALS" jpm test
