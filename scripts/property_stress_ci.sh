#!/usr/bin/env bash
set -euo pipefail

TRIALS="${TEST_TRIALS:-150}"

TEST_TRIALS="$TRIALS" bash "$(dirname "$0")/property_stress.sh" 101 202

printf 'CI property stress passed with TEST_TRIALS=%s\n' "$TRIALS"
