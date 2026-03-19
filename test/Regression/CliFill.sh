#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$repo_root"

check_output=$(janet requiem.janet check "examples/hole-fill.requiem")
case "$check_output" in
  *"?goal : Nat"*) ;;
  *)
    printf 'expected check output to mention the Nat goal\n' >&2
    exit 1
    ;;
esac

fill_check_output=$(janet requiem.janet fill "examples/hole-fill.requiem" goal "zero")
case "$fill_check_output" in
  *"Target: check block 1"*"Filled ?goal with zero"*"=> zero"*) ;;
  *)
    printf 'expected fill output for check block target\n' >&2
    exit 1
    ;;
esac

fill_clause_output=$(janet requiem.janet fill "examples/clause-hole-fill.requiem" goal "zero")
case "$fill_clause_output" in
  *"Target: function id clause 1"*"Filled ?goal with zero"*"=> zero"*) ;;
  *)
    printf 'expected fill output for function clause target\n' >&2
    exit 1
    ;;
esac

if janet requiem.janet fill "examples/clause-hole-fill.requiem" goal "Type0" >/tmp/requiem-cli-fill.err 2>&1; then
  printf 'expected ill-typed fill to fail\n' >&2
  exit 1
fi

bad_fill_output=$(< /tmp/requiem-cli-fill.err)
case "$bad_fill_output" in
  *"type mismatch between expected type and inferred type"*) ;;
  *)
    printf 'expected ill-typed fill error output\n' >&2
    exit 1
    ;;
esac

rm -f /tmp/requiem-cli-fill.err
printf 'CLI fill regression script passed\n'
