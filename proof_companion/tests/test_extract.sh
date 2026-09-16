#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
test_dir=$(mktemp -d)
trap 'rm -rf "$test_dir"' EXIT

extract() {
  lake env lean --run proof_companion/Extract.lean "$@"
}

extract proof_companion/tests/Fixture.lean "$test_dir/fixture.json" \
  CompanionFixture.identity CompanionFixture.branched CompanionFixture.assumed_bound

jq -e '
  .schema_version == 1 and
  (.declarations | length) == 3 and
  (.declarations[] | select(.name == "CompanionFixture.identity") |
    (.statement | contains("α")) and (.tactics | length) == 0) and
  (.declarations[] | select(.name == "CompanionFixture.branched") |
    any(.tactics[]; .source == "constructor" and
      (.goals_before | length) == 1 and (.goals_after | length) == 2) and
    any(.tactics[]; .source == "exact hP" and (.goals_after | length) == 0)) and
  (.declarations[] | select(.name == "CompanionFixture.assumed_bound") |
    (.proof_dependencies | index("CompanionFixture.Calibration.bounded")) != null) and
  any(.structures[]; .name == "CompanionFixture.Calibration" and
    any(.fields[]; .name == "CompanionFixture.Calibration.bounded")) and
  (.anonymous_examples | length) == 1
' "$test_dir/fixture.json" >/dev/null

extract proof_companion/tests/Fixture.lean "$test_dir/repeat.json" \
  CompanionFixture.identity CompanionFixture.branched CompanionFixture.assumed_bound
cmp "$test_dir/fixture.json" "$test_dir/repeat.json"

if extract proof_companion/tests/Fixture.lean "$test_dir/missing.json" \
  CompanionFixture.does_not_exist >"$test_dir/missing.log" 2>&1; then
  echo 'FAIL: a missing selection was accepted' >&2
  exit 1
fi
test ! -e "$test_dir/missing.json"

cat >"$test_dir/Invalid.lean" <<'LEAN'
import Lean
theorem unfinished : False := by skip
LEAN
if extract "$test_dir/Invalid.lean" "$test_dir/invalid.json" unfinished \
  >"$test_dir/invalid.log" 2>&1; then
  echo 'FAIL: an unfinished proof was accepted' >&2
  exit 1
fi
test ! -e "$test_dir/invalid.json"
echo 'Extraction tests passed: statements, branches, term proofs, fields, examples, determinism, failures.'
