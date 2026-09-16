#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
test_dir=$(mktemp -d)
trap 'rm -rf "$test_dir"' EXIT

bash proof_companion/render.sh proof_companion/selection.json proof_companion/data \
  "$test_dir/generated"
diff -ru proof_companion/generated "$test_dir/generated"

# A renamed declaration must fail, rather than silently disappear from the document.
jq '.[0].declarations[0].name = "PhysicsOfConsciousness.missing_companion_declaration"' \
  proof_companion/selection.json >"$test_dir/missing.json"
if bash proof_companion/render.sh "$test_dir/missing.json" proof_companion/data \
  "$test_dir/missing-output" >"$test_dir/missing.log" 2>&1; then
  echo 'FAIL: rendering silently accepted a missing declaration' >&2
  exit 1
fi

# Duplicate document IDs would overwrite statement files and cross-reference labels.
jq '.[0].declarations[1].id = .[0].declarations[0].id' \
  proof_companion/selection.json >"$test_dir/duplicate.json"
if bash proof_companion/render.sh "$test_dir/duplicate.json" proof_companion/data \
  "$test_dir/duplicate-output" >"$test_dir/duplicate.log" 2>&1; then
  echo 'FAIL: rendering accepted duplicate document IDs' >&2
  exit 1
fi
echo 'Rendering tests passed: reproducibility, missing declarations, and duplicate IDs.'
