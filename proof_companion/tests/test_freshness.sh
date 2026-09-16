#!/usr/bin/env bash
# Mutate a disposable copy, never the user's source or deliverables.
set -euo pipefail
cd "$(dirname "$0")/../.."
test_dir=$(mktemp -d)
trap 'rm -rf "$test_dir"' EXIT
replica="$test_dir/repo"
mkdir -p "$replica/proof_companion"
mapfile -t sources < <(awk '{print $2}' proof_companion/data/SOURCE_MANIFEST.sha256)
cp --parents "${sources[@]}" "$replica/"
cp -R proof_companion/data proof_companion/generated proof_companion/chapters \
  "$replica/proof_companion/"
cp proof_companion/run.sh proof_companion/render.sh proof_companion/companion.tex \
  proof_companion/companion.pdf proof_companion/BUILD_MANIFEST.sha256 \
  "$replica/proof_companion/"

check_replica() {
  bash "$replica/proof_companion/run.sh" check >"$test_dir/check.log" 2>&1
}

must_fail() {
  if check_replica; then
    echo "FAIL: freshness accepted $1" >&2
    exit 1
  fi
}

check_replica
printf '\n-- Test mutation\n' >>"$replica/PhysicsOfConsciousness/Phase1_Primitives.lean"
must_fail 'a changed Lean input'
cp --parents PhysicsOfConsciousness/Phase1_Primitives.lean "$replica/"

printf '%s\n' '-- New input' >"$replica/PhysicsOfConsciousness/FreshnessProbe.lean"
must_fail 'a newly added Lean source'
rm "$replica/PhysicsOfConsciousness/FreshnessProbe.lean"

printf '\n' >>"$replica/proof_companion/data/gluing.json"
must_fail 'a modified extraction snapshot'
cp proof_companion/data/gluing.json "$replica/proof_companion/data/"

printf '\nchanged\n' >>"$replica/proof_companion/generated/sheaf-property.statement.txt"
must_fail 'a modified generated statement'
cp proof_companion/generated/sheaf-property.statement.txt "$replica/proof_companion/generated/"

printf '\nchanged\n' >>"$replica/proof_companion/companion.pdf"
must_fail 'a modified PDF'
echo 'Freshness tests passed: changed/new Lean inputs, snapshot, generated statement, and PDF.'
