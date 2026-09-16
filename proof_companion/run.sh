#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
action=${1:-check}
companion_dir=proof_companion

source_manifest() {
  {
    printf '%s\n' lean-toolchain lake-manifest.json lakefile.toml \
      PhysicsOfConsciousness.lean proof_companion/Extract.lean proof_companion/selection.json
    find PhysicsOfConsciousness -name '*.lean' -type f
  } | LC_ALL=C sort | xargs sha256sum
}

case "$action" in
  extract)
    mapfile -t modules < <(jq -r '.[].module + ":olean"' "$companion_dir/selection.json")
    if ! lake build "${modules[@]}" >"$companion_dir/.extract-build.log" 2>&1; then
      tail -n 60 "$companion_dir/.extract-build.log" >&2
      exit 1
    fi
    work_dir=$(mktemp -d)
    trap 'rm -rf "$work_dir"' EXIT
    source_manifest >"$work_dir/SOURCE_MANIFEST.sha256"
    while IFS=$'\t' read -r id source; do
      mapfile -t names < <(jq -r --arg id "$id" \
        '.[] | select(.id == $id) | .declarations[].name' "$companion_dir/selection.json")
      lake env lean --run "$companion_dir/Extract.lean" "$source" "$work_dir/$id.json" \
        "${names[@]}"
    done < <(jq -r '.[] | [.id, .source] | @tsv' "$companion_dir/selection.json")
    sha256sum --check --status "$work_dir/SOURCE_MANIFEST.sha256"
    mkdir -p "$companion_dir/data"
    cp "$work_dir/"* "$companion_dir/data/"
    sha256sum "$companion_dir/data/"*.json "$companion_dir/data/SOURCE_MANIFEST.sha256" \
      >"$companion_dir/data/SNAPSHOT_MANIFEST.sha256"
    ;;
  render)
    bash "$companion_dir/render.sh"
    ;;
  pdf)
    bash "$companion_dir/render.sh"
    # Some TeX installations have XeTeX and LaTeX sources but no xelatex format.
    # Build that format locally, without changing the system TeX installation.
    mkdir -p "$companion_dir/.tex-cache"
    if command -v xelatex >/dev/null; then
      tex_engine=(xelatex)
    else
      if test ! -f "$companion_dir/.tex-cache/xelatex.fmt"; then
        xetex -ini -etex -jobname=xelatex -output-directory="$companion_dir/.tex-cache" \
          -interaction=nonstopmode -halt-on-error '\input xelatex.ini' \
          >"$companion_dir/.tex-cache/format.log" 2>&1
      fi
      tex_engine=(xetex "-fmt=$PWD/$companion_dir/.tex-cache/xelatex.fmt")
    fi
    (
      cd "$companion_dir"
      "${tex_engine[@]}" -interaction=nonstopmode -halt-on-error companion.tex >.latex-pass1.log
      "${tex_engine[@]}" -interaction=nonstopmode -halt-on-error companion.tex >.latex-pass2.log
    )
    if rg 'Missing character:|LaTeX Warning:.*undefined|Overfull' "$companion_dir/companion.log"; then
      echo 'PDF has missing glyphs, unresolved references, or overflowing content.' >&2
      exit 1
    fi
    sha256sum "$companion_dir/companion.tex" "$companion_dir/chapters/"*.tex \
      "$companion_dir/generated/"* "$companion_dir/companion.pdf" \
      >"$companion_dir/BUILD_MANIFEST.sha256"
    ;;
  check)
    sha256sum --check --status "$companion_dir/data/SOURCE_MANIFEST.sha256"
    work_dir=$(mktemp -d)
    trap 'rm -rf "$work_dir"' EXIT
    source_manifest >"$work_dir/sources.sha256"
    cmp "$companion_dir/data/SOURCE_MANIFEST.sha256" "$work_dir/sources.sha256"
    sha256sum --check --status "$companion_dir/data/SNAPSHOT_MANIFEST.sha256"
    bash "$companion_dir/render.sh" "$companion_dir/selection.json" \
      "$companion_dir/data" "$work_dir/generated"
    diff -ru "$companion_dir/generated" "$work_dir/generated"
    sha256sum --check --status "$companion_dir/BUILD_MANIFEST.sha256"
    echo 'Proof companion: sources, snapshot, generated text, and PDF match their manifests.'
    ;;
  test)
    bash "$companion_dir/tests/test_extract.sh"
    bash "$companion_dir/tests/test_render.sh"
    bash "$companion_dir/tests/test_freshness.sh"
    ;;
  *)
    echo 'Usage: bash proof_companion/run.sh {extract|render|pdf|check|test}' >&2
    exit 2
    ;;
esac
