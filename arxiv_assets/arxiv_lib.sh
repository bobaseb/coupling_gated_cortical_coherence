# Helpers shared by the arXiv builds: ./prepare_arxiv.sh (the companion) and
# unity/prepare_arxiv.sh (the physical-unity paper). Sourced, not run.
#
# They carry the guarantees AGENTS.md section 7 asks of every submission, so a
# second paper gets them by calling these rather than by copying them: every
# sed edit is checked to have applied, the submission is compiled from the
# unpacked tarball, and the build records the digest of every source it packed.

# edit_file <file> <description> <sed expression>
#
# A sed whose pattern no longer matches is the failure a build cannot otherwise
# see: the document still compiles, and it is the wrong document -- unstyled,
# double-spaced, or carrying line numbers into a posted preprint.
edit_file() {
  local file="$1" what="$2" expression="$3" before
  before="$(sha256sum "$file" | cut -d' ' -f1)"
  sed -i "$expression" "$file"
  if [ "$before" = "$(sha256sum "$file" | cut -d' ' -f1)" ]; then
    echo "prepare_arxiv: '$what' changed nothing -- $file no longer matches this script" >&2
    exit 1
  fi
}

# A citation link broken across a page break makes pdfTeX abort with
# "\pdfendlink ended up in different nesting level" -- a fatal signal, not a
# warning, and one no source file can predict: which citation lands on a break
# depends on every word before it, and a restyled document paginates unlike the
# source. Boxing each citation link removes the class of failure rather than the
# instance. The box goes around each reference's link, not around the whole
# group: a boxed group cannot break at its "; " either, and a two-reference
# group then leaves the line before it stretched to a few words.
# \emergencystretch is the last-resort slack that keeps a citation too wide for
# the space left from overfilling its line instead. Both belong in the build
# rather than in the sources: the unstyled documents paginate differently.
# shellcheck disable=SC2034  # read by the scripts that source this file
CITE_BOXING='s/\\renewcommand{\\cite}\[1\]{\\citep{#1}}/\\renewcommand{\\cite}[1]{\\citep{#1}}\n\\makeatletter\n\\AtBeginDocument{\\let\\NATlink@start\\hyper@natlinkstart\\let\\NATlink@end\\hyper@natlinkend\\def\\hyper@natlinkstart#1{\\leavevmode\\hbox\\bgroup\\NATlink@start{#1}}\\def\\hyper@natlinkend{\\NATlink@end\\egroup}}\n\\makeatother\n\\emergencystretch=6em/'

# The NeurIPS preprint style in place of a 12pt article. \pdfoutput=1 on the
# first line tells arXiv to run pdflatex rather than guessing from the file set.
# shellcheck disable=SC2034
NEURIPS_STYLE='s/\\documentclass\[12pt\]{article}/\\pdfoutput=1\n\\documentclass{article}\n\\usepackage[preprint]{neurips_2026}/'

# verify_tarball <tarball>
#
# Compile what is about to be shipped, from the unpacked archive and nothing
# else, and copy the PDF beside the tarball as main.pdf. Compiling in place
# would pass on a file that exists in the build directory and is missing from
# the tarball, which is the one failure a local build cannot distinguish from
# success.
verify_tarball() {
  local tarball="$1" verify fail=0 pattern what
  echo "prepare_arxiv: verifying the packed submission compiles"
  verify="$(mktemp -d)"
  tar -xzf "$tarball" -C "$verify"
  (
    cd "$verify"
    for pass in 1 2 3; do
      pdflatex -interaction=nonstopmode -file-line-error main.tex > "pass$pass.out" 2>&1 || true
    done
  )
  while IFS='|' read -r what pattern; do
    if grep -qE "$pattern" "$verify/main.log"; then
      echo "prepare_arxiv: $what" >&2
      grep -E "$pattern" "$verify/main.log" | head -5 >&2
      fail=1
    fi
  done <<'CHECKS'
LaTeX errors in the assembled document|^(\./)?[^ ]*:[0-9]+: |^! 
undefined references|LaTeX Warning: Reference .* undefined
undefined citations|LaTeX Warning: Citation .* undefined
missing graphics|File .* not found
CHECKS
  [ -f "$verify/main.pdf" ] || { echo "prepare_arxiv: no main.pdf produced" >&2; fail=1; }
  if [ "$fail" -ne 0 ]; then
    rm -rf "$verify"
    echo "prepare_arxiv: NOT shipping a broken submission" >&2
    exit 1
  fi
  cp "$verify/main.pdf" main.pdf
  rm -rf "$verify"
  echo "prepare_arxiv: compiled cleanly from the tarball, $(pdfinfo main.pdf | awk '/^Pages:/{print $2}') pages"
}

# write_manifest <repository root> <regenerate command> <source>...
#
# Record what this was built from. A submission directory is not tracked, so
# nothing else can tell whether the one sitting there is the current manuscript
# or last week's; check_arxiv_freshness.py answers that from this file.
write_manifest() {
  local root="$1" command="$2"
  shift 2
  printf '# arXiv submission built %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '# from commit %s%s\n' \
    "$(git -C "$root" rev-parse --short HEAD)" \
    "$(git -C "$root" diff --quiet HEAD 2>/dev/null || echo ' (working tree modified)')"
  printf '# regenerate with %s\n' "$command"
  printf '%s\n' "$@" | sort -u | while IFS= read -r src; do
    sha256sum "$root/$src" | sed "s| .*| $src|"
  done
}
