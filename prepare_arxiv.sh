#!/bin/bash
# Build the arXiv submission from the manuscript sources, and the bioRxiv pair
# (the same NeurIPS-styled article and supplement as separate PDFs) beside it
# in arxiv_submit/biorxiv/.
#
# Four rules keep this from going stale or shipping something broken. The file
# set is *read from the .tex sources* on every run rather than listed here, so a
# figure added to or dropped from the article needs no edit to this script. Every
# edit this script makes to the sources is checked to have applied, because a sed
# that silently matches nothing produces a document that still compiles and is no
# longer the one intended. The tarball is packed from the files actually copied,
# not from a hardcoded list that can omit one. And the assembled document is
# compiled *from the unpacked tarball*, so a file missing from the archive fails
# the build here rather than on arXiv's.
#
# Layout: the `simulations/` subtree is reproduced rather than flattened, so
# main.tex's own \graphicspath and \input paths resolve unchanged and no path
# rewriting is needed. arXiv accepts subdirectories.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="$ROOT/arxiv_submit"
cd "$ROOT"

rm -rf "$OUT"
mkdir -p "$OUT/simulations"

# Every repository file that goes into the submission, recorded as it is copied.
# The manifest written at the end is built from this, and so is the tar command:
# a file that is copied is packed, and one that is not copied is not silently
# expected to be there.
sources=(prepare_arxiv.sh)

copy_in() {  # copy_in <repo-relative path> [destination directory]
  local src="$1" dest="${2:-$OUT}"
  mkdir -p "$dest"
  cp "$src" "$dest/"
  sources+=("$src")
}

# 1. Sources and the generated macro files the article \inputs. The macro
#    files are read out of the \input lines rather than listed here, on the
#    same principle as the figures below: a generated file added to either
#    document is packed with no edit to this script, and one that stops being
#    \input stops being packed. `references` is copied above, so it drops out
#    of the derived list by the existence test.
for f in main.tex supplementary.tex references.tex; do copy_in "$f"; done
while IFS= read -r inp; do
  [ -f "$inp.tex" ] || { echo "\\input{$inp} has no source file" >&2; exit 1; }
  case "$inp" in */*) copy_in "$inp.tex" "$OUT/${inp%/*}" ;; *) ;; esac
done < <(grep -ho '\\input{[^}]*}' main.tex supplementary.tex |
  sed 's/.*{\(.*\)}/\1/' | sort -u)
copy_in arxiv_assets/neurips_2026.sty

# 2. Figures, resolved the way \graphicspath{{simulations/}{./}} resolves them.
#    A reference with no source file on disk is an error, not a warning. So is
#    the same file printed twice: main.tex and supplementary.tex are one
#    document after the merge below, and a figure both of them include is
#    printed twice in the submitted PDF under two numbers. The two spellings
#    need not match -- the article reaches a figure through \graphicspath and
#    the supplement spells the path out -- so the check is on the resolved file.
missing=0
declare -a figures=()
while IFS= read -r fig; do
  src=""
  for prefix in "" "simulations/"; do
    if [ -f "$prefix$fig" ]; then src="$prefix$fig"; break; fi
  done
  if [ -z "$src" ]; then
    echo "prepare_arxiv: no file on disk for \\includegraphics{$fig}" >&2
    missing=1
    continue
  fi
  figures+=("$src")
done < <(grep -ho '\\includegraphics\(\[[^]]*\]\)\?{[^}]*}' main.tex supplementary.tex |
         sed 's/.*{//; s/}$//')
[ "$missing" -eq 0 ] || { echo "prepare_arxiv: figure references unresolved" >&2; exit 1; }

repeated="$(printf '%s\n' "${figures[@]}" | sort | uniq -d)"
if [ -n "$repeated" ]; then
  echo "prepare_arxiv: these figures are printed more than once in the merged document:" >&2
  printf '  %s\n' "$repeated" >&2
  echo "prepare_arxiv: point at the one printing with \\ref instead (AGENTS.md section 7)" >&2
  exit 1
fi

while IFS= read -r src; do
  copy_in "$src" "$OUT/$(dirname "$src")"
  echo "  figure: $src"
done < <(printf '%s\n' "${figures[@]}" | sort -u)

cd "$OUT"

# 3. Apply the NeurIPS style and drop what the arXiv build does not use.
#    neurips_2026.sty loads natbib itself, so main.tex's own natbib line goes.
#    longtable is added because it is in supplementary.tex's preamble, which is
#    discarded by the merge below while its Table S1 still needs the package.
# \pdfoutput=1 on the first line tells arXiv to run pdflatex rather than
# guessing from the file set.
#
# Each edit is checked to have changed the file. A sed whose pattern no longer
# matches is the failure this script cannot otherwise see: the document still
# compiles, and it is the wrong document -- unstyled, double-spaced, or carrying
# line numbers into a posted preprint.
edit_file() {  # edit_file <file> <description> <sed expression>
  local file="$1" what="$2" expression="$3" before
  before="$(sha256sum "$file" | cut -d' ' -f1)"
  sed -i "$expression" "$file"
  if [ "$before" = "$(sha256sum "$file" | cut -d' ' -f1)" ]; then
    echo "prepare_arxiv: '$what' changed nothing -- $file no longer matches this script" >&2
    exit 1
  fi
}
edit() { edit_file main.tex "$@"; }  # edit <description> <sed expression>

edit "apply the NeurIPS style" 's/\\documentclass\[12pt\]{article}/\\pdfoutput=1\n\\documentclass{article}\n\\usepackage[preprint]{neurips_2026}\n\\usepackage{longtable}/'
edit "drop the article's own natbib" '/\\usepackage\[round\]{natbib}/d'
edit "drop double spacing"           '/\\doublespacing/d'
edit "drop the date"                 '/^\\date{/d'
edit "drop the lineno package"       '/\\usepackage{lineno}/d'
edit "drop \\linenumbers"            '/^\\linenumbers$/d'

# A citation link broken across a page break makes pdfTeX abort with
# "\pdfendlink ended up in different nesting level" -- a fatal signal, not a
# warning, and one no source file can predict: which citation lands on a break
# depends on every word before it, and the merged document paginates unlike
# either half. Boxing each citation link removes the class of failure rather
# than the instance. The box goes around each reference's link, not around the
# whole group: a boxed group cannot break at its "; " either, and a two-reference
# group then leaves the line before it stretched to a few words.
# \emergencystretch is the last-resort slack that keeps a citation too wide for
# the space left from overfilling its line instead. Both belong here rather
# than in main.tex: the standalone article paginates differently.
CITE_BOXING='s/\\renewcommand{\\cite}\[1\]{\\citep{#1}}/\\renewcommand{\\cite}[1]{\\citep{#1}}\n\\makeatletter\n\\AtBeginDocument{\\let\\NATlink@start\\hyper@natlinkstart\\let\\NATlink@end\\hyper@natlinkend\\def\\hyper@natlinkstart#1{\\leavevmode\\hbox\\bgroup\\NATlink@start{#1}}\\def\\hyper@natlinkend{\\NATlink@end\\egroup}}\n\\makeatother\n\\emergencystretch=6em/'
edit "keep citation links off page breaks" "$CITE_BOXING"

# 4. The bioRxiv pair: the same NeurIPS-styled article on its own, and the
#    supplement styled to match as a separate file. bioRxiv takes the article
#    as one PDF and supplemental material as separate files, so these two PDFs
#    are built from the styled sources before the merge below absorbs the
#    supplement. The supplement's \externaldocument{main} reads the styled
#    article's .aux, so its pointers carry the article's own numbering. The
#    supplement's edits are checked like the article's: an unmatched pattern
#    would leave it unstyled or on the wrong page size.
split="$(mktemp -d)"
cp -r . "$split/"
(
  cd "$split"
  edit_file supplementary.tex "style the supplement" 's/^\\documentclass{article}$/\\documentclass{article}\n\\usepackage[preprint]{neurips_2026}/'
  edit_file supplementary.tex "drop the supplement's natbib" '/\\usepackage\[round\]{natbib}/d'
  edit_file supplementary.tex "drop the supplement's geometry package" '/^\\usepackage{geometry}$/d'
  edit_file supplementary.tex "drop the supplement's page geometry" '/^\\geometry{/d'
  edit_file supplementary.tex "keep the supplement's citation links off page breaks" "$CITE_BOXING"
  # A standalone supplement carries the article's byline. It is read out of
  # main.tex rather than written here, so the author block lives in one place.
  AUTHOR="$(awk '/^\\author\{/{f=1} f{print} f&&/\}\}$/{exit}' main.tex)"
  [ -n "$AUTHOR" ] || { echo "prepare_arxiv: no \\author block found in main.tex" >&2; exit 1; }
  before="$(sha256sum supplementary.tex)"
  AUTHOR="$AUTHOR" awk '$0=="\\author{}"{print ENVIRON["AUTHOR"]; next} {print}' supplementary.tex > supp.tmp
  mv supp.tmp supplementary.tex
  [ "$before" != "$(sha256sum supplementary.tex)" ] || {
    echo "prepare_arxiv: supplementary.tex no longer has an empty \\author{} to fill" >&2; exit 1; }
  for doc in main supplementary; do
    for pass in 1 2; do
      pdflatex -interaction=nonstopmode -file-line-error "$doc.tex" > "$doc-pass$pass.out" 2>&1 || true
    done
  done
)
split_fail=0
for doc in main supplementary; do
  log="$split/$doc.log"
  if grep -qE '^(\./)?[^ ]*:[0-9]+: |^! |LaTeX Warning: (Reference|Citation) .* undefined|File .* not found' "$log"; then
    echo "prepare_arxiv: the standalone $doc.tex has errors or unresolved references" >&2
    grep -E '^(\./)?[^ ]*:[0-9]+: |^! |LaTeX Warning: (Reference|Citation) .* undefined|File .* not found' "$log" | head -5 >&2
    split_fail=1
  fi
  [ -f "$split/$doc.pdf" ] || { echo "prepare_arxiv: no standalone $doc.pdf produced" >&2; split_fail=1; }
done
[ "$split_fail" -eq 0 ] || { rm -rf "$split"; echo "prepare_arxiv: NOT shipping a broken bioRxiv pair" >&2; exit 1; }
mkdir -p biorxiv
cp "$split/main.pdf" biorxiv/main.pdf
cp "$split/supplementary.pdf" biorxiv/supplementary.pdf
rm -rf "$split"
echo "prepare_arxiv: bioRxiv pair built, $(pdfinfo biorxiv/main.pdf | awk '/^Pages:/{print $2}') + $(pdfinfo biorxiv/supplementary.pdf | awk '/^Pages:/{print $2}') pages"

# 5. Merge the supplement in as an appendix. Its preamble is dropped, and so is
#    its own \input{references}: the merged document has one bibliography.
#    Copying from the \section*{Overview} marker is what carries the S-prefix
#    renumbering that sits just after it, so both the marker and the renumbering
#    are checked to have survived: without them the supplement's floats continue
#    the article's numbering and every "Table S1" in the text points at nothing.
sed -n '/\\section\*{Overview}/,$p' supplementary.tex |
  sed '/\\end{document}/d; /\\input{references}/d' > supp_body.tex

sections_expected="$(grep -c '^\\section' supplementary.tex)"
sections_merged="$(grep -c '^\\section' supp_body.tex || true)"
if [ "$sections_merged" != "$sections_expected" ]; then
  echo "prepare_arxiv: the appendix merge captured $sections_merged of $sections_expected sections" >&2
  echo "prepare_arxiv: supplementary.tex's \\section*{Overview} marker moved or was renamed" >&2
  exit 1
fi
grep -q 'renewcommand{\\thefigure}{S' supp_body.tex || {
  echo "prepare_arxiv: the merged appendix does not renumber its figures with an S prefix" >&2
  exit 1
}

end_line=$(grep -n '^\\end{document}' main.tex | head -1 | cut -d: -f1)
{
  head -n "$((end_line - 1))" main.tex
  printf '\\clearpage\n\\appendix\n'
  cat supp_body.tex
  printf '\\end{document}\n'
  # arXiv reruns LaTeX until this stops appearing in the log.
  printf '\\typeout{get arXiv to do 4 passes: Label(s) may have changed. Rerun}\n'
} > merged.tex

grep -v '^%' merged.tex > final_main.tex
mv final_main.tex main.tex
rm -f supp_body.tex merged.tex supplementary.tex

# 6. Pack the sources: main.tex as merged above, and everything copied in that
#    the merged document still reads. supplementary.tex is gone, absorbed.
declare -a packed=(main.tex)
while IFS= read -r src; do
  case "$src" in
    main.tex|supplementary.tex|prepare_arxiv.sh) continue ;;
    arxiv_assets/*) packed+=("$(basename "$src")") ;;
    *) packed+=("$src") ;;
  esac
done < <(printf '%s\n' "${sources[@]}" | sort -u)

rm -f ./*.aux ./*.log ./*.out ./*.toc
tar -czf ax.tar.gz "${packed[@]}"

# 7. Compile what is about to be shipped, from the unpacked archive and nothing
#    else. Compiling in place would pass on a file that exists in this directory
#    and is missing from the tarball, which is the one failure a local build
#    cannot distinguish from success.
echo "prepare_arxiv: verifying the packed submission compiles"
verify="$(mktemp -d)"
trap 'rm -rf "$verify"' EXIT
tar -xzf ax.tar.gz -C "$verify"
(
  cd "$verify"
  for pass in 1 2 3; do
    pdflatex -interaction=nonstopmode -file-line-error main.tex > "pass$pass.out" 2>&1 || true
  done
)

fail=0
check() {  # check <description> <grep-pattern>
  if grep -qE "$2" "$verify/main.log"; then
    echo "prepare_arxiv: $1" >&2
    grep -E "$2" "$verify/main.log" | head -5 >&2
    fail=1
  fi
}
check "LaTeX errors in the assembled document" '^(\./)?[^ ]*:[0-9]+: |^! '
check "undefined references"                   'LaTeX Warning: Reference .* undefined'
check "undefined citations"                    'LaTeX Warning: Citation .* undefined'
check "missing graphics"                       'File .* not found'
[ -f "$verify/main.pdf" ] || { echo "prepare_arxiv: no main.pdf produced" >&2; fail=1; }
[ "$fail" -eq 0 ] || { echo "prepare_arxiv: NOT shipping a broken submission" >&2; exit 1; }

cp "$verify/main.pdf" main.pdf
pages=$(pdfinfo main.pdf | awk '/^Pages:/{print $2}')
echo "prepare_arxiv: compiled cleanly from the tarball, $pages pages"

# 8. Record what this was built from. arxiv_submit/ is not tracked, so nothing
#    else can tell whether the directory sitting here is the current manuscript
#    or last week's; check_arxiv_freshness.py answers that from this file.
{
  printf '# arXiv submission built %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '# from commit %s%s\n' \
    "$(git -C "$ROOT" rev-parse --short HEAD)" \
    "$(git -C "$ROOT" diff --quiet HEAD 2>/dev/null || echo ' (working tree modified)')"
  printf '# regenerate with ./prepare_arxiv.sh\n'
  printf '%s\n' "${sources[@]}" | sort -u | while IFS= read -r src; do
    sha256sum "$ROOT/$src" | sed "s| .*| $src|"
  done
} > BUILD_MANIFEST

echo "prepare_arxiv: $OUT/ax.tar.gz is ready"
tar -tzf ax.tar.gz
