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
# shellcheck source=arxiv_assets/arxiv_lib.sh
source "$ROOT/arxiv_assets/arxiv_lib.sh"

rm -rf "$OUT"
mkdir -p "$OUT/simulations"

# Every repository file that goes into the submission, recorded as it is copied.
# The manifest written at the end is built from this, and so is the tar command:
# a file that is copied is packed, and one that is not copied is not silently
# expected to be there.
# The shared helpers are a source of the build without being part of the paper.
sources=(prepare_arxiv.sh arxiv_assets/arxiv_lib.sh)

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
#    Each edit is checked to have changed the file (edit_file, arxiv_lib.sh).
edit() { edit_file main.tex "$@"; }  # edit <description> <sed expression>

edit "apply the NeurIPS style"       "$NEURIPS_STYLE"
edit "add longtable for Table S1"    's/^\\usepackage\[preprint\]{neurips_2026}$/&\n\\usepackage{longtable}/'
edit "drop the article's own natbib" '/\\usepackage\[round\]{natbib}/d'
edit "drop double spacing"           '/\\doublespacing/d'
edit "drop the date"                 '/^\\date{/d'
edit "drop the lineno package"       '/\\usepackage{lineno}/d'
edit "drop \\linenumbers"            '/^\\linenumbers$/d'
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
    main.tex|supplementary.tex|prepare_arxiv.sh|arxiv_assets/arxiv_lib.sh) continue ;;
    arxiv_assets/*) packed+=("$(basename "$src")") ;;
    *) packed+=("$src") ;;
  esac
done < <(printf '%s\n' "${sources[@]}" | sort -u)

rm -f ./*.aux ./*.log ./*.out ./*.toc
tar -czf ax.tar.gz "${packed[@]}"

# 7. Compile what is about to be shipped, from the unpacked archive and nothing
#    else (verify_tarball, arxiv_lib.sh).
verify_tarball ax.tar.gz

# 8. Record what this was built from, for check_arxiv_freshness.py.
write_manifest "$ROOT" ./prepare_arxiv.sh "${sources[@]}" > BUILD_MANIFEST

echo "prepare_arxiv: $OUT/ax.tar.gz is ready"
tar -tzf ax.tar.gz
