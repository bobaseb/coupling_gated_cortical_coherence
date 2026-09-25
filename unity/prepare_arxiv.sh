#!/bin/bash
# Build the arXiv submission of the physical-unity paper, and its bioRxiv PDF,
# in unity/arxiv_submit/.
#
# The same rules as ./prepare_arxiv.sh, through the helpers both share
# (arxiv_assets/arxiv_lib.sh). The file set is *read from main.tex* on every
# run, so an \input or a figure added to the paper needs no edit here. Every
# edit this script makes is checked to have applied. The tarball is packed from
# the files actually copied. And the submission is compiled *from the unpacked
# tarball*, so a file missing from the archive fails here rather than on arXiv.
#
# The paper is one file with its appendix, so there is no merge: the arXiv
# document and the bioRxiv article are the same styled PDF.

set -euo pipefail

UNITY="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$UNITY/.." && pwd)"
OUT="$UNITY/arxiv_submit"
cd "$UNITY"
# shellcheck source=../arxiv_assets/arxiv_lib.sh
source "$ROOT/arxiv_assets/arxiv_lib.sh"

rm -rf "$OUT"
mkdir -p "$OUT"

# Every repository file that goes into the submission, repository-relative as
# check_arxiv_freshness.py names them, recorded as it is copied.
sources=(unity/prepare_arxiv.sh arxiv_assets/arxiv_lib.sh)
declare -a packed=()

copy_in() {  # copy_in <path relative to unity/>
  local src="$1"
  cp "$src" "$OUT/"
  sources+=("$(realpath --relative-to="$ROOT" "$src")")
  packed+=("$(basename "$src")")
}

# 1. The paper, every file it \inputs, and the style.
copy_in main.tex
while IFS= read -r inp; do
  [ -f "$inp.tex" ] || { echo "\\input{$inp} has no source file" >&2; exit 1; }
  copy_in "$inp.tex"
done < <(grep -v '^%' main.tex | grep -o '\\input{[^}]*}' | sed 's/.*{\(.*\)}/\1/' | sort -u)
copy_in ../arxiv_assets/neurips_2026.sty

# 2. Figures, resolved against the paper's own directory. None today; one added
#    later is packed with no edit here, and one with no file on disk is an error.
while IFS= read -r fig; do
  [ -f "$fig" ] || { echo "prepare_arxiv: no file on disk for \\includegraphics{$fig}" >&2; exit 1; }
  case "$fig" in */*) echo "prepare_arxiv: figures in subdirectories are not supported: $fig" >&2; exit 1 ;; *) ;; esac
  copy_in "$fig"
  echo "  figure: $fig"
done < <(grep -v '^%' main.tex | grep -o '\\includegraphics\(\[[^]]*\]\)\?{[^}]*}' |
         sed 's/.*{//; s/}$//' | sort -u)

cd "$OUT"

# 3. Apply the NeurIPS style and drop what it replaces: its own natbib, the
#    one-and-a-half spacing and the empty date. Each edit is checked to apply.
edit() { edit_file main.tex "$@"; }  # edit <description> <sed expression>

edit "apply the NeurIPS style"       "$NEURIPS_STYLE"
edit "drop the paper's own natbib"   '/\\usepackage\[round\]{natbib}/d'
edit "drop the setspace package"     '/^\\usepackage{setspace}$/d'
edit "drop one-and-a-half spacing"   '/^\\onehalfspacing$/d'
edit "drop the date"                 '/^\\date{/d'
edit "keep citation links off page breaks" "$CITE_BOXING"

# arXiv reruns LaTeX until this stops appearing in the log.
printf '\\typeout{get arXiv to do 4 passes: Label(s) may have changed. Rerun}\n' >> main.tex
grep -v '^%' main.tex > main.stripped && mv main.stripped main.tex

# 4. Pack the files copied above, and compile the archive, not this directory.
tar -czf ax.tar.gz "${packed[@]}"
verify_tarball ax.tar.gz

# 5. bioRxiv takes the article as one PDF; the appendix travels with it.
mkdir -p biorxiv
cp main.pdf biorxiv/main.pdf

# 6. Record what this was built from, for check_arxiv_freshness.py.
write_manifest "$ROOT" unity/prepare_arxiv.sh "${sources[@]}" > BUILD_MANIFEST

echo "prepare_arxiv: $OUT/ax.tar.gz is ready"
tar -tzf ax.tar.gz
