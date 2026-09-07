#!/bin/bash
# Build the arXiv submission from the manuscript sources.
#
# Two rules keep this from going stale. The file set is *read from the .tex
# sources* on every run rather than listed here, so a figure added to or dropped
# from the article needs no edit to this script. And the assembled document is
# compiled before it is packed, with any LaTeX error, missing graphic, or
# undefined reference or citation failing the build -- a tarball that does not
# compile is never written.
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

# 1. Sources and the generated macro files the article \inputs.
cp main.tex supplementary.tex references.tex "$OUT/"
cp simulations/fermi_params.tex simulations/simulation_results.tex "$OUT/simulations/"
cp arxiv_assets/neurips_2026.sty "$OUT/"

# 2. Figures, resolved the way \graphicspath{{simulations/}{./}} resolves them.
#    A reference with no source file on disk is an error, not a warning.
missing=0
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
  mkdir -p "$OUT/$(dirname "$src")"
  cp "$src" "$OUT/$src"
  echo "  figure: $src"
done < <(grep -ho '\\includegraphics\(\[[^]]*\]\)\?{[^}]*}' main.tex supplementary.tex |
         sed 's/.*{//; s/}$//' | sort -u)
[ "$missing" -eq 0 ] || { echo "prepare_arxiv: figure references unresolved" >&2; exit 1; }

cd "$OUT"

# 3. Apply the NeurIPS style and drop what the arXiv build does not use.
#    neurips_2026.sty loads natbib itself, so main.tex's own natbib line goes.
#    longtable is added because it is in supplementary.tex's preamble, which is
#    discarded by the merge below while its Table S1 still needs the package.
# \pdfoutput=1 on the first line tells arXiv to run pdflatex rather than
# guessing from the file set.
sed -i 's/\\documentclass\[12pt\]{article}/\\pdfoutput=1\n\\documentclass{article}\n\\usepackage[preprint]{neurips_2026}\n\\usepackage{longtable}/' main.tex
sed -i '/\\usepackage\[round\]{natbib}/d' main.tex
sed -i '/\\doublespacing/d' main.tex
sed -i '/^\\date{/d' main.tex
sed -i '/\\usepackage{lineno}/d' main.tex
sed -i '/^\\linenumbers$/d' main.tex

# 4. Merge the supplement in as an appendix. Its preamble is dropped, and so is
#    its own \input{references}: the merged document has one bibliography.
sed -n '/\\section\*{Overview}/,$p' supplementary.tex |
  sed '/\\end{document}/d; /\\input{references}/d' > supp_body.tex

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

# 5. Compile what is about to be shipped, and refuse to ship it if it is broken.
echo "prepare_arxiv: verifying the assembled document compiles"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -file-line-error main.tex > "pass$pass.out" 2>&1 || true
done

fail=0
check() {  # check <description> <grep-pattern>
  if grep -qE "$2" main.log; then
    echo "prepare_arxiv: $1" >&2
    grep -E "$2" main.log | head -5 >&2
    fail=1
  fi
}
check "LaTeX errors in the assembled document" '^(\./)?[^ ]*:[0-9]+: |^! '
check "undefined references"                   'LaTeX Warning: Reference .* undefined'
check "undefined citations"                    'LaTeX Warning: Citation .* undefined'
[ -f main.pdf ] || { echo "prepare_arxiv: no main.pdf produced" >&2; fail=1; }
[ "$fail" -eq 0 ] || { echo "prepare_arxiv: NOT packing a broken submission" >&2; exit 1; }

pages=$(pdfinfo main.pdf | awk '/^Pages:/{print $2}')
echo "prepare_arxiv: compiled cleanly, $pages pages"

# 6. Pack the sources. Build artifacts stay out of the tarball.
rm -f ./*.aux ./*.log ./*.out ./*.toc
tar -czf ax.tar.gz main.tex references.tex neurips_2026.sty simulations
echo "prepare_arxiv: $OUT/ax.tar.gz is ready"
tar -tzf ax.tar.gz
