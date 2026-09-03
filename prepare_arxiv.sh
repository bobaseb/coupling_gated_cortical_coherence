#!/bin/bash
rm -rf arxiv_submit
mkdir arxiv_submit
cp main.tex arxiv_submit/
cp supplementary.tex arxiv_submit/
cp simulations/fermi_params.tex arxiv_submit/
cp arxiv_assets/neurips_2026.sty arxiv_submit/
# Figures, flattened: main.tex sets \graphicspath so bare filenames resolve either way.
cp simulations/bifurcation_diagram.png \
   simulations/kuramoto_transition.png \
   simulations/mesh_refinement_convergence.png \
   simulations/structural_resonance.png \
   simulations/hardware_comparison.png arxiv_submit/

cd arxiv_submit

# 0. Apply NeurIPS 2026 style and remove line numbers
sed -i 's/\\documentclass\[12pt\]{article}/\\documentclass{article}\n\\usepackage[preprint]{neurips_2026}/' main.tex
sed -i '/\\usepackage\[round\]{natbib}/d' main.tex
sed -i '/\\doublespacing/d' main.tex
sed -i '/^\\date{/d' main.tex
sed -i '/\\usepackage{lineno}/d' main.tex
sed -i '/\\linenumbers/d' main.tex

# Fix input path for fermi_params after flattening
sed -i 's/\\input{simulations\/fermi_params}/\\input{fermi_params}/' main.tex

# 1. Merge supplementary into main.tex before \end{document}
# Extract content from supplementary.tex starting from \section*{Overview} to the end, excluding \end{document}
sed -n '/\\section\*{Overview}/,/\\end{document}/p' supplementary.tex | grep -v "\\end{document}" > supp_body.tex

# Create a merged main.tex
# Find the line number of \end{document} in main.tex
END_LINE=$(grep -n "\\end{document}" main.tex | cut -d: -f1)

# Split main.tex
head -n $((END_LINE - 1)) main.tex > merged.tex
echo "\\clearpage" >> merged.tex
echo "\\appendix" >> merged.tex
cat supp_body.tex >> merged.tex
echo "\\end{document}" >> merged.tex

# 2. Add \typeout instruction AFTER \end{document}
echo "\\typeout{get arXiv to do 4 passes: Label(s) may have changed. Rerun}" >> merged.tex

# 3. Remove whole-line comments only (safer than inline comment removal)
grep -v '^%' merged.tex > final_main.tex

# 4. Clean up
mv final_main.tex main.tex
rm supp_body.tex merged.tex supplementary.tex

# 5. Create tarball
tar -cvvf ax.tar main.tex neurips_2026.sty fermi_params.tex *.png

echo "Done! arxiv_submit/ax.tar is ready."