#!/usr/bin/env python3
"""Gate: no figure is printed twice in the publication.

``main.tex`` and ``supplementary.tex`` are two documents on this machine and one
document on arXiv. ``prepare_arxiv.sh`` merges the supplement in as an appendix,
so a figure included by both files is printed twice in the submitted PDF, under
two numbers, with two captions -- and the second printing is not a cross
reference a reader can follow back to the first. It reads as a mistake because it
is one.

The failure is invisible from either source file. Each includes the figure once;
each compiles cleanly; the two spellings of the path need not even match, since
``main.tex`` reaches the file through ``\\graphicspath`` and the supplement spells
it out in full. Nothing notices until someone reads the merged PDF end to end,
which is what happened here: the plasticity figure was Figure 3 and Figure S3 of
the same document.

The rule is therefore about resolved files rather than about the strings in the
sources, and it counts *printings* rather than dependencies: a figure included
twice within one file breaks it in the same way.

What to write instead. The supplement points into the main article by label --
``\\usepackage{xr}`` and ``\\externaldocument{main}`` in its preamble make
``\\ref{fig:resonance}`` resolve there -- and the caption detail that belongs to
the supplement goes into the supplement's prose. The merged document resolves
the same label natively, so one sentence serves both builds.

Run: python simulations/check_figures.py

Exit 0 if every figure is printed once, 1 otherwise.
"""

from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

from check_pdf_freshness import PUBLICATION, REPO, figure_uses

GUIDANCE = """
A figure printed twice is printed twice on arXiv (AGENTS.md section 7).

prepare_arxiv.sh merges supplementary.tex into main.tex as an appendix, so the
figures above appear twice in the one submitted PDF under two numbers. Keep the
printing in the document that argues from it, and point at it from the other:

    % supplementary.tex preamble, already present
    \\usepackage{xr}
    \\externaldocument{main}

    ... Figure~\\ref{fig:resonance} in the main article ...

The number is then read from main.aux rather than written by hand, and the
merged document resolves the same label natively. Caption text the pointing
document needs goes into its prose, not into a second copy of the figure.
"""


def printings(root: Path) -> Counter[str]:
    """How many times each figure is printed across the publication, by repository path."""
    counted: Counter[str] = Counter()
    for document in PUBLICATION:
        for figure in figure_uses(root / document):
            counted[figure.relative_to(root.resolve()).as_posix()] += 1
    return counted


def repeated(counted: Counter[str]) -> list[tuple[str, int]]:
    """The figures printed more than once, worst first."""
    return sorted(
        ((f, n) for f, n in counted.items() if n > 1), key=lambda item: (-item[1], item[0])
    )


def main(argv: list[str]) -> int:
    """Fail on a figure the publication prints more than once."""
    root = Path(argv[1]) if len(argv) > 1 else REPO
    counted = printings(root)
    duplicates = repeated(counted)
    for figure, times in duplicates:
        print(f"{figure}: printed {times} times across {', '.join(PUBLICATION)}")
    if duplicates:
        print(GUIDANCE)
        return 1
    print(f"check_figures: {len(counted)} figure(s), each printed once.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
