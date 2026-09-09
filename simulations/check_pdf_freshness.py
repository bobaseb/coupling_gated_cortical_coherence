#!/usr/bin/env python3
"""Gate: a tracked PDF is a deliverable, and a deliverable is never behind its source.

Three PDFs are tracked in this repository -- ``main.pdf``, ``supplementary.pdf``
and ``docs/primer.pdf`` -- because ``README.md`` and ``index.html`` link them
directly. A reader who follows one of those links never sees the ``.tex`` file
beside it, so for that reader the PDF *is* the document.

The failure mode is silent and one-sided. A commit edits ``docs/primer.tex``,
LaTeX is not run, and the tracked ``docs/primer.pdf`` still carries the previous
text. Nothing complains: the sources are consistent with each other, the Lean
build is unaffected, and every other gate here reads ``.tex`` and ``.lean``
files rather than the artifacts built from them. The staleness is visible only
to the person who downloads the PDF, which is the one person who cannot report
it.

Two levels, because two different things go stale.

**Hard gate.** A commit that changes a document's own sources -- its ``.tex``
file, anything it ``\\input``s transitively, and every figure it includes --
must also carry the rebuilt PDF. This has a yes/no answer, so it fails the
commit. The dependency set is *read from the sources on every run* rather than
listed here, on the same principle as ``prepare_arxiv.sh``: a figure added to
the article needs no edit to this script.

**Advisory.** The primer is a companion document; it explains the mathematics
the manuscript uses. It therefore goes stale in a second way, when the
manuscript's content moves and the primer's explanation of it does not. That has
no yes/no answer -- most edits to ``main.tex`` need no primer change at all --
so a changed publication with an untouched primer is reported and nothing more,
in the manner of ``check_hedging.py``.

Run: python simulations/check_pdf_freshness.py

Exit 0 if every tracked PDF is as new as the sources this commit changes, 1
otherwise.
"""

from __future__ import annotations

import re
import subprocess  # nosec B404 -- fixed argv below, no shell
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Tracked deliverable, and the root source it is built from.
DOCUMENTS: tuple[tuple[str, str], ...] = (
    ("main.pdf", "main.tex"),
    ("supplementary.pdf", "supplementary.tex"),
    ("docs/primer.pdf", "docs/primer.tex"),
)

# The advisory pair: the publication, and the companion that explains it.
PUBLICATION: tuple[str, ...] = ("main.tex", "supplementary.tex")
COMPANION: str = "docs/primer.tex"

# Extensions tried when a \input or \includegraphics argument omits one.
SUFFIXES: tuple[str, ...] = ("", ".tex", ".png", ".pdf")

_COMMENT = re.compile(r"(?<!\\)%.*$", re.MULTILINE)
_INPUT = re.compile(r"\\(?:input|include)\{([^}]*)\}")
# xr's cross-document link: the supplement reads the main article's numbering out
# of its .aux, so a change that renumbers the article leaves the supplement's
# pointers into it stale. The .aux is a build artifact and not a source; the
# source it is built from is the .tex of the same name, which is what this
# resolves to.
_EXTERNAL = re.compile(r"\\externaldocument(?:\[[^\]]*\])?\{([^}]*)\}")
_GRAPHICS = re.compile(r"\\includegraphics(?:\[[^\]]*\])?\{([^}]*)\}")
_GRAPHICSPATH = re.compile(r"\\graphicspath\{((?:\{[^{}]*\})+)\}")
_BRACED = re.compile(r"\{([^{}]*)\}")

GUIDANCE = """
A tracked PDF is a deliverable (AGENTS.md section 6).

README.md and index.html link these PDFs directly, so a reader who follows one
of those links reads whatever was last committed there. Rebuild the document
above and stage the PDF with the source change:

    pdflatex -interaction=nonstopmode main.tex          # twice, from the repo root
    pdflatex -interaction=nonstopmode supplementary.tex # twice, from the repo root
    cd docs && pdflatex -interaction=nonstopmode primer.tex  # twice, from docs/

Two passes: the second resolves the table of contents and cross-references the
first one wrote. Splitting the rebuild into a later commit is what this gate
exists to prevent -- the interval between the two is exactly when the linked
artifact is wrong.
"""

COMPANION_NOTE = """
docs/primer.tex is untouched by a commit that changes the publication.

The primer is a companion: it explains the mathematics main.tex and
supplementary.tex use, and it goes stale when their content moves rather than
when their wording does. Most edits need no primer change, which is why this is
a note and not a failure. Check whether this one does.
"""


def _read(path: Path) -> str:
    """File text with LaTeX comments stripped, so a commented-out input is not a dependency."""
    return _COMMENT.sub("", path.read_text(encoding="utf-8"))


def _resolve(name: str, directories: list[Path]) -> Path | None:
    """The first file matching *name* under *directories*, trying the LaTeX extensions.

    Resolved, because ``docs/primer.tex`` reaches its generated macros as
    ``../simulations/simulation_results`` and two spellings of one file would be
    two dependencies.
    """
    for directory in directories:
        for suffix in SUFFIXES:
            candidate = directory / (name + suffix)
            if candidate.is_file():
                return candidate.resolve()
    return None


def _graphics_dirs(text: str, base: Path) -> list[Path]:
    """Where \\includegraphics looks: the document's \\graphicspath, then its own directory."""
    match = _GRAPHICSPATH.search(text)
    entries = _BRACED.findall(match.group(1)) if match else []
    return [base / entry for entry in entries] + [base]


def dependencies(tex: Path) -> set[Path]:
    """Every file *tex* pulls in: inputs, transitively, and the figures they include.

    A name that resolves to nothing on disk is skipped rather than reported.
    Missing figures and missing inputs are a build error, caught by the LaTeX run
    and by ``prepare_arxiv.sh``; this script's question is narrower.
    """
    found: set[Path] = set()
    pending = [tex]
    while pending:
        current = pending.pop()
        text = _read(current)
        for name in _INPUT.findall(text) + _EXTERNAL.findall(text):
            child = _resolve(name, [current.parent])
            if child is not None and child not in found:
                found.add(child)
                pending.append(child)
        for name in _GRAPHICS.findall(text):
            figure = _resolve(name, _graphics_dirs(text, current.parent))
            if figure is not None:
                found.add(figure)
    return found


def figure_uses(tex: Path) -> list[Path]:
    """Every figure *tex* prints, resolved, one entry per \\includegraphics.

    Repeats are kept and the transitive ``\\input``s are followed, because the
    question this answers is how many times a figure is *printed*, not which
    figures a document depends on. ``\\externaldocument`` is not followed: the
    other document's figures are printed by that document, not by this one.
    """
    uses: list[Path] = []
    seen: set[Path] = set()
    pending = [tex]
    while pending:
        current = pending.pop()
        text = _read(current)
        for name in _INPUT.findall(text):
            child = _resolve(name, [current.parent])
            if child is not None and child not in seen:
                seen.add(child)
                pending.append(child)
        for name in _GRAPHICS.findall(text):
            figure = _resolve(name, _graphics_dirs(text, current.parent))
            if figure is not None:
                uses.append(figure)
    return uses


def document_sources(root: Path) -> dict[str, set[str]]:
    """Repository-relative sources of each tracked PDF, keyed by the PDF's path."""
    sources: dict[str, set[str]] = {}
    for pdf, tex in DOCUMENTS:
        paths = dependencies(root / tex) | {(root / tex).resolve()}
        sources[pdf] = {path.relative_to(root.resolve()).as_posix() for path in paths}
    return sources


def behind_sources(pdf: str, sources: set[str], changed: set[str]) -> list[str]:
    """Sources of *pdf* that this commit changes without rebuilding it."""
    return [] if pdf in changed else sorted(sources & changed)


def companion_is_untouched(changed: set[str]) -> bool:
    """Whether the commit moves the publication and leaves the primer alone."""
    return bool(changed & set(PUBLICATION)) and COMPANION not in changed


def changed_paths(root: Path) -> set[str]:
    """Repository-relative paths staged in the commit being made."""
    result = subprocess.run(  # noqa: S603  # nosec B603 B607 -- fixed argv, no shell
        ["git", "diff", "--cached", "--name-only", "--diff-filter=ACMR"],  # noqa: S607
        cwd=root,
        capture_output=True,
        text=True,
        check=True,
    )
    return {line for line in result.stdout.splitlines() if line}


def report(stale: dict[str, list[str]]) -> None:
    """One line per stale PDF, naming the source changes it is behind."""
    for pdf, behind in sorted(stale.items()):
        print(f"{pdf}: not rebuilt -- {', '.join(behind)} changed in this commit")


def main(argv: list[str]) -> int:
    """Fail on a PDF left behind its sources; note an untouched primer and pass."""
    root = Path(argv[1]) if len(argv) > 1 else REPO
    changed = changed_paths(root)
    sources = document_sources(root)
    stale = {
        pdf: behind
        for pdf, paths in sources.items()
        if (behind := behind_sources(pdf, paths, changed))
    }
    report(stale)
    if stale:
        print(GUIDANCE)
    if companion_is_untouched(changed):
        print(COMPANION_NOTE)
    if not stale:
        print(f"check_pdf_freshness: {len(sources)} tracked PDF(s) are current.")
    return 1 if stale else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
