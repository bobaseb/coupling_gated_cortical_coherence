#!/usr/bin/env python3
"""Gate: the main text of either paper names no Lean declaration.

A reader of the article never opens the Lean development. An identifier such as
``conductance_le_shell`` in a sentence is a pointer that reader cannot follow,
and a paragraph carrying several of them reads as a code listing. Each result is
stated in words where it is argued, and the map from result to declaration
lives where a reader who wants it will look: Table S1 of the companion's
supplement, and the formal-results appendix of the physical-unity paper.

## What the main text is

Everything before ``\\appendix``, or before ``\\end{document}`` in a paper with
no appendix. The companion's supplement is a separate file and is not read;
the unity paper's appendix is its claim map and is exempt for the same reason.
TeX comments are removed first, with line numbers kept.

## What counts as a Lean name

The Lean sources decide, not a list kept here -- the principle of
``check_pdf_freshness.py`` deriving its dependency set from the sources:

* a ``\\texttt{}`` span whose final dot-separated segment is declared under
  ``PhysicsOfConsciousness/``, is a module name there, or ends in ``.lean``;
* an identifier written with escaped underscores outside any span
  (``conductance\\_le\\_shell``) whose final segment is declared.

A declaration name used as a prose word (``energy``) is prose, which is why bare
words are only checked when they carry an escaped underscore.

There is no allowlist, for the reason AGENTS.md section 5 gives.

Run: python simulations/check_lean_names.py [repo root]

Exit 0 if no main text names a Lean identifier, 1 otherwise.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from check_leaves import declarations, strip_comments
from repo_root import REPO

LEAN_DIR = REPO / "PhysicsOfConsciousness"
DOCUMENTS: tuple[Path, ...] = (REPO / "main.tex", REPO / "unity" / "main.tex")

TEXTTT_RE = re.compile(r"\\texttt\{([^}]*)\}", re.DOTALL)
BARE_RE = re.compile(r"[A-Za-z][A-Za-z0-9.']*(?:\\_[A-Za-z0-9.']+)+")
TEX_COMMENT_RE = re.compile(r"(?<!\\)%.*$")
END_RE = re.compile(r"^\s*\\(?:appendix\b|end\{document\})")

GUIDANCE = """
The main text of a paper names no Lean identifier (AGENTS.md section 9).

State the result in words where it is argued. The identifier belongs in the
claim map: a row of Table S1 in supplementary.tex for the companion, a row of
the formal-results appendix for unity/main.tex.
"""


def normalise(span: str) -> str:
    """The identifier a span spells, with LaTeX break and escape markup removed."""
    text = span.replace(r"\allowbreak", "").replace(r"\-", "").replace(r"\_", "_")
    return re.sub(r"\s+", "", text)


def lean_names(lean_dir: Path) -> tuple[set[str], set[str]]:
    """Final segments of every declaration, and every module name, under *lean_dir*."""
    declared: set[str] = set()
    modules: set[str] = set()
    for path in sorted(lean_dir.rglob("*.lean")):
        modules.add(path.stem)
        declared |= declarations(strip_comments(path.read_text(encoding="utf-8")))
    return {name.split(".")[-1] for name in declared}, modules


def main_text(tex: str) -> str:
    """The text before the appendix, comments removed and line numbers kept."""
    kept: list[str] = []
    for line in tex.splitlines():
        if END_RE.match(line):
            break
        kept.append(TEX_COMMENT_RE.sub("", line))
    return "\n".join(kept) + "\n"


def _blank(text: str, start: int, end: int) -> str:
    """*text* with ``[start, end)`` replaced by its newlines only."""
    return text[:start] + "\n" * text.count("\n", start, end) + text[end:]


def findings(text: str, declared: set[str], modules: set[str]) -> list[tuple[int, str]]:
    """Line number and identifier of each Lean name in *text*, in reading order."""
    found: list[tuple[int, int, str]] = []
    bare_text = text
    for match in reversed(list(TEXTTT_RE.finditer(text))):
        name = normalise(match.group(1))
        if name.endswith(".lean") or name in modules or name.split(".")[-1] in declared:
            found.append((match.start(), text.count("\n", 0, match.start()) + 1, name))
        bare_text = _blank(bare_text, match.start(), match.end())
    for match in BARE_RE.finditer(bare_text):
        name = normalise(match.group(0))
        if name in modules or name.split(".")[-1] in declared:
            found.append((match.start(), bare_text.count("\n", 0, match.start()) + 1, name))
    return [(line, name) for _, line, name in sorted(found)]


def main(argv: list[str]) -> int:
    """Check each paper's main text against the Lean sources."""
    root = Path(argv[1]) if len(argv) > 1 else REPO
    declared, modules = lean_names(root / LEAN_DIR.relative_to(REPO))
    failures = 0
    for document in DOCUMENTS:
        path = root / document.relative_to(REPO)
        for line, name in findings(main_text(path.read_text(encoding="utf-8")), declared, modules):
            print(f"{path}:{line}: {name} -- a Lean name in the main text")
            failures += 1
    if failures:
        print(f"\ncheck_lean_names: {failures} Lean name(s) in the main text.")
        print(GUIDANCE)
        return 1
    print(f"check_lean_names: the main text of {len(DOCUMENTS)} paper(s) names no Lean identifier.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
