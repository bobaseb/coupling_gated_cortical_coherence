#!/usr/bin/env python3
"""Gate: every Lean declaration the article names has a row in Table S1.

Table S1 says of itself that it is the claim-by-claim map -- each row names the
Lean identifier that carries a claim and states that identifier's scope
limitation. ``check_tableS1.py`` validates the *status* column against
``Chain.lean`` and measures no coverage, so a theorem could be argued from in
the article and appear in no row at all. That is not hypothetical: the winding
and amplitude results were cited in both documents and mapped in neither, and
every gate in the repository passed while they were.

## Why the rule stops at the article

The obvious rule -- every Lean name in either publication file needs a row --
demands the table absorb the supplement, which names several hundred working
lemmas in the course of its proofs. Those are not claims, and a table listing
them would stop being a map.

The article is where the claims are. It names a Lean identifier only when it
rests an argument on it, which is exactly the set the table exists to cover, so
that is the set this gate checks. A name the supplement alone uses is a step in
a proof and is not covered here.

Coverage runs one way. A row may carry an identifier the article never spells,
because a claim can be stated in prose and carried by a theorem the reader meets
only in the map.

## What counts as a declaration

The Lean sources decide, not a list kept here: a ``\\texttt{}`` span is checked
only if its final dot-separated segment is declared somewhere under
``PhysicsOfConsciousness/``. Module names (``Phase4_KuramotoDynamics``), file
names (``Chain.lean``) and directory names (``Examples``) declare nothing and
are therefore ignored without being enumerated -- the same principle as
``check_pdf_freshness.py`` deriving its dependency set from the sources.

Matching is on the final segment, because the publication spells a name in full
where the namespace matters and by its tail where it does not, and both spellings
reach the same constant.

Run: python simulations/check_table_coverage.py

Exit 0 if every declaration the article names has a row, 1 otherwise.
"""

from __future__ import annotations

import re
from pathlib import Path

from check_leaves import declarations, strip_comments
from repo_root import REPO

LEAN_DIR = REPO / "PhysicsOfConsciousness"
ARTICLE = REPO / "main.tex"
SUPPLEMENT = REPO / "supplementary.tex"

# The claim map is the longtable carrying this label.
TABLE_LABEL = r"\label{tab:full}"
LONGTABLE_RE = re.compile(r"\\begin\{longtable\}.*?\\end\{longtable\}", re.DOTALL)
TEXTTT_RE = re.compile(r"\\texttt\{([^}]*)\}", re.DOTALL)

GUIDANCE = """
Table S1 is the claim-by-claim map (AGENTS.md section 8 and the table's own
preamble): each row names the Lean identifier carrying a claim and states that
identifier's scope limitation.

An identifier the article argues from and the table omits is a claim with no
recorded scope. Give it a row, in the same commit, ending on what the identifier
does not reach -- or, if the article does not rest on it, take the name out of
the article and leave it to the supplement.

check_tableS1.py validates the status column and measures no coverage, which is
why this is a separate gate.
"""


class TableNotFound(Exception):
    """The claim map is missing, which is a failure and not an empty result."""


def normalise(span: str) -> str:
    """The identifier a ``\\texttt{}`` span spells, with LaTeX markup removed.

    The publication breaks long names with ``\\allowbreak`` and ``\\-`` and
    escapes underscores, and a span may run across a line. None of that is part
    of the name.
    """
    text = span.replace(r"\allowbreak", "").replace(r"\-", "").replace(r"\_", "_")
    return re.sub(r"\s+", "", text)


def declared_tails(lean_dir: Path) -> set[str]:
    """Final segments of every declaration under *lean_dir*.

    Comments are stripped first, on the same principle as ``check_leaves.py``:
    a name discussed only in a docstring declares nothing.
    """
    names: set[str] = set()
    for path in sorted(lean_dir.rglob("*.lean")):
        names |= declarations(strip_comments(path.read_text(encoding="utf-8")))
    return {name.split(".")[-1] for name in names}


def table_region(supplement: str) -> str:
    """The longtable carrying the claim map."""
    for match in LONGTABLE_RE.finditer(supplement):
        if TABLE_LABEL in match.group(0):
            return match.group(0)
    raise TableNotFound(f"no longtable carrying {TABLE_LABEL}")


def covered_tails(table: str) -> set[str]:
    """Final segments of every identifier the claim map spells."""
    return {normalise(span).split(".")[-1] for span in TEXTTT_RE.findall(table)}


def article_references(article: str, declared: set[str]) -> list[tuple[int, str]]:
    """Line number and identifier for each declaration the article names."""
    found: list[tuple[int, str]] = []
    for lineno, line in enumerate(article.splitlines(), start=1):
        for span in TEXTTT_RE.findall(line):
            name = normalise(span)
            if name.split(".")[-1] in declared:
                found.append((lineno, name))
    return found


def uncovered(article: str, supplement: str, declared: set[str]) -> list[tuple[int, str]]:
    """Declarations the article names and the claim map does not carry."""
    rows = covered_tails(table_region(supplement))
    return [
        (lineno, name)
        for lineno, name in article_references(article, declared)
        if name.split(".")[-1] not in rows
    ]


def report(findings: list[tuple[int, str]]) -> None:
    """One line per uncovered identifier, in the form an editor can jump to."""
    for lineno, name in findings:
        print(f"{ARTICLE}:{lineno}: {name} -- named by the article, no row in Table S1")


def main() -> int:
    """Check the article's declaration references against the claim map."""
    declared = declared_tails(LEAN_DIR)
    findings = uncovered(
        ARTICLE.read_text(encoding="utf-8"),
        SUPPLEMENT.read_text(encoding="utf-8"),
        declared,
    )
    if findings:
        report(findings)
        print(f"\ncheck_table_coverage: {len(findings)} claim(s) with no row.")
        print(GUIDANCE)
        return 1
    checked = len(article_references(ARTICLE.read_text(encoding="utf-8"), declared))
    print(f"check_table_coverage: {checked} declaration(s) named by the article, all mapped.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
