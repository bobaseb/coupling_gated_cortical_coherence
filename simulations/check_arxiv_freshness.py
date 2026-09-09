#!/usr/bin/env python3
"""Gate: a built arXiv submission is not behind the manuscript.

``arxiv_submit/`` is what gets uploaded, and it is not tracked in git. Nothing
else in this repository can tell whether the directory sitting there is the
current manuscript or last week's: the sources stay consistent with each other,
the tracked PDFs are gated by ``check_pdf_freshness.py``, and the tarball is
build output that no diff ever shows. The staleness is discovered by opening
``arxiv_submit/main.pdf``, finding text nobody wrote any more, and wondering
which of the two documents is real -- or it is not discovered at all, and a
superseded manuscript is posted.

``prepare_arxiv.sh`` records what it built from in ``arxiv_submit/BUILD_MANIFEST``:
one SHA-256 per source file, plus the commit and the build time. This script
recomputes those digests and, independently, re-derives the source set from
``main.tex`` and ``supplementary.tex`` the same way the freshness gate does, so
that a figure *added* to the article since the last build is caught as well as
one that changed.

Under ``pre-commit`` the working tree it reads is the staged state, since
unstaged changes are stashed for the duration of the hooks. So the question it
answers on commit is whether the built submission matches *the commit being
made*, which is the useful one: a manuscript change split across two commits
leaves the first of them describing a document nobody can build.

The escape hatch is to have no built submission rather than to have a stale one:
``rm -rf arxiv_submit`` passes, because a directory that is not there cannot be
mistaken for the current one. While iterating on the manuscript, that is the
state to be in.

Run: python simulations/check_arxiv_freshness.py

Exit 0 if there is no built submission or it matches the sources, 1 otherwise.
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path

from check_pdf_freshness import PUBLICATION, REPO, dependencies

SUBMISSION = "arxiv_submit"
MANIFEST = f"{SUBMISSION}/BUILD_MANIFEST"

# Sources of the submission that no \input or \includegraphics names: the style
# the arXiv build applies, and the script that assembles the document.
UNREFERENCED: tuple[str, ...] = ("arxiv_assets/neurips_2026.sty", "prepare_arxiv.sh")

GUIDANCE = f"""
The built arXiv submission is behind the manuscript (AGENTS.md section 7).

{SUBMISSION}/ is not tracked, so nothing else here notices. Rebuild it, which
also recompiles and repacks it:

    ./prepare_arxiv.sh

Or delete it: rm -rf {SUBMISSION}. A submission that is not there cannot be
uploaded by mistake; one that is stale can.
"""


def digest(path: Path) -> str:
    """SHA-256 of a file, in the spelling ``sha256sum`` writes."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_sources(root: Path) -> set[str]:
    """Repository-relative files the submission is assembled from, read from the sources."""
    found: set[Path] = set()
    for document in PUBLICATION:
        found |= dependencies(root / document) | {(root / document).resolve()}
    named = {path.relative_to(root.resolve()).as_posix() for path in found}
    return named | set(UNREFERENCED)


def recorded_sources(manifest: Path) -> dict[str, str]:
    """The digest the last build recorded for each source it packed."""
    entries: dict[str, str] = {}
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        checksum, _, name = line.partition(" ")
        entries[name.strip()] = checksum
    return entries


def drift(root: Path, recorded: dict[str, str]) -> list[str]:
    """One line per source the built submission does not match, empty if it is current."""
    reasons = []
    expected = expected_sources(root)
    for name in sorted(expected - set(recorded)):
        reasons.append(f"{name}: in the manuscript, not in the built submission")
    for name in sorted(set(recorded) - expected):
        reasons.append(f"{name}: in the built submission, no longer a source")
    for name in sorted(expected & set(recorded)):
        path = root / name
        if not path.is_file():
            reasons.append(f"{name}: gone from the working tree")
        elif digest(path) != recorded[name]:
            reasons.append(f"{name}: changed since the submission was built")
    return reasons


def main(argv: list[str]) -> int:
    """Fail on a built submission that is behind its sources; pass if there is none."""
    root = Path(argv[1]) if len(argv) > 1 else REPO
    if not (root / SUBMISSION).is_dir():
        print(f"check_arxiv_freshness: no {SUBMISSION}/ to be stale.")
        return 0
    manifest = root / MANIFEST
    if not manifest.is_file():
        print(f"{MANIFEST}: missing -- {SUBMISSION}/ was not built by prepare_arxiv.sh")
        print(GUIDANCE)
        return 1
    reasons = drift(root, recorded_sources(manifest))
    for reason in reasons:
        print(reason)
    if reasons:
        print(GUIDANCE)
        return 1
    print(f"check_arxiv_freshness: {SUBMISSION}/ is current.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
