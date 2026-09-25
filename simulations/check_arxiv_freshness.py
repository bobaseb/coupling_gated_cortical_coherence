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

Each paper has its own build: ``prepare_arxiv.sh`` writes ``arxiv_submit/`` for
the companion, and ``unity/prepare_arxiv.sh`` writes ``unity/arxiv_submit/`` for
the physical-unity paper. Every submission present is checked, each against
the sources of its own document, and either can be absent.

Run: python simulations/check_arxiv_freshness.py

Exit 0 if there is no built submission or it matches the sources, 1 otherwise.
"""

from __future__ import annotations

import hashlib
import sys
from dataclasses import dataclass
from pathlib import Path

from check_pdf_freshness import dependencies
from repo_root import REPO

STYLE = "arxiv_assets/neurips_2026.sty"
HELPERS = "arxiv_assets/arxiv_lib.sh"


@dataclass(frozen=True)
class Submission:
    """One built submission: where it lands, what it is built from, and how."""

    directory: str
    documents: tuple[str, ...]
    # Sources that no \input or \includegraphics names: the style the build
    # applies, the helpers it shares, and the script that assembles it.
    unreferenced: tuple[str, ...]
    script: str

    @property
    def manifest(self) -> str:
        """Where the build records the digest of every source it packed."""
        return f"{self.directory}/BUILD_MANIFEST"


COMPANION = Submission(
    "arxiv_submit",
    ("main.tex", "supplementary.tex"),
    (STYLE, HELPERS, "prepare_arxiv.sh"),
    "./prepare_arxiv.sh",
)
UNITY = Submission(
    "unity/arxiv_submit",
    ("unity/main.tex",),
    (STYLE, HELPERS, "unity/prepare_arxiv.sh"),
    "unity/prepare_arxiv.sh",
)
SUBMISSIONS: tuple[Submission, ...] = (COMPANION, UNITY)

GUIDANCE = """
The built arXiv submission is behind the manuscript (AGENTS.md section 7).

{directory}/ is not tracked, so nothing else here notices. Rebuild it, which
also recompiles and repacks it:

    {script}

Or delete it: rm -rf {directory}. A submission that is not there cannot be
uploaded by mistake; one that is stale can.
"""


def digest(path: Path) -> str:
    """SHA-256 of a file, in the spelling ``sha256sum`` writes."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expected_sources(root: Path, submission: Submission) -> set[str]:
    """Repository-relative files *submission* is assembled from, read from the sources."""
    found: set[Path] = set()
    for document in submission.documents:
        found |= dependencies(root / document) | {(root / document).resolve()}
    named = {path.relative_to(root.resolve()).as_posix() for path in found}
    return named | set(submission.unreferenced)


def recorded_sources(manifest: Path) -> dict[str, str]:
    """The digest the last build recorded for each source it packed."""
    entries: dict[str, str] = {}
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        checksum, _, name = line.partition(" ")
        entries[name.strip()] = checksum
    return entries


def drift(root: Path, submission: Submission, recorded: dict[str, str]) -> list[str]:
    """One line per source the built submission does not match, empty if it is current."""
    reasons = []
    expected = expected_sources(root, submission)
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


def stale(root: Path, submission: Submission) -> bool:
    """Report on one submission; true if it is present and behind its sources."""
    if not (root / submission.directory).is_dir():
        print(f"check_arxiv_freshness: no {submission.directory}/ to be stale.")
        return False
    manifest = root / submission.manifest
    if not manifest.is_file():
        built_by = f"{submission.directory}/ was not built by {submission.script}"
        print(f"{submission.manifest}: missing -- {built_by}")
        reasons = ["no manifest"]
    else:
        reasons = drift(root, submission, recorded_sources(manifest))
        for reason in reasons:
            print(reason)
    if reasons:
        print(GUIDANCE.format(directory=submission.directory, script=submission.script))
        return True
    print(f"check_arxiv_freshness: {submission.directory}/ is current.")
    return False


def main(argv: list[str]) -> int:
    """Fail on any built submission that is behind its sources; pass if there is none."""
    root = Path(argv[1]) if len(argv) > 1 else REPO
    failures = [submission for submission in SUBMISSIONS if stale(root, submission)]
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
