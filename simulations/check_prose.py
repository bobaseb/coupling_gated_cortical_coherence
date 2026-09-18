"""Gate: publication prose stands alone, without drafting history or Markdown references.

``main.tex`` and ``supplementary.tex`` state the theory's current state only. A
reader of the paper has never seen a previous draft, so a sentence that only
makes sense to someone who has is not addressed to them. Drafting history
belongs in the repository -- ``CHANGELOG.md``, Lean docstrings,
``tasks/lessons.md`` and the ledger under ``tasks/`` -- and this script is what
keeps it there. See ``AGENTS.md`` section 5.

The test a passage has to meet is not "is this about our past" but *does this
sentence still make sense to a reader who has never seen a previous draft?* A
refutation of an axiom shape is a permanent mathematical fact and stays; "earlier
drafts of this work declared five axioms" is autobiography and goes.

There is deliberately **no allowlist** (reaffirmed 2026-09-01 per R6:
no concrete case has arisen requiring one; an escape hatch with one entry
becomes an escape hatch with twenty, and the gate erodes to nothing).
An escape hatch with one entry becomes an
escape hatch with twenty, and the gate erodes to nothing. Where a pattern below
has a legitimate non-autobiographical use -- a sequence that is no longer
monotone, a quantity previously defined in the same document -- the fix is to
reword the sentence, not to widen the gate.

Internal Markdown filenames and links also send readers outside the publication
for content it must state itself. Reject their extensions even inside LaTeX
markup and URL targets. Lean theorem names and source files remain valid formal
references, and the code-availability section can link the repository itself.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from repo_root import REPO

# Each pattern identifies drafting history or a reference to internal notes,
# with a reason so the report explains what needs rewriting.
PATTERNS: list[tuple[str, str]] = [
    # Direct appeals to a version of the document the reader cannot see.
    (r"earlier draft", "names a version of this document the reader has never seen"),
    (r"earlier version", "same, with 'version' for 'draft'"),
    (r"an earlier", "catches 'an earlier statement', 'an earlier form' and the like"),
    (r"the old", "'the old predicate', 'the old statement' -- old relative to what?"),
    (r"formerly", "asserts a change of status rather than a status"),
    (r"previously", "the commonest form; also has legitimate intra-document uses"),
    (r"until recently", "dates the claim to the drafting, not to the physics"),
    (r"no longer", "'X no longer holds' is a claim about the draft, not about X"),
    (r"have since been", "narrates the repair rather than stating the result"),
    # First-person narration of the project's own corrections.
    (r"we had recorded", "reports a past belief of the authors"),
    (r"withdraw", "covers withdraw/withdrawn/withdraws: retraction narration"),
    (r"retract", "covers retract/retracted/retraction"),
    (r"misdiagnos", "covers misdiagnosis/misdiagnosed"),
    # Match the extension so escaped underscores and path markup cannot hide it.
    (r"\.(?:md|markdown)\b", "references a Markdown file instead of stating the content"),
]

FILES: tuple[str, ...] = ("main.tex", "supplementary.tex")

GUIDANCE = """
The publication must stand alone (AGENTS.md section 5).

Drafting-history hits ask the reader to remember a draft they have never seen.
Rewrite them as present-tense statements of scope, or delete them. The
mathematical content of a correction is permanent and stays; whose correction
it was does not.

Markdown-file references send the reader to internal notes. State the relevant
methods or results in the publication and keep file provenance in the
repository. Lean theorem names and .lean source references are allowed, as is
the repository link in code availability.

Destinations for what is removed: CHANGELOG.md for what a reader of the
repository needs, a Lean docstring where the content is technical, tasks/ for the
working record.
"""


def find_hits(path: Path) -> list[tuple[int, str, str, str]]:
    """Return (line number, pattern, reason, line text) for every match in *path*."""
    hits: list[tuple[int, str, str, str]] = []
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        for pattern, reason in PATTERNS:
            if re.search(pattern, line, flags=re.IGNORECASE):
                hits.append((lineno, pattern, reason, line.strip()))
    return hits


def excerpt(line: str, pattern: str, width: int = 72) -> str:
    """The matched phrase with a little context, so the hit can be read in place."""
    match = re.search(pattern, line, flags=re.IGNORECASE)
    if match is None:  # pragma: no cover - find_hits only reports matches
        return line[:width]
    start = max(0, match.start() - width // 2)
    end = min(len(line), match.end() + width // 2)
    return ("..." if start else "") + line[start:end] + ("..." if end < len(line) else "")


def report(path: Path, hits: list[tuple[int, str, str, str]]) -> None:
    """Print one block per file, in the file:line: form editors can jump to."""
    for lineno, pattern, reason, line in hits:
        print(f"{path}:{lineno}: '{pattern}' -- {reason}")
        print(f"    {excerpt(line, pattern)}")


def main(argv: list[str]) -> int:
    """Check every named file, or the two publication files by default."""
    targets = [Path(a) for a in argv[1:]] or [REPO / name for name in FILES]
    total = 0
    for path in targets:
        if not path.exists():
            print(f"check_prose: {path} not found", file=sys.stderr)
            return 2
        hits = find_hits(path)
        total += len(hits)
        report(path, hits)
    if total:
        print(f"\ncheck_prose: {total} publication-prose violation(s).")
        print(GUIDANCE)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
