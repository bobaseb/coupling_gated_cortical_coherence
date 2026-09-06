"""Advisory report: disclaimer and reader-instruction language in the publication.

Sibling of ``check_prose.py``, and deliberately unlike it. That gate enforces a
rule with a yes/no answer -- a sentence either asks the reader to remember a
draft they have never seen or it does not -- so it fails the commit. Hedging has
no such answer. A scope statement that keeps a claim honest and one that pads a
paragraph look identical to a regex, and this article needs a great many of the
first kind. So this script decides nothing: it reports, and the person or agent
holding the paragraph decides whether each hit earns its place.

Three categories, treated differently because they differ in kind:

``reader-instruction``
    Prose that tells the reader how to value a passage rather than stating it.
    "This is the most portable result" and "the negative result is worth stating"
    are the author grading the material. Usually the fix is to delete the frame
    and keep the sentence, which then has to carry its own weight.

``empty-hedge``
    Softening that carries no scope information. "Arguably", "somewhat",
    "clearly": removing them changes what the sentence commits to by nothing at
    all, which is the test for whether they were doing anything.

``scope-disclaimer``
    Statements of what a result does not establish. These are the honesty of the
    article and are never flagged line by line -- flagging them would be advice
    to overclaim. They are counted, and the count is reported as a density per
    thousand words, because the failure mode is not any single disclaimer but a
    paragraph in which four of them interrupt one argument.

Usage::

    uv run python check_hedging.py                 # advisory, always exits 0
    uv run python check_hedging.py --strict         # exit 1 on flagged hits

The default is advisory. ``--strict`` exists for a caller that has already read
the report and wants the current state held.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

from check_prose import excerpt

FILES: tuple[str, ...] = ("main.tex", "supplementary.tex")

# Commands whose braced argument is an identifier rather than prose. Their
# arguments are removed before matching so that \label{sec:important} is not
# read as a sentence about importance.
_IDENTIFIER_COMMANDS = (
    "label|ref|eqref|cite|citep|citet|input|include|includegraphics"
    "|graphicspath|href|url|bibliography|texttt|hyperref"
)
_IDENTIFIER_CALL = re.compile(rf"\\(?:{_IDENTIFIER_COMMANDS})\b(?:\[[^\]]*\])?(?:\{{[^{{}}]*\}})*")
_ANY_COMMAND = re.compile(r"\\[A-Za-z@]+")

# Telling the reader what to think of a passage, in place of the passage.
READER_INSTRUCTION: list[tuple[str, str]] = [
    (
        r"\bworth (?:noting|stating|emphasi[sz]ing|mentioning|remarking|saying)\b",
        "grades the material instead of stating it; delete the frame, keep the claim",
    ),
    (r"\bimportant to note\b", "same, in its commonest form"),
    (
        r"\bit should be (?:noted|emphasi[sz]ed|stressed|remembered)\b",
        "agentless instruction to the reader",
    ),
    (
        r"\bwe (?:stress|emphasi[sz]e|underline|highlight)\b",
        "the sentence should carry its own emphasis",
    ),
    (
        r"\b(?:importantly|notably|crucially|tellingly|strikingly)\b",
        "adverb asserting significance the sentence has not shown",
    ),
    (
        r"\bthe (?:key|crucial|central|main) point (?:here )?is\b",
        "announces a point rather than making it",
    ),
    (r"\bthe most \w+ result\b", "ranks the article's own results for the reader"),
    (r"\bis doing real work\b", "asserts that a distinction matters; show it instead"),
    (r"\beasy to over-?read\b", "pre-empts a reading rather than closing it off"),
    (r"\bneedless to say\b", "if it is needless, cut it"),
]

# Softening that removes nothing when removed.
EMPTY_HEDGE: list[tuple[str, str]] = [
    (r"\barguably\b", "concedes an argument without giving one"),
    (r"\bsomewhat\b", "unquantified softener"),
    (r"\b(?:fairly|relatively|reasonably) \w+", "unquantified comparative with no comparand"),
    (r"\bto some extent\b", "no extent is given"),
    (r"\bin some sense\b", "the sense is the content; name it or cut it"),
    (r"\bit is possible that\b", "true of nearly everything"),
    (r"\b(?:may|might) (?:possibly|perhaps|conceivably)\b", "stacked modals"),
    (r"\bmore or less\b", "unquantified softener"),
    (
        r"\b(?:clearly|obviously|evidently)\b",
        "appeals to obviousness in place of an argument, and often marks a gap",
    ),
    (
        r"\b(?:essentially|basically|virtually|effectively) \w+",
        "signals an approximation without saying which",
    ),
    (r"\bof course\b", "assumes the reader's agreement"),
]

# Statements of scope. Counted for density; never flagged individually.
SCOPE_DISCLAIMER: list[str] = [
    r"\b(?:does|do) not (?:imply|establish|show|prove|follow|determine|measure|derive"
    r"|require|specify|guarantee|settle|address|resolve|constitute|validate|replace)\b",
    r"\bcannot\b",
    r"\bnot by itself\b",
    r"\bno theorem\b",
    r"\bis not (?:a |an )?(?:theorem|claim|proof|measurement|evidence|substitute)\b",
    r"\bconditional on\b",
    r"\brather than\b",
    r"\bwe (?:claim|assert|offer) no\b",
    r"\ban additional (?:assumption|hypothesis|modelling step|step|question)\b",
    r"\bremains? (?:an )?open\b",
]

GUIDANCE = """
Hedging is a judgement call, which is why nothing above failed.

reader-instruction and empty-hedge hits are candidates for deletion: read the
sentence without the flagged phrase and keep the cut if the claim survives
unchanged. A scope-disclaimer density well above the article's own norm marks a
paragraph that states a result, states its limit, then explains why stating the
limit matters -- consolidate the limits into one statement and let the argument
move.

Scope statements themselves are load-bearing here. Do not remove one to lower a
number; that trades honesty for a metric.
"""


@dataclass(frozen=True)
class Hit:
    """One flagged phrase, located well enough to jump to."""

    lineno: int
    category: str
    pattern: str
    reason: str
    line: str


def strip_latex(line: str) -> str:
    """Drop markup so that macro and label names are not read as prose."""
    return _ANY_COMMAND.sub(" ", _IDENTIFIER_CALL.sub(" ", line))


def _prose_lines(path: Path) -> list[tuple[int, str]]:
    """Numbered lines with markup removed and comment-only lines dropped."""
    lines = path.read_text(encoding="utf-8").splitlines()
    return [
        (n, strip_latex(line))
        for n, line in enumerate(lines, start=1)
        if not line.lstrip().startswith("%")
    ]


def find_hits(path: Path) -> list[Hit]:
    """Every reader-instruction and empty-hedge match, in file order."""
    groups = (("reader-instruction", READER_INSTRUCTION), ("empty-hedge", EMPTY_HEDGE))
    hits: list[Hit] = []
    for lineno, line in _prose_lines(path):
        for category, patterns in groups:
            for pattern, reason in patterns:
                if re.search(pattern, line, flags=re.IGNORECASE):
                    hits.append(Hit(lineno, category, pattern, reason, line.strip()))
    return hits


def count_scope(path: Path) -> int:
    """How many scope statements the file makes."""
    return sum(
        len(re.findall(pattern, line, flags=re.IGNORECASE))
        for _, line in _prose_lines(path)
        for pattern in SCOPE_DISCLAIMER
    )


def scope_density(path: Path) -> float:
    """Scope statements per thousand words, the comparable figure across files."""
    words = sum(len(line.split()) for _, line in _prose_lines(path))
    return 0.0 if words == 0 else 1000.0 * count_scope(path) / words


def report(path: Path, hits: list[Hit]) -> None:
    """One block per file, in the file:line: form editors can jump to."""
    for hit in hits:
        print(f"{path}:{hit.lineno}: [{hit.category}] '{hit.pattern}' -- {hit.reason}")
        print(f"    {excerpt(hit.line, hit.pattern)}")
    print(
        f"{path}: {len(hits)} flagged, "
        f"{count_scope(path)} scope statement(s), "
        f"{scope_density(path):.1f} per 1000 words."
    )


def _targets(names: list[str]) -> list[Path]:
    """The files named on the command line, or the publication by default."""
    root = Path(__file__).resolve().parent.parent
    return [Path(name) for name in names] or [root / name for name in FILES]


def _report_all(targets: list[Path]) -> int | None:
    """Total flagged hits across *targets*, or None if one of them is missing."""
    flagged = 0
    for path in targets:
        if not path.exists():
            print(f"check_hedging: {path} not found", file=sys.stderr)
            return None
        hits = find_hits(path)
        flagged += len(hits)
        report(path, hits)
    return flagged


def main(argv: list[str]) -> int:
    """Report on every named file, or on the publication by default."""
    strict = "--strict" in argv[1:]
    flagged = _report_all(_targets([a for a in argv[1:] if a != "--strict"]))
    if flagged is None:
        return 2
    if flagged:
        print(GUIDANCE)
    return 1 if (strict and flagged) else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
