"""Claims first, limitations in one place: the structural gate against hedging.

``check_hedging.py`` counts scope disclaimers and decides nothing, because
whether one disclaimer earns its place is a judgement about its paragraph. What
it cannot see is the failure this repository's prose actually has: no single
sentence is a hedge, but nearly every paragraph carries a scope clause, so the
article reads as a list of what it does not show. That is a property of *where*
disclaimers sit, and position has a yes/no answer.

The rules, for the physical-unity paper and the article ``main.tex``:

* A section labelled ``sec:limitations`` exists, and disclaimers are unlimited
  there.
* Every other section, the abstract included, carries at most one disclaimer. A
  result that needs a scope clause states it once, in its theorem statement.
* The introduction states numbered claims as ``\\claim{label}{text}``, and each
  label is defined somewhere in the paper, so every claim points at the section
  that argues it.

A disclaimer is anything ``check_hedging.SCOPE_DISCLAIMER`` counts; the lexicon
lives there so the two gates cannot disagree about what a disclaimer is.

The gate cannot check meaning. A disclaimer cut from the running text has to
reappear in ``sec:limitations`` or in a theorem statement; the point is to move
qualification, not to delete it.

Usage::

    uv run python check_claims.py                   # hard, on unity/main.tex
    uv run python check_claims.py ../main.tex       # hard, on the article
    uv run python check_claims.py --advisory ../supplementary.tex  # report only

A paper that does not exist yet passes: the gate predates the paper it guards.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

from check_hedging import count_scope_text, strip_latex
from repo_root import REPO

TARGET = REPO / "unity" / "main.tex"
LIMITATIONS = "sec:limitations"
ALLOWED_OUTSIDE = 1
WORST_SHOWN = 5

_COMMENT = re.compile(r"(?<!\\)%.*")
_ABSTRACT = re.compile(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", re.DOTALL)
_SECTION = re.compile(r"\\section\*?\{((?:[^{}]|\{[^{}]*\})*)\}")
_END = re.compile(r"\\end\{document\}")
_LABEL = re.compile(r"\\label\{([^}]*)\}")
_CLAIM = re.compile(r"\\claim\{([^}]*)\}")


@dataclass(frozen=True)
class Section:
    """One unit the placement rule applies to: a section or the abstract."""

    title: str
    body: str

    @property
    def label(self) -> str | None:
        """The section's own label: the first one in its body."""
        found = _LABEL.search(self.body)
        return found.group(1) if found else None

    @property
    def disclaimers(self) -> int:
        """Scope statements in the section's prose, counted across line breaks."""
        prose = strip_latex(_CLAIM.sub(" ", self.body))
        return count_scope_text(" ".join(prose.split()))


def _source(path: Path) -> str:
    """The file with comments removed, so that commented-out prose is not read."""
    lines = path.read_text(encoding="utf-8").splitlines()
    return "\n".join(_COMMENT.sub("", line) for line in lines)


def sections(path: Path) -> list[Section]:
    """The abstract, if any, then every ``\\section`` up to ``\\end{document}``."""
    text = _source(path)
    abstract = _ABSTRACT.search(text)
    found = [Section("abstract", abstract.group(1))] if abstract else []
    end = _END.search(text)
    stop = end.start() if end else len(text)
    heads = list(_SECTION.finditer(text, 0, stop))
    for head, following in zip(heads, [*heads[1:], None]):
        body_end = following.start() if following else stop
        found.append(Section(head.group(1), text[head.end() : body_end]))
    return found


def section_counts(path: Path) -> list[tuple[str, int]]:
    """Disclaimers per section, in document order."""
    return [(s.title, s.disclaimers) for s in sections(path)]


def _placement(found: list[Section]) -> list[str]:
    """Violations of the rule that disclaimers live in ``sec:limitations``."""
    home = any(s.label == LIMITATIONS for s in found)
    missing = [] if home else [f"no section is labelled {LIMITATIONS}; limitations need one home"]
    return missing + [
        f"{s.title}: {s.disclaimers} scope disclaimers; "
        f"at most {ALLOWED_OUTSIDE} outside {LIMITATIONS}"
        for s in found
        if s.label != LIMITATIONS and s.disclaimers > ALLOWED_OUTSIDE
    ]


def _claims(path: Path, found: list[Section]) -> list[str]:
    """Violations of the rule that the introduction states cross-referenced claims."""
    intro = next((s for s in found if s.title != "abstract"), None)
    if intro is None or not _CLAIM.search(intro.body):
        return ["the introduction states no numbered \\claim{label}{text}"]
    defined = set(_LABEL.findall(_source(path)))
    return [
        f"\\claim points at undefined label {label}"
        for label in _CLAIM.findall(intro.body)
        if label not in defined
    ]


def violations(path: Path) -> list[str]:
    """Every rule the paper at *path* breaks, placement first."""
    found = sections(path)
    return _placement(found) + _claims(path, found)


def report(path: Path, problems: list[str]) -> None:
    """Violations, then the disclaimer ratio and the worst sections."""
    for problem in problems:
        print(f"{path}: {problem}")
    counts = section_counts(path)
    total = sum(n for _, n in counts)
    claims = len(_CLAIM.findall(_source(path)))
    ratio = f"{total / claims:.1f} per claim" if claims else "no claims stated"
    print(f"{path}: {total} scope disclaimer(s) in {len(counts)} section(s); {ratio}.")
    for title, n in sorted(counts, key=lambda item: -item[1])[:WORST_SHOWN]:
        print(f"    {n:3d}  {title}")


def main(argv: list[str]) -> int:
    """Check every named paper, or the physical-unity paper by default."""
    advisory = "--advisory" in argv[1:]
    targets = [Path(a) for a in argv[1:] if a != "--advisory"] or [TARGET]
    failed = False
    for path in targets:
        if not path.exists():
            print(f"check_claims: {path} not written yet; nothing to check")
            continue
        problems = violations(path)
        report(path, problems)
        failed = failed or bool(problems)
    return 1 if (failed and not advisory) else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
