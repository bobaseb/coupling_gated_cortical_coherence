#!/usr/bin/env python3
"""Gate: no ``sorry`` in any Lean source.

``lake build`` does not fail on a ``sorry``. It prints
``declaration uses 'sorry'`` as a *warning*, the build goes green, and the
manuscript keeps saying the development is machine-checked. That is the whole
reason this gate is textual and local: it fires in the two seconds before the
commit, not in the ninety minutes of a CI Lean job.

``Audit.lean`` is the real check — it sweeps every declaration in the library
and rejects ``sorryAx`` along with any other stray axiom. This script exists
for the one case the sweep structurally cannot see and for the case where the
sweep is too slow to be useful:

* ``example ... := sorry`` adds no constant to the environment, so no
  environment sweep will ever find it.
* A ``sorry`` in a file that is not imported by the root aggregator compiles
  (or does not) entirely outside the audit's reach.

**Comments are stripped before searching**, on the same principle as
``check_leaves.py``: ``Axioms.lean`` §5 discusses removed postulates in prose,
and a gate that counted prose would fail on the record of its own success.
``_archive/`` is excluded -- it is superseded material, kept as history, and
nothing builds it.

Run: python simulations/check_sorry.py

Exit 0 if no Lean source contains ``sorry`` outside a comment, 1 otherwise.
"""

from __future__ import annotations

import re
from pathlib import Path

from repo_root import REPO

EXCLUDED_DIRS = {"_archive", ".lake"}

BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
# ``sorry`` as a whole token: ``sorryAx`` in a docstring is a discussion of the
# axiom, and a name like ``not_sorry`` is not the tactic.
SORRY_RE = re.compile(r"\bsorry\b")


def lean_sources() -> list[Path]:
    """Every tracked Lean source the build could reach."""
    return sorted(
        p for p in REPO.rglob("*.lean") if not EXCLUDED_DIRS.intersection(p.relative_to(REPO).parts)
    )


def offenders(path: Path) -> list[int]:
    """Line numbers carrying a ``sorry`` outside a comment.

    Comments are blanked rather than deleted, so the surviving line numbers are
    the ones the author will see in their editor.
    """
    text = path.read_text(encoding="utf-8")
    blanked = BLOCK_COMMENT_RE.sub(lambda m: re.sub(r"[^\n]", " ", m.group()), text)
    blanked = LINE_COMMENT_RE.sub(lambda m: " " * len(m.group()), blanked)
    return [n for n, line in enumerate(blanked.splitlines(), 1) if SORRY_RE.search(line)]


def main() -> int:
    found = {p: lines for p in lean_sources() if (lines := offenders(p))}

    if not found:
        print(f"check_sorry: no `sorry` in {len(lean_sources())} Lean sources.")
        return 0

    print("check_sorry: `sorry` found in Lean source.\n")
    for path, lines in found.items():
        for line in lines:
            print(f"  {path.relative_to(REPO)}:{line}")
    print(
        "\nThe manuscript claims the chain is machine-checked and that "
        "`#print axioms` reports only propext, Classical.choice and Quot.sound. "
        "A `sorry` makes both sentences false while `lake build` stays green."
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
