#!/usr/bin/env python3
"""Gate: detect modules whose theorems are consumed by nothing outside themselves.

C1's defect — a module that is imported but none of whose theorems are referenced
anywhere outside itself, ``Examples.lean`` and the root aggregator — is the exact
shape that made ``Phase8_SelfConsistency`` a leaf in the edge graph. The build
certifies that every module compiles, not that any module's results feed into
another.

This script checks, for each phase module, whether any of its public declarations
appear in a *non-trivial consumer* (any Lean file except the module itself,
``PhysicsOfConsciousness.lean``, and ``Examples.lean``). A module with zero such
references is a leaf — its types are imported; its theorems are dead.

**Comments are stripped before searching.** A name that appears only in a
docstring is exactly the state C1 was in: discussed in prose, unused in code.
Counting prose as consumption would let the gate certify the defect it exists to
find. (The block-comment stripper is a non-greedy match and does not model Lean's
nested ``/- -/``; a nested comment leaves a fragment behind, which can only make
the check stricter, never laxer.)

``ALLOWED_LEAVES`` is the recorded baseline: modules that are leaves today, each
with the reason. A leaf outside that set fails the gate, and so does an entry
that has stopped being a leaf — an exemption nobody removes is how a gate rots.

Run: python simulations/check_leaves.py

Exit 0 if the leaf set is exactly ``ALLOWED_LEAVES``, 1 otherwise.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN_DIR = REPO / "PhysicsOfConsciousness"

# Modules whose declarations need not be consumed by anything else:
#   Chain.lean — top composition module, no consumer by design.
#   PhysicsOfConsciousness.lean — root aggregator, no content.
#   Axioms.lean — empty of theorems.
#   Examples.lean — witness sink, its own declarations are not intended for use.
NOT_CHECKED = {
    "Chain.lean",
    "PhysicsOfConsciousness.lean",
    "Axioms.lean",
    "Examples.lean",
}
# Consumers that do not count as real consumption:
#   PhysicsOfConsciousness.lean — just re-exports, no content.
#   Examples.lean — imports everything as a witness; consumption there is not
#     usage but presence.  Treating it as a consumer would make every module
#     look non-leaf and defeat the check.
NOT_CONSUMERS = {"PhysicsOfConsciousness.lean", "Examples.lean"}

# The recorded baseline. Each entry is a module that is a leaf *and is known to
# be one*, with the reason it is tolerated. Adding to this dict is a decision;
# it should be made in the ledger, not in passing.
ALLOWED_LEAVES: dict[str, str] = {
    "Phase3_KLBound.lean": (
        "referenced only from Phase3_PredictiveThermodynamics docstrings "
        "(`structural_resonance_bound`, `discrete_entropy_rate_nonneg`) and from "
        "the supplement; no theorem consumes it. Recorded, not endorsed — this is "
        "the C1 shape, and giving it a consumer is open work"
    ),
    "Phase5_PhaseLifts.lean": (
        "deliberate — F2's results are about the obstruction, and the chain routes "
        "around it rather than through it"
    ),
    "Phase5_TwistedGluing.lean": (
        "deliberate — F4's twisted-gluing results are not wired into `chain`"
    ),
    "Phase8_CriticalExponent.lean": (
        "referenced only from a Phase8_SelfConsistency docstring "
        "(`vonMisesSRatio_second_order`) and from the manuscript. The exponent is "
        "a terminal prediction: nothing in Lean is downstream of beta = 1/2, and "
        "nothing is expected to be"
    ),
}

DECL_RE = re.compile(
    r"^(?:(?:noncomputable|protected|private)\s+)?"
    r"(?:structure|theorem|lemma|def|opaque)\s+"
    r"([a-zA-Z_]\w*)"
)

BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)


def strip_comments(text: str) -> str:
    """Remove Lean block and line comments, so prose never counts as usage."""
    return LINE_COMMENT_RE.sub("", BLOCK_COMMENT_RE.sub("", text))


def extract_decls(path: Path) -> set[str]:
    """Return set of top-level theorem/def/lemma names in *path*."""
    names: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        m = DECL_RE.match(line)
        if m:
            names.add(m.group(1))
    return names


def module_has_consumer(mod_path: Path, consumer_dir: Path) -> bool:
    """Return True if at least one declaration from *mod_path* is referenced
    in the *code* of a consumer file outside NOT_CONSUMERS and the module
    itself."""
    decls = extract_decls(mod_path)
    if not decls:
        return True  # no declarations to be a leaf

    for consumer in consumer_dir.rglob("*.lean"):
        if consumer.resolve() == mod_path.resolve():
            continue
        if consumer.name in NOT_CONSUMERS:
            continue
        content = strip_comments(consumer.read_text(encoding="utf-8"))
        for d in decls:
            if re.search(rf"\b{re.escape(d)}\b", content):
                return True

    return False


def find_leaves() -> list[Path]:
    """Every checked module with no code-level consumer, in path order."""
    return [
        mod
        for mod in sorted(LEAN_DIR.rglob("*.lean"))
        if mod.name not in NOT_CHECKED and not module_has_consumer(mod, LEAN_DIR)
    ]


def classify(leaves: list[Path]) -> tuple[list[Path], list[str]]:
    """Split the leaf set against the recorded baseline.

    Returns the leaves nobody has recorded and the recorded names that have
    since acquired a consumer — the two ways the tree and `ALLOWED_LEAVES` can
    disagree, and both are failures.
    """
    leaf_names = {mod.name for mod in leaves}
    unrecorded = [mod for mod in leaves if mod.name not in ALLOWED_LEAVES]
    stale = sorted(name for name in ALLOWED_LEAVES if name not in leaf_names)
    return unrecorded, stale


def report_unrecorded(unrecorded: list[Path]) -> None:
    print(
        f"check_leaves: {len(unrecorded)} module(s) have zero declarations "
        "consumed\n  outside themselves, Examples.lean, and the root "
        "aggregator.\n"
    )
    for mod in unrecorded:
        print(f"  {mod.relative_to(REPO)}")
    print(
        "\n"
        "A module whose declarations are referenced by nothing outside\n"
        "itself and Examples.lean is a leaf in the edge graph.\n"
        "Its types are imported; its theorems are not. That is how C1's\n"
        "defect arose in Phase8_SelfConsistency. Wire a consumer, or record\n"
        "the module in ALLOWED_LEAVES with the reason it stays dangling.\n"
    )


def report_stale(stale: list[str]) -> None:
    print(
        f"check_leaves: {len(stale)} recorded leaf(s) now have a consumer.\n"
        "  Delete them from ALLOWED_LEAVES — an exemption nobody removes is\n"
        "  how a gate stops meaning anything.\n"
    )
    for name in stale:
        print(f"  {name}")
    print()


def main() -> int:
    unrecorded, stale = classify(find_leaves())

    if not unrecorded and not stale:
        print(
            "check_leaves: no unrecorded leaf modules "
            f"({len(ALLOWED_LEAVES)} recorded, all still leaves)."
        )
        return 0

    if unrecorded:
        report_unrecorded(unrecorded)
    if stale:
        report_stale(stale)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
