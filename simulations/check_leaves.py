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

Run: python simulations/check_leaves.py

Exit 0 if no leaf modules found, 1 otherwise.
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

DECL_RE = re.compile(
    r"^(?:(?:noncomputable|protected|private)\s+)?"
    r"(?:structure|theorem|lemma|def|opaque)\s+"
    r"([a-zA-Z_]\w*)"
)


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
    in a consumer file outside NOT_CONSUMERS and the module itself."""
    decls = extract_decls(mod_path)
    if not decls:
        return True  # no declarations to be a leaf

    for consumer in consumer_dir.rglob("*.lean"):
        if consumer.resolve() == mod_path.resolve():
            continue
        if consumer.name in NOT_CONSUMERS:
            continue
        content = consumer.read_text(encoding="utf-8")
        for d in decls:
            if re.search(rf"\b{re.escape(d)}\b", content):
                return True

    return False


def main() -> int:
    modules = sorted(LEAN_DIR.rglob("*.lean"))
    leaves: list[str] = []

    for mod in modules:
        if mod.name in NOT_CHECKED:
            continue
        if not module_has_consumer(mod, LEAN_DIR):
            rel = mod.relative_to(REPO)
            leaves.append(str(rel))

    if leaves:
        print(
            f"check_leaves: {len(leaves)} modules have zero declarations consumed\n"
            f"  outside themselves, Examples.lean, and the root aggregator.\n"
        )
        for lf in leaves:
            print(f"  {lf}")
        print(
            "\n"
            "A module whose declarations are referenced by nothing outside\n"
            "itself and Examples.lean is a leaf in the edge graph.\n"
            "Its types are imported; its theorems are not. That is how C1's\n"
            "defect arose in Phase8_SelfConsistency.\n"
        )
        return 1

    print("check_leaves: every phase module has at least one declaration consumed elsewhere.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
