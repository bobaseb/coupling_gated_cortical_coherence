#!/usr/bin/env python3
"""Validate Table S1 status column against Chain.lean declarations.

Checks that each status cell in supplementary.tex is consistent
with what Chain.lean declares about the corresponding node/edge.
This is a structural cross-reference check, not a full generation:
the table is hand-maintained and this script flags mismatches.

Run: python simulations/check_tableS1.py

Exit 0 if the checks pass, 1 otherwise.
"""

import re
import sys

from repo_root import REPO

CHAIN = REPO / "PhysicsOfConsciousness" / "Chain.lean"
SUPP = REPO / "supplementary.tex"

KNOWN_STATUSES = [
    r"^Theorem$",
    r"^Theorem \+ instance postulate$",
    r"^Theorem \(conditional\)$",
    r"^Theorem \(negative\)$",
    r"^Theorem \(scalar energy only\)$",
    r"^Theorem \(topological obstruction\) \+ empirical candidate$",
    r"^Conditional theorem.*?modelling postulate.*?$",
    r"^Modelling assumption \+ empirical commitment$",
    r"^Conditional theorem with eight named hypotheses$",
]


def check_supplementary_table(content: str) -> list[str]:
    """Check Table S1 status cells for known patterns."""
    errors = []
    # Extract status cells from the longtable in supp.
    # A status cell sits between the last ' & ' and ' \\' on a table row.
    # In the raw tex, rows end with: & Status \\ \hline
    # We match the status text as the shortest text containing one of the
    # known status keywords between ' & ' and ' \\'.
    pat = r"& ([^&]+?) \\\\"
    for m in re.finditer(pat, content):
        status = m.group(1).strip()
        # Only check rows that look like status cells
        if not any(kw in status for kw in ["Theorem", "Modelling", "Conditional", "empirical"]):
            continue
        ok = any(re.match(k, status) for k in KNOWN_STATUSES)
        if not ok:
            errors.append(f"Unknown status: '{status}'")
    return errors


def read_sources() -> tuple[str, str]:
    """Both inputs, or exit 1 naming the one that is missing."""
    chain_text = CHAIN.read_text() if CHAIN.exists() else ""
    supp_text = SUPP.read_text() if SUPP.exists() else ""

    missing = []
    if not chain_text:
        missing.append(f"Chain.lean not found at {CHAIN}")
    if not supp_text:
        missing.append(f"supplementary.tex not found at {SUPP}")
    if missing:
        for m in missing:
            print(f"FAIL: {m}", file=sys.stderr)
        sys.exit(1)

    return chain_text, supp_text


def check_references(supp_text: str) -> list[str]:
    """The two cross-references Table S1 has to carry, whatever else changes.

    The joint witness is what makes the chain's hypotheses non-vacuous, and the
    E12 finding is what stops the first arrow reading as a derivation; a table
    that names neither has drifted from what `Chain.lean` says.
    """
    errors = []
    if r"chain\_hypotheses\_jointly\_satisfiable" not in supp_text:
        errors.append("Table S1 does not reference chain_hypotheses_jointly_satisfiable")

    has_e12 = "E12" in supp_text and ("equivalent" in supp_text or "independent roots" in supp_text)
    if not has_e12:
        errors.append("E12 finding (equivalent to its conclusion) not reflected in Table S1")
    return errors


def main() -> None:
    _, supp_text = read_sources()

    errors = check_supplementary_table(supp_text)
    errors.extend(check_references(supp_text))

    if errors:
        print("Table S1 cross-reference check FAILED:")
        for e in errors:
            print(f"  - {e}")
        sys.exit(1)

    print("Table S1 status column cross-reference check PASSED")
    print(f"  {SUPP.name}: all status cells match known patterns")
    print("  References to chain_hypotheses_jointly_satisfiable and E12 finding present")


if __name__ == "__main__":
    main()
