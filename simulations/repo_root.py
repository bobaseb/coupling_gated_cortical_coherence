#!/usr/bin/env python3
"""The repository root, found by walking up rather than by counting directories.

Every gate and every sweep that reads a tracked document needs the repository
root, and the obvious spelling for it is ``Path(__file__).parent.parent``. That
spelling is a hidden assertion that this file sits exactly one directory below
the root, and mutation testing breaks it: ``mutmut`` copies this whole directory
into ``simulations/mutants/`` and runs the suite from there, so every module
under test is suddenly two levels down and every such path silently resolves to
``simulations/`` instead. The failures that follow look like missing documents,
not like a relocated tree.

Walking up to the nearest directory that holds ``main.tex`` is the same answer
wherever the file is copied to, so the copy needs no special case. ``main.tex``
is the marker because it is the publication this repository is built around: it
is tracked, it sits only at the root, and a checkout without it is not one any
gate here has anything to say about.
"""

from __future__ import annotations

from pathlib import Path

MARKER = "main.tex"


def find_repo_root(start: Path | None = None) -> Path:
    """Return the nearest ancestor of ``start`` that holds ``main.tex``."""
    origin = (start or Path(__file__)).resolve()
    for candidate in (origin, *origin.parents):
        if (candidate / MARKER).is_file():
            return candidate
    raise FileNotFoundError(f"no ancestor of {origin} holds {MARKER}")


REPO = find_repo_root()
