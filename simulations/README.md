# Simulations, analysis and repository gates

Python supporting `main.tex` and `supplementary.tex`: the numerical controls
reported in the manuscript, the exploratory EEG analysis, and the check scripts
that keep the two documents honest.

Published numbers are **not** recomputed at build time. Each simulation writes a
saved summary, and `simulation_tex.py` turns those summaries into the LaTeX
macros that `simulation_results.tex` and `fermi_params.tex` define. The
manuscript reads only those macros, so a figure or a quoted value cannot drift
from the run that produced it, and rebuilding the PDFs does not require
rerunning a production sweep.

## Setup

Dependencies are managed with [uv](https://docs.astral.sh/uv/).

```bash
cd simulations
uv sync --group dev
```

## Tests

```bash
uv run pytest
```

80 tests, no production sweep among them; they exercise the estimators,
analysis and report generators on small fixtures and run in well under a minute.

## Repository gates

These run under `pre-commit` (see `.pre-commit-config.yaml` at the repository
root) and can each be run directly from this directory:

| Script | What it enforces |
| :--- | :--- |
| `check_prose.py` | The publication is not a changelog: no sentence in `main.tex` or `supplementary.tex` may ask the reader to remember a draft they have never seen. Fails the commit. |
| `check_hedging.py` | Reports disclaimer and reader-instruction density. Advisory — it always passes, because whether a hedge earns its place is a judgement about its paragraph. |
| `check_tableS1.py` | Supplement Table S1's status column still matches `Chain.lean`. |
| `check_leaves.py` | Every Lean phase module has at least one theorem consumed outside itself and `Examples.lean`. |
| `check_pdf_freshness.py` | The tracked PDFs are no older than the sources they are built from, since `README.md` and `index.html` link them directly. |

The Python quality gates — `ruff`, `mypy`, `bandit`, `vulture`, `xenon`, `tach`
— are configured in `pyproject.toml` and `tach.toml` and also run under
`pre-commit`.

## Data

The exploratory EEG analysis uses OpenNeuro dataset
[ds005620](https://openneuro.org/datasets/ds005620). Recordings are cached to
`cache_ds005620/`, which is git-ignored: this repository carries the analysis,
not the raw human recordings, and does not redistribute them.
