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

125 tests, no production sweep among them; they exercise the estimators,
analysis and report generators on small fixtures and run in about a minute and a
half.

## Repository gates

These run under `pre-commit` (see `.pre-commit-config.yaml` at the repository
root) and can each be run directly from this directory:

| Script | What it enforces |
| :--- | :--- |
| `check_prose.py` | The publication is not a changelog: no sentence in `main.tex` or `supplementary.tex` may ask the reader to remember a draft they have never seen. Fails the commit. |
| `check_hedging.py` | Reports disclaimer and reader-instruction density. Advisory — it always passes, because whether a hedge earns its place is a judgement about its paragraph. |
| `check_tableS1.py` | Supplement Table S1's status column still matches `Chain.lean`. |
| `check_leaves.py` | Every Lean phase module has at least one theorem consumed outside itself and the `Examples/` witnesses. |
| `check_pdf_freshness.py` | The tracked PDFs are no older than the sources they are built from, since `README.md` and `index.html` link them directly. |

The Python quality gates — `ruff`, `mypy`, `bandit`, `vulture`, `xenon`, `tach`
— are configured in `pyproject.toml` and `tach.toml` and also run under
`pre-commit`.

`tach.toml` declares each file here as a module and sorts them into six layers,
so the architecture is enforced without a directory tree to carry it. Two of the
layer rules are the reason it exists, and each restates a rule this repository
already had in prose:

* **No gate imports a simulation.** `gate` is the bottom layer. A gate runs on
  every commit, and one that reached a sweep module would put an integration in
  the commit path.
* **Nothing imports `simulation_tex`.** It is the top layer, so the macro
  generator is a sink: regenerating publication macros never reruns a production
  sweep (`AGENTS.md` section 3).

`exact = true`, so an import no rule permits fails the commit and so does a rule
no import uses — the file cannot drift from the code in either direction.

## Data

The exploratory EEG analysis uses OpenNeuro dataset
[ds005620](https://openneuro.org/datasets/ds005620). Recordings are cached to
`cache_ds005620/`, which is git-ignored: this repository carries the analysis,
not the raw human recordings, and does not redistribute them.

## Outputs

Everything a run writes under `figures/` is tracked — the `.npz` checkpoints as
well as the `summary.json`, the `REPORT.md` and the figures built from them. The
checkpoints are what `simulation_tex.py` reads to generate the publication
macros, so a summary without the run behind it would leave a quoted number with
nothing to recompute it from. The cost is a repository that grows by the size of
each sweep; that is the trade this project makes deliberately, and it is why the
EEG cache above is the one output that is *not* tracked.

Where a sweep has a matching report module — `dynamic_ramp`,
`structural_resonance`, `geometric_frustration` — the sweep writes only data,
and the figures and the `REPORT.md` are built afterwards from the saved
`.npz` and `summary.json` by a second command that integrates nothing. A lost or
restyled figure then costs a second of plotting rather than the sweep behind it.
`tach.toml` enforces the direction: `report` sits above `simulation`, so a
report reads a sweep's paths and constants and a sweep cannot call a report.
The remaining runs carry no report module and plot inline as they finish.

The practical consequence is that `git status` is the record of whether a sweep
finished. A run that leaves untracked files under `figures/` is a run whose
artifacts have not been committed yet, not a run whose artifacts do not belong.

Output paths are addressed from the module file, never from the working
directory:

```python
FIGURES = Path(__file__).resolve().parent / "figures"
```

A path relative to the working directory fails silently rather than loudly — a
sweep started from anywhere but this directory writes a fresh, empty `figures/`
tree beside itself, and the report generator that reads the real one afterwards
finds nothing, or finds last week's run.
