"""The per-window link of the occupancy test at every window length (U94).

``unity_occupancy.py`` asks whether some carrier of a region enters a passing
state within a window of a content's time scale, at two windows: the
integration time that precedes a conscious percept and a tenth of it. Both are
tied to one estimate of that time. This module sweeps the window independently
of it, from one time step up to a second, and reports where the membrane stops
linking two regions.

For each declared regime and noise share the chance ``h(W)`` that one
stationary carrier occupies a passing state at some step of a window ``W`` is
propagated once, step by step, on the chain of ``unity_occupancy``, so every
window up to the longest comes from the same pass. ``K`` independent carriers
link two regions within ``W`` with probability ``1 − (1 − h(W))^K``. The
membrane links a pair within ``W`` when that probability reaches ``LEVEL`` in
every regime and at every noise share; since ``h`` grows with ``W``, it then
links within every longer window, so the shortest such window is the lower end
of the range over which the separation from the value a latch reads holds. The
latched value passes at no state, so it links in no window of any length.

Declared: the level is one half, a link more often than not. The shortest
window a content can have is taken from the temporal-order threshold, the
shortest interval at which two events are perceived in order, about 20 ms in
every modality tested:

  Hirsh & Sherrick 1961, J Exp Psychol 62:423-432

A run at half the grid step and half the time step, up to ``CHECK_MS``, is
saved beside the result: finer resolution moves every lower end earlier, so the
coarse ends are the conservative ones. Independent carriers only;
``unity_correlated.py`` treats shared input at the two windows of the occupancy
summary. ``window.json`` is written beside the occupancy summaries, and
``unity_macros.py`` reads it.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np
from numpy.typing import NDArray

from unity_occupancy import (
    CHANGE_SCALES,
    INDEPENDENT_CARRIERS,
    RATES_HZ,
    REFRACTORY_MS,
    TAUS_MS,
    WINDOWS_MS,
    Grid,
    Membrane,
    _chain,
    _stationary_mass,
    calibrate,
    laws,
    link_probability,
    passing_states,
)

FloatArray = NDArray[np.float64]

OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_occupancy"

# A link more often than not.
LEVEL = 0.5
# The temporal-order threshold (Hirsh & Sherrick 1961).
PERCEPT_LOW_MS = 20.0
LONGEST_MS = 1000.0
# The resolution check halves the grid and the time step up to this window.
CHECK_MS = 100.0
# Windows at which the curves are saved; the lower ends use every step.
SAVED_MS = (0.5, 1, 2, 3, 5, 7, 10, 15, 20, 30, 40, 50, 70, 100, 150, 200, 300, 400, 700, 1000)


def hit_curve(
    grid: Grid, membrane: Membrane, passing: NDArray[np.bool_], steps: int, dt_ms: float
) -> FloatArray:
    """Chance of occupying a passing state within ``k`` steps, for ``k = 0 … steps``."""
    step, _ = _chain(grid, membrane, dt_ms)
    target = np.zeros(step.shape[0], dtype=bool)
    target[: grid.nodes.size] = passing
    mass = _stationary_mass(step)
    curve = np.empty(steps + 1)
    hit = float(mass[target].sum())
    mass[target] = 0.0
    curve[0] = hit
    for k in range(1, steps + 1):
        mass = step @ mass
        hit += float(mass[target].sum())
        mass[target] = 0.0
        curve[k] = hit
    return np.minimum(curve, 1.0)


def lower_end_ms(curves: FloatArray, carriers: int, level: float, dt_ms: float) -> float | None:
    """The shortest window within which ``carriers`` link in every curve, or ``None``."""
    worst = 1.0 - (1.0 - curves.min(axis=0)) ** carriers
    reached = np.flatnonzero(worst >= level)
    return None if reached.size == 0 else float(reached[0] * dt_ms)


def _curves(grid: Grid, dt_ms: float, steps: int) -> list[dict[str, Any]]:
    rows = []
    for tau in TAUS_MS:
        for rate in RATES_HZ:
            membrane = calibrate(grid, tau, REFRACTORY_MS, rate, dt_ms)
            for window in WINDOWS_MS:
                table = laws(grid, membrane, window, dt_ms)
                for scale in CHANGE_SCALES:
                    passing = passing_states(table, grid, scale)
                    curve = hit_curve(grid, membrane, passing, steps, dt_ms)
                    config = {
                        "tau_ms": tau,
                        "rate_hz": rate,
                        "window_ms": window,
                        "share": scale**2,
                    }
                    rows.append({"config": config, "curve": curve})
    return rows


def run(grid: Grid, dt_ms: float, max_ms: float = LONGEST_MS) -> dict[str, Any]:
    """Every regime and share, swept over windows up to ``max_ms``."""
    steps = round(max_ms / dt_ms)
    rows = _curves(grid, dt_ms, steps)
    curves = np.array([r["curve"] for r in rows])
    saved = [w for w in SAVED_MS if w <= max_ms]
    at = {f"{w:g}": round(w / dt_ms) for w in saved}
    percept = round(PERCEPT_LOW_MS / dt_ms)
    return {
        "level": LEVEL,
        "percept_low_ms": PERCEPT_LOW_MS,
        "dt_ms": dt_ms,
        "longest_ms": max_ms,
        "carriers": list(INDEPENDENT_CARRIERS),
        "lower_end_ms": {
            f"{k}": lower_end_ms(curves, k, LEVEL, dt_ms) for k in INDEPENDENT_CARRIERS
        },
        "least_link_at_percept_low": {
            f"{k}": link_probability(float(curves[:, min(percept, steps)].min()), k)
            for k in INDEPENDENT_CARRIERS
        },
        "curves": [
            {"config": r["config"], "hit": {w: float(r["curve"][k]) for w, k in at.items()}}
            for r in rows
        ],
    }


def write(directory: Path, grid: Grid, dt_ms: float, max_ms: float = LONGEST_MS) -> None:
    """Save the sweep; publication macros read it later."""
    directory.mkdir(parents=True, exist_ok=True)
    swept = run(grid, dt_ms, max_ms)
    fine = run(Grid(grid.low, grid.step / 2), dt_ms / 2, min(max_ms, CHECK_MS))
    swept["resolution_check"] = {
        "longest_ms": fine["longest_ms"],
        "lower_end_ms": fine["lower_end_ms"],
    }
    (directory / "window.json").write_text(json.dumps(swept, indent=2) + "\n")


def main() -> None:
    """Run the declared sweep at the occupancy summary's resolution."""
    parser = argparse.ArgumentParser(description="Per-window link at every window length")
    parser.add_argument("--step", type=float, default=0.05)
    parser.add_argument("--low", type=float, default=-8.0)
    parser.add_argument("--dt-ms", type=float, default=0.1)
    args = parser.parse_args()
    write(OUTPUT, Grid(args.low, args.step), args.dt_ms)


if __name__ == "__main__":
    main()
