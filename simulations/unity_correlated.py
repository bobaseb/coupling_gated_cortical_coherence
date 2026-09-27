"""Carriers that share part of their input: the window bound without independence (U47).

The window bound of ``unity_occupancy`` treats the carriers joining two regions
as independent, so that none of ``K`` passes within a window with probability
``(1 − h)^K``. The carriers joining region ``a`` to region ``b`` are cells of
``b`` that receive from ``a``, and neighbouring membranes share input. This
script replaces independence with a shared input of declared size.

Each membrane is ``V_i = S + P_i``: ``S`` an Ornstein-Uhlenbeck process of
variance ``c`` common to every carrier, ``P_i`` a private one of variance
``1 − c``, both with the membrane's time constant, so every carrier's own law is
the one ``unity_occupancy`` computes and the correlation of two membranes is
``c``. Given the path of ``S`` the carriers are independent, so

    P(no carrier passes) = E_S[(1 − h_S)^K],

where ``h_S`` is the chance that one carrier enters a passing state within the
window given that path, and two carriers pass together with correlation
``ρ = Var(h_S) / (h̄(1 − h̄))``. Passing states are those of the marginal carrier.

For each of ``M`` sampled shared paths the membrane's probability is propagated
on the voltage grid through the exact Ornstein-Uhlenbeck step with the private
part of the noise, its centre moved by the shared path's increment
``S(t + dt) − S(t) e^{−dt/τ}`` rounded to a quarter of the grid step. A crossing
between samples is counted with the Brownian-bridge probability of the whole
spread, exact at ``c = 0`` and an approximation of order ``dt`` otherwise; a run
at half the grid step and half the time step is saved as its check. Each path
starts from the stationary law and runs a burn-in of several
time constants before the window opens. The paths are drawn from a fixed seed,
and the standard error over paths is reported.

Scope: one shared component, with the membrane's own time constant; a declared
share, not a fit. No theorem, and no recording.
"""

from __future__ import annotations

import argparse
import json
import math
from typing import Any

import numpy as np
from numpy.typing import NDArray

from unity_occupancy import (
    CHANGE_SCALES,
    CONTENT_WINDOWS_MS,
    OUTPUT,
    RATES_HZ,
    REFRACTORY_MS,
    TAUS_MS,
    WINDOWS_MS,
    Grid,
    Membrane,
    NeuronConfig,
    _chain,
    _stationary_mass,
    calibrate,
    laws,
    passing_states,
)

FloatArray = NDArray[np.float64]

SHARES = (0.0, 0.1, 0.25, 0.5, 0.75, 0.9)
CARRIERS = (10, 100, 1000, 10000)
PATHS = 256
SEED = 20260927
BURN_IN_TAUS = 5.0
# The shared increment is applied inside the exact step, rounded to this many
# quanta per grid step, so that no interpolation adds variance of its own.
QUANTA_PER_STEP = 4
# The share tolerated is the largest at which K carriers still link two regions
# within the longer content window with this probability.
LINK_TARGET = 0.9
LINK_CARRIERS = 100


def shared_paths(
    rng: np.random.Generator, share: float, tau_ms: float, dt_ms: float, steps: int, count: int
) -> FloatArray:
    """``count`` stationary Ornstein-Uhlenbeck paths of variance ``share``, one per column."""
    decay = math.exp(-dt_ms / tau_ms)
    innovation = math.sqrt(share * (1.0 - decay**2))
    path = np.empty((steps + 1, count))
    path[0] = math.sqrt(share) * rng.standard_normal(count)
    noise = rng.standard_normal((steps, count))
    for t in range(steps):
        path[t + 1] = path[t] * decay + innovation * noise[t]
    return path


class _Kernels:
    """Chains whose centres move by one quantum of the shared increment, built on demand."""

    def __init__(self, grid: Grid, membrane: Membrane, dt_ms: float, share: float) -> None:
        self.grid, self.membrane, self.dt_ms, self.share = grid, membrane, dt_ms, share
        self.quantum = grid.step / QUANTA_PER_STEP
        self.cache: dict[int, FloatArray] = {}

    def advance(self, mass: FloatArray, increment: FloatArray) -> FloatArray:
        """One step of every column, column ``m`` shifted by ``increment[m]``."""
        bins = np.rint(increment / self.quantum).astype(np.int64)
        advanced = np.empty_like(mass)
        for b in np.unique(bins).tolist():
            if b not in self.cache:
                offset = b * self.quantum
                self.cache[b] = _chain(self.grid, self.membrane, self.dt_ms, self.share, offset)[0]
            columns = bins == b
            advanced[:, columns] = self.cache[b] @ mass[:, columns]
        return advanced


def correlated_hits(
    grid: Grid,
    membrane: Membrane,
    passing: NDArray[np.bool_],
    share: float,
    windows_ms: tuple[float, ...],
    dt_ms: float,
    paths: int,
    seed: int,
) -> dict[str, FloatArray]:
    """Per window, the chance ``h_S`` that one carrier passes within it, for each shared path."""
    kernels = _Kernels(grid, membrane, dt_ms, share)
    stationary = _stationary_mass(_chain(grid, membrane, dt_ms)[0])
    target = np.zeros(stationary.size, dtype=bool)
    target[: grid.nodes.size] = passing
    burn = round(BURN_IN_TAUS * membrane.tau_ms / dt_ms) if share > 0 else 0
    records = {round(w / dt_ms): f"{w:g}" for w in windows_ms}
    steps = max(records)
    shared = shared_paths(
        np.random.default_rng(seed), share, membrane.tau_ms, dt_ms, burn + steps, paths
    )
    decay = math.exp(-dt_ms / membrane.tau_ms)
    mass = np.repeat(stationary[:, None], paths, axis=1)
    hit = np.zeros(paths)
    found: dict[str, FloatArray] = {}
    for t in range(burn + steps + 1):
        if t >= burn:
            hit += mass[target].sum(axis=0)
            mass[target] = 0.0
            if t - burn in records:
                found[records[t - burn]] = np.minimum(hit, 1.0)
        if t < burn + steps:
            mass = kernels.advance(mass, shared[t + 1] - shared[t] * decay)
    return found


def pair_correlation(hits: FloatArray) -> float:
    """Correlation of two carriers' passing: ``Var(h_S) / (h̄(1 − h̄))``."""
    mean = float(hits.mean())
    if not 0.0 < mean < 1.0:
        return 0.0
    return float(hits.var()) / (mean * (1.0 - mean))


def no_link(hits: FloatArray, carriers: int) -> dict[str, float]:
    """Chance that none of ``carriers`` passes, ``E_S[(1 − h_S)^K]``, and its standard error."""
    values = (1.0 - hits) ** carriers
    error = float(values.std(ddof=1)) / math.sqrt(values.size) if values.size > 1 else 0.0
    return {"probability": float(values.mean()), "standard_error": error}


def largest_share(links: dict[str, float], target: float) -> float | None:
    """The largest share up to which every link probability reaches ``target``."""
    tolerated = None
    for share in sorted(links, key=float):
        if links[share] < target:
            break
        tolerated = float(share)
    return tolerated


def _share_row(hits: FloatArray) -> dict[str, Any]:
    return {
        "hit_mean": float(hits.mean()),
        "pair_correlation": pair_correlation(hits),
        "no_link": {f"{k}": no_link(hits, k) for k in CARRIERS},
    }


def _scale_rows(
    grid: Grid, membrane: Membrane, passing: NDArray[np.bool_], dt_ms: float, paths: int
) -> dict[str, dict[str, Any]]:
    """Every declared share, both content windows, from the same seed."""
    rows = {}
    for share in SHARES:
        hits = correlated_hits(
            grid, membrane, passing, share, CONTENT_WINDOWS_MS, dt_ms, paths, SEED
        )
        rows[f"{share:g}"] = {w: _share_row(h) for w, h in hits.items()}
    return rows


def _tolerated(rows: dict[str, dict[str, Any]]) -> float | None:
    window = f"{max(CONTENT_WINDOWS_MS):g}"
    links = {
        share: 1.0 - per[window]["no_link"][f"{LINK_CARRIERS}"]["probability"]
        for share, per in rows.items()
    }
    return largest_share(links, LINK_TARGET)


def correlated_summary(
    grid: Grid, config: NeuronConfig, dt_ms: float, paths: int, scales: tuple[float, ...]
) -> dict[str, Any]:
    """One regime: every share, noise share of the change and content window."""
    membrane = calibrate(grid, config.tau_ms, REFRACTORY_MS, config.rate_hz, dt_ms)
    table = laws(grid, membrane, config.window_ms, dt_ms)
    by_scale = {
        f"{c:g}": _scale_rows(grid, membrane, passing_states(table, grid, c), dt_ms, paths)
        for c in scales
    }
    return {
        "config": {
            "tau_ms": config.tau_ms,
            "rate_hz": config.rate_hz,
            "window_ms": config.window_ms,
        },
        "by_scale": by_scale,
        "largest_share": {scale: _tolerated(rows) for scale, rows in by_scale.items()},
    }


def run(grid: Grid, dt_ms: float, paths: int) -> dict[str, Any]:
    """Every declared regime, and the resolution check."""
    check = NeuronConfig(TAUS_MS[0], RATES_HZ[1], WINDOWS_MS[0])
    fine = Grid(grid.low, grid.step / 2)
    return {
        "shares": list(SHARES),
        "carriers": list(CARRIERS),
        "paths": paths,
        "seed": SEED,
        "grid": {"low": grid.low, "step": grid.step},
        "dt_ms": dt_ms,
        "link_target": LINK_TARGET,
        "link_carriers": LINK_CARRIERS,
        "neurons": [
            correlated_summary(grid, NeuronConfig(tau, rate, window), dt_ms, paths, CHANGE_SCALES)
            for tau in TAUS_MS
            for rate in RATES_HZ
            for window in WINDOWS_MS
        ],
        "resolution_check": {
            "coarse": correlated_summary(grid, check, dt_ms, paths, (1.0,)),
            "fine": correlated_summary(fine, check, dt_ms / 2, paths, (1.0,)),
        },
    }


def main() -> None:
    """Run the declared sweep and save its summary; publication macros read it later."""
    parser = argparse.ArgumentParser(description="Carriers sharing part of their input")
    parser.add_argument("--step", type=float, default=0.05)
    parser.add_argument("--low", type=float, default=-8.0)
    parser.add_argument("--dt-ms", type=float, default=0.1)
    parser.add_argument("--paths", type=int, default=PATHS)
    args = parser.parse_args()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    summary = run(Grid(args.low, args.step), args.dt_ms, args.paths)
    (OUTPUT / "correlated.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
