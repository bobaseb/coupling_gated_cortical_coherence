"""The noise-floor test of a carrier, weighted by the states it occupies (U36).

The paper's criterion asks every change of a carrier larger than its own noise,
and smaller than the change that crosses its threshold, to move the next content
by at least the fluctuation ``θ* = 2Φ(1/2) − 1``. A single estimate evaluates it
at one state: a spike time at the moment the membrane rises through threshold,
or a bit between thresholds. This script evaluates it at every state a carrier
occupies, weighted by how often it occupies it, under one protocol for both.

The membrane is a leaky integrate-and-fire cell in the fluctuation-driven regime:
between spikes an Ornstein-Uhlenbeck process of time constant ``τ`` and
stationary standard deviation one, the unit of every voltage here, with the
threshold at zero. After a spike it is refractory, then reset to its mean. The
mean is calibrated so that the stationary rate equals a declared rate. The next
content is the time of the first spike within a window, or its absence; the
response at a state is the total variation between its laws from the state and
from the state moved by a change. Coarser contents, the same time read through a
clock of a declared period, are functions of it, so they respond no more.

The bit is a carrier restored each step to a rail ``M`` noise amplitudes from
its threshold, read after one step of unit Gaussian noise. Its occupancy is the
rail plus that noise.

Everything is computed on a voltage grid by propagating probability exactly:
the transition is the exact Ornstein-Uhlenbeck step, and a crossing between two
sampled times is counted with the Brownian-bridge probability
``exp(−2 x y / s²)``. Nothing is sampled, so there is no seed. Voltages below
the grid's floor are lumped into its lowest node; the floor sits far below the
occupied range. A run at half the grid step and half the time step is saved
beside the result, as its resolution check. ``--yardstick`` repeats the test at
other yardsticks in place of ``θ*`` and writes ``yardstick.json`` beside it
(U49), leaving the main summary untouched.

Declared parameters, not measured ones: the time constant spans the in vivo
high-conductance value, about fivefold below the quiescent one (Destexhe & Paré
1999, J Neurophysiol 81:1531-1547; Destexhe, Rudolph & Paré 2003, Nat Rev
Neurosci 4:739-751); rates span the sparse, lognormally distributed rates of
awake cortex (Hromádka, DeWeese & Zador 2008, PLoS Biol 6:e16); the window
spans one to a few membrane time constants. A refractory state counts as failing.

Scope: one cell, white-noise drive, a threshold without its own dynamics. No
theorem, and no recording.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import numpy as np
from numpy.typing import NDArray
from scipy.special import ndtr

from unity_estimates import CONTENT_TIME_S, FLUCTUATION_TV, log10_gaussian_tail, noise_floor

FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_occupancy"

# Changes, in noise amplitudes, at which "every change above the noise" is checked.
SHIFTS = (1.0, 2.0, 3.0)
# A region's afferent drive onto a cell supplies a fraction φ of the cell's
# membrane variance, so one noise amplitude of that carrier is √φ in the cell's
# units: φ = 1/16, 1/4, 1.
CHANGE_SCALES = (0.25, 0.5, 1.0)
# Effectively independent carriers joining two regions, declared: membrane
# potentials of nearby cells are correlated, so fewer than the anatomical count.
INDEPENDENT_CARRIERS = (10, 100, 1000)
# P asks for a passing carrier within each content window: a tenth of the
# integration time that precedes a conscious percept, and all of it.
CONTENT_WINDOWS_MS = (100.0 * CONTENT_TIME_S, 1000.0 * CONTENT_TIME_S)
REFRACTORY_MS = 2.0
TAUS_MS = (5.0, 20.0)
RATES_HZ = (0.5, 2.0, 8.0)
WINDOWS_MS = (10.0, 30.0)
LATCH_PERIODS_MS = (1.0, 5.0)
BIT_MARGINS = (0.5, 1.0, 2.0, 4.0)
# Occupied states of a bit: its rail plus this many noise amplitudes either side.
BIT_SPAN = 8.0
# Yardsticks at which the separation is rechecked (U49), from a hundredth of a
# probability to above the fluctuation.
YARDSTICKS = (0.01, 0.1, 0.2, 0.3, FLUCTUATION_TV, 0.45, 0.5, 0.6)


@dataclass(frozen=True)
class Grid:
    """Voltage nodes ``low, low + step, …`` strictly below the threshold at zero."""

    low: float
    step: float

    @property
    def nodes(self) -> FloatArray:
        count = round(-self.low / self.step)
        return self.low + self.step * np.arange(count, dtype=np.float64)

    def index(self, voltage: float) -> int:
        k = round((voltage - self.low) / self.step)
        if not 0 <= k < self.nodes.size or abs(self.nodes[k] - voltage) > 1e-9:
            raise ValueError(f"{voltage} is not a node below threshold")
        return k


@dataclass(frozen=True)
class Membrane:
    """An integrate-and-fire membrane in units of its own noise amplitude."""

    tau_ms: float
    mean: float
    reset: float
    refractory_ms: float


@dataclass(frozen=True)
class NeuronConfig:
    """One declared regime: time constant, stationary rate, content window."""

    tau_ms: float
    rate_hz: float
    window_ms: float


def _step(
    grid: Grid, membrane: Membrane, dt_ms: float, share: float = 0.0, offset: float = 0.0
) -> tuple[FloatArray, FloatArray]:
    """Surviving transition ``T[j, i]`` from node ``i`` to ``j``, and each node's spike mass.

    With ``share > 0`` the step carries only the private part of the noise, a
    fraction ``1 − share`` of its variance, and the shared part's increment
    moves every centre by ``offset`` (``unity_correlated``). A crossing between
    samples is still counted with the whole spread, since neither part is
    observed between them.
    """
    v = grid.nodes
    decay = math.exp(-dt_ms / membrane.tau_ms)
    spread = math.sqrt(1.0 - decay**2)
    centre = membrane.mean + (v - membrane.mean) * decay + offset
    upper = np.append(v[:-1] + grid.step / 2, 0.0)
    private = spread * math.sqrt(1.0 - share)
    cumulative = ndtr((upper[:, None] - centre[None, :]) / private)
    cell = np.diff(np.vstack([np.zeros_like(centre), cumulative]), axis=0)
    # A path between two sub-threshold samples may still have crossed.
    bridge = np.exp(-2.0 * np.outer(v, v) / spread**2)
    surviving = cell * (1.0 - bridge)
    return surviving, 1.0 - surviving.sum(axis=0)


def laws(grid: Grid, membrane: Membrane, window_ms: float, dt_ms: float) -> FloatArray:
    """Column ``i``: spike mass at each step of the window from node ``i``, then survival."""
    surviving, spiking = _step(grid, membrane, dt_ms)
    mass = np.eye(grid.nodes.size)
    rows = []
    for _ in range(round(window_ms / dt_ms)):
        rows.append(spiking @ mass)
        mass = surviving @ mass
    rows.append(mass.sum(axis=0))
    return np.vstack(rows)


def first_passage_law(
    grid: Grid, membrane: Membrane, start: float, window_ms: float, dt_ms: float
) -> FloatArray:
    """The law of the first spike time in the window, or of its absence."""
    return laws(grid, membrane, window_ms, dt_ms)[:, grid.index(start)]


def latch(law: FloatArray, dt_ms: float, period_ms: float) -> FloatArray:
    """The same law read through a clock: spike times binned to the period."""
    per_bin = round(period_ms / dt_ms)
    spikes = law[:-1]
    bins = [spikes[k : k + per_bin].sum() for k in range(0, spikes.size, per_bin)]
    return np.append(np.array(bins), law[-1])


def _tv(first: FloatArray, second: FloatArray) -> float:
    return float(0.5 * np.abs(first - second).sum())


def response(
    grid: Grid,
    membrane: Membrane,
    start: float,
    shift: float,
    window_ms: float,
    dt_ms: float,
    period_ms: float | None = None,
) -> float:
    """Total variation a change ``shift`` toward threshold makes to the next content."""
    if shift == 0.0:
        return 0.0
    table = laws(grid, membrane, window_ms, dt_ms)
    pair = [table[:, grid.index(v)] for v in (start, start + shift)]
    if period_ms is not None:
        pair = [latch(law, dt_ms, period_ms) for law in pair]
    return _tv(*pair)


def _reset_mass(grid: Grid, voltage: float) -> FloatArray:
    """A reset between two nodes, split linearly so the rate is continuous in it."""
    position = (voltage - grid.low) / grid.step
    k = min(max(int(math.floor(position)), 0), grid.nodes.size - 2)
    upper = min(max(position - k, 0.0), 1.0)
    mass = np.zeros(grid.nodes.size)
    mass[k], mass[k + 1] = 1.0 - upper, upper
    return mass


def _chain(
    grid: Grid, membrane: Membrane, dt_ms: float, share: float = 0.0, offset: float = 0.0
) -> tuple[FloatArray, FloatArray]:
    """One time step over the nodes then the refractory stages, and each node's spike mass."""
    surviving, spiking = _step(grid, membrane, dt_ms, share, offset)
    n, stages = grid.nodes.size, max(1, round(membrane.refractory_ms / dt_ms))
    chain = np.zeros((n + stages, n + stages))
    chain[:n, :n] = surviving
    chain[n, :n] = spiking
    for k in range(stages - 1):
        chain[n + k + 1, n + k] = 1.0
    chain[:n, n + stages - 1] = _reset_mass(grid, membrane.reset)
    return chain, spiking


def _stationary_mass(chain: FloatArray) -> FloatArray:
    system = chain - np.eye(chain.shape[0])
    system[-1, :] = 1.0
    target = np.zeros(chain.shape[0])
    target[-1] = 1.0
    return np.clip(np.linalg.solve(system, target), 0.0, None)


def stationary(grid: Grid, membrane: Membrane, dt_ms: float) -> tuple[FloatArray, float, float]:
    """Stationary mass on the nodes, the refractory mass, and the rate in Hz."""
    chain, spiking = _chain(grid, membrane, dt_ms)
    mass = _stationary_mass(chain)
    n = grid.nodes.size
    density = mass[:n]
    return density, float(mass[n:].sum()), float(spiking @ density) * 1000.0 / dt_ms


def hit_probability(
    grid: Grid, membrane: Membrane, passing: NDArray[np.bool_], window_ms: float, dt_ms: float
) -> float:
    """Chance that a stationary carrier occupies a passing state at some step of the window."""
    chain, _ = _chain(grid, membrane, dt_ms)
    target = np.zeros(chain.shape[0], dtype=bool)
    target[: grid.nodes.size] = passing
    mass = _stationary_mass(chain)
    hit = float(mass[target].sum())
    mass[target] = 0.0
    for _ in range(round(window_ms / dt_ms)):
        mass = chain @ mass
        hit += float(mass[target].sum())
        mass[target] = 0.0
    return min(hit, 1.0)


def calibrate(
    grid: Grid, tau_ms: float, refractory_ms: float, rate_hz: float, dt_ms: float
) -> Membrane:
    """The membrane, reset to its mean, whose stationary rate is ``rate_hz``."""
    low, high = grid.low / 2, -grid.step
    for _ in range(50):
        mean = (low + high) / 2
        if stationary(grid, Membrane(tau_ms, mean, mean, refractory_ms), dt_ms)[2] < rate_hz:
            low = mean
        else:
            high = mean
    mean = (low + high) / 2
    return Membrane(tau_ms, mean, mean, refractory_ms)


def _least_response(table: FloatArray, grid: Grid, node: int, scale: float) -> float | None:
    """The smallest response over every admissible change of the state at ``node``."""
    offsets = [round(scale * s / grid.step) for s in SHIFTS]
    targets = [node + k for k in offsets] + [node - k for k in offsets]
    admissible = [t for t in targets if 0 <= t < grid.nodes.size]
    if not admissible:
        return None
    return min(_tv(table[:, node], table[:, t]) for t in admissible)


def passing_states(
    table: FloatArray, grid: Grid, scale: float, yardstick: float = FLUCTUATION_TV
) -> NDArray[np.bool_]:
    """The nodes at which every admissible change moves the next content by ``yardstick``."""
    least = [_least_response(table, grid, node, scale) for node in range(grid.nodes.size)]
    return np.array([r is not None and r >= yardstick for r in least])


def _occupancy_pass(
    table: FloatArray, grid: Grid, density: FloatArray, scale: float = 1.0
) -> tuple[float, float]:
    """Mass of occupied states passing the criterion, and the mean least response."""
    passing = mean = 0.0
    for node, weight in enumerate(density):
        least = _least_response(table, grid, node, scale)
        if least is not None:
            passing += weight * (least >= FLUCTUATION_TV)
            mean += weight * least
    return passing, mean


def _latched_table(table: FloatArray, dt_ms: float, period_ms: float) -> FloatArray:
    return np.column_stack([latch(table[:, i], dt_ms, period_ms) for i in range(table.shape[1])])


def neuron_summary(
    grid: Grid, config: NeuronConfig, dt_ms: float, periods_ms: tuple[float, ...]
) -> dict[str, Any]:
    """Occupancy, and the fraction of occupied states that pass, for one regime."""
    membrane = calibrate(grid, config.tau_ms, REFRACTORY_MS, config.rate_hz, dt_ms)
    density, refractory, rate = stationary(grid, membrane, dt_ms)
    table = laws(grid, membrane, config.window_ms, dt_ms)
    passing, mean_response = _occupancy_pass(table, grid, density)
    latched = {
        f"{period:g}": _occupancy_pass(_latched_table(table, dt_ms, period), grid, density)[0]
        for period in periods_ms
    }
    by_scale = {f"{c:g}": _occupancy_pass(table, grid, density, c)[0] for c in CHANGE_SCALES}
    hits = {
        f"{c:g}": {
            f"{w:g}": hit_probability(grid, membrane, passing_states(table, grid, c), w, dt_ms)
            for w in CONTENT_WINDOWS_MS
        }
        for c in CHANGE_SCALES
    }
    return {
        "config": asdict(config),
        "mean": membrane.mean,
        "rate_hz": rate,
        "refractory_mass": refractory,
        "mean_distance": float(-(grid.nodes @ density) / density.sum()),
        "pass_fraction": passing,
        "mean_response": mean_response,
        "latched_pass_fraction": latched,
        "pass_fraction_by_scale": by_scale,
        "link_probability": {
            scale: {f"{k}": link_probability(p, k) for k in INDEPENDENT_CARRIERS}
            for scale, p in by_scale.items()
        },
        "window_hit_probability": hits,
        "window_link_probability": {
            scale: {
                w: {f"{k}": link_probability(h, k) for k in INDEPENDENT_CARRIERS}
                for w, h in per_window.items()
            }
            for scale, per_window in hits.items()
        },
    }


def link_probability(pass_fraction: float, carriers: int) -> float:
    """Chance that some of ``carriers`` independent carriers passes at an occupied state."""
    return 1.0 - (1.0 - pass_fraction) ** carriers


def bit_response(distance: float, shift: float) -> float:
    """Total variation a ``shift`` toward threshold makes to a bit read after unit noise."""
    return abs(float(ndtr(distance)) - float(ndtr(distance - shift)))


def _log10_bit_response(distance: float, shift: float) -> float:
    """``log10`` of the response, without underflow far from the threshold."""
    near, far = sorted((distance, distance - shift), key=abs)
    if min(near, far) < 5.0:
        return math.log10(max(bit_response(distance, shift), 1e-300))
    low, high = min(near, far), max(near, far)
    ratio = 10.0 ** (log10_gaussian_tail(high) - log10_gaussian_tail(low))
    return log10_gaussian_tail(low) + math.log10(1.0 - ratio)


def bit_summary(margin: float, yardstick: float = FLUCTUATION_TV) -> dict[str, float]:
    """Fraction of a restored bit's occupied states that pass, and its largest response."""
    states = np.linspace(margin - BIT_SPAN, margin + BIT_SPAN, 1601)
    weights = np.exp(-0.5 * (states - margin) ** 2)
    weights /= weights.sum()
    passing, best = 0.0, -math.inf
    for x, weight in zip(np.abs(states), weights, strict=True):
        changes = [s for s in SHIFTS if s < x] + [-s for s in SHIFTS]
        least = min(_log10_bit_response(float(x), s) for s in changes)
        passing += weight * (least >= math.log10(yardstick))
        best = max(best, least)
    return {"margin": margin, "pass_fraction": float(passing), "log10_max_response": best}


def _yardstick_row(
    grid: Grid,
    membrane: Membrane,
    table: FloatArray,
    density: FloatArray,
    yardstick: float,
    windows_ms: tuple[float, ...],
    dt_ms: float,
) -> dict[str, Any]:
    """Pass fraction at full scale, and window visit probability at every noise share."""
    hits = {}
    for c in CHANGE_SCALES:
        passing = passing_states(table, grid, c, yardstick)
        hits[f"{c:g}"] = {
            f"{w:g}": hit_probability(grid, membrane, passing, w, dt_ms) for w in windows_ms
        }
    full = passing_states(table, grid, 1.0, yardstick)
    return {
        "yardstick": yardstick,
        "pass_fraction": float(density @ full),
        "window_hit_probability": hits,
    }


def yardstick_summary(
    grid: Grid,
    config: NeuronConfig,
    dt_ms: float,
    yardsticks: tuple[float, ...],
    windows_ms: tuple[float, ...],
) -> dict[str, Any]:
    """One regime at each yardstick, and its best response at each noise share."""
    membrane = calibrate(grid, config.tau_ms, REFRACTORY_MS, config.rate_hz, dt_ms)
    density = stationary(grid, membrane, dt_ms)[0]
    table = laws(grid, membrane, config.window_ms, dt_ms)
    best = {}
    for c in CHANGE_SCALES:
        least = [_least_response(table, grid, node, c) for node in range(grid.nodes.size)]
        best[f"{c:g}"] = max(r for r in least if r is not None)
    rows = [
        _yardstick_row(grid, membrane, table, density, y, windows_ms, dt_ms) for y in yardsticks
    ]
    return {"config": asdict(config), "best_response": best, "by_yardstick": rows}


def yardstick_run(grid: Grid, dt_ms: float) -> dict[str, Any]:
    """Every declared regime and bit margin, rechecked at each swept yardstick."""
    margins = (*BIT_MARGINS, noise_floor()["marginToNoise"])
    return {
        "yardsticks": list(YARDSTICKS),
        "binary_ceiling": float(ndtr(1.0)) - 0.5,
        "neurons": [
            yardstick_summary(
                grid, NeuronConfig(tau, rate, window), dt_ms, YARDSTICKS, CONTENT_WINDOWS_MS
            )
            for tau in TAUS_MS
            for rate in RATES_HZ
            for window in WINDOWS_MS
        ],
        "bits": [
            {"margin": m, "pass_fraction": [bit_summary(m, y)["pass_fraction"] for y in YARDSTICKS]}
            for m in margins
        ],
    }


def run(grid: Grid, dt_ms: float) -> dict[str, Any]:
    """Every declared regime, every latch, every bit margin, and the resolution check."""
    neurons = [
        neuron_summary(grid, NeuronConfig(tau, rate, window), dt_ms, (*LATCH_PERIODS_MS, window))
        for tau in TAUS_MS
        for rate in RATES_HZ
        for window in WINDOWS_MS
    ]
    logic = noise_floor()["marginToNoise"]
    check = NeuronConfig(TAUS_MS[0], RATES_HZ[1], WINDOWS_MS[0])
    fine = Grid(grid.low, grid.step / 2)
    return {
        "fluctuation_tv": FLUCTUATION_TV,
        "shifts": list(SHIFTS),
        "grid": asdict(grid),
        "dt_ms": dt_ms,
        "neurons": neurons,
        "bits": [bit_summary(m) for m in (*BIT_MARGINS, logic)],
        "resolution_check": {
            "coarse": neuron_summary(grid, check, dt_ms, ()),
            "fine": neuron_summary(fine, check, dt_ms / 2, ()),
        },
    }


def main() -> None:
    """Run the declared sweep and save its summary; publication macros read it later."""
    parser = argparse.ArgumentParser(description="Occupancy-weighted noise-floor test")
    parser.add_argument("--step", type=float, default=0.05)
    parser.add_argument("--low", type=float, default=-8.0)
    parser.add_argument("--dt-ms", type=float, default=0.1)
    parser.add_argument("--yardstick", action="store_true", help="the U49 sweep only")
    args = parser.parse_args()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    grid = Grid(args.low, args.step)
    if args.yardstick:
        swept = yardstick_run(grid, args.dt_ms)
        (OUTPUT / "yardstick.json").write_text(json.dumps(swept, indent=2) + "\n")
        return
    summary = run(grid, args.dt_ms)
    (OUTPUT / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
