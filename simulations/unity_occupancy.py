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
beside the result, as its resolution check.

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

from unity_estimates import FLUCTUATION_TV, log10_gaussian_tail, noise_floor

FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_occupancy"

# Changes, in noise amplitudes, at which "every change above the noise" is checked.
SHIFTS = (1.0, 1.5, 2.0, 3.0)
REFRACTORY_MS = 2.0
TAUS_MS = (5.0, 20.0)
RATES_HZ = (0.5, 2.0, 8.0)
WINDOWS_MS = (10.0, 30.0)
LATCH_PERIODS_MS = (1.0, 5.0)
BIT_MARGINS = (0.5, 1.0, 2.0, 4.0)
# Occupied states of a bit: its rail plus this many noise amplitudes either side.
BIT_SPAN = 8.0


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


def _step(grid: Grid, membrane: Membrane, dt_ms: float) -> tuple[FloatArray, FloatArray]:
    """Surviving transition ``T[j, i]`` from node ``i`` to ``j``, and each node's spike mass."""
    v = grid.nodes
    decay = math.exp(-dt_ms / membrane.tau_ms)
    spread = math.sqrt(1.0 - decay**2)
    centre = membrane.mean + (v - membrane.mean) * decay
    upper = np.append(v[:-1] + grid.step / 2, 0.0)
    cumulative = ndtr((upper[:, None] - centre[None, :]) / spread)
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


def stationary(grid: Grid, membrane: Membrane, dt_ms: float) -> tuple[FloatArray, float, float]:
    """Stationary mass on the nodes, the refractory mass, and the rate in Hz."""
    surviving, spiking = _step(grid, membrane, dt_ms)
    n, stages = grid.nodes.size, max(1, round(membrane.refractory_ms / dt_ms))
    chain = np.zeros((n + stages, n + stages))
    chain[:n, :n] = surviving
    chain[n, :n] = spiking
    for k in range(stages - 1):
        chain[n + k + 1, n + k] = 1.0
    chain[:n, n + stages - 1] = _reset_mass(grid, membrane.reset)
    system = chain - np.eye(n + stages)
    system[-1, :] = 1.0
    target = np.zeros(n + stages)
    target[-1] = 1.0
    mass = np.linalg.solve(system, target)
    density = np.clip(mass[:n], 0.0, None)
    return density, float(mass[n:].sum()), float(spiking @ density) * 1000.0 / dt_ms


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


def _least_response(table: FloatArray, grid: Grid, node: int) -> float | None:
    """The smallest response over every admissible change of the state at ``node``."""
    offsets = [round(s / grid.step) for s in SHIFTS]
    targets = [node + k for k in offsets] + [node - k for k in offsets]
    admissible = [t for t in targets if 0 <= t < grid.nodes.size]
    if not admissible:
        return None
    return min(_tv(table[:, node], table[:, t]) for t in admissible)


def _occupancy_pass(table: FloatArray, grid: Grid, density: FloatArray) -> tuple[float, float]:
    """Mass of occupied states passing the criterion, and the mean least response."""
    passing = mean = 0.0
    for node, weight in enumerate(density):
        least = _least_response(table, grid, node)
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
    return {
        "config": asdict(config),
        "mean": membrane.mean,
        "rate_hz": rate,
        "refractory_mass": refractory,
        "mean_distance": float(-(grid.nodes @ density) / density.sum()),
        "pass_fraction": passing,
        "mean_response": mean_response,
        "latched_pass_fraction": latched,
    }


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


def bit_summary(margin: float) -> dict[str, float]:
    """Fraction of a restored bit's occupied states that pass, and its largest response."""
    states = np.linspace(margin - BIT_SPAN, margin + BIT_SPAN, 1601)
    weights = np.exp(-0.5 * (states - margin) ** 2)
    weights /= weights.sum()
    passing, best = 0.0, -math.inf
    for x, weight in zip(np.abs(states), weights, strict=True):
        changes = [s for s in SHIFTS if s < x] + [-s for s in SHIFTS]
        least = min(_log10_bit_response(float(x), s) for s in changes)
        passing += weight * (least >= math.log10(FLUCTUATION_TV))
        best = max(best, least)
    return {"margin": margin, "pass_fraction": float(passing), "log10_max_response": best}


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
    args = parser.parse_args()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    summary = run(Grid(args.low, args.step), args.dt_ms)
    (OUTPUT / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
