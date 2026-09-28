"""Whether the bridge's two loops can be matched, and how many trials it needs (U95, U98).

The bridge reconnects two cortical regions through an analog loop and through a
quantized one, and asks the loops to carry the same information, in total and
about the task, while falling on opposite sides of P. Its two settings are the
quantizer's step and the analog loop's cutoff. Two settings for two conditions
may have no solution, so this module simulates both loops on a model pair of
regions and looks.

The model, in units of region A's own noise amplitude, at a 1 ms step:

* a task variable ``s``, an Ornstein-Uhlenbeck process of declared standard
  deviation and time constant, drives region A, whose activity is ``s`` plus
  its own noise, an Ornstein-Uhlenbeck process of unit standard deviation and
  10 ms time constant;
* A is recorded with white noise of its own amplitude, the largest at which
  the analog loop still passes (``unity_estimates.bridge``), and passed through
  a first-order filter both loops share;
* the analog loop adds a first-order filter at its cutoff; the quantized loop
  rounds to the nearest multiple of its step; an output stage both loops share,
  a first-order filter, drives region B;
* region B is a leaky integrator of the delivered current with a 10 ms time
  constant and unit noise, recorded with unit white noise.

Both quantities are estimated twice (U98). The *linear* estimator: transfer
entropy from A's recording to B's by the linear-Gaussian formula with five 1 ms
lags, in bits per second, and task decodability as the variance of ``s``
explained by a linear decoder of B's recording at lags up to 40 ms, fitted on
half the trials and scored on the other half. It misses whatever the
quantizer's nonlinearity passes on. The *neighbour* estimator: the same
transfer entropy, as the conditional mutual information of the Frenzel-Pompe
nearest-neighbour estimator (Frenzel & Pompe 2007, Phys Rev Lett 99:204101,
extending Kraskov, Stögbauer & Grassberger 2004, Phys Rev E 69:066138) with the
same lags, and decodability as ``1 - exp(-2 I)`` for the nearest-neighbour
mutual information ``I`` between ``s`` and B's lagged recording: the variance a
decoder would explain if the information were Gaussian, so that on a linear
loop the two estimators agree. Both use every fourth sample and four
neighbours. Decodability is the task information that reaches B, which is what
the loops must match. Every quantity is computed on the same trials for both
loops (common random numbers).

For each step and estimator, two analog cutoffs are read off a grid of
cutoffs, from the floor that keeps the analog loop within the content's window
(``unity_estimates``) up to 1 kHz, by interpolation in the logarithm of the
cutoff: the one that matches the quantized loop's transfer entropy, and the one
that matches its decodability. Both measures rise with the cutoff, so at the
lower of the two the analog loop carries no more of either than the quantized
loop: that cutoff *binds*. The *gap* is the analog loop's decodability at the
transfer-entropy match minus the quantized loop's, and the *shortfall* is the
fraction of the quantized loop's transfer entropy the analog loop lacks at the
decodability match. A gap at or below zero, or a shortfall at or above zero,
says which match binds. The lower of the two estimators' binding cutoffs is the
one a preparation sets, and both estimators are evaluated there again: the
analog loop's excess over the quantized loop, relative in transfer entropy and
absolute in decodability. Where neither excess is positive, an account on which
unity follows information predicts no advantage for the analog loop.

Trials. At the declared step the common cutoff is repeated on independent
blocks, and the spread of the relative difference in transfer
entropy and of the difference in decodability across blocks gives
their confidence intervals at any trial count, shrinking as its square root.
The behavioural comparison is two proportions and the neural one two means,
each at a declared effect size, two-sided ``α = 0.05`` and power 0.8.

Declared, not measured: every time constant, noise amplitude and filter above;
the task regimes; the behavioural effect, accuracy 0.75 against 0.70; the
neural effect, a standardized difference of 0.2 (small, by the usual
convention). The model has no spikes, no stimulation artefact and no
plasticity. ``bridge.json`` is written beside the occupancy summaries, and
``unity_macros.py`` reads it.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from statistics import NormalDist
from typing import Any, Literal

import numpy as np
from numpy.typing import NDArray
from scipy.signal import lfilter
from scipy.spatial import cKDTree
from scipy.special import digamma

from unity_estimates import BRIDGE_STEP_TO_NOISE, estimates, quantized_fail_fraction

FloatArray = NDArray[np.float64]

OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_occupancy"

DT_S = 1e-3
TRIAL_STEPS = 400
BURN_STEPS = 200
REGION_TAU_MS = 10.0
RECORDING_NOISE = 1.0
FILTER_HZ = 100.0
TE_LAGS = 5
DECODER_LAGS = (0, 2, 5, 10, 20, 40)
MAX_CUTOFF_HZ = 1000.0
DECLARED_STEP = BRIDGE_STEP_TO_NOISE
STEPS = (6.0, 8.0, 10.0, 12.0, 15.0, 20.0, 30.0)
TRIALS = 200
CUTOFFS = 40
BLOCK_TRIALS = 100
SEEDS = 16
ALPHA = 0.05
POWER = 0.8
ACCURACY_HIGH = 0.75
ACCURACY_LOW = 0.70
NEURAL_EFFECT = 0.2
NEIGHBOURS = 4
THIN = 4
ESTIMATORS = ("linear", "neighbour")


@dataclass(frozen=True)
class Task:
    """The task variable: standard deviation in region noise amplitudes, time constant."""

    sd: float
    tau_ms: float


TASKS = tuple(Task(sd, tau) for sd in (2.0, 5.0, 10.0) for tau in (20.0, 100.0))


@dataclass(frozen=True)
class Loop:
    """An analog loop at a cutoff in Hz, or a quantized loop at a step."""

    kind: Literal["analog", "quantized"]
    setting: float


@dataclass(frozen=True)
class Trials:
    """One block: the task variable and the two recordings, trial by sample."""

    task: FloatArray
    recorded_a: FloatArray
    recorded_b: FloatArray


@dataclass(frozen=True)
class Measures:
    """Transfer entropy from A to B in bits per second, and task decodability from B."""

    transfer_entropy: float
    decodability: float


def lowpass(x: FloatArray, cutoff_hz: float) -> FloatArray:
    """A first-order low-pass filter along the last axis, unit gain at zero frequency."""
    a = math.exp(-2 * math.pi * cutoff_hz * DT_S)
    return np.asarray(lfilter([1 - a], [1, -a], x, axis=-1), dtype=np.float64)


def quantize(x: FloatArray, step: float) -> FloatArray:
    """The nearest multiple of ``step``."""
    return np.asarray(step * np.round(x / step), dtype=np.float64)


def _ou(rng: np.random.Generator, shape: tuple[int, int], tau_ms: float, sd: float) -> FloatArray:
    a = math.exp(-DT_S * 1000 / tau_ms)
    kicks = rng.standard_normal(shape) * sd * math.sqrt(1 - a * a)
    return np.asarray(lfilter([1], [1, -a], kicks, axis=-1), dtype=np.float64)


def simulate(task: Task, loop: Loop, trials: int, seed: int) -> Trials:
    """One block of trials through one loop."""
    rng = np.random.default_rng(seed)
    shape = (trials, TRIAL_STEPS + BURN_STEPS)
    s = _ou(rng, shape, task.tau_ms, task.sd)
    recorded_a = (
        s + _ou(rng, shape, REGION_TAU_MS, 1.0) + RECORDING_NOISE * rng.standard_normal(shape)
    )
    shared = lowpass(recorded_a, FILTER_HZ)
    if loop.kind == "analog":
        drive = lowpass(shared, loop.setting)
    else:
        drive = quantize(shared, loop.setting)
    current = lowpass(drive, FILTER_HZ)
    leak = math.exp(-DT_S * 1000 / REGION_TAU_MS)
    kicks = (1 - leak) * np.roll(current, 1, axis=-1) + math.sqrt(
        1 - leak**2
    ) * rng.standard_normal(shape)
    kicks[:, 0] = 0.0
    b = np.asarray(lfilter([1], [1, -leak], kicks, axis=-1), dtype=np.float64)
    recorded_b = b + RECORDING_NOISE * rng.standard_normal(shape)
    keep = slice(BURN_STEPS, None)
    return Trials(s[:, keep], recorded_a[:, keep], recorded_b[:, keep])


def _lagged(x: FloatArray, lags: tuple[int, ...] | range, start: int) -> FloatArray:
    n = x.shape[1]
    return np.stack([x[:, start - k : n - k].ravel() for k in lags], axis=1)


def _residual_variance(target: FloatArray, design: FloatArray) -> float:
    design = np.column_stack([design, np.ones(len(design))])
    coef, *_ = np.linalg.lstsq(design, target, rcond=None)
    return float(np.var(target - design @ coef))


def transfer_entropy(source: FloatArray, target: FloatArray, lags: int = TE_LAGS) -> float:
    """Linear-Gaussian transfer entropy from ``source`` to ``target``, in bits per second."""
    past = range(1, lags + 1)
    now = target[:, lags:].ravel()
    own = _lagged(target, past, lags)
    both = np.column_stack([own, _lagged(source, past, lags)])
    ratio = _residual_variance(now, own) / _residual_variance(now, both)
    return 0.5 * math.log2(ratio) / DT_S


def decodability(task: FloatArray, recorded: FloatArray) -> float:
    """Variance of the task variable a linear decoder explains on held-out trials."""
    start, half = max(DECODER_LAGS), task.shape[0] // 2

    def design(rows: slice) -> FloatArray:
        lagged = _lagged(recorded[rows], DECODER_LAGS, start)
        return np.column_stack([lagged, np.ones(len(lagged))])

    fit, held = slice(0, half), slice(half, None)
    coef, *_ = np.linalg.lstsq(design(fit), task[fit, start:].ravel(), rcond=None)
    target = task[held, start:].ravel()
    return 1.0 - float(np.var(target - design(held) @ coef) / np.var(target))


def _standardized(x: FloatArray) -> FloatArray:
    return np.asarray((x - x.mean(axis=0)) / x.std(axis=0), dtype=np.float64)


def _radius(points: FloatArray, k: int) -> FloatArray:
    """Each point's distance to its ``k``-th neighbour in the maximum norm, exclusive."""
    distances, _ = cKDTree(points).query(points, k + 1, p=np.inf, workers=-1)
    return np.asarray(np.nextafter(distances[:, -1], 0), dtype=np.float64)


def _within(points: FloatArray, radius: FloatArray) -> FloatArray:
    """How many other points lie strictly within each point's radius."""
    tree = cKDTree(points)
    counts = tree.query_ball_point(points, radius, p=np.inf, return_length=True, workers=-1)
    return np.asarray(counts, dtype=np.float64) - 1


def mutual_information(x: FloatArray, y: FloatArray, k: int = NEIGHBOURS) -> float:
    """Nearest-neighbour estimate of ``I(X; Y)`` in nats (Kraskov et al., first estimator)."""
    x, y = _standardized(x), _standardized(y)
    radius = _radius(np.column_stack([x, y]), k)
    counts = digamma(_within(x, radius) + 1) + digamma(_within(y, radius) + 1)
    return float(digamma(k) + digamma(len(x)) - np.mean(counts))


def conditional_mutual_information(
    x: FloatArray, y: FloatArray, z: FloatArray, k: int = NEIGHBOURS
) -> float:
    """Nearest-neighbour estimate of ``I(X; Y | Z)`` in nats (Frenzel & Pompe)."""
    x, y, z = _standardized(x), _standardized(y), _standardized(z)
    radius = _radius(np.column_stack([x, y, z]), k)
    terms = (
        digamma(_within(z, radius) + 1)
        - digamma(_within(np.column_stack([x, z]), radius) + 1)
        - digamma(_within(np.column_stack([y, z]), radius) + 1)
    )
    return float(digamma(k) + np.mean(terms))


def _thinned(x: FloatArray, lags: tuple[int, ...] | range, start: int) -> FloatArray:
    n = x.shape[1]
    return np.stack([x[:, start - k : n - k][:, ::THIN].ravel() for k in lags], axis=1)


def transfer_entropy_neighbours(
    source: FloatArray, target: FloatArray, lags: int = TE_LAGS
) -> float:
    """Nearest-neighbour transfer entropy from ``source`` to ``target``, in bits per second."""
    past = range(1, lags + 1)
    now = _thinned(target, (0,), lags)
    info = conditional_mutual_information(
        now, _thinned(source, past, lags), _thinned(target, past, lags)
    )
    return info / math.log(2) / DT_S


def decodability_neighbours(task: FloatArray, recorded: FloatArray) -> float:
    """Variance of the task a decoder would explain, from nearest-neighbour information."""
    start = max(DECODER_LAGS)
    info = mutual_information(_thinned(task, (0,), start), _thinned(recorded, DECODER_LAGS, start))
    return 1.0 - math.exp(-2.0 * info)


def evaluate(task: Task, loop: Loop, trials: int, seed: int) -> dict[str, Measures]:
    """Transfer entropy and task decodability of one loop on one block, by each estimator."""
    block = simulate(task, loop, trials, seed)
    a, b = block.recorded_a, block.recorded_b
    return {
        "linear": Measures(transfer_entropy(a, b), decodability(block.task, b)),
        "neighbour": Measures(
            transfer_entropy_neighbours(a, b), decodability_neighbours(block.task, b)
        ),
    }


def matched_cutoff(cutoffs: FloatArray, values: list[float], target: float) -> float | None:
    """The cutoff at which the analog loop's measure equals ``target``, if in range."""
    measured = np.array(values)
    if not measured.min() <= target <= measured.max():
        return None
    order = np.argsort(measured)
    return float(np.exp(np.interp(target, measured[order], np.log(cutoffs[order]))))


def binding(row: dict[str, Any]) -> tuple[str | None, float | None]:
    """The lower of the two matched cutoffs, and which measure it matches."""
    matches = [
        (cutoff, name)
        for name, cutoff in (
            ("transfer_entropy", row["te_cutoff_hz"]),
            ("decodability", row["decodability_cutoff_hz"]),
        )
        if cutoff is not None
    ]
    if not matches:
        return None, None
    cutoff, name = min(matches)
    return name, cutoff


def trials_two_proportions(high: float, low: float, alpha: float, power: float) -> int:
    """Trials per loop to tell two accuracies apart, two-sided."""
    z = NormalDist().inv_cdf(1 - alpha / 2) + NormalDist().inv_cdf(power)
    spread = high * (1 - high) + low * (1 - low)
    return math.ceil(z**2 * spread / (high - low) ** 2)


def trials_two_means(effect: float, alpha: float, power: float) -> int:
    """Trials per loop to tell two means apart at a standardized effect, two-sided."""
    z = NormalDist().inv_cdf(1 - alpha / 2) + NormalDist().inv_cdf(power)
    return math.ceil(2 * z**2 / effect**2)


def half_width(sd: float, measured_trials: int, trials: int) -> float:
    """95% confidence half-width at ``trials``, from a spread measured at ``measured_trials``."""
    return NormalDist().inv_cdf(0.975) * sd * math.sqrt(measured_trials / trials)


def _estimator_row(
    task: Task,
    cutoffs: FloatArray,
    analog: list[Measures],
    quantized: Measures,
    trials: int,
    estimator: str,
) -> dict[str, Any]:
    """Both matches of one step under one estimator, and which of them binds."""
    te = [m.transfer_entropy for m in analog]
    row: dict[str, Any] = {
        "transfer_entropy": quantized.transfer_entropy,
        "decodability": quantized.decodability,
        "te_cutoff_hz": matched_cutoff(cutoffs, te, quantized.transfer_entropy),
        "te_above_grid": quantized.transfer_entropy > max(te),
        "decodability_cutoff_hz": matched_cutoff(
            cutoffs, [m.decodability for m in analog], quantized.decodability
        ),
        "gap": None,
        "te_shortfall": None,
    }
    if row["te_cutoff_hz"] is not None:
        at = evaluate(task, Loop("analog", row["te_cutoff_hz"]), trials, 0)[estimator]
        row["gap"] = at.decodability - quantized.decodability
    if row["decodability_cutoff_hz"] is not None:
        at = evaluate(task, Loop("analog", row["decodability_cutoff_hz"]), trials, 0)[estimator]
        row["te_shortfall"] = 1 - at.transfer_entropy / quantized.transfer_entropy
    row["binds"], row["cutoff_hz"] = binding(row)
    return row


def _step_row(
    task: Task, step: float, cutoffs: FloatArray, analog: list[dict[str, Measures]], trials: int
) -> dict[str, Any]:
    quantized = evaluate(task, Loop("quantized", step), trials, 0)
    row: dict[str, Any] = {
        "step": step,
        "fail_fraction": quantized_fail_fraction(step, 1.0, RECORDING_NOISE),
    }
    for name in ESTIMATORS:
        row[name] = _estimator_row(
            task, cutoffs, [m[name] for m in analog], quantized[name], trials, name
        )
    row["common"] = _common(task, row, quantized, trials)
    return row


def _common(
    task: Task, row: dict[str, Any], quantized: dict[str, Measures], trials: int
) -> dict[str, Any] | None:
    """Both estimators at the lowest binding cutoff of either: the one a preparation sets."""
    bound = [row[name]["cutoff_hz"] for name in ESTIMATORS if row[name]["cutoff_hz"] is not None]
    if not bound:
        return None
    cutoff = min(bound)
    analog = evaluate(task, Loop("analog", cutoff), trials, 0)
    common: dict[str, Any] = {"cutoff_hz": cutoff}
    for name in ESTIMATORS:
        common[name] = {
            "relative_te_excess": analog[name].transfer_entropy / quantized[name].transfer_entropy
            - 1,
            "decodability_excess": analog[name].decodability - quantized[name].decodability,
        }
    return common


def _spread(task: Task, cutoff: float, seeds: int) -> dict[str, Any]:
    """Spread across blocks of the two loops' differences at the common cutoff, by estimator."""
    te: dict[str, list[float]] = {name: [] for name in ESTIMATORS}
    gap: dict[str, list[float]] = {name: [] for name in ESTIMATORS}
    for seed in range(1, seeds + 1):
        analog = evaluate(task, Loop("analog", cutoff), BLOCK_TRIALS, seed)
        quantized = evaluate(task, Loop("quantized", DECLARED_STEP), BLOCK_TRIALS, seed)
        for name in ESTIMATORS:
            a, q = analog[name], quantized[name]
            te[name].append(a.transfer_entropy / q.transfer_entropy - 1)
            gap[name].append(a.decodability - q.decodability)
    spread: dict[str, Any] = {"cutoff_hz": cutoff}
    for name in ESTIMATORS:
        spread[name] = {
            "relative_te_sd": float(np.std(te[name], ddof=1)),
            "gap_sd": float(np.std(gap[name], ddof=1)),
        }
    return spread


def regime(
    task: Task, steps: tuple[float, ...], trials: int, cutoffs: int, seeds: int
) -> dict[str, Any]:
    """Every step's match for one task, and the spread at the declared step."""
    grid = np.geomspace(estimates()["bridgeMinCutoffHz"], MAX_CUTOFF_HZ, cutoffs, dtype=np.float64)
    analog = [evaluate(task, Loop("analog", f), trials, 0) for f in grid]
    rows = [_step_row(task, step, grid, analog, trials) for step in steps]
    declared = next((r for r in rows if r["step"] == DECLARED_STEP), None)
    spread = None
    if declared is not None and declared["common"] is not None:
        spread = _spread(task, declared["common"]["cutoff_hz"], seeds)
    return {"task": {"sd": task.sd, "tau_ms": task.tau_ms}, "steps": rows, "spread": spread}


def run(
    tasks: tuple[Task, ...] = TASKS,
    steps: tuple[float, ...] = STEPS,
    trials: int = TRIALS,
    cutoffs: int = CUTOFFS,
    seeds: int = SEEDS,
) -> dict[str, Any]:
    """Every declared task regime and step, and the trial counts."""
    return {
        "declared_step": DECLARED_STEP,
        "cutoff_floor_hz": estimates()["bridgeMinCutoffHz"],
        "block_trials": BLOCK_TRIALS,
        "estimators": list(ESTIMATORS),
        "effects": {
            "accuracy_high": ACCURACY_HIGH,
            "accuracy_low": ACCURACY_LOW,
            "neural": NEURAL_EFFECT,
            "alpha": ALPHA,
            "power": POWER,
        },
        "trials": {
            "behaviour": trials_two_proportions(ACCURACY_HIGH, ACCURACY_LOW, ALPHA, POWER),
            "neural": trials_two_means(NEURAL_EFFECT, ALPHA, POWER),
        },
        "regimes": [regime(t, steps, trials, cutoffs, seeds) for t in tasks],
    }


def write(directory: Path, **options: Any) -> None:
    """Save the run; publication macros read it later."""
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "bridge.json").write_text(json.dumps(run(**options), indent=2) + "\n")


if __name__ == "__main__":
    write(OUTPUT)
