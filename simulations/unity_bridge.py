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

A *held* task (U106) replaces the continuous task variable with one stimulus
per trial, held for the trial, at a centre of the declared step up to a small
declared spread. It answers criterion G, which passes a loop whose quantizer
input *visits* the passing band anywhere in a content window: a continuous
variable spanning half a step crosses the step's edges and visits it in almost
every window, so the quantized arm could never be certified to fail, while a
held stimulus sits mid-step. A trial lasts one content window, and each step's
``visit_fraction`` is the share of trials that visit. The window opens
``SETTLE_TAUS`` time constants of the slowest analog loop after the stimulus,
once that loop has settled at the new level.

A session can be *relabelled* (U107) by shifting the held stimuli and the
quantizer's levels together by a fraction of a step. Every other stage is
linear and time-invariant and the quantizer commutes with the joint shift, so
every signal moves by a constant: what the loop carries and its visits to the
passing band are unchanged, while the currents it delivers are ones the
unshifted sessions never delivered, which invalidates a code learned from
them.

Settled on a held stimulus, the analog loop at its slowest cutoff carries more
linear transfer entropy than the quantized loop at every step whose input stays
clear of the passing band, so a third setting matches them: white noise of the
analog loop's own, added before its cutoff filter. The filter leaves little of
it at the delivered current (``channel_noise``), where the loop passes while
that noise stays within one region amplitude. For each held regime the noise
is read off a grid at which the analog loop's linear transfer entropy falls
``NOISE_MARGIN`` below the quantized loop's at the declared step, and its
decodability to the quantized loop's; the larger binds. The largest over
regimes is then checked on independent blocks (``held_noise``).

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

from unity_estimates import (
    BRIDGE_STEP_TO_NOISE,
    estimates,
    fail_distance,
    quantized_fail_fraction,
)

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
# Declared: a held stimulus lies within this many region noise amplitudes of a
# step's centre. The spread also keeps the neighbour estimator free of ties.
HELD_SPREAD = 0.5
# Declared: a held trial's window opens this many time constants of the slowest
# analog loop after the stimulus, once that loop has settled at the new level.
SETTLE_TAUS = 5.0
# The analog loop's own noise, in region noise amplitudes, added before its
# cutoff filter; the pilot's match is read off this grid.
NOISE_GRID = tuple(2.5 * k for k in range(13))
# Declared: the noise is matched to this fraction below the quantized loop's
# transfer entropy, so that independent blocks do not reverse the order.
NOISE_MARGIN = 0.05
IMPULSE_STEPS = 5000
NEIGHBOURS = 4
THIN = 4
ESTIMATORS = ("linear", "neighbour")


@dataclass(frozen=True)
class Task:
    """The task variable: standard deviation in region noise amplitudes, time constant.

    An ``ou`` task varies continuously. A ``held`` task holds one stimulus for
    the trial, at one of ``2 levels + 1`` centres of the declared step, and its
    time constant is the trial's length. A session's ``offset``, in steps,
    relabels it (U107): the stimuli and the quantizer's levels move together.
    """

    sd: float
    tau_ms: float
    kind: Literal["ou", "held"] = "ou"
    levels: int = 0
    offset: float = 0.0


def held(levels: int, offset: float = 0.0) -> Task:
    """Stimuli held for the trial at the declared step's centres ``-levels .. levels``.

    An ``offset`` shifts every centre by that fraction of a step, and the
    quantizer's levels with them.
    """
    centres = DECLARED_STEP * np.arange(-levels, levels + 1)
    sd = math.sqrt(float(np.mean(centres**2)) + HELD_SPREAD**2 / 3)
    return Task(sd, TRIAL_STEPS * DT_S * 1000, "held", levels, offset)


TASKS = (
    *(Task(sd, tau) for sd in (2.0, 5.0, 10.0) for tau in (20.0, 100.0)),
    held(1),
    held(2),
)


@dataclass(frozen=True)
class Loop:
    """An analog loop at a cutoff in Hz, or a quantized loop at a step.

    An analog loop may add white noise of its own, ``noise`` region amplitudes,
    before its cutoff filter.
    """

    kind: Literal["analog", "quantized"]
    setting: float
    noise: float = 0.0


@dataclass(frozen=True)
class Trials:
    """One block: the task variable and the two recordings, trial by sample."""

    task: FloatArray
    recorded_a: FloatArray
    recorded_b: FloatArray
    quantizer_input: FloatArray


@dataclass(frozen=True)
class Measures:
    """Transfer entropy from A to B in bits per second, and task decodability from B."""

    transfer_entropy: float
    decodability: float


def lowpass(x: FloatArray, cutoff_hz: float) -> FloatArray:
    """A first-order low-pass filter along the last axis, unit gain at zero frequency."""
    a = math.exp(-2 * math.pi * cutoff_hz * DT_S)
    return np.asarray(lfilter([1 - a], [1, -a], x, axis=-1), dtype=np.float64)


def quantize(x: FloatArray, step: float, offset: float = 0.0) -> FloatArray:
    """The nearest of the levels ``step * (k + offset)``."""
    return np.asarray(step * (np.round(x / step - offset) + offset), dtype=np.float64)


def _ou(rng: np.random.Generator, shape: tuple[int, int], tau_ms: float, sd: float) -> FloatArray:
    a = math.exp(-DT_S * 1000 / tau_ms)
    kicks = rng.standard_normal(shape) * sd * math.sqrt(1 - a * a)
    return np.asarray(lfilter([1], [1, -a], kicks, axis=-1), dtype=np.float64)


def _held(rng: np.random.Generator, shape: tuple[int, int], task: Task) -> FloatArray:
    k = rng.integers(-task.levels, task.levels + 1, size=(shape[0], 1))
    centre = DECLARED_STEP * (k + task.offset)
    level = centre + rng.uniform(-HELD_SPREAD, HELD_SPREAD, size=(shape[0], 1))
    return np.asarray(np.broadcast_to(level, shape), dtype=np.float64)


def burn_steps(task: Task) -> int:
    """Steps before the window: a held stimulus waits for the slowest analog loop to settle."""
    if task.kind == "ou":
        return BURN_STEPS
    tau_ms = 1000 / (2 * math.pi * estimates()["bridgeMinCutoffHz"])
    return max(BURN_STEPS, math.ceil(SETTLE_TAUS * tau_ms / (DT_S * 1000)))


def _drive(shared: FloatArray, loop: Loop, seed: int, offset: float) -> FloatArray:
    if loop.kind == "quantized":
        return quantize(shared, loop.setting, offset)
    if loop.noise == 0.0:
        return lowpass(shared, loop.setting)
    # The loop's own generator, so every other draw is shared with the silent loop.
    own = np.random.default_rng((seed, 1)).standard_normal(shared.shape)
    return lowpass(shared + loop.noise * own, loop.setting)


def simulate(task: Task, loop: Loop, trials: int, seed: int) -> Trials:
    """One block of trials through one loop."""
    rng = np.random.default_rng(seed)
    burn = burn_steps(task)
    shape = (trials, TRIAL_STEPS + burn)
    s = _held(rng, shape, task) if task.kind == "held" else _ou(rng, shape, task.tau_ms, task.sd)
    recorded_a = (
        s + _ou(rng, shape, REGION_TAU_MS, 1.0) + RECORDING_NOISE * rng.standard_normal(shape)
    )
    shared = lowpass(recorded_a, FILTER_HZ)
    current = lowpass(_drive(shared, loop, seed, task.offset), FILTER_HZ)
    leak = math.exp(-DT_S * 1000 / REGION_TAU_MS)
    kicks = (1 - leak) * np.roll(current, 1, axis=-1) + math.sqrt(
        1 - leak**2
    ) * rng.standard_normal(shape)
    kicks[:, 0] = 0.0
    b = np.asarray(lfilter([1], [1, -leak], kicks, axis=-1), dtype=np.float64)
    recorded_b = b + RECORDING_NOISE * rng.standard_normal(shape)
    keep = slice(burn, None)
    return Trials(s[:, keep], recorded_a[:, keep], recorded_b[:, keep], shared[:, keep])


def visit_fraction(task: Task, step: float, trials: int, seed: int) -> float:
    """Share of trials, one content window each, whose quantizer input enters the passing band.

    A state passes when it lies within ``fail_distance`` of an edge, halfway
    between two of the quantizer's levels (``unity_estimates``); criterion G asks
    only whether the window visits such a state.
    """
    x = simulate(task, Loop("quantized", step), trials, seed).quantizer_input
    to_edge = step / 2 - np.abs(x - quantize(x, step, task.offset))
    return float(np.mean(np.any(to_edge <= fail_distance(1.0, RECORDING_NOISE), axis=1)))


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


def linear(block: Trials) -> Measures:
    """Transfer entropy and task decodability of one block by the linear estimator."""
    b = block.recorded_b
    return Measures(transfer_entropy(block.recorded_a, b), decodability(block.task, b))


def evaluate(task: Task, loop: Loop, trials: int, seed: int) -> dict[str, Measures]:
    """Transfer entropy and task decodability of one loop on one block, by each estimator."""
    block = simulate(task, loop, trials, seed)
    a, b = block.recorded_a, block.recorded_b
    return {
        "linear": linear(block),
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


def matched_noise(grid: tuple[float, ...], values: list[float], target: float) -> float | None:
    """The loop noise at which a measure that falls with it reaches ``target``, if in range."""
    measured = np.array(values)
    if measured[0] <= target:
        return 0.0
    if measured.min() > target:
        return None
    order = np.argsort(measured)
    return float(np.interp(target, measured[order], np.array(grid)[order]))


def channel_noise(loop: Loop) -> float:
    """The analog loop's own noise at the delivered current, in region noise amplitudes.

    Recording noise and the loop's added noise, each white, through the filters
    between it and the current; the budget within which the loop passes is one
    region amplitude (``unity_estimates.analog_passes``).
    """
    impulse = np.zeros(IMPULSE_STEPS)
    impulse[0] = 1.0
    added = lowpass(lowpass(impulse, loop.setting), FILTER_HZ)
    recorded = lowpass(added, FILTER_HZ)
    variance = loop.noise**2 * np.sum(added**2) + RECORDING_NOISE**2 * np.sum(recorded**2)
    return float(np.sqrt(variance))


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
        "visit_fraction": visit_fraction(task, step, trials, 0),
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


def _noise_match(
    task: Task, cutoff: float, quantized: dict[str, Any], trials: int
) -> dict[str, Any]:
    """The analog loop's noise, at ``cutoff``, that brings it to the quantized loop's measures."""
    measured = [linear(simulate(task, Loop("analog", cutoff, n), trials, 0)) for n in NOISE_GRID]
    te_noise = matched_noise(
        NOISE_GRID,
        [m.transfer_entropy for m in measured],
        (1 - NOISE_MARGIN) * quantized["transfer_entropy"],
    )
    decodability_noise = matched_noise(
        NOISE_GRID, [m.decodability for m in measured], quantized["decodability"]
    )
    both = (te_noise, decodability_noise)
    return {
        "cutoff_hz": cutoff,
        "te_noise": te_noise,
        "decodability_noise": decodability_noise,
        # Both measures fall with the noise: at the larger, neither exceeds its target.
        "noise": None if None in both else max(n for n in both if n is not None),
    }


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
    saved = {"sd": task.sd, "tau_ms": task.tau_ms, "kind": task.kind, "levels": task.levels}
    # The analog loop at the slowest cutoff that settles within the window.
    floor: dict[str, Any] = {"cutoff_hz": float(grid[0])}
    for name in ESTIMATORS:
        floor[name] = {
            "transfer_entropy": analog[0][name].transfer_entropy,
            "decodability": analog[0][name].decodability,
        }
    noise = None
    if task.kind == "held" and declared is not None:
        noise = _noise_match(task, float(grid[0]), declared["linear"], trials)
    return {"task": saved, "steps": rows, "spread": spread, "floor": floor, "noise_match": noise}


def _noise_blocks(task: Task, loop: Loop, seeds: int) -> dict[str, Any]:
    """The noisy analog loop against the quantized one on independent blocks, linear estimator."""
    te, gap = [], []
    for seed in range(1, seeds + 1):
        analog = linear(simulate(task, loop, BLOCK_TRIALS, seed))
        quantized = linear(simulate(task, Loop("quantized", DECLARED_STEP), BLOCK_TRIALS, seed))
        te.append(analog.transfer_entropy / quantized.transfer_entropy - 1)
        gap.append(analog.decodability - quantized.decodability)
    return {
        "levels": task.levels,
        "relative_te_excess_mean": float(np.mean(te)),
        "relative_te_excess_sd": float(np.std(te, ddof=1)),
        "decodability_gap_mean": float(np.mean(gap)),
        "decodability_gap_sd": float(np.std(gap, ddof=1)),
    }


def held_noise(
    tasks: tuple[Task, ...], regimes: list[dict[str, Any]], seeds: int
) -> dict[str, Any] | None:
    """One noise for every held regime, the largest matched, checked on independent blocks."""
    held = [(t, r["noise_match"]) for t, r in zip(tasks, regimes, strict=True) if t.kind == "held"]
    noises = [m["noise"] if m is not None else None for _, m in held]
    if not held or None in noises:
        return None
    first = held[0][1]
    loop = Loop("analog", first["cutoff_hz"], max(n for n in noises if n is not None))
    return {
        "cutoff_hz": loop.setting,
        "noise": loop.noise,
        "channel_noise": channel_noise(loop),
        "block_count": seeds,
        "blocks": [_noise_blocks(t, loop, seeds) for t, _ in held],
    }


def run(
    tasks: tuple[Task, ...] = TASKS,
    steps: tuple[float, ...] = STEPS,
    trials: int = TRIALS,
    cutoffs: int = CUTOFFS,
    seeds: int = SEEDS,
) -> dict[str, Any]:
    """Every declared task regime and step, and the trial counts."""
    regimes = [regime(t, steps, trials, cutoffs, seeds) for t in tasks]
    return {
        "declared_step": DECLARED_STEP,
        "cutoff_floor_hz": estimates()["bridgeMinCutoffHz"],
        "block_trials": BLOCK_TRIALS,
        "held_spread": HELD_SPREAD,
        "settle_taus": SETTLE_TAUS,
        "noise_margin": NOISE_MARGIN,
        "noise_grid": list(NOISE_GRID),
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
        "regimes": regimes,
        "held_noise": held_noise(tasks, regimes, seeds),
    }


def write(directory: Path, **options: Any) -> None:
    """Save the run; publication macros read it later."""
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "bridge.json").write_text(json.dumps(run(**options), indent=2) + "\n")


if __name__ == "__main__":
    write(OUTPUT)
