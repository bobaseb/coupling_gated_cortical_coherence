"""The occupancy test on recorded membranes of awake cortex (U100).

``unity_occupancy`` asks how often a membrane occupies a state at which every
change of one to three noise amplitudes moves its next spike time by the
fluctuation, for a model membrane whose time constant, rate and distance from
threshold are declared ranges. This module asks the same of membranes recorded
in awake mice.

The recordings are the whole-cell current-clamp recordings of Kiritani, Pala,
Gasselin, Crochet & Petersen (2023, PLoS ONE 18:e0287174) from layer 2/3 to 5
of the barrel cortex of awake head-restrained mice, deposited on Zenodo
(10.5281/zenodo.7833080) under CC BY 4.0, with the behavioural epochs the
authors scored from high-speed whisker filming: quiet wakefulness, free
whisking and active touch. ``fetch`` downloads the deposit into an ignored
cache; ``run`` reads it and writes ``recordings.json``.

Per cell and behavioural state:

* Spikes are detected with the authors' own procedure and per-cell slope
  criterion (a rise of the membrane's derivative through the criterion, a
  peak at least 5 mV above the onset within 1.5 ms), and the threshold is the
  potential at the onset. A cell's threshold is the median over all its spikes.
  Each spike, from onset to repolarisation found as the authors find it, counts
  as a failing state, as refractory states do in the model.
* The awake potential moves on two time scales: fluctuations of tens of
  milliseconds, and a slow wander over hundreds that carries up to half its
  variance. A single Ornstein-Uhlenbeck membrane fitted to both misses the
  fast fluctuations that set the next spike, and fires far too rarely. So the
  potential, spikes cut to straight lines, is split into its running mean over
  ``SLOW_MS``, the slow part, and a fast remainder.
* The unit, the noise amplitude, and the twin's time constant are those at
  which the model membrane, analysed exactly as the recording is (spikes cut,
  the same running mean removed, its autocovariance propagated through its
  chain), gives the remainder's spread and correlation time (``calibrate``).
* The passing states are those of the cell's *twin*: at each moment, the model
  membrane with that time constant held at the mean behind the slow part's
  current level (``QuasiStatic``). The twin supplies the law of the next spike
  time from each state, which a recording of one path cannot. The measured pass
  fraction is the share of recorded samples, at 10 kHz, that lie in a passing
  state; the measured window visit is the share of content windows, tiled
  inside epochs of one state, that contain one. The pass fraction is set beside
  the twin's, and the twin's rate beside the measured rate, which checks the
  description the passing states come from.

Scope: cells that fired at least ``MIN_SPIKES`` times, so that a threshold can
be read; one threshold per cell; one noise amplitude and time constant per cell
and state, from potentials pooled over its sweeps; a slow part that is constant
within a next-content window.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import multiprocessing
import os
import sys
import time
import urllib.request
import zipfile
from collections.abc import Sequence
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np
from numpy.typing import NDArray
from scipy.ndimage import uniform_filter1d
from scipy.signal import fftconvolve

import unity_occupancy as uo

FloatArray = NDArray[np.float64]
BoolArray = NDArray[np.bool_]

# Kiritani, Pala, Gasselin, Crochet & Petersen (2023), PLoS ONE 18:e0287174,
# deposited on Zenodo under CC BY 4.0. The data stay out of the tree.
RECORD_URL = "https://zenodo.org/api/records/7833080/files/Kiritani_data_code.zip/content"
RECORD_BYTES = 5_099_939_019
RECORD_MD5 = "65cedc4cea102c139764c03fa0c9638f"
DATA_MEMBER = "Data/Kiritani_Data.mat"
CACHE = Path(__file__).resolve().parent / "cache_kiritani2023"
CHUNK_BYTES = 64 * 2**20
FETCH_ATTEMPTS = 8

# The authors' detector (Function_Detect_APs.m): the peak is sought within
# 1.5 ms of the onset and must stand 5 mV above it.
PEAK_SEARCH_S = 0.0015
MIN_AMPLITUDE_V = 0.005
MIN_ONSET_GAP_S = 0.001
# Repolarisation is sought up to 15 ms after the peak (Function_CutAPs.m).
REPOLARISATION_S = 0.015
MIN_SPIKES = 5
GRID_STEP = 0.05
GRID_FLOOR = 8.0
# Samples are read at the model's time step, 0.1 ms.
DT_MS = 0.1
# Whisking is scored clear of contact by this margin either side
# (Function_Select_QorA_Epochs.m).
CONTACT_GUARD_S = 0.1
STATES = ("quiet", "whisking")
MAX_CORRELATION_MS = 1000.0
FIT_ROUNDS = 6
# A state enters a cell's record only with this much of it recorded.
MIN_STATE_MS = 10_000.0
# The slow part of the potential is its running mean over this span, three times
# the longer next-content window; within a window it acts as the twin's mean.
SLOW_MS = 100.0
# Levels of the slow part at which a twin is computed, in noise amplitudes.
MEAN_STEP = 0.2
OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_occupancy"


@dataclass(frozen=True)
class Spikes:
    """Sample indices of each spike's onset, peak and repolarisation, and its threshold."""

    onsets: NDArray[np.int64]
    peaks: NDArray[np.int64]
    thresholds: FloatArray


def _onset_candidates(v: FloatArray, rate_hz: float, slope_v_per_s: float) -> list[int]:
    """Samples at which the derivative rises through the slope criterion, 1 ms apart."""
    above = np.sign(np.diff(v) * rate_hz - slope_v_per_s)
    rises = np.flatnonzero(np.diff(above) > 0.1)
    gap, kept = MIN_ONSET_GAP_S * rate_hz, list[int]()
    for k in rises:
        if not kept or k - kept[-1] >= gap:
            kept.append(int(k))
    return kept


def _outliers(amplitudes: FloatArray, peaks: FloatArray) -> BoolArray:
    """The authors' rejection: both amplitude and peak five deviations below the median."""
    if amplitudes.size < 2:
        return np.zeros(amplitudes.size, dtype=bool)
    amp_floor = min(float(np.median(amplitudes) - 5 * np.std(amplitudes, ddof=1)), 0.03)
    peak_floor = min(float(np.median(peaks) - 5 * np.std(peaks, ddof=1)), -0.02)
    return (amplitudes < amp_floor) & (peaks < peak_floor)


def detect_spikes(v: FloatArray, rate_hz: float, slope_v_per_s: float) -> Spikes:
    """Spikes of a trace in volts, by the authors' criterion for that cell."""
    span, median = round(PEAK_SEARCH_S * rate_hz), float(np.median(v))
    onsets, peaks = [], []
    for k in _onset_candidates(v, rate_hz, slope_v_per_s):
        if k + span >= v.size:
            continue
        peak = k + int(np.argmax(v[k : k + span + 1]))
        if v[peak] - v[k] > MIN_AMPLITUDE_V and v[peak] > median:
            onsets.append(k)
            peaks.append(peak)
    on, pk = np.array(onsets, dtype=np.int64), np.array(peaks, dtype=np.int64)
    keep = ~_outliers(v[pk] - v[on], v[pk])
    return Spikes(on[keep], pk[keep], v[on[keep]])


def _repolarisation(v: FloatArray, rate_hz: float, onset: int, peak: int) -> int:
    """Where the smoothed potential returns to its onset value or turns upward."""
    stop = min(v.size - 1, peak + round(REPOLARISATION_S * rate_hz))
    width = max(1, round(rate_hz / 2000))
    segment = np.convolve(v[onset : stop + 1], np.ones(width) / width, mode="same")
    level = v[onset]
    for j in range(peak - onset + 21, segment.size):
        if segment[j] < level or segment[j] > segment[j - 1]:
            return min(v.size - 1, onset + j)
    return min(v.size - 1, onset + segment.size)


def spike_mask(v: FloatArray, spikes: Spikes, rate_hz: float) -> BoolArray:
    """Samples from each spike's onset through its repolarisation."""
    mask = np.zeros(v.size, dtype=bool)
    for onset, peak in zip(spikes.onsets, spikes.peaks, strict=True):
        mask[onset : _repolarisation(v, rate_hz, int(onset), int(peak)) + 1] = True
    return mask


def correlation_time_ms(segments: Sequence[FloatArray], dt_ms: float) -> float:
    """Lag at which the autocorrelation about the pooled mean first falls to ``1/e``."""
    mean = float(np.mean(np.concatenate(segments)))
    length = max(s.size for s in segments)
    products, counts = np.zeros(length), np.zeros(length)
    for s in segments:
        centred = s - mean
        full = fftconvolve(centred, centred[::-1], mode="full")[s.size - 1 :]
        products[: s.size] += full
        counts[: s.size] += np.arange(s.size, 0, -1)
    valid = counts > 0
    auto = products[valid] / counts[valid]
    return _one_e(auto / auto[0], dt_ms)


def window_hits(passing: BoolArray, epochs: Sequence[tuple[int, int]], window: int) -> float:
    """Share of whole windows, tiled inside each epoch, that contain a passing sample."""
    hits = total = 0
    for start, stop in epochs:
        count = (stop - start) // window
        if count:
            blocks = passing[start : start + count * window].reshape(count, window)
            hits += int(blocks.any(axis=1).sum())
            total += count
    return hits / total if total else math.nan


Interval = tuple[float, float]


def _rows(times: FloatArray) -> list[Interval]:
    """Epoch rows ``[start, stop]`` in seconds; the deposit marks none with a lone NaN."""
    table = np.atleast_2d(times)
    if table.shape[1] != 2:
        return []
    return [(float(a), float(b)) for a, b in table if not math.isnan(a)]


def _subtract(epoch: Interval, cuts: Sequence[Interval]) -> list[Interval]:
    pieces = [epoch]
    for lo, hi in sorted(cuts):
        pieces = [q for a, b in pieces for q in ((a, min(b, lo)), (max(a, hi), b)) if q[1] > q[0]]
    return pieces


def state_epochs(
    quiet: FloatArray, whisking: FloatArray, contacts: FloatArray
) -> dict[str, list[Interval]]:
    """Quiet epochs that touch no contact, and whisking with each contact guarded out."""
    touch = _rows(contacts)
    clear = [(a, b) for a, b in _rows(quiet) if all(hi < a or lo > b for lo, hi in touch)]
    guarded = [(lo - CONTACT_GUARD_S, hi + CONTACT_GUARD_S) for lo, hi in touch]
    active = [q for epoch in _rows(whisking) for q in _subtract(epoch, guarded)]
    return {"quiet": clear, "whisking": active}


def _observable(
    grid: uo.Grid, membrane: uo.Membrane, dt_ms: float
) -> tuple[FloatArray, FloatArray, FloatArray]:
    """The model's chain, the potential a recording reads in each state, and the stationary mass.

    A cut spike is a straight line from threshold to where the membrane resumes,
    so each refractory stage reads as its point on the line from zero to the reset.
    """
    chain, _ = uo._chain(grid, membrane, dt_ms)
    stages = chain.shape[0] - grid.nodes.size
    ramp = membrane.reset * np.arange(1, stages + 1) / (stages + 1)
    return chain, np.concatenate([grid.nodes, ramp]), uo._stationary_mass(chain)


def _level(grid: uo.Grid, membrane: uo.Membrane, dt_ms: float) -> float:
    """The mean potential a recording of the model reads, from threshold."""
    _, values, mass = _observable(grid, membrane, dt_ms)
    return float(values @ mass)


def twin_autocovariance(
    grid: uo.Grid, membrane: uo.Membrane, dt_ms: float, lags: int
) -> FloatArray:
    """Autocovariance of the potential a recording of the model reads, propagated exactly."""
    chain, values, mass = _observable(grid, membrane, dt_ms)
    centred = values - float(values @ mass)
    carried, out = centred * mass, np.empty(lags)
    for k in range(lags):
        out[k] = centred @ carried
        carried = chain @ carried
    return out


def _one_e(auto: FloatArray, dt_ms: float) -> float:
    """Lag at which a normalised autocorrelation first falls to ``1/e``."""
    below = np.flatnonzero(auto < math.exp(-1.0))
    if below.size == 0:
        return math.nan
    k = int(below[0])
    fraction = (auto[k - 1] - math.exp(-1.0)) / (auto[k - 1] - auto[k])
    return float((k - 1 + fraction) * dt_ms)


def twin_correlation_time_ms(grid: uo.Grid, membrane: uo.Membrane, dt_ms: float) -> float:
    """The correlation time a recording of the model would show, spikes cut as in the data."""
    cov = twin_autocovariance(grid, membrane, dt_ms, round(MAX_CORRELATION_MS / dt_ms))
    return _one_e(cov / cov[0], dt_ms)


def residual_autocovariance(cov: FloatArray, width: int) -> FloatArray:
    """Autocovariance of a stationary process less its centred running mean of ``width`` samples.

    With ``b`` the running-mean kernel, the remainder's autocovariance is
    ``C - 2 b*C + b*b*C``; ``cov`` holds ``C`` at non-negative lags and must
    reach well beyond two widths.
    """
    full = np.concatenate([cov[:0:-1], cov])
    kernel = np.ones(width) / width
    once = np.convolve(full, kernel, mode="same")
    twice = np.convolve(once, kernel, mode="same")
    return np.asarray((full - 2 * once + twice)[cov.size - 1 :], dtype=np.float64)


def _mean_for_level(grid: uo.Grid, level: float, tau_ms: float, dt_ms: float) -> float:
    """The model mean at which a recording would read mean potential ``level``."""
    low, high = grid.low + 4.0, -GRID_STEP
    for _ in range(40):
        mean = (low + high) / 2
        if _level(grid, uo.Membrane(tau_ms, mean, mean, uo.REFRACTORY_MS), dt_ms) < level:
            low = mean
        else:
            high = mean
    return (low + high) / 2


@dataclass(frozen=True)
class Calibration:
    """The recording's noise amplitude, the twin's time constant, and the grid they share."""

    grid: uo.Grid
    sigma: float
    tau_ms: float


def calibrate(
    fast_sd: float, fast_ms: float, level: float, dt_ms: float, slow_ms: float = SLOW_MS
) -> Calibration:
    """Noise amplitude and time constant at which the model, analysed as the recording is, agrees.

    The running mean that separates the slow part takes some of the fast
    process's variance with it, and the threshold cuts off more, so the fast
    remainder's spread is below the noise amplitude; both, and the resets, also
    shorten its correlation time. The model at the recording's mean level is
    therefore passed through the same separation exactly, and the amplitude and
    time constant are adjusted until its remainder has the recording's spread
    and correlation time. ``level`` is the mean potential from threshold, in volts.
    """
    grid = uo.Grid(-max(GRID_FLOOR, math.ceil(-level / fast_sd + 6.0)), GRID_STEP)
    width = round(slow_ms / dt_ms)
    sigma, tau = fast_sd, fast_ms
    for _ in range(FIT_ROUNDS):
        mean = _mean_for_level(grid, level / sigma, tau, dt_ms)
        membrane = uo.Membrane(tau, mean, mean, uo.REFRACTORY_MS)
        cov = twin_autocovariance(grid, membrane, dt_ms, 3 * width)
        remainder = residual_autocovariance(cov, width)
        sigma = fast_sd / math.sqrt(float(remainder[0]))
        tau *= fast_ms / _one_e(remainder / remainder[0], dt_ms)
    return Calibration(grid, sigma, tau)


def twin_means(calibration: Calibration, levels: FloatArray, dt_ms: float) -> FloatArray:
    """The model mean behind each slow level, in noise amplitudes, through the model's own curve."""
    grid, tau = calibration.grid, calibration.tau_ms
    means = np.arange(grid.low + 4.0, 0.0, MEAN_STEP)
    read = np.array([_level(grid, uo.Membrane(tau, m, m, uo.REFRACTORY_MS), dt_ms) for m in means])
    return np.asarray(np.interp(levels, read, means), dtype=np.float64)


def shorten(table: FloatArray, steps: int) -> FloatArray:
    """The law table of a shorter window, read off a longer one.

    A spike after the shorter window, and survival to the end of the longer
    one, are both survival of the shorter window.
    """
    return np.vstack([table[:steps], table[steps:].sum(axis=0)])


class Twin:
    """The model membrane fitted to a recorded cell, asked about one next-content window."""

    def __init__(
        self,
        grid: uo.Grid,
        membrane: uo.Membrane,
        window_ms: float,
        dt_ms: float,
        longer: FloatArray | None = None,
    ):
        self.grid, self.membrane, self.dt_ms = grid, membrane, dt_ms
        steps = round(window_ms / dt_ms)
        if longer is None:
            self.table = uo.laws(grid, membrane, window_ms, dt_ms)
        else:
            self.table = shorten(longer, steps)
        self.density, _, self.rate_hz = uo.stationary(grid, membrane, dt_ms)
        self._passing: dict[float, BoolArray] = {}

    def passing(self, scale: float) -> BoolArray:
        if scale not in self._passing:
            self._passing[scale] = uo.passing_states(self.table, self.grid, scale)
        return self._passing[scale]

    def pass_fraction(self, scale: float) -> float:
        return float(self.density @ self.passing(scale))

    def hit_probability(self, scale: float, content_ms: float) -> float:
        return uo.hit_probability(
            self.grid, self.membrane, self.passing(scale), content_ms, self.dt_ms
        )

    def occupied(self, x: FloatArray, failing: BoolArray, scale: float) -> BoolArray:
        """Whether each recorded sample, in noise amplitudes from threshold, passes."""
        nodes, inside = _nodes(self.grid, x, failing)
        return inside & self.passing(scale)[nodes]


def _nodes(grid: uo.Grid, x: FloatArray, failing: BoolArray) -> tuple[NDArray[np.int64], BoolArray]:
    """Each sample's nearest grid node, and whether it is a subthreshold state on the grid."""
    finite = np.nan_to_num(x, nan=1.0)
    nodes = np.rint((finite - grid.low) / grid.step).astype(np.int64)
    inside = (~failing) & (finite < 0.0) & (nodes >= 0)
    return np.clip(nodes, 0, grid.nodes.size - 1), inside


class QuasiStatic:
    """Twins held at every mean the slow part of the potential visits.

    Within a next-content window the slow part barely moves, so the law of the
    next spike time from a state is that of the model membrane at the mean
    behind the slow part's current level. Means are binned to ``MEAN_STEP``; the
    twin's rate and pass fraction are averages over them, weighted by the time
    spent at each.
    """

    def __init__(self, grid: uo.Grid, means: FloatArray, tau_ms: float):
        binned = np.minimum(np.rint(means / MEAN_STEP).astype(np.int64), -1)
        steps, self.index, counts = np.unique(binned, return_inverse=True, return_counts=True)
        self.grid = grid
        self.weights = counts / counts.sum()
        self.twins: dict[float, list[Twin]] = {w: [] for w in uo.WINDOWS_MS}
        longest = max(uo.WINDOWS_MS)
        for m in (float(k) * MEAN_STEP for k in steps):
            membrane = uo.Membrane(tau_ms, m, m, uo.REFRACTORY_MS)
            table = uo.laws(grid, membrane, longest, DT_MS)
            for w in uo.WINDOWS_MS:
                self.twins[w].append(Twin(grid, membrane, w, DT_MS, longer=table))

    @property
    def rate_hz(self) -> float:
        twins = self.twins[uo.WINDOWS_MS[0]]
        return float(sum(w * t.rate_hz for w, t in zip(self.weights, twins, strict=True)))

    def pass_fraction(self, window_ms: float, scale: float) -> float:
        pairs = zip(self.weights, self.twins[window_ms], strict=True)
        return float(sum(w * t.pass_fraction(scale) for w, t in pairs))

    def occupied(
        self, window_ms: float, x: FloatArray, failing: BoolArray, scale: float
    ) -> BoolArray:
        table = np.stack([t.passing(scale) for t in self.twins[window_ms]])
        nodes, inside = _nodes(self.grid, x, failing)
        return np.asarray(inside & table[self.index, nodes], dtype=bool)


def _interpolated(v: FloatArray, failing: BoolArray) -> FloatArray:
    """The potential with each failing stretch replaced by a straight line, as spikes are cut."""
    kept = np.flatnonzero(~failing)
    return np.interp(np.arange(v.size), kept, v[kept])


def _slow_part(
    smooth: FloatArray, epochs: Sequence[tuple[int, int]], dt_ms: float, slow_ms: float
) -> FloatArray:
    """A centred running mean over ``slow_ms`` within each epoch."""
    width = round(slow_ms / dt_ms)
    return np.concatenate([uniform_filter1d(smooth[a:b], width, mode="nearest") for a, b in epochs])


def _twin_row(
    x: FloatArray,
    failing: BoolArray,
    epochs: Sequence[tuple[int, int]],
    twin: QuasiStatic,
    window_ms: float,
) -> dict[str, Any]:
    """Measured beside twin at every noise share; measured visits in every content window."""
    row: dict[str, Any] = {"window_ms": window_ms}
    row["pass_fraction"], row["window_hit_probability"] = {}, {}
    for scale in uo.CHANGE_SCALES:
        passing = twin.occupied(window_ms, x, failing, scale)
        row["pass_fraction"][f"{scale:g}"] = {
            "measured": float(passing.mean()),
            "twin": twin.pass_fraction(window_ms, scale),
        }
        row["window_hit_probability"][f"{scale:g}"] = {
            f"{w:g}": window_hits(passing, epochs, round(w / DT_MS)) for w in uo.CONTENT_WINDOWS_MS
        }
    return row


def measure_state(
    v: FloatArray,
    failing: BoolArray,
    epochs: Sequence[tuple[int, int]],
    threshold: float,
    spikes: int,
    dt_ms: float,
    slow_ms: float = SLOW_MS,
) -> dict[str, Any]:
    """One cell in one state: its statistics, and its occupancy beside its twin's.

    The potential, spikes cut, splits into a slow part, its running mean over
    ``SLOW_MS``, and a fast remainder. The fast remainder's standard deviation
    is the noise amplitude and its correlation time the twin's time constant;
    the slow part, in those amplitudes from threshold, is the twin's level.
    """
    smooth = _interpolated(v, failing)
    slow = _slow_part(smooth, epochs, dt_ms, slow_ms)
    fast = smooth - slow
    fast_ms = correlation_time_ms([fast[a:b] for a, b in epochs], dt_ms)
    level = float(smooth.mean()) - threshold
    fit = calibrate(float(fast[~failing].std()), fast_ms, level, dt_ms, slow_ms)
    x = np.asarray((v - threshold) / fit.sigma, dtype=np.float64)
    means = twin_means(fit, np.asarray((slow - threshold) / fit.sigma), dt_ms)
    duration_s = v.size * dt_ms / 1000.0
    result: dict[str, Any] = {
        "duration_s": duration_s,
        "spikes": spikes,
        "rate_hz": spikes / duration_s,
        "sigma_mv": 1000.0 * fit.sigma,
        "tau_ms": fit.tau_ms,
        "fast_correlation_ms": fast_ms,
        "distance": float(-x[~failing].mean()),
        "mean_level": float(means.mean()),
        "slow_sd": float(means.std()),
    }
    twin = QuasiStatic(fit.grid, means, fit.tau_ms)
    result["twin_rate_hz"] = twin.rate_hz
    result["windows"] = [_twin_row(x, failing, epochs, twin, w) for w in uo.WINDOWS_MS]
    return result


class Deposit:
    """The authors' MATLAB v7.3 structure ``data``: one row per sweep, fields as columns."""

    def __init__(self, path: Path):
        import h5py  # a dependency of this command alone, not of the pipeline's tests

        self.file = h5py.File(path, "r")
        self.data = self.file["data"]

    def _cell(self, field: str, row: int) -> Any:
        return self.file[self.data[field][()].ravel()[row]]

    def rows(self) -> int:
        return int(self.data["Cell_ID"].size)

    def text(self, field: str, row: int) -> str:
        codes = np.asarray(self._cell(field, row)[()]).ravel()
        return "".join(chr(int(c)) for c in codes)

    def number(self, field: str, row: int) -> float:
        return float(np.asarray(self.data[field][()]).ravel()[row])

    def array(self, field: str, row: int) -> FloatArray:
        """A numeric cell entry in MATLAB's orientation; an empty entry as a NaN row."""
        entry = self._cell(field, row)
        if entry.attrs.get("MATLAB_empty", 0):
            return np.full((1, 2), np.nan)
        return np.asarray(entry[()], dtype=np.float64).T


@dataclass
class _Pooled:
    """One state's samples from every sweep of a cell, at the model's time step."""

    volts: list[FloatArray]
    failing: list[BoolArray]
    spikes: int = 0

    def epochs(self) -> list[tuple[int, int]]:
        edges = np.cumsum([0] + [len(v) for v in self.volts])
        return [(int(a), int(b)) for a, b in zip(edges[:-1], edges[1:], strict=True)]


def _decimate(v: FloatArray, mask: BoolArray, rate_hz: float) -> tuple[FloatArray, BoolArray]:
    """Block means of the potential at the model's step; a block fails if any sample does."""
    k = round(rate_hz * DT_MS / 1000.0)
    n = v.size // k
    means = np.asarray(v[: n * k].reshape(n, k).mean(axis=1), dtype=np.float64)
    return means, np.asarray(mask[: n * k].reshape(n, k).any(axis=1), dtype=bool)


def _contacts(deposit: Deposit, row: int) -> FloatArray:
    active = deposit.array("Sweep_ActiveContactTimes", row)
    passive = deposit.array("Sweep_PassiveContactTimes", row)
    rows = _rows(active) + _rows(passive)
    return np.array(rows, dtype=np.float64).reshape(len(rows), 2)


def _pool_sweep(
    deposit: Deposit, row: int, pooled: dict[str, _Pooled], thresholds: list[FloatArray]
) -> None:
    """Add one sweep's spikes and its samples in each state to the cell's pools."""
    v = deposit.array("Sweep_MembranePotential", row).ravel()
    missing = ~np.isfinite(v)
    if missing.any():  # bridged for detection, and counted as failing states
        v = _interpolated(np.nan_to_num(v), missing)
    rate = deposit.number("Sweep_MembranePotential_SamplingRate", row)
    spikes = detect_spikes(v, rate, deposit.number("Cell_APThreshold_Slope", row))
    thresholds.append(spikes.thresholds)
    volts, failing = _decimate(v, spike_mask(v, spikes, rate) | missing, rate)
    onsets = spikes.onsets / rate
    epochs = state_epochs(
        deposit.array("Sweep_QuietTimes", row),
        deposit.array("Sweep_WhiskingTimes", row),
        _contacts(deposit, row),
    )
    step = DT_MS / 1000.0
    for state, spans in epochs.items():
        for a, b in spans:
            lo, hi = round(a / step), min(round(b / step), volts.size)
            if hi > lo:
                pooled[state].volts.append(volts[lo:hi])
                pooled[state].failing.append(failing[lo:hi])
                pooled[state].spikes += int(np.sum((onsets >= a) & (onsets < b)))


def measure_cell(deposit: Deposit, rows: Sequence[int], slow_ms: float = SLOW_MS) -> dict[str, Any]:
    """Every state of one cell with enough spikes to read its threshold."""
    first = rows[0]
    cell: dict[str, Any] = {
        "cell": deposit.text("Cell_ID", first),
        "type": deposit.text("Cell_Type", first),
        "depth_um": deposit.number("Cell_Depth", first),
        "sweeps": len(rows),
    }
    pooled = {state: _Pooled([], []) for state in STATES}
    thresholds: list[FloatArray] = []
    for row in rows:
        _pool_sweep(deposit, row, pooled, thresholds)
    every = np.concatenate(thresholds)
    cell["spikes"] = int(every.size)
    if every.size < MIN_SPIKES:
        return cell
    threshold = float(np.median(every))
    cell["threshold_mv"] = 1000.0 * threshold
    cell["states"] = {
        state: measure_state(
            np.concatenate(p.volts),
            np.concatenate(p.failing),
            p.epochs(),
            threshold,
            p.spikes,
            DT_MS,
            slow_ms,
        )
        for state, p in pooled.items()
        if sum(len(v) for v in p.volts) * DT_MS >= MIN_STATE_MS
    }
    return cell


def _pairs(deposit: Deposit) -> dict[str, int]:
    """Sweeps timed to the second, and those shared by two cells of one mouse.

    Some sweeps carry a date and no time of day; they cannot show a pair and
    are left out.
    """
    stamps = np.asarray(deposit.data["Sweep_StartTime"][()])
    timed = np.flatnonzero(np.any(stamps[3:] != 0, axis=0))
    starts: dict[tuple[str, tuple[float, ...]], set[str]] = {}
    for row in (int(r) for r in timed):
        key = (deposit.text("Mouse_Name", row), tuple(stamps[:, row].tolist()))
        starts.setdefault(key, set()).add(deposit.text("Cell_ID", row))
    return {
        "sweeps": deposit.rows(),
        "timed_sweeps": int(timed.size),
        "shared_starts": sum(1 for cells in starts.values() if len(cells) > 1),
    }


def _measure_rows(path: Path, rows: list[int], slow_ms: float) -> dict[str, Any]:
    return measure_cell(Deposit(path), rows, slow_ms)


def run(
    path: Path, slow_ms: float = SLOW_MS, types: Sequence[str] = (), workers: int = 4
) -> dict[str, Any]:
    """Every cell of the deposit (or of ``types``), grouped from its sweeps, in worker processes.

    Each worker runs single-threaded linear algebra: on matrices of a few
    hundred rows the threads of a parallel BLAS cost more than they save.
    """
    deposit = Deposit(path)
    by_cell: dict[str, list[int]] = {}
    for row in range(deposit.rows()):
        if not types or deposit.text("Cell_Type", row) in types:
            by_cell.setdefault(deposit.text("Cell_ID", row), []).append(row)
    os.environ["OPENBLAS_NUM_THREADS"] = "1"
    context = multiprocessing.get_context("spawn")
    cells = []
    with ProcessPoolExecutor(workers, mp_context=context) as pool:
        jobs = pool.map(
            _measure_rows, [path] * len(by_cell), by_cell.values(), [slow_ms] * len(by_cell)
        )
        for count, cell in enumerate(jobs, 1):
            print(f"{count}/{len(by_cell)} {cell['cell']}", file=sys.stderr, flush=True)
            cells.append(cell)
    return {
        "source": "Kiritani et al. 2023, PLoS ONE 18:e0287174; doi:10.5281/zenodo.7833080",
        "licence": "CC-BY-4.0",
        "dt_ms": DT_MS,
        "min_spikes": MIN_SPIKES,
        "min_state_s": MIN_STATE_MS / 1000.0,
        "pairs": _pairs(deposit),
        "slow_ms": slow_ms,
        "cells": cells,
    }


def _fetch_chunk(url: str, path: Path, start: int, stop: int) -> None:
    """Bytes ``[start, stop)`` of ``url`` into ``path``, resuming until the chunk is whole.

    A server that closes the connection early ends the read without an error,
    so completeness is judged by the chunk's size, not by the read returning.
    Only attempts that add no bytes count toward the limit.
    """
    stalled = 0
    while (done := path.stat().st_size if path.exists() else 0) < stop - start:
        try:
            _fetch_once(url, path, start, stop)
        except OSError:  # URLError and timeouts; the chunk resumes where it stopped
            pass
        if (path.stat().st_size if path.exists() else 0) > done:
            stalled = 0
            continue
        stalled += 1
        if stalled == FETCH_ATTEMPTS:
            raise RuntimeError(f"no progress on bytes {start + done}-{stop - 1}")
        time.sleep(2.0**stalled)


def _fetch_once(url: str, path: Path, start: int, stop: int) -> None:
    """Bytes ``[start, stop)`` of ``url`` into ``path``, resuming a partial chunk."""
    done = path.stat().st_size if path.exists() else 0
    if done >= stop - start:
        return
    if not url.startswith("https://"):
        raise ValueError(f"refusing to fetch {url}: not https")
    span = {"Range": f"bytes={start + done}-{stop - 1}"}
    request = urllib.request.Request(url, headers=span)  # noqa: S310  # nosec B310
    with (
        urllib.request.urlopen(request, timeout=120) as response,  # noqa: S310  # nosec B310
        path.open("ab") as out,
    ):
        while block := response.read(2**20):
            out.write(block)


def fetch(cache: Path = CACHE, workers: int = 16) -> Path:
    """Download the deposit in parallel ranges, check its digest, extract the data file."""
    target = cache / Path(DATA_MEMBER).name
    if target.exists():
        return target
    parts = cache / "parts"
    parts.mkdir(parents=True, exist_ok=True)
    starts = range(0, RECORD_BYTES, CHUNK_BYTES)
    paths = [parts / f"{k:05d}" for k in range(len(starts))]
    with ThreadPoolExecutor(workers) as pool:
        jobs = [
            pool.submit(_fetch_chunk, RECORD_URL, p, s, min(s + CHUNK_BYTES, RECORD_BYTES))
            for p, s in zip(paths, starts, strict=True)
        ]
        for job in jobs:
            job.result()
    archive = cache / "Kiritani_data_code.zip"
    digest = hashlib.md5(usedforsecurity=False)
    with archive.open("wb") as out:
        for p in paths:
            data = p.read_bytes()
            digest.update(data)
            out.write(data)
    if digest.hexdigest() != RECORD_MD5:
        raise RuntimeError("the downloaded archive does not match the deposit's digest")
    with zipfile.ZipFile(archive) as z, z.open(DATA_MEMBER) as src, target.open("wb") as dst:
        while block := src.read(2**24):
            dst.write(block)
    archive.unlink()
    for p in paths:
        p.unlink()
    parts.rmdir()
    return target


def main() -> None:
    """``fetch`` downloads the deposit; ``run`` reads it and writes ``recordings.json``.

    ``run --slow-ms`` repeats the analysis at another split between the slow
    part and the fast remainder, and writes ``recordings_slow<ms>.json``
    beside the main summary, leaving it untouched.
    """
    parser = argparse.ArgumentParser(description="Occupancy of recorded membranes")
    parser.add_argument("command", choices=["fetch", "run"])
    parser.add_argument("--slow-ms", type=float, default=SLOW_MS)
    parser.add_argument("--type", action="append", default=[], help="cell types, default all")
    args = parser.parse_args()
    if args.command == "fetch":
        fetch()
        return
    summary = run(CACHE / Path(DATA_MEMBER).name, args.slow_ms, args.type)
    name = "recordings.json" if args.slow_ms == SLOW_MS else f"recordings_slow{args.slow_ms:g}.json"
    (OUTPUT / name).write_text(json.dumps(summary, indent=2) + "\n")


if __name__ == "__main__":
    main()
