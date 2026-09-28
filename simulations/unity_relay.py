"""The noise-floor test of a thalamic relay cell, in tonic and in burst mode (U99).

P predicts more unity across cortical patches joined through the thalamus in
whichever mode of its relay cells passes more often within a content window.
This module applies the occupancy protocol of ``unity_occupancy`` to a relay
cell that has both modes, so that the direction is computed rather than left
to a measurement.

The cell is the integrate-and-fire-or-burst model of Smith, Cox, Sherman &
Rinzel (2000, J Neurophysiol 83:588-610): a leaky integrate-and-fire membrane
with a low-threshold calcium current ``g_T h (V - E_T)`` that flows only above
``V_h``, whose inactivation ``h`` relaxes toward one below ``V_h`` with time
constant ``τ_h+`` and toward zero above it with ``τ_h-``. Parameters are the
published ones: ``C = 2 µF/cm²``, ``g_L = 0.035 mS/cm²``, ``E_L = -65 mV``,
``g_T = 0.07 mS/cm²``, ``E_T = 120 mV``, ``V_h = -60 mV``, spike threshold
``-35 mV``, reset ``-50 mV``, ``τ_h- = 20 ms``, ``τ_h+ = 100 ms``. White
noise is added to the membrane, of the amplitude that gives the passive
membrane a stationary standard deviation ``σ``, the unit of every change here.

The two modes are two ranges of a constant bias current: in burst mode the
membrane rests below ``V_h``, the calcium current is de-inactivated, and noise
that carries the membrane past ``V_h`` sets off a burst (the rest lies two to
six noise amplitudes below ``V_h``; closer, the rate falls again as the
current inactivates between bursts); in tonic mode it rests
at least three noise amplitudes above ``V_h``, the current is inactivated, and
the cell is an integrate-and-fire membrane. In each mode the bias is calibrated
so that the stationary firing rate equals a declared rate, so the modes are
compared at matched rates.

The protocol is that of ``unity_occupancy``. The next content is the time of
the first spike within a window, or its absence; the response of a state to a
change is the total variation between the laws of that content from the state
and from the state with the membrane moved by the change, ``h`` unchanged. A
state passes when every change of one, two or three noise amplitudes, either
way, that stays below the spike threshold moves the content by at least ``θ*``.
The pass fraction is the stationary mass of passing states, and the window hit
probability the chance that a stationary cell occupies a passing state at some
step of a content window. Everything is computed on a grid in ``(V, h)`` by
propagating probability exactly: the membrane's step is Gaussian about its
deterministic update, a crossing between two samples is counted with the
Brownian-bridge probability, and ``h`` moves deterministically and is split
between its two nearest nodes. Nothing is sampled. Each mode's calibrated cell
is rerun at half every grid step, with its bias kept, as the resolution check.

Declared, not measured: the noise amplitudes, the rates, the windows, and that
one bias current, with no synaptic conductance, sets the mode. The model has no
feedback from the reticular nucleus and no cortical input with its own
dynamics. ``relay.json`` is written beside the occupancy summaries, and
``unity_macros.py`` reads it.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

import numpy as np
import scipy.sparse as sp
from numpy.typing import NDArray
from scipy.optimize import brentq
from scipy.sparse.linalg import spsolve
from scipy.special import ndtr

from unity_estimates import FLUCTUATION_TV
from unity_occupancy import (
    CONTENT_WINDOWS_MS,
    INDEPENDENT_CARRIERS,
    SHIFTS,
    WINDOWS_MS,
    link_probability,
)

FloatArray = NDArray[np.float64]
BoolArray = NDArray[np.bool_]
Mode = Literal["burst", "tonic"]

OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_occupancy"

# Smith, Cox, Sherman & Rinzel (2000): mV, ms, µF/cm², mS/cm², µA/cm².
C = 2.0
GL = 0.035
EL = -65.0
GT = 0.07
ET = 120.0
VH = -60.0
VTH = -35.0
VRESET = -50.0
TAU_H_MINUS = 20.0
TAU_H_PLUS = 100.0
TAU_MS = C / GL
# The grid's floor, in noise amplitudes below V_h: four below the lowest burst rest.
FLOOR_SIGMAS = 10.0

SIGMAS_MV = (2.0, 4.0)
RATES_HZ = (0.5, 2.0)
MODES: tuple[Mode, ...] = ("burst", "tonic")
# Resting potentials, in noise amplitudes from V_h, that bound each mode's bias.
# Burst rate peaks near a rest two amplitudes below V_h; above it the current
# inactivates between bursts, so the burst range stops there.
REST_RANGE = {"burst": (-6.0, -2.0), "tonic": (3.0, 14.0)}


@dataclass(frozen=True)
class Resolution:
    """Grid steps: membrane in noise amplitudes, inactivation, and time in ms."""

    dv_per_sigma: float
    dh: float
    dt_ms: float

    def halved(self) -> Resolution:
        return Resolution(self.dv_per_sigma / 2, self.dh / 2, self.dt_ms / 2)


# The membrane's step must span about a grid step, or mass is pulled back from
# the threshold onto the top node: at this resolution the tonic rate is within
# a few per cent of the integrate-and-fire (Siegert) rate.
DEFAULT = Resolution(dv_per_sigma=0.05, dh=0.05, dt_ms=0.4)


def next_h(v: FloatArray, h: FloatArray, dt_ms: float) -> FloatArray:
    """Inactivation after one step: toward one below ``V_h``, toward zero above it."""
    rising = 1.0 - (1.0 - h) * math.exp(-dt_ms / TAU_H_PLUS)
    falling = h * math.exp(-dt_ms / TAU_H_MINUS)
    return np.asarray(np.where(v < VH, rising, falling), dtype=np.float64)


def drift(v: FloatArray, h: FloatArray, bias: float) -> FloatArray:
    """``dV/dt`` in mV per ms."""
    calcium = GT * h * (v >= VH) * (v - ET)
    return np.asarray((bias - GL * (v - EL) - calcium) / C, dtype=np.float64)


def _split(values: FloatArray, low: float, step: float, count: int) -> tuple[FloatArray, ...]:
    """Lower node and the weight on the node above, for linear interpolation."""
    position = (values - low) / step
    lower = np.clip(np.floor(position), 0, count - 2).astype(np.int64)
    upper = np.clip(position - lower, 0.0, 1.0)
    return lower.astype(np.float64), upper


class RelayCell:
    """One relay cell at a noise amplitude and bias, on a ``(V, h)`` grid."""

    def __init__(self, sigma_mv: float, bias: float, resolution: Resolution = DEFAULT) -> None:
        self.sigma, self.bias, self.dt = sigma_mv, bias, resolution.dt_ms
        self.dv = resolution.dv_per_sigma * sigma_mv
        # Nodes below the threshold, the top one half a step below it.
        count = math.ceil((VTH - VH + FLOOR_SIGMAS * sigma_mv) / self.dv)
        self.v = VTH - self.dv * (np.arange(count, 0, -1) - 0.5)
        self.h = np.linspace(0.0, 1.0, round(1.0 / resolution.dh) + 1)
        self.nv, self.nh = self.v.size, self.h.size
        self.v_of_state = np.tile(self.v, self.nh)
        self.h_of_state = np.repeat(self.h, self.nv)
        self.surviving, self.chain = self._matrices()
        self.spiking = 1.0 - np.asarray(self.surviving.sum(axis=0)).ravel()

    def index(self, voltage: float, inactivation: float) -> int:
        """The state nearest a membrane potential and an inactivation."""
        iv = int(np.argmin(np.abs(self.v - voltage)))
        ih = int(np.argmin(np.abs(self.h - inactivation)))
        return ih * self.nv + iv

    def _h_targets(self) -> tuple[NDArray[np.int64], FloatArray]:
        v: FloatArray = self.v_of_state
        h: FloatArray = self.h_of_state
        h_next = next_h(v, h, self.dt)
        lower, upper = _split(h_next, 0.0, float(self.h[1]), self.nh)
        return lower.astype(np.int64), upper

    def _v_step(self) -> tuple[list[NDArray[np.int64]], list[FloatArray]]:
        """Target membrane node and surviving probability, for each offset about the centre."""
        spread = self.sigma * math.sqrt(1.0 - math.exp(-2.0 * self.dt / TAU_MS))
        v: FloatArray = self.v_of_state
        h: FloatArray = self.h_of_state
        centre = v + drift(v, h, self.bias) * self.dt
        nearest = np.rint((centre - self.v[0]) / self.dv)
        nearest = np.clip(nearest, 0, self.nv - 1).astype(np.int64)
        upper_edge = np.append(self.v[:-1] + self.dv / 2, VTH)
        lower_edge = np.append(-np.inf, upper_edge[:-1])
        half = int(math.ceil(6.0 * spread / self.dv)) + 1
        targets, probabilities = [], []
        for offset in range(-half, half + 1):
            target = nearest + offset
            inside = (target >= 0) & (target < self.nv)
            target = np.clip(target, 0, self.nv - 1)
            cell = ndtr((upper_edge[target] - centre) / spread)
            cell = cell - ndtr((lower_edge[target] - centre) / spread)
            # A path between two sub-threshold samples may still have crossed.
            crossed = np.exp(-2.0 * (VTH - v) * (VTH - self.v[target]) / spread**2)
            targets.append(target)
            probabilities.append(np.where(inside, cell * (1.0 - crossed), 0.0))
        return targets, probabilities

    def _matrices(self) -> tuple[sp.csc_matrix, sp.csc_matrix]:
        """The surviving transition, and the full chain with a spike reset to ``V_reset``."""
        n = self.nv * self.nh
        source = np.arange(n)
        h_low, h_up = self._h_targets()
        rows, cols, values = [], [], []
        for target, probability in zip(*self._v_step(), strict=True):
            for h_node, weight in ((h_low, 1.0 - h_up), (h_low + 1, h_up)):
                rows.append(h_node * self.nv + target)
                cols.append(source)
                values.append(probability * weight)
        shape = (n, n)
        surviving = sp.csc_matrix(
            (np.concatenate(values), (np.concatenate(rows), np.concatenate(cols))), shape=shape
        )
        spiking = 1.0 - np.asarray(surviving.sum(axis=0)).ravel()
        reset = int(np.argmin(np.abs(self.v - VRESET)))
        jump = sp.csc_matrix(
            (
                np.concatenate([spiking * (1.0 - h_up), spiking * h_up]),
                (
                    np.concatenate([h_low * self.nv + reset, (h_low + 1) * self.nv + reset]),
                    np.concatenate([source, source]),
                ),
            ),
            shape=shape,
        )
        return surviving, sp.csc_matrix(surviving + jump)

    def stationary(self) -> tuple[FloatArray, float]:
        """Stationary mass on the states, and the firing rate in Hz."""
        n = self.chain.shape[0]
        system = sp.vstack([(self.chain - sp.identity(n))[1:], np.ones((1, n))]).tocsc()
        target = np.zeros(n)
        target[-1] = 1.0
        mass = np.clip(spsolve(system, target), 0.0, None)
        mass /= mass.sum()
        return mass, float(self.spiking @ mass) * 1000.0 / self.dt

    def laws(self, window_ms: float) -> FloatArray:
        """Column ``i``: spike mass at each step of the window from state ``i``, then survival."""
        backward = self.surviving.T.tocsr()
        steps = round(window_ms / self.dt)
        rows = np.empty((steps + 1, self.nv * self.nh))
        first = self.spiking.copy()
        for t in range(steps):
            rows[t] = first
            first = backward @ first
        rows[steps] = 1.0 - rows[:steps].sum(axis=0)
        return rows

    def least_response(self, window_ms: float) -> FloatArray:
        """The smallest response over every admissible change, or NaN where none is."""
        table = self.laws(window_ms).reshape(-1, self.nh, self.nv)
        least = np.full((self.nh, self.nv), np.inf)
        for shift in SHIFTS:
            k = round(shift * self.sigma / self.dv)
            moved = 0.5 * np.abs(table[:, :, k:] - table[:, :, :-k]).sum(axis=0)
            least[:, :-k] = np.minimum(least[:, :-k], moved)
            least[:, k:] = np.minimum(least[:, k:], moved)
        return np.where(np.isfinite(least), least, np.nan).ravel()

    def passing(self, window_ms: float) -> BoolArray:
        """The states at which every admissible change moves the next content by ``θ*``."""
        return np.asarray(np.nan_to_num(self.least_response(window_ms)) >= FLUCTUATION_TV)

    def hit_probability(self, mass: FloatArray, passing: BoolArray, window_ms: float) -> float:
        """Chance that a stationary cell occupies a passing state at some step of the window."""
        mass = mass.copy()
        hit = float(mass[passing].sum())
        mass[passing] = 0.0
        for _ in range(round(window_ms / self.dt)):
            mass = self.chain @ mass
            hit += float(mass[passing].sum())
            mass[passing] = 0.0
        return min(hit, 1.0)


def bias_for_rest(rest_mv: float) -> float:
    """The bias current at which the passive membrane rests at ``rest_mv``."""
    return GL * (rest_mv - EL)


def calibrate(
    mode: Mode, sigma_mv: float, rate_hz: float, resolution: Resolution = DEFAULT
) -> RelayCell:
    """The cell in ``mode`` whose stationary rate is ``rate_hz``."""
    low, high = (bias_for_rest(VH + k * sigma_mv) for k in REST_RANGE[mode])

    def excess(bias: float) -> float:
        return RelayCell(sigma_mv, bias, resolution).stationary()[1] - rate_hz

    try:
        bias = brentq(excess, low, high, xtol=1e-4)
    except ValueError as error:
        message = f"{rate_hz} Hz is out of reach in {mode} mode at σ = {sigma_mv} mV"
        raise ValueError(message) from error
    return RelayCell(sigma_mv, float(bias), resolution)


def cell_summary(
    mode: Mode,
    sigma_mv: float,
    rate_hz: float,
    windows_ms: tuple[float, ...],
    resolution: Resolution,
) -> list[dict[str, Any]]:
    """One calibrated cell, tested at every next-content window."""
    cell = calibrate(mode, sigma_mv, rate_hz, resolution)
    return summarize(cell, mode, rate_hz, windows_ms)


def summarize(
    cell: RelayCell, mode: Mode, rate_hz: float, windows_ms: tuple[float, ...]
) -> list[dict[str, Any]]:
    """Occupancy, passing mass and window visits of one cell at every next-content window."""
    sigma_mv = cell.sigma
    mass, rate = cell.stationary()
    rows = []
    for window in windows_ms:
        passing = cell.passing(window)
        hits = {f"{w:g}": cell.hit_probability(mass, passing, w) for w in CONTENT_WINDOWS_MS}
        rows.append(
            {
                "mode": mode,
                "config": {"sigma_mv": sigma_mv, "rate_hz": rate_hz, "window_ms": window},
                "bias": cell.bias,
                "rate_hz": rate,
                "mean_v": float(mass @ cell.v_of_state),
                "mean_h": float(mass @ cell.h_of_state),
                "pass_fraction": float(mass @ passing),
                "window_hit_probability": hits,
                "window_link_probability": {
                    w: {f"{k}": link_probability(h, k) for k in INDEPENDENT_CARRIERS}
                    for w, h in hits.items()
                },
            }
        )
    return rows


def run(
    sigmas_mv: tuple[float, ...] = SIGMAS_MV,
    rates_hz: tuple[float, ...] = RATES_HZ,
    windows_ms: tuple[float, ...] = WINDOWS_MS,
    resolution: Resolution = DEFAULT,
    check: bool = True,
) -> dict[str, Any]:
    """Both modes at every declared noise amplitude, rate and window, and the check."""
    cells = [
        row
        for sigma in sigmas_mv
        for rate in rates_hz
        for mode in MODES
        for row in cell_summary(mode, sigma, rate, windows_ms, resolution)
    ]
    summary: dict[str, Any] = {
        "fluctuation_tv": FLUCTUATION_TV,
        "shifts": list(SHIFTS),
        "resolution": vars(resolution),
        "cells": cells,
    }
    if check:
        summary["resolution_check"] = _check(sigmas_mv[-1], rates_hz[-1], windows_ms[0], resolution)
    return summary


def _check(sigma_mv: float, rate_hz: float, window_ms: float, resolution: Resolution) -> Any:
    """Each mode's calibrated cell again at half every grid step, with its bias kept."""
    rows: dict[str, list[dict[str, Any]]] = {"coarse": [], "fine": []}
    for mode in MODES:
        cell = calibrate(mode, sigma_mv, rate_hz, resolution)
        fine = RelayCell(sigma_mv, cell.bias, resolution.halved())
        rows["coarse"] += summarize(cell, mode, rate_hz, (window_ms,))
        rows["fine"] += summarize(fine, mode, rate_hz, (window_ms,))
    return rows


def write(directory: Path, **options: Any) -> None:
    """Save the run; publication macros read it later."""
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "relay.json").write_text(json.dumps(run(**options), indent=2) + "\n")


if __name__ == "__main__":
    write(OUTPUT)
