"""Post-processing helpers for the finite-N dynamic-ramp simulation.

The fitted quantities are summaries of finite sampled trajectories. They are
heuristic numerical evidence, not trajectory theorems or proofs of adiabaticity.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
from numpy.typing import NDArray
from scipy.optimize import curve_fit

from bifurcation import bessel_ratio


FloatArray = NDArray[np.float64]


@dataclass(frozen=True)
class PowerLawFit:
    """Least-squares fit of ``y = prefactor * x**exponent`` in log space."""

    exponent: float
    prefactor: float


@dataclass(frozen=True)
class OnsetFit:
    """Shifted-power fit on the early macroscopic foot."""

    amplitude: float
    onset_coupling: float
    exponent: float


def fit_power_law(x: FloatArray, y: FloatArray) -> PowerLawFit:
    """Fit a positive power law by ordinary least squares in log coordinates."""
    if x.shape != y.shape or x.size < 2:
        raise ValueError("power-law inputs must have equal shape and at least two values")
    if np.any(x <= 0.0) or np.any(y <= 0.0):
        raise ValueError("power-law inputs must be strictly positive")
    exponent, log_prefactor = np.polyfit(np.log(x), np.log(y), 1)
    return PowerLawFit(float(exponent), float(np.exp(log_prefactor)))


def _first_sustained(values: FloatArray, level: float, sustain: int) -> int | None:
    above = values >= level
    kernel = np.ones(sustain, dtype=int)
    runs = np.convolve(above.astype(int), kernel, mode="valid")
    indices = np.flatnonzero(runs == sustain)
    return None if indices.size == 0 else int(indices[0])


def replica_escape_couplings(
    coupling: FloatArray,
    order_replicas: FloatArray,
    level: float = 0.2,
    sustain: int = 3,
    critical_coupling: float = 2.0,
) -> FloatArray:
    """Return each replica's first sustained crossing of a fixed macroscopic level."""
    if order_replicas.shape[0] != coupling.size:
        raise ValueError("one coupling value is required per order-parameter sample")
    if sustain <= 0:
        raise ValueError("sustain must be positive")
    postcritical = coupling >= critical_coupling
    eligible_coupling = coupling[postcritical]
    eligible_order = order_replicas[postcritical]
    escape = np.full(order_replicas.shape[1], np.nan)
    for replica in range(order_replicas.shape[1]):
        index = _first_sustained(eligible_order[:, replica], level, sustain)
        if index is not None:
            escape[replica] = eligible_coupling[index]
    return escape


def collapse_deviation(concentration: FloatArray, order: FloatArray) -> float:
    """Return RMS residual from the parameter-free Bessel-ratio curve."""
    if concentration.shape != order.shape:
        raise ValueError("concentration and order arrays must have equal shape")
    predicted = np.array([bessel_ratio(float(value)) for value in concentration])
    return float(np.sqrt(np.mean((order - predicted) ** 2)))


def _shifted_power(coupling: FloatArray, amplitude: float, onset: float, beta: float) -> FloatArray:
    return amplitude * np.maximum(coupling - onset, 1e-12) ** beta


def fit_onset_exponent(
    coupling: FloatArray,
    order: FloatArray,
    critical_coupling: float = 2.0,
    foot_min: float = 0.1,
    foot_max: float = 0.4,
) -> OnsetFit:
    """Fit ``r=A(K-K0)^beta`` over a fixed early-foot order range."""
    selected = (coupling > critical_coupling) & (order >= foot_min) & (order <= foot_max)
    x = coupling[selected]
    y = order[selected]
    if x.size < 5:
        raise ValueError("at least five early-foot samples are required")
    upper_onset = float(x[0] - 1e-8)
    parameters, _ = curve_fit(
        _shifted_power,
        x,
        y,
        p0=(0.8, critical_coupling, 0.5),
        bounds=([0.0, critical_coupling, 0.1], [10.0, upper_onset, 2.0]),
        maxfev=50_000,
    )
    return OnsetFit(*(float(value) for value in parameters))
