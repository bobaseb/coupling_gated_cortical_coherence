"""Post-processing helpers for the finite-N dynamic-ramp simulation.

The fitted quantities are summaries of finite sampled trajectories. They are
heuristic numerical evidence, not trajectory theorems or proofs of adiabaticity.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from numpy.typing import NDArray
from scipy.optimize import curve_fit
from scipy.stats import t as student_t

from bifurcation import bessel_ratio


FloatArray = NDArray[np.float64]

# curve_fit returns a parameter at a box bound to within rounding, not exactly.
_BOUND_TOLERANCE = 1e-8


@dataclass(frozen=True)
class BootstrapResult:
    exponent: float
    ci_low: float
    ci_high: float
    n_boot: int
    p_above: float
    n_invalid: int = 0


@dataclass(frozen=True)
class PowerLawFit:
    """Least-squares fit of ``y = prefactor * x**exponent`` in log space.

    The interval is the ordinary regression interval on the slope: Student's
    ``t`` at 95% on ``n - 2`` degrees of freedom, computed from the scatter of
    the points about the fitted line. It is a statement about how well a power
    law describes these legs, and not about seed variability, integrator error
    or the estimator's own bias, none of which enter it. With two points there
    is no residual degree of freedom and the interval is undefined.
    """

    exponent: float
    prefactor: float
    exponent_low: float
    exponent_high: float


@dataclass(frozen=True)
class OnsetFit:
    """Shifted-power fit on the early macroscopic foot, with the window it realised.

    The window is declared as an order range, so what a trajectory realises is
    whichever part of that range it reaches. Two fits are comparable only if
    they realised comparable windows, which is why the realised range, the
    coupling excess it sits at and the sample count travel with the exponent.
    """

    amplitude: float
    onset_coupling: float
    exponent: float
    order_min: float
    order_max: float
    excess_min: float
    excess_max: float
    samples: int
    onset_pinned: bool


def fit_power_law(x: FloatArray, y: FloatArray) -> PowerLawFit:
    """Fit a positive power law by ordinary least squares in log coordinates."""
    if x.shape != y.shape or x.size < 2:
        raise ValueError("power-law inputs must have equal shape and at least two values")
    if np.any(x <= 0.0) or np.any(y <= 0.0):
        raise ValueError("power-law inputs must be strictly positive")
    log_x = np.log(x)
    log_y = np.log(y)
    exponent, log_prefactor = np.polyfit(log_x, log_y, 1)
    low, high = _slope_interval(log_x, log_y, float(exponent), float(log_prefactor))
    return PowerLawFit(float(exponent), float(np.exp(log_prefactor)), low, high)


def _slope_interval(
    log_x: FloatArray, log_y: FloatArray, slope: float, intercept: float
) -> tuple[float, float]:
    """Return the 95% Student-``t`` interval on a least-squares slope."""
    dof = log_x.size - 2
    if dof < 1:
        return float("nan"), float("nan")
    residual = log_y - (slope * log_x + intercept)
    variance = float(np.sum(residual**2)) / dof
    spread = float(np.sum((log_x - log_x.mean()) ** 2))
    half_width = float(student_t.ppf(0.975, dof)) * math.sqrt(variance / spread)
    return slope - half_width, slope + half_width


def split_span_exponents(x: FloatArray, y: FloatArray) -> tuple[PowerLawFit, PowerLawFit]:
    """Fit the fast and slow halves of a speed sweep separately.

    A single exponent over three decades cannot say whether the shortfall from
    the predicted 1/2 is a property of the law or of the range it was measured
    over. Splitting the legs at their median speed and fitting each half asks
    that question directly: two halves agreeing is evidence the shortfall is the
    estimator's, and not a slow drift of the apparent exponent with rate.

    The halves overlap by one leg when the count is odd, so that neither fit is
    built from fewer points than the other.
    """
    if x.size < 4:
        raise ValueError("a split-span fit needs at least four speeds")
    order = np.argsort(x)
    sorted_x, sorted_y = x[order], y[order]
    half = (x.size + 1) // 2
    slow = fit_power_law(sorted_x[:half], sorted_y[:half])
    fast = fit_power_law(sorted_x[-half:], sorted_y[-half:])
    return fast, slow


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
    amplitude, onset, beta = (float(value) for value in parameters)
    return OnsetFit(
        amplitude=amplitude,
        onset_coupling=onset,
        exponent=beta,
        order_min=float(y.min()),
        order_max=float(y.max()),
        excess_min=float(x.min()) - critical_coupling,
        excess_max=float(x.max()) - critical_coupling,
        samples=int(x.size),
        onset_pinned=onset - critical_coupling <= _BOUND_TOLERANCE,
    )


def _bootstrap_means(rng: np.random.Generator, replica_delays: list[FloatArray]) -> FloatArray:
    """Resample replicas independently at each speed."""
    means = np.empty(len(replica_delays), dtype=np.float64)
    for index, delays in enumerate(replica_delays):
        means[index] = float(np.mean(rng.choice(delays, size=len(delays), replace=True)))
    return means


def _validate_bootstrap_inputs(
    speeds: FloatArray, replica_delays: list[FloatArray], n_boot: int
) -> None:
    if len(speeds) != len(replica_delays):
        raise ValueError("speeds and replica_delays must have the same length")
    if n_boot <= 0:
        raise ValueError("n_boot must be positive")
    if any(len(delays) == 0 or not np.all(np.isfinite(delays)) for delays in replica_delays):
        raise ValueError("each speed needs finite replica delays")


def bootstrap_delay_exponent(
    speeds: FloatArray,
    replica_delays: list[FloatArray],
    n_boot: int = 10000,
    threshold: float = 0.5,
    seed: int = 20260903,
) -> BootstrapResult:
    _validate_bootstrap_inputs(speeds, replica_delays, n_boot)
    rng = np.random.default_rng(seed)

    boot_exponents = np.empty(n_boot, dtype=np.float64)

    # Original data estimate
    orig_means = np.array([np.mean(delays) for delays in replica_delays])
    orig_fit = fit_power_law(speeds, orig_means)

    valid = 0
    invalid = 0
    while valid < n_boot:
        boot_means = _bootstrap_means(rng, replica_delays)
        if np.any(boot_means <= 0):
            invalid += 1
            if invalid > 10 * n_boot:
                raise ValueError("too many zero-delay resamples for a log-log fit")
            continue
        boot_exponents[valid] = fit_power_law(speeds, boot_means).exponent
        valid += 1

    ci_low = float(np.percentile(boot_exponents, 2.5))
    ci_high = float(np.percentile(boot_exponents, 97.5))
    p_above = float(np.mean(boot_exponents >= threshold))

    return BootstrapResult(
        exponent=orig_fit.exponent,
        ci_low=ci_low,
        ci_high=ci_high,
        n_boot=n_boot,
        p_above=p_above,
        n_invalid=invalid,
    )
