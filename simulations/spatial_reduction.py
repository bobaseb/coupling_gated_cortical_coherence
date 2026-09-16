"""How far the scalar reduction of a spatially decaying kernel moves `K_c = 2D`.

`Phase8` proves the threshold `critical_coupling D = 2 * D` for a *scalar*
mean-field coupling at identical natural frequencies. A cortical kernel is not
scalar, so using that threshold requires an aggregation rule carrying the
spatial kernel to one number, and nothing so far bounds the error that rule
introduces. This module states the rule, measures the error and reports the
regime, if any, in which the threshold survives.

**The aggregation rule.** For a kernel `K(x, y) >= 0` with zero diagonal, the
scalar coupling is the *row sum*

    K_eff(i) = sum_j K_ij ,

which is constant in `i` for a translation-invariant kernel on a torus. It is
the coupling that enters `critical_coupling`, because the mean-field drift
`(K/N) sum_j sin(theta_j - theta_i)` has row sum `K` as well: the two models are
compared at equal row sum, not at equal peak strength or equal neighbour count.

**The sign convention.** The drift is `+ sum_j K_ij sin(theta_j - theta_i)`, so
a nonnegative kernel is attractive, and `K_ii = 0` excludes self-coupling.

**Where the population count went.** Write `w_max` for the largest off-diagonal
entry of a row and `N_eff = K_eff / w_max` for the effective neighbour count.
Then `K_eff = N_eff * w_max` *identically* — the population size is already
inside the row sum. A reduction that estimates a per-neighbour strength and
then multiplies by the number of neighbours within a decay length has counted
the population twice; `row_normalized_excludes_double_counting` is the check
that it has not been done here. The visible consequence is that the reduced
coupling of `build_decay_kernel` does not depend on the decay length at all, so
every decay dependence measured below is error of the reduction rather than a
change in the quantity being reduced.

**What this is not.** No cortical kernel, decay length or population size is
estimated here; the decay lengths swept are the published range already
declared in `fermi_estimate_check.py`, used as a range and not as a
measurement. The observable is the steady global order of a finite sheet.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import cast

import numpy as np
from numpy.typing import NDArray

import bifurcation
from fermi_estimate_check import FERMI_LAM_MAX, FERMI_LAM_MIN
from spatial_kernel import build_kernel, coupling_drift


FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
FIGURES = Path(__file__).resolve().parent / "figures"
PRODUCTION_OUTPUT = FIGURES / "spatial_reduction"

# The mid-range decay length `fermi_estimate_check.DEFAULTS` uses, named here so
# the three swept lengths read as one declared range rather than three numbers.
FERMI_LAM_MID = 0.2

# The coarse sheet each side is compared against. Two sheet sizes are what make
# the crossing estimate below possible, and halving the side is the largest step
# that still leaves the coarse sheet larger than the longest decay length swept.
FINITE_SIZE_RATIO = 2

# Fractions of the largest measured excess order that the threshold fit is
# repeated over. The spread of the resulting intercepts is the sensitivity bound
# reported for each leg: a threshold that moves with the fit window is a
# threshold the window chose.
FIT_WINDOWS = (0.15, 0.25, 0.40, 0.60)


@dataclass(frozen=True)
class ReductionConfig:
    """One sheet, one noise level and one integration schedule."""

    side: int = 64
    extent_mm: float = 2.0
    diffusion: float = 0.5
    frequency_sigma: float = 0.0
    total_time: float = 200.0
    max_dt: float = 0.01
    max_phase_step: float = 0.2
    burn_fraction: float = 0.5
    samples: int = 200
    seed: int = 20260916

    @property
    def n_sites(self) -> int:
        return self.side * self.side

    @property
    def scalar_threshold(self) -> float:
        """`critical_coupling D = 2 * D`, the quantity this module tests."""
        return 2.0 * self.diffusion


@dataclass(frozen=True)
class LegResult:
    """Steady order against reduced coupling for one kernel family."""

    name: str
    decay_mm: float | None
    frequency_sigma: float
    side: int
    coupling: FloatArray
    steady_order: FloatArray
    effective_neighbours: float
    runtime_seconds: float


@dataclass(frozen=True)
class Threshold:
    """A threshold location with the spread the fit window accounts for."""

    estimate: float
    low: float
    high: float
    points_used: int


@dataclass(frozen=True)
class Crossing:
    """A threshold located where two sheet sizes agree on the scaled order."""

    estimate: float
    scaled_order: float
    small_sites: int
    large_sites: int


def _validate(config: ReductionConfig) -> None:
    positive = (config.side, config.extent_mm, config.total_time, config.max_dt, config.samples)
    if any(value <= 0 for value in positive):
        raise ValueError("sheet size, extent, time, step ceiling and sample count are positive")
    if config.diffusion < 0.0 or config.frequency_sigma < 0.0:
        raise ValueError("diffusion and frequency spread are nonnegative")
    if not 0.0 <= config.burn_fraction < 1.0:
        raise ValueError("burn-in fraction lies in [0, 1)")


def build_uniform_kernel(side: int, coupling: float) -> FloatArray:
    """The all-to-all kernel of the same row sum: the scalar model itself.

    Every off-diagonal displacement carries equal weight, so this is the
    mean-field coupling `K/N` written in the same convolution form as the
    decaying kernels. It is the leg on which `K_c = 2D` is a prediction rather
    than an approximation, which is what makes it the validation target.
    """
    if side <= 1 or coupling <= 0.0:
        raise ValueError("sheet size and coupling must be positive")
    weights = np.ones((side, side))
    weights[0, 0] = 0.0
    return coupling * weights / np.sum(weights)


def build_decay_kernel(config: ReductionConfig, decay_mm: float, coupling: float) -> FloatArray:
    """The row-normalized exponential kernel of `spatial_kernel`, in grid units."""
    return build_kernel(config.side, decay_mm * config.side / config.extent_mm, coupling)


def reduced_coupling(kernel: FloatArray) -> float:
    """The aggregation rule: the row sum of a translation-invariant kernel."""
    return float(np.sum(kernel))


def effective_neighbours(kernel: FloatArray) -> float:
    """`N_eff = K_eff / w_max`, the count the row sum already contains."""
    peak = float(np.max(kernel))
    if peak <= 0.0:
        raise ValueError("a kernel with no positive entry has no neighbour count")
    return reduced_coupling(kernel) / peak


def _wrap(angle: FloatArray) -> FloatArray:
    return (angle + np.pi) % (2.0 * np.pi) - np.pi


def _schedule(config: ReductionConfig, coupling: float) -> tuple[float, int]:
    """Step size and count: the drift is bounded by the row sum, so cap `dt * K`.

    A fixed `dt` that is adequate at the bottom of a geometric coupling sweep
    integrates a different equation at the top of it. Bounding the per-step
    phase advance by `max_phase_step` keeps one integrator across the sweep and
    buys the accuracy with steps rather than with a silently coarser solution.
    """
    dt = min(config.max_dt, config.max_phase_step / coupling)
    return dt, int(round(config.total_time / dt))


def steady_order(config: ReductionConfig, kernel: FloatArray, seed: int) -> float:
    """Integrate one trajectory and return the tail-mean global order."""
    _validate(config)
    coupling = reduced_coupling(kernel)
    dt, steps = _schedule(config, coupling)
    rng = np.random.default_rng(seed)
    phases = rng.uniform(-np.pi, np.pi, size=(config.side, config.side))
    frequencies = (
        rng.normal(0.0, config.frequency_sigma, size=phases.shape)
        if config.frequency_sigma > 0.0
        else np.zeros_like(phases)
    )
    kernel_fft = np.fft.fft2(kernel)
    noise_scale = np.sqrt(2.0 * config.diffusion * dt)
    first_sample = int(config.burn_fraction * steps)
    stride = max(1, (steps - first_sample) // config.samples)
    orders: list[float] = []
    for step in range(steps):
        drift = frequencies + coupling_drift(phases, kernel_fft)
        phases = _wrap(phases + dt * drift + noise_scale * rng.standard_normal(phases.shape))
        if step >= first_sample and (step - first_sample) % stride == 0:
            orders.append(float(np.abs(np.mean(np.exp(1j * phases)))))
    return float(np.mean(orders))


def excess_order_squared(order: FloatArray, n_sites: int) -> FloatArray:
    """`r^2 - 1/N`: the squared order with the incoherent expectation removed.

    `N` independent uniform phases have `E[r^2] = 1/N` exactly, so this is the
    part of the measured order that is not the finite-sheet floor. Near a
    continuous threshold it is linear in the coupling, which is what makes the
    intercept below a threshold estimate rather than a crossing of an
    arbitrary level.
    """
    return np.asarray(order) ** 2 - 1.0 / n_sites


def _intercept(coupling: FloatArray, excess: FloatArray) -> float | None:
    if coupling.size < 2 or np.ptp(coupling) <= 0.0:
        return None
    slope, offset = np.polyfit(coupling, excess, 1)
    if slope <= 0.0:
        return None
    return float(-offset / slope)


def threshold_location(
    coupling: FloatArray, order: FloatArray, n_sites: int, windows: tuple[float, ...] = FIT_WINDOWS
) -> Threshold | None:
    """Extrapolate the excess order to zero, over several fit windows.

    The estimate is the fit over the widest window; `low` and `high` bracket
    every window's answer, so a leg whose threshold is an artifact of how much
    of the ordered branch was fitted reports a bracket wide enough to say so.
    """
    excess = excess_order_squared(order, n_sites)
    positive = excess > 0.0
    if not np.any(positive):
        return None
    ceiling = float(np.max(excess[positive]))
    estimates: list[tuple[float, int]] = []
    for fraction in sorted(windows):
        keep = positive & (excess <= fraction * ceiling)
        value = _intercept(coupling[keep], excess[keep])
        if value is not None:
            estimates.append((value, int(np.count_nonzero(keep))))
    if not estimates:
        return None
    values = [value for value, _ in estimates]
    return Threshold(
        estimate=estimates[-1][0],
        low=min(values),
        high=max(values),
        points_used=estimates[-1][1],
    )


def crossing_threshold(
    coupling: FloatArray,
    order_small: FloatArray,
    small_sites: int,
    order_large: FloatArray,
    large_sites: int,
) -> Crossing | None:
    """Locate the threshold where two sheet sizes agree on `N^(1/4) r`.

    A finite population rounds the transition off: at the threshold itself the
    order parameter is not zero but of order `N^(-1/4)`, so extrapolating the
    ordered branch to zero returns a coupling below the true one however fine
    the grid is. Scaling by `N^(1/4)` removes exactly that: below threshold
    `r ~ N^(-1/2)` and the scaled order falls with size, above it `r` tends to a
    size-independent constant and the scaled order rises with size, and at the
    threshold the two sheets agree. The crossing is therefore an estimate the
    rounding does not bias, and it is reported beside the extrapolated intercept
    rather than instead of it: the two disagreeing is the finite-size effect
    being visible rather than assumed.
    """
    scaled_small = small_sites**0.25 * np.asarray(order_small)
    scaled_large = large_sites**0.25 * np.asarray(order_large)
    difference = scaled_large - scaled_small
    for index in range(1, difference.size):
        low, high = float(difference[index - 1]), float(difference[index])
        if low <= 0.0 < high:
            fraction = -low / (high - low)
            estimate = float(
                coupling[index - 1] + fraction * (coupling[index] - coupling[index - 1])
            )
            scaled = float(
                scaled_large[index - 1] + fraction * (scaled_large[index] - scaled_large[index - 1])
            )
            return Crossing(
                estimate=estimate,
                scaled_order=scaled,
                small_sites=small_sites,
                large_sites=large_sites,
            )
    return None


def run_leg(
    config: ReductionConfig,
    couplings: FloatArray,
    name: str,
    decay_mm: float | None,
) -> LegResult:
    """Sweep one kernel family across the reduced coupling."""
    started = time.monotonic()
    orders: list[float] = []
    neighbours = 0.0
    for index, coupling in enumerate(couplings):
        kernel = (
            build_uniform_kernel(config.side, float(coupling))
            if decay_mm is None
            else build_decay_kernel(config, decay_mm, float(coupling))
        )
        neighbours = effective_neighbours(kernel)
        order = steady_order(config, kernel, config.seed + 1000 * index)
        orders.append(order)
        print(f"{name} K={coupling:.4f} r={order:.4f}", flush=True)
    return LegResult(
        name=name,
        decay_mm=decay_mm,
        frequency_sigma=config.frequency_sigma,
        side=config.side,
        coupling=np.asarray(couplings),
        steady_order=np.asarray(orders),
        effective_neighbours=neighbours,
        runtime_seconds=time.monotonic() - started,
    )


def mean_field_reference(couplings: FloatArray, diffusion: float) -> FloatArray:
    """The self-consistent branch `r = R(K r / D)` solved in `bifurcation`."""
    return np.asarray([bifurcation.coherent_r(float(k), diffusion) for k in couplings])


def production_couplings() -> FloatArray:
    """The sweep grid: dense through both onsets, sparse across the ordered branch.

    The identical-frequency legs turn over near `2D = 1`, the heterogeneous
    controls near the larger threshold a frequency spread imposes, and the
    mean-field validation needs the far branch as well. One grid covering all
    three keeps every leg on the same couplings, which is what makes the
    thresholds comparable.
    """
    dense = np.linspace(0.6, 3.6, 16)
    far = np.array([4.0, 5.0, 6.0, 8.0, 12.0, 16.0])
    return cast(FloatArray, np.unique(np.concatenate((dense, far))))


def _legs(config: ReductionConfig) -> list[tuple[str, float | None, ReductionConfig]]:
    """The four identical-frequency legs and the two heterogeneous controls."""
    hetero = replace(config, frequency_sigma=1.5)
    return [
        ("mean_field", None, config),
        ("lambda_min", FERMI_LAM_MIN, config),
        ("lambda_mid", FERMI_LAM_MID, config),
        ("lambda_max", FERMI_LAM_MAX, config),
        ("mean_field_heterogeneous", None, hetero),
        ("lambda_mid_heterogeneous", FERMI_LAM_MID, hetero),
    ]


def _leg_payload(leg: LegResult, coarse: LegResult, config: ReductionConfig) -> dict[str, object]:
    threshold = threshold_location(leg.coupling, leg.steady_order, config.n_sites)
    coarse_sites = coarse.side * coarse.side
    crossing = crossing_threshold(
        leg.coupling, coarse.steady_order, coarse_sites, leg.steady_order, config.n_sites
    )
    payload: dict[str, object] = {
        "name": leg.name,
        "decay_mm": leg.decay_mm,
        "frequency_sigma": leg.frequency_sigma,
        "side": leg.side,
        "coarse_side": coarse.side,
        "effective_neighbours": leg.effective_neighbours,
        "coarse_effective_neighbours": coarse.effective_neighbours,
        "coupling": leg.coupling.tolist(),
        "steady_order": leg.steady_order.tolist(),
        "coarse_steady_order": coarse.steady_order.tolist(),
        "runtime_seconds": leg.runtime_seconds + coarse.runtime_seconds,
        "threshold": None if threshold is None else asdict(threshold),
        "crossing": None if crossing is None else asdict(crossing),
    }
    if threshold is not None:
        payload["threshold_ratio"] = threshold.estimate / config.scalar_threshold
        payload["threshold_ratio_low"] = threshold.low / config.scalar_threshold
        payload["threshold_ratio_high"] = threshold.high / config.scalar_threshold
    if crossing is not None:
        payload["crossing_ratio"] = crossing.estimate / config.scalar_threshold
    return payload


def _validation_payload(leg: LegResult, config: ReductionConfig) -> dict[str, object]:
    """Residual of the mean-field leg against the self-consistency curve."""
    reference = mean_field_reference(leg.coupling, config.diffusion)
    above = leg.coupling > config.scalar_threshold
    residual = leg.steady_order[above] - reference[above]
    return {
        "reference_order": reference.tolist(),
        "supercritical_points": int(np.count_nonzero(above)),
        "residual_max_abs": float(np.max(np.abs(residual))) if residual.size else None,
        "residual_mean": float(np.mean(residual)) if residual.size else None,
    }


def run_sweep(config: ReductionConfig, couplings: FloatArray, output: Path) -> dict[str, object]:
    """Run every leg, save the summary and return it."""
    results = {
        name: run_leg(leg_config, couplings, name, decay)
        for name, decay, leg_config in _legs(config)
    }
    coarse = {
        name: run_leg(
            replace(leg_config, side=leg_config.side // FINITE_SIZE_RATIO),
            couplings,
            f"{name}_coarse",
            decay,
        )
        for name, decay, leg_config in _legs(config)
    }
    legs = {
        name: _leg_payload(leg, coarse[name], replace(config, frequency_sigma=leg.frequency_sigma))
        for name, leg in results.items()
    }
    summary: dict[str, object] = {
        "source": "spatial_reduction.py",
        "config": asdict(config),
        "scalar_threshold": config.scalar_threshold,
        "aggregation_rule": "scalar coupling = row sum of the kernel; zero diagonal; "
        "population count already inside the row sum",
        "fit_windows": list(FIT_WINDOWS),
        "finite_size_ratio": FINITE_SIZE_RATIO,
        "legs": legs,
        "mean_field_validation": _validation_payload(results["mean_field"], config),
        "scope": "finite-sheet measurement of one reduction rule; no cortical kernel is estimated",
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "spatial_reduction_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return summary


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="run a reduced deterministic sweep")
    parser.add_argument("--output", type=Path, default=None)
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    config = (
        ReductionConfig(side=16, total_time=2.0, samples=5) if args.smoke else ReductionConfig()
    )
    couplings = np.geomspace(0.5, 8.0, 4) if args.smoke else production_couplings()
    summary = run_sweep(config, couplings, args.output or PRODUCTION_OUTPUT)
    legs = cast(dict[str, dict[str, object]], summary["legs"])
    for name, payload in legs.items():
        threshold = payload["threshold"]
        located = "not bracketed" if threshold is None else f"{payload['threshold_ratio']:.2f}"
        crossed = (
            "not bracketed" if payload["crossing"] is None else f"{payload['crossing_ratio']:.2f}"
        )
        print(f"{name}: extrapolated / 2D = {located}, size crossing / 2D = {crossed}")
    print("scope: finite-sheet measurement of one reduction rule")


if __name__ == "__main__":
    main()
