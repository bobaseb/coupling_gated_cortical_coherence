"""Finite-N evidence about dynamical selection in the noisy Kuramoto model.

The runs exhibit behaviour at sampled parameters and prove no trajectory theorem.
In particular, they do not establish dynamical selection of the coherent branch.
Natural frequencies are zero because the comparison target is the identical-frequency
von Mises self-consistency curve with critical coupling ``K_c = 2D``.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import cast

import matplotlib.pyplot as plt
import numpy as np
from numpy.typing import NDArray

from bifurcation import coherent_r


FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
FIGURES = Path(__file__).resolve().parent / "figures"

# Growth-fit window, stated relative to the two scales that bound it: the
# finite-size floor 1/sqrt(N) below and the static coherent branch above.
_FLOOR_MULTIPLE = 2.0
_SATURATION_FRACTION = 0.5

# Step-size control: the production step, then the same duration at these
# refinements of it.
_DT_REFINEMENTS = (2, 4)


@dataclass(frozen=True)
class SelectionConfig:
    """Parameters for an ensemble at one fixed coupling."""

    n_oscillators: int = 1000
    n_replicas: int = 500
    diffusion: float = 1.0
    coupling: float = 2.6
    dt: float = 0.01
    steps: int = 5000
    sample_every: int = 10
    seed: int = 20260904

    @property
    def critical_coupling(self) -> float:
        """Return the identical-frequency threshold ``K_c = 2D``."""
        return 2.0 * self.diffusion


@dataclass(frozen=True)
class SelectionResult:
    """Decimated order summaries, with no oscillator phase history."""

    time: FloatArray
    order_mean: FloatArray
    order_std: FloatArray
    finite_size_floor: float
    runtime_seconds: float


@dataclass(frozen=True)
class GrowthFit:
    """Log-linear fit over a declared early, pre-saturation window."""

    rate: float
    intercept: float
    r_squared: float
    sample_count: int
    lower_bound: float
    upper_bound: float


@dataclass(frozen=True)
class ExperimentSummary:
    """Numerical summaries from the trajectory and growth-rate sweeps."""

    regime_coupling: FloatArray
    regime_final_order: FloatArray
    regime_theory_order: FloatArray
    growth_coupling: FloatArray
    growth_rate: FloatArray
    growth_r_squared: FloatArray
    growth_window_lower: list[float]
    growth_window_upper: list[float]
    rate_slope: float
    rate_intercept: float
    dt_control_coupling: float
    dt_control_dt: list[float]
    dt_control_order: list[float]
    runtime_seconds: float


def _validate_config(config: SelectionConfig) -> None:
    positive = (
        config.n_oscillators,
        config.n_replicas,
        config.diffusion,
        config.coupling,
        config.dt,
        config.steps,
        config.sample_every,
    )
    if any(value <= 0 for value in positive):
        raise ValueError("all selection configuration scales must be positive")


def mean_field_drift(phases: FloatArray, coupling: float) -> FloatArray:
    """Evaluate all-to-all sine coupling in O(N) work per replica."""
    complex_order = np.mean(np.exp(1j * phases), axis=1)
    order = np.abs(complex_order)[:, None]
    mean_phase = np.angle(complex_order)[:, None]
    return cast(FloatArray, coupling * order * np.sin(mean_phase - phases))


def _sample_steps(steps: int, sample_every: int) -> set[int]:
    return set(range(0, steps + 1, sample_every)) | {steps}


def _record_order(phases: FloatArray) -> FloatArray:
    return cast(FloatArray, np.abs(np.mean(np.exp(1j * phases), axis=1)))


def simulate_selection(config: SelectionConfig) -> SelectionResult:
    """Integrate seeded Euler--Maruyama replicas and retain only order summaries."""
    _validate_config(config)
    rng = np.random.default_rng(config.seed)
    phases = rng.uniform(-np.pi, np.pi, (config.n_replicas, config.n_oscillators))
    sampled_steps = _sample_steps(config.steps, config.sample_every)
    times: list[float] = []
    order_means: list[float] = []
    order_stds: list[float] = []
    noise_scale = np.sqrt(2.0 * config.diffusion * config.dt)
    started = time.monotonic()
    for step in range(config.steps + 1):
        if step in sampled_steps:
            times.append(step * config.dt)
            order = _record_order(phases)
            order_means.append(float(np.mean(order)))
            order_stds.append(float(np.std(order)))
        if step == config.steps:
            break
        phases += config.dt * mean_field_drift(phases, config.coupling)
        phases += noise_scale * rng.standard_normal(phases.shape)
        phases = (phases + np.pi) % (2.0 * np.pi) - np.pi
    return SelectionResult(
        time=np.asarray(times),
        order_mean=np.asarray(order_means),
        order_std=np.asarray(order_stds),
        finite_size_floor=1.0 / np.sqrt(config.n_oscillators),
        runtime_seconds=time.monotonic() - started,
    )


def theoretical_growth_rate(coupling: FloatArray, diffusion: float) -> FloatArray:
    """Return the exact linearized first-harmonic rate ``(K - 2D) / 2``."""
    return (coupling - 2.0 * diffusion) / 2.0


def _first_contiguous_block(mask: NDArray[np.bool_]) -> NDArray[np.bool_]:
    """Keep the first run of ``True`` and drop any later re-entry.

    The window is a band of order values, and a trajectory that saturates and
    then fluctuates can cross back into it. Only the first crossing is early
    growth; a later one would contribute samples from the saturated regime to a
    fit that is defined on the exponential one.
    """
    indices = np.flatnonzero(mask)
    if indices.size == 0:
        return mask
    gaps = np.flatnonzero(np.diff(indices) > 1)
    stop = int(gaps[0]) + 1 if gaps.size else indices.size
    block = np.zeros_like(mask)
    block[indices[:stop]] = True
    return block


def estimate_growth_rate(
    time_values: FloatArray,
    order: FloatArray,
    lower_bound: float,
    upper_bound: float,
) -> GrowthFit:
    """Fit log order over the first excursion between the two declared bounds."""
    mask = _first_contiguous_block((order > lower_bound) & (order < upper_bound))
    if np.count_nonzero(mask) < 3:
        raise ValueError("at least three samples are required in the growth-fit window")
    x_values = time_values[mask]
    y_values = np.log(order[mask])
    slope, intercept = np.polyfit(x_values, y_values, 1)
    fitted = slope * x_values + intercept
    residual_sum = float(np.sum((y_values - fitted) ** 2))
    total_sum = float(np.sum((y_values - np.mean(y_values)) ** 2))
    r_squared = 1.0 if total_sum == 0.0 else 1.0 - residual_sum / total_sum
    return GrowthFit(
        float(slope), float(intercept), r_squared, int(x_values.size), lower_bound, upper_bound
    )


def _steady_order(result: SelectionResult) -> float:
    tail = max(1, result.order_mean.size // 4)
    return float(np.mean(result.order_mean[-tail:]))


def _run_configs(configs: list[SelectionConfig]) -> list[SelectionResult]:
    results: list[SelectionResult] = []
    for config in configs:
        result = simulate_selection(config)
        results.append(result)
        print(
            f"K={config.coupling:.3f} steps={config.steps} "
            f"final_r={_steady_order(result):.4f} runtime={result.runtime_seconds:.1f}s",
            flush=True,
        )
    return results


def _fit_growth_sweep(
    configs: list[SelectionConfig], results: list[SelectionResult]
) -> tuple[FloatArray, FloatArray, float, float, list[float], list[float]]:
    fits = []
    for config, result in zip(configs, results, strict=True):
        # Both bounds are relative, so the window follows the trace rather than
        # a fixed interval: it opens clear of the finite-size floor and closes
        # short of the branch the growth saturates onto.
        lower_bound = _FLOOR_MULTIPLE * result.finite_size_floor
        upper_bound = _SATURATION_FRACTION * coherent_r(config.coupling, config.diffusion)
        fits.append(estimate_growth_rate(result.time, result.order_mean, lower_bound, upper_bound))

    rates = np.asarray([fit.rate for fit in fits])
    r_squared = np.asarray([fit.r_squared for fit in fits])
    lower_bounds = [fit.lower_bound for fit in fits]
    upper_bounds = [fit.upper_bound for fit in fits]
    slope, intercept = np.polyfit(np.asarray([config.coupling for config in configs]), rates, 1)
    return rates, r_squared, float(slope), float(intercept), lower_bounds, upper_bounds


def _save_run(path: Path, config: SelectionConfig, result: SelectionResult) -> None:
    np.savez_compressed(
        path,
        config=np.asarray(json.dumps(asdict(config), sort_keys=True)),
        time=result.time,
        order_mean=result.order_mean,
        order_std=result.order_std,
        finite_size_floor=np.asarray(result.finite_size_floor),
        runtime_seconds=np.asarray(result.runtime_seconds),
    )


def _plot_experiment(
    output: Path,
    regime_configs: list[SelectionConfig],
    regime_results: list[SelectionResult],
    summary: ExperimentSummary,
) -> None:
    figure, axes = plt.subplots(1, 3, figsize=(14, 4.2))
    for axis, config, result in zip(axes, regime_configs, regime_results, strict=True):
        axis.semilogy(result.time, result.order_mean, color="tab:blue")
        axis.axhline(result.finite_size_floor, color="black", linestyle="--", label=r"$1/\sqrt{N}$")
        axis.set(xlabel="time", ylabel="ensemble mean r", title=f"K={config.coupling:g}")
        axis.legend()
    figure.suptitle("Finite-N escape trajectories; identical frequencies")
    figure.tight_layout()
    figure.savefig(output / "selection_escape_trajectories.png", dpi=180)
    plt.close(figure)

    comparison, axis = plt.subplots(figsize=(6.5, 4.5))
    theory_coupling = np.linspace(0.0, max(4.0, float(np.max(summary.regime_coupling))), 180)
    theory_order = np.asarray(
        [coherent_r(value, regime_configs[0].diffusion) for value in theory_coupling]
    )
    axis.plot(theory_coupling, theory_order, label="static coherent branch")
    axis.scatter(
        summary.regime_coupling, summary.regime_final_order, color="tab:red", label="simulation"
    )
    axis.axhline(
        regime_results[0].finite_size_floor, color="black", linestyle="--", label=r"$1/\sqrt{N}$"
    )
    axis.set(xlabel="coupling K", ylabel="steady order r", title="Static-branch comparison")
    axis.legend()
    comparison.tight_layout()
    comparison.savefig(output / "selection_static_comparison.png", dpi=180)
    plt.close(comparison)

    growth, axis = plt.subplots(figsize=(6.5, 4.5))
    predicted = theoretical_growth_rate(summary.growth_coupling, regime_configs[0].diffusion)
    axis.plot(summary.growth_coupling, predicted, label=r"predicted $(K-2D)/2$")
    axis.scatter(summary.growth_coupling, summary.growth_rate, color="tab:red", label="simulation")
    axis.set(xlabel="coupling K", ylabel="growth rate λ", title="Early first-harmonic growth")
    axis.legend()
    growth.tight_layout()
    growth.savefig(output / "selection_growth_rates.png", dpi=180)
    plt.close(growth)


def dt_control_configs(base: SelectionConfig, coupling: float) -> list[SelectionConfig]:
    """Refine the integration step at fixed duration and fixed sampling density.

    The control asks what the reported steady order does as the step shrinks,
    so everything else about the run is held fixed: the same coupling, the same
    physical duration and the same number of samples in the tail the steady
    order averages over. The production step itself opens the series and is not
    repeated here, because the regime sweep has already run it.
    """
    return [
        replace(
            base,
            coupling=coupling,
            dt=base.dt / factor,
            steps=base.steps * factor,
            sample_every=base.sample_every * factor,
        )
        for factor in _DT_REFINEMENTS
    ]


def run_experiment(
    base: SelectionConfig,
    regime_couplings: FloatArray,
    growth_couplings: FloatArray,
    output: Path,
) -> ExperimentSummary:
    """Run fixed-coupling trajectories, save compact artifacts, and plot analyses."""
    output.mkdir(parents=True, exist_ok=True)
    regime_configs = [
        SelectionConfig(**{**asdict(base), "coupling": float(value)}) for value in regime_couplings
    ]
    growth_base = {**asdict(base), "steps": min(base.steps, 1000), "sample_every": 5}
    growth_configs = [
        SelectionConfig(**{**growth_base, "coupling": float(value)}) for value in growth_couplings
    ]
    regime_results = _run_configs(regime_configs)
    growth_results = _run_configs(growth_configs)

    dt_index = int(np.argmax(regime_couplings))
    dt_control_coupling = float(regime_couplings[dt_index])
    dt_configs = dt_control_configs(base, dt_control_coupling)
    dt_results = _run_configs(dt_configs)
    dt_steps = [base.dt, *(config.dt for config in dt_configs)]
    dt_orders = [
        float(_steady_order(regime_results[dt_index])),
        *(float(_steady_order(result)) for result in dt_results),
    ]

    rates, fit_quality, slope, intercept, lower_bounds, upper_bounds = _fit_growth_sweep(
        growth_configs, growth_results
    )
    regime_final = np.asarray([_steady_order(result) for result in regime_results])
    regime_theory = np.asarray(
        [coherent_r(config.coupling, config.diffusion) for config in regime_configs]
    )
    summary = ExperimentSummary(
        regime_coupling=regime_couplings,
        regime_final_order=regime_final,
        regime_theory_order=regime_theory,
        growth_coupling=growth_couplings,
        growth_rate=rates,
        growth_r_squared=fit_quality,
        growth_window_lower=lower_bounds,
        growth_window_upper=upper_bounds,
        rate_slope=slope,
        rate_intercept=intercept,
        dt_control_coupling=dt_control_coupling,
        dt_control_dt=dt_steps,
        dt_control_order=dt_orders,
        runtime_seconds=float(
            sum(result.runtime_seconds for result in regime_results + growth_results + dt_results)
        ),
    )
    for label, config, result in zip(
        ("subcritical", "critical", "supercritical"), regime_configs, regime_results, strict=True
    ):
        _save_run(output / f"selection_{label}.npz", config, result)
    for dt_config, result in zip(dt_configs, dt_results, strict=True):
        _save_run(output / f"selection_dt_control_dt{dt_config.dt:g}.npz", dt_config, result)
    _save_summary(output, base, summary)
    _plot_experiment(output, regime_configs, regime_results, summary)
    return summary


def _save_summary(output: Path, config: SelectionConfig, summary: ExperimentSummary) -> None:
    payload = {
        "config": asdict(config),
        "regime_coupling": summary.regime_coupling.tolist(),
        "regime_final_order": summary.regime_final_order.tolist(),
        "regime_theory_order": summary.regime_theory_order.tolist(),
        "growth_coupling": summary.growth_coupling.tolist(),
        "growth_rate": summary.growth_rate.tolist(),
        "growth_r_squared": summary.growth_r_squared.tolist(),
        "growth_window_lower": summary.growth_window_lower,
        "growth_window_upper": summary.growth_window_upper,
        "rate_fit_slope": summary.rate_slope,
        "rate_fit_intercept": summary.rate_intercept,
        "predicted_slope": 0.5,
        "predicted_intercept": -config.diffusion,
        "dt_control_coupling": summary.dt_control_coupling,
        "dt_control_dt": summary.dt_control_dt,
        "dt_control_order": summary.dt_control_order,
        "runtime_seconds": summary.runtime_seconds,
        "scope": "finite-N heuristic evidence; no dynamical-selection theorem",
    }
    (output / "dynamical_selection_summary.json").write_text(json.dumps(payload, indent=2) + "\n")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--output", type=Path, default=FIGURES / "dynamical_selection")
    return parser.parse_args()


def main() -> None:
    """Run a reduced smoke experiment or the specified production sweep."""
    args = _parse_args()
    if args.smoke:
        base = SelectionConfig(
            n_oscillators=128,
            n_replicas=16,
            dt=0.02,
            steps=300,
            sample_every=5,
        )
        regimes = np.array([1.6, 2.0, 2.8])
        growth = np.array([2.1, 2.2, 2.3])
    else:
        base = SelectionConfig()
        regimes = np.array([1.6, 2.0, 2.8])
        growth = np.linspace(2.2, 3.1, 10)
    summary = run_experiment(base, regimes, growth, args.output)
    print(
        f"growth fit lambda={summary.rate_slope:.4f} K {summary.rate_intercept:+.4f}; "
        "prediction is 0.5 K - 1.0"
    )
    print("scope: finite-N heuristic evidence; no dynamical-selection theorem")


if __name__ == "__main__":
    main()
