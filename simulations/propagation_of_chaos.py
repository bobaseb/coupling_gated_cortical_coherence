"""Finite-N convergence evidence for the stochastic mean-field Kuramoto model.

The sampled simulations are heuristic evidence only: they do not prove propagation
of chaos or discharge any Lean obligation. Natural frequencies are identically zero,
as required for comparison with the von Mises stationary density. Replicas start with
their circular mean aligned to zero; final lab-frame pairs retain collective phase
diffusion, while density validation uses phases relative to each replica's final mean.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import cast

import matplotlib.pyplot as plt
import numpy as np
from numpy.typing import NDArray
from scipy.stats import wasserstein_distance

from bifurcation import bessel_ratio


FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
FIGURES = Path(__file__).resolve().parent / "figures"
Summary = dict[str, object]


@dataclass(frozen=True)
class ChaosConfig:
    """Parameters for one ensemble sweep point."""

    n_oscillators: int = 1000
    n_ensembles: int = 1000
    diffusion: float = 1.0
    coupling: float = 3.0
    dt: float = 0.01
    steps: int = 5000
    seed: int = 20260904


@dataclass(frozen=True)
class Snapshot:
    """Compact final-time observables; no full oscillator state or phase history."""

    theta_one: FloatArray
    theta_two: FloatArray
    aligned_theta_one: FloatArray
    mean_order: float
    finite_size_floor: float
    measured_concentration: float
    runtime_seconds: float


@dataclass(frozen=True)
class Metrics:
    """Dependence and stationary-density summaries for one sweep point."""

    correlation: float
    distance_mean: float
    distance_std: float
    density_l1_error: float
    self_consistency_error: float


def _validate_config(config: ChaosConfig) -> None:
    if config.n_oscillators < 2:
        raise ValueError("at least two oscillators are required")
    positive = (config.n_ensembles, config.diffusion, config.coupling, config.dt, config.steps)
    if any(value <= 0 for value in positive):
        raise ValueError("all configuration scales must be positive")


def _circular_mean(values: FloatArray, axis: int | None = None) -> FloatArray:
    return cast(FloatArray, np.angle(np.mean(np.exp(1j * values), axis=axis)))


def circular_correlation(first: FloatArray, second: FloatArray) -> float:
    """Return the branch-cut-invariant Jammalamadaka circular correlation."""
    if first.shape != second.shape or first.ndim != 1:
        raise ValueError("circular-correlation samples must be matched one-dimensional arrays")
    centered_first = np.sin(first - _circular_mean(first))
    centered_second = np.sin(second - _circular_mean(second))
    denominator = np.sqrt(np.sum(centered_first**2) * np.sum(centered_second**2))
    if denominator <= np.finfo(float).eps:
        raise ValueError("circular correlation requires non-degenerate samples")
    return float(np.sum(centered_first * centered_second) / denominator)


def _torus_embedding(first: FloatArray, second: FloatArray) -> FloatArray:
    return np.column_stack((np.cos(first), np.sin(first), np.cos(second), np.sin(second)))


def sliced_joint_product_distance(
    first: FloatArray, second: FloatArray, n_slices: int, seed: int
) -> float:
    """Compare a matched joint sample with a permuted product sample in torus coordinates."""
    if first.shape != second.shape or first.ndim != 1 or first.size < 2:
        raise ValueError("distance samples must be matched non-trivial one-dimensional arrays")
    if n_slices <= 0:
        raise ValueError("the number of slices must be positive")
    rng = np.random.default_rng(seed)
    joint = _torus_embedding(first, second)
    product = _torus_embedding(first, rng.permutation(second))
    directions = rng.standard_normal((n_slices, joint.shape[1]))
    directions /= np.linalg.norm(directions, axis=1, keepdims=True)
    distances = [
        wasserstein_distance(joint @ direction, product @ direction) for direction in directions
    ]
    return float(np.mean(distances))


def von_mises_density(theta: FloatArray, concentration: float) -> FloatArray:
    """Return the normalized zero-mean von Mises density."""
    if concentration < 0.0:
        raise ValueError("concentration must be non-negative")
    return np.exp(concentration * np.cos(theta)) / (2.0 * np.pi * np.i0(concentration))


def simulate_snapshot(config: ChaosConfig) -> Snapshot:
    """Integrate seeded Euler--Maruyama replicas and retain final pair observables only."""
    _validate_config(config)
    rng = np.random.default_rng(config.seed)
    phases = rng.uniform(-np.pi, np.pi, (config.n_ensembles, config.n_oscillators))
    phases -= _circular_mean(phases, axis=1)[:, None]
    noise_scale = np.sqrt(2.0 * config.diffusion * config.dt)
    started = time.monotonic()
    for _ in range(config.steps):
        complex_order = np.mean(np.exp(1j * phases), axis=1)
        order = np.abs(complex_order)[:, None]
        mean_phase = np.angle(complex_order)[:, None]
        phases += config.dt * config.coupling * order * np.sin(mean_phase - phases)
        phases += noise_scale * rng.standard_normal(phases.shape)
        phases = (phases + np.pi) % (2.0 * np.pi) - np.pi
    complex_order = np.mean(np.exp(1j * phases), axis=1)
    mean_order = float(np.mean(np.abs(complex_order)))
    aligned = (phases[:, 0] - np.angle(complex_order) + np.pi) % (2.0 * np.pi) - np.pi
    return Snapshot(
        theta_one=phases[:, 0].copy(),
        theta_two=phases[:, 1].copy(),
        aligned_theta_one=aligned,
        mean_order=mean_order,
        finite_size_floor=1.0 / np.sqrt(config.n_oscillators),
        measured_concentration=config.coupling * mean_order / config.diffusion,
        runtime_seconds=time.monotonic() - started,
    )


def _bootstrap_distance(
    snapshot: Snapshot, sample_size: int, bootstraps: int, n_slices: int, seed: int
) -> tuple[float, float]:
    rng = np.random.default_rng(seed)
    distances: list[float] = []
    for bootstrap in range(bootstraps):
        indices = rng.choice(snapshot.theta_one.size, size=sample_size, replace=True)
        distances.append(
            sliced_joint_product_distance(
                snapshot.theta_one[indices],
                snapshot.theta_two[indices],
                n_slices,
                seed + bootstrap,
            )
        )
    return float(np.mean(distances)), float(np.std(distances, ddof=1))


def _density_error(snapshot: Snapshot) -> float:
    counts, edges = np.histogram(snapshot.aligned_theta_one, bins=40, range=(-np.pi, np.pi))
    widths = np.diff(edges)
    empirical = counts / (np.sum(counts) * widths)
    centers = 0.5 * (edges[:-1] + edges[1:])
    theory = von_mises_density(centers, snapshot.measured_concentration)
    return float(np.sum(np.abs(empirical - theory) * widths))


def compute_metrics(
    snapshot: Snapshot, sample_size: int, bootstraps: int, n_slices: int, seed: int
) -> Metrics:
    """Compute all required final-snapshot statistics with matched bootstrap sizes."""
    if sample_size > snapshot.theta_one.size:
        raise ValueError("distance sample size cannot exceed the ensemble count")
    distance_mean, distance_std = _bootstrap_distance(
        snapshot, sample_size, bootstraps, n_slices, seed
    )
    return Metrics(
        correlation=circular_correlation(snapshot.theta_one, snapshot.theta_two),
        distance_mean=distance_mean,
        distance_std=distance_std,
        density_l1_error=_density_error(snapshot),
        self_consistency_error=abs(
            snapshot.mean_order - bessel_ratio(snapshot.measured_concentration)
        ),
    )


def _save_snapshot(path: Path, config: ChaosConfig, snapshot: Snapshot) -> None:
    np.savez_compressed(
        path,
        config=np.asarray(json.dumps(asdict(config), sort_keys=True)),
        theta_one=snapshot.theta_one,
        theta_two=snapshot.theta_two,
        aligned_theta_one=snapshot.aligned_theta_one,
        mean_order=np.asarray(snapshot.mean_order),
        finite_size_floor=np.asarray(snapshot.finite_size_floor),
        measured_concentration=np.asarray(snapshot.measured_concentration),
        runtime_seconds=np.asarray(snapshot.runtime_seconds),
    )


def _plot_results(
    output: Path,
    sizes: FloatArray,
    metrics_by_coupling: dict[float, list[Metrics]],
    snapshots_by_coupling: dict[float, list[Snapshot]],
) -> None:
    figure, axes = plt.subplots(1, 3, figsize=(14.5, 4.4))
    for coupling, metrics in metrics_by_coupling.items():
        correlations = np.abs([metric.correlation for metric in metrics])
        axes[0].loglog(sizes, correlations, "o-", label=f"K={coupling:g}")
        axes[1].errorbar(
            sizes,
            [metric.distance_mean for metric in metrics],
            yerr=[metric.distance_std for metric in metrics],
            marker="o",
            label=f"K={coupling:g}",
        )
    reference = max(float(next(iter(metrics_by_coupling.values()))[0].correlation), 0.05)
    axes[0].loglog(sizes, abs(reference) * sizes[0] / sizes, "k--", label=r"$1/N$ slope")
    axes[0].set(xlabel="oscillators N", ylabel="absolute circular correlation")
    axes[1].set(xscale="log", xlabel="oscillators N", ylabel="sliced joint-product distance")
    for axis in axes[:2]:
        axis.legend()
    coupling = max(snapshots_by_coupling)
    snapshot = snapshots_by_coupling[coupling][-1]
    theta = np.linspace(-np.pi, np.pi, 400)
    axes[2].hist(snapshot.aligned_theta_one, bins=40, density=True, alpha=0.45, label="simulation")
    axes[2].plot(
        theta, von_mises_density(theta, snapshot.measured_concentration), label="von Mises"
    )
    axes[2].set(
        xlabel=r"aligned phase $\theta-\psi$",
        ylabel="density",
        title=f"N={int(sizes[-1])}, measured a={snapshot.measured_concentration:.3f}",
    )
    axes[2].legend()
    figure.suptitle("Finite-N convergence diagnostics; identical frequencies")
    figure.tight_layout()
    figure.savefig(output / "propagation_of_chaos.png", dpi=180)
    plt.close(figure)


def run_experiment(
    base: ChaosConfig,
    sizes: list[int],
    couplings: list[float],
    output: Path,
    sample_size: int,
    bootstraps: int,
    n_slices: int,
) -> dict[str, object]:
    """Run both controls, save compact snapshots, and return a JSON-ready summary."""
    output.mkdir(parents=True, exist_ok=True)
    all_metrics: dict[float, list[Metrics]] = {}
    all_snapshots: dict[float, list[Snapshot]] = {}
    records: list[dict[str, object]] = []
    for coupling_index, coupling in enumerate(couplings):
        all_metrics[coupling] = []
        all_snapshots[coupling] = []
        for size_index, size in enumerate(sizes):
            config = ChaosConfig(
                **{
                    **asdict(base),
                    "n_oscillators": size,
                    "coupling": coupling,
                    "seed": base.seed + 100 * coupling_index + size_index,
                }
            )
            snapshot = simulate_snapshot(config)
            metrics = compute_metrics(
                snapshot,
                min(sample_size, config.n_ensembles),
                bootstraps,
                n_slices,
                config.seed + 10_000,
            )
            all_snapshots[coupling].append(snapshot)
            all_metrics[coupling].append(metrics)
            _save_snapshot(output / f"chaos_K{coupling:g}_N{size}.npz", config, snapshot)
            record: dict[str, object] = {
                "config": asdict(config),
                "snapshot": asdict(snapshot),
                "metrics": asdict(metrics),
            }
            record["snapshot"] = {
                key: value
                for key, value in cast(dict[str, object], record["snapshot"]).items()
                if not isinstance(value, np.ndarray)
            }
            records.append(record)
            print(
                f"K={coupling:g} N={size} r={snapshot.mean_order:.4f} "
                f"rho={metrics.correlation:+.4f} W={metrics.distance_mean:.4f} "
                f"density_L1={metrics.density_l1_error:.4f} "
                f"self_consistency={metrics.self_consistency_error:.4f} "
                f"runtime={snapshot.runtime_seconds:.1f}s",
                flush=True,
            )
    size_values = np.asarray(sizes, dtype=float)
    _plot_results(output, size_values, all_metrics, all_snapshots)
    summary: dict[str, object] = {"records": records}
    (output / "propagation_of_chaos_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    return summary


def _summary_records(summary: Summary) -> list[dict[str, object]]:
    records = summary.get("records")
    if not isinstance(records, list) or not records:
        raise ValueError("summary must contain a non-empty records list")
    return cast(list[dict[str, object]], records)


def _record_for(records: list[dict[str, object]], coupling: float, size: int) -> dict[str, object]:
    for record in records:
        config = cast(dict[str, object], record["config"])
        if (
            float(cast(float, config["coupling"])) == coupling
            and int(cast(int, config["n_oscillators"])) == size
        ):
            return record
    raise ValueError(f"summary lacks K={coupling:g}, N={size}")


def _macro(name: str, value: str) -> str:
    return f"\\newcommand{{\\{name}}}{{{value}}}"


def write_tex_macros(summary: Summary, output: Path) -> None:
    """Generate publication macros directly from a completed JSON summary."""
    records = _summary_records(summary)
    sizes = sorted(
        {
            int(cast(int, cast(dict[str, object], record["config"])["n_oscillators"]))
            for record in records
        }
    )
    low_size, high_size = sizes[0], sizes[-1]
    sub_low = _record_for(records, 1.0, low_size)
    sub_high = _record_for(records, 1.0, high_size)
    super_low = _record_for(records, 3.0, low_size)
    super_high = _record_for(records, 3.0, high_size)

    def snapshot(record: dict[str, object]) -> dict[str, float]:
        return cast(dict[str, float], record["snapshot"])

    def metrics(record: dict[str, object]) -> dict[str, float]:
        return cast(dict[str, float], record["metrics"])

    super_correlations = [
        abs(metrics(record)["correlation"])
        for record in records
        if float(cast(float, cast(dict[str, object], record["config"])["coupling"])) == 3.0
    ]
    runtime = sum(snapshot(record)["runtime_seconds"] for record in records)
    lines = [
        "%% Auto-generated by propagation_of_chaos.py --write-tex",
        "%% Do not edit manually. Regenerate from propagation_of_chaos_summary.json.",
        _macro("chaosNMin", str(low_size)),
        _macro("chaosNMax", str(high_size)),
        _macro("chaosSubOrderLowN", f"{snapshot(sub_low)['mean_order']:.4f}"),
        _macro("chaosSubOrderHighN", f"{snapshot(sub_high)['mean_order']:.4f}"),
        _macro("chaosSubCorrelationLowN", f"{abs(metrics(sub_low)['correlation']):.4f}"),
        _macro("chaosSubCorrelationHighN", f"{abs(metrics(sub_high)['correlation']):.4f}"),
        _macro("chaosSubDistanceLowN", f"{metrics(sub_low)['distance_mean']:.4f}"),
        _macro("chaosSubDistanceHighN", f"{metrics(sub_high)['distance_mean']:.4f}"),
        _macro("chaosSubDensityLowN", f"{metrics(sub_low)['density_l1_error']:.4f}"),
        _macro("chaosSubDensityHighN", f"{metrics(sub_high)['density_l1_error']:.4f}"),
        _macro("chaosSuperOrder", f"{snapshot(super_high)['mean_order']:.4f}"),
        _macro("chaosSuperCorrelationMin", f"{min(super_correlations):.3f}"),
        _macro("chaosSuperCorrelationMax", f"{max(super_correlations):.3f}"),
        _macro("chaosSuperDistanceLowN", f"{metrics(super_low)['distance_mean']:.4f}"),
        _macro("chaosSuperDistanceHighN", f"{metrics(super_high)['distance_mean']:.4f}"),
        _macro(
            "chaosMeasuredConcentration", f"{snapshot(super_high)['measured_concentration']:.4f}"
        ),
        _macro("chaosDensityError", f"{metrics(super_high)['density_l1_error']:.4f}"),
        _macro("chaosBesselResidual", f"{metrics(super_high)['self_consistency_error']:.5f}"),
        _macro("chaosRuntimeSeconds", f"{runtime:.2f}"),
    ]
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--output", type=Path, default=FIGURES / "propagation_of_chaos")
    parser.add_argument("--write-tex", type=Path)
    parser.add_argument(
        "--summary",
        type=Path,
        default=FIGURES / "propagation_of_chaos" / "propagation_of_chaos_summary.json",
    )
    return parser.parse_args()


def main() -> None:
    """Run the reduced deterministic check or the specified production sweep."""
    args = _parse_args()
    if args.write_tex is not None:
        summary = cast(Summary, json.loads(args.summary.read_text(encoding="utf-8")))
        write_tex_macros(summary, args.write_tex)
        return
    if args.smoke:
        base = ChaosConfig(n_ensembles=64, dt=0.02, steps=100, seed=20260904)
        sizes, sample_size, bootstraps, n_slices = [10, 40], 64, 4, 16
    else:
        base = ChaosConfig()
        sizes, sample_size, bootstraps, n_slices = [10, 50, 100, 500, 1000], 250, 30, 64
    run_experiment(base, sizes, [1.0, 3.0], args.output, sample_size, bootstraps, n_slices)


if __name__ == "__main__":
    main()
