"""Finite-N Dale-balanced rescue illustration; no Lean obligation is discharged.

The field conversion follows the repository Fermi arithmetic conditionally: its
N*shift*f is dimensionless, so a physical inverse-time calibration is missing.
Run with OPENBLAS_NUM_THREADS=1 to avoid threading overhead for small matrices.

This module writes artifacts and nothing else: `summary.json`, one `.npz` per
leg and, when the baseline gate fails, the matched noise control. The figures
and the readout are built from those files afterwards by
`geometric_frustration_report.py`, which is a second command over a finished
run and never integrates anything itself.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import time
from typing import Any

import numpy as np
from numpy.typing import NDArray

from fermi_estimate_check import DEFAULTS, compute_k

Array = NDArray[np.float64]
ROOT = Path(__file__).resolve().parent / "figures" / "geometric_frustration"

# Interior couplings added inside the coarse step that brackets the crossing.
REFINEMENT_POINTS = 9

# The arrays every saved leg carries, and what a run writes instead of a sweep
# when its zero-field baseline is already ordered. Both are read back by
# `geometric_frustration_report.py`, so they are named here rather than spelled
# twice.
LEG_KEYS = ("time", "order", "final_phases", "runtime_seconds")
FAILED_BASELINE = "baseline_failed_sweep_not_run"


@dataclass(frozen=True)
class Config:
    n: int = 500
    diffusion: float = 1.0
    dt: float = 0.01
    steps: int = 10000
    sample_every: int = 10
    seed: int = 20260905
    probability: float = 0.2
    positive_sum: float = 4.0


def balanced_network(n: int, probability: float, positive_sum: float, seed: int) -> Array:
    """Draw ER topology, reject missing signs, and normalize each sign separately."""
    if positive_sum < 0:
        raise ValueError("Synaptic strength must be nonnegative")
    rng = np.random.default_rng(seed)
    edges = rng.random((n, n)) < probability
    np.fill_diagonal(edges, False)
    split = int(0.8 * n)
    excitatory = edges[:, :split].sum(axis=1)
    inhibitory = edges[:, split:].sum(axis=1)
    if np.any(excitatory == 0) or np.any(inhibitory == 0):
        raise ValueError("Topology has a row missing one sign; choose a denser configuration")
    matrix = edges.astype(float)
    matrix[:, :split] *= (positive_sum / excitatory)[:, None]
    matrix[:, split:] *= (-positive_sum / inhibitory)[:, None]
    return matrix


def drift(phases: Array, matrix: Array, epsilon: float) -> Array:
    """Exact sine-difference factorization, with presynaptic columns."""
    sine, cosine = np.sin(phases), np.cos(phases)
    return np.asarray(
        cosine * (matrix @ sine + epsilon * sine.sum())
        - sine * (matrix @ cosine + epsilon * cosine.sum())
    )


def field_required(coupling: float, decay_mm: float, rate: float = 1.0) -> float:
    """Conditional mV/mm number under the existing Fermi numerical calibration."""
    if rate <= 0:
        raise ValueError("Rate calibration must be positive")
    _, _, per_field = compute_k(1.0, DEFAULTS["shift"], decay_mm, DEFAULTS["rho"], DEFAULTS["f"])
    return coupling / (rate * per_field)


def simulate(config: Config, matrix: Array, epsilon: float, seed: int) -> dict[str, Array]:
    """Euler--Maruyama at omega=0; retain decimated order and final phases only."""
    if min(config.n, config.diffusion, config.dt, config.steps, config.sample_every) <= 0:
        raise ValueError("Configuration values must be positive")
    rng = np.random.default_rng(seed)
    phases = rng.uniform(-np.pi, np.pi, config.n)
    times, orders = [], []
    started = time.perf_counter()
    for step in range(config.steps + 1):
        if step % config.sample_every == 0 or step == config.steps:
            times.append(step * config.dt)
            orders.append(abs(np.exp(1j * phases).mean()))
        if step < config.steps:
            phases += config.dt * drift(phases, matrix, epsilon)
            phases += np.sqrt(2 * config.diffusion * config.dt) * rng.standard_normal(config.n)
            phases = (phases + np.pi) % (2 * np.pi) - np.pi
    return {
        "time": np.array(times),
        "order": np.array(orders),
        "final_phases": phases,
        "runtime_seconds": np.array(time.perf_counter() - started),
    }


def threshold(epsilon: Array, order: Array) -> tuple[float, float, float]:
    """Interpolate r=0.2 at the first crossing after which all samples exceed it."""
    below = np.flatnonzero(order <= 0.2)
    if below.size == 0 or below[-1] == order.size - 1:
        raise ValueError("Operational threshold is not bracketed")
    index = int(below[-1])
    fraction = (0.2 - order[index]) / (order[index + 1] - order[index])
    value = epsilon[index] + fraction * (epsilon[index + 1] - epsilon[index])
    return float(value), float(epsilon[index]), float(epsilon[index + 1])


def _leg(
    config: Config, matrix: Array, epsilon: float, index: int, output: Path
) -> dict[str, Array]:
    path = output / f"leg_{index:02d}.npz"
    metadata = json.dumps(
        {"config": asdict(config), "epsilon": epsilon, "seed": config.seed + index + 1}
    )
    if path.exists():
        with np.load(path, allow_pickle=False) as saved:
            if str(saved["metadata"]) != metadata:
                raise ValueError(f"Cached configuration mismatch: {path}")
            return {key: saved[key] for key in LEG_KEYS}
    result = simulate(config, matrix, epsilon, config.seed + index + 1)
    np.savez_compressed(path, **result, metadata=np.array(metadata), allow_pickle=False)
    return result


def epsilon_grid(config: Config) -> Array:
    """Include zero and bracket 2D even when synaptic positive sum is below 2D."""
    upper = max(4 * config.diffusion, config.positive_sum)
    return np.asarray(np.r_[0.0, np.geomspace(0.4 * config.diffusion, upper, 19) / config.n])


def refinement_grid(bracket: tuple[float, float], points: int = REFINEMENT_POINTS) -> Array:
    """Return equally spaced interior couplings of the step a crossing was found in.

    The two ends are grid values the sweep has already integrated, so they are
    excluded; the step is read off the bracket rather than fixed, so a narrower
    bracket is refined more finely by the same call.
    """
    if bracket[1] <= bracket[0]:
        raise ValueError("Refinement bracket must be increasing")
    return np.asarray(np.linspace(bracket[0], bracket[1], points + 2)[1:-1])


def _steady(config: Config, leg: dict[str, Array]) -> float:
    return float(leg["order"][leg["time"] >= config.steps * config.dt / 2].mean())


def _refine(
    config: Config,
    matrix: Array,
    epsilon: Array,
    orders: Array,
    bracket: tuple[float, float],
    output: Path,
) -> tuple[Array, Array, list[dict[str, Array]]]:
    """Integrate inside the coarse crossing step and return the merged sweep.

    Leg indices continue past the coarse grid, so every cached coarse run keeps
    the filename and the noise stream it was saved with and is not re-integrated.
    """
    refined = refinement_grid(bracket)
    legs = []
    for index, value in enumerate(refined):
        leg = _leg(config, matrix, float(value), epsilon.size + index, output)
        legs.append(leg)
        print(
            f"refinement {index + 1}/{refined.size} epsilon={value:.6g} "
            f"steady r={_steady(config, leg):.5f}",
            flush=True,
        )
    steady = np.asarray([_steady(config, leg) for leg in legs])
    merged = np.concatenate((epsilon, refined))
    order = np.argsort(merged)
    return merged[order], np.concatenate((orders, steady))[order], legs


def run(config: Config, output: Path) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    matrix = balanced_network(config.n, config.probability, config.positive_sum, config.seed)
    rows = matrix.sum(axis=1)
    print(
        f"Row sums: min={rows.min():.3g}, mean={rows.mean():.3g}, max={rows.max():.3g}", flush=True
    )
    coarse = epsilon_grid(config)
    legs = []
    for index, value in enumerate(coarse):
        leg = _leg(config, matrix, float(value), index, output)
        steady = _steady(config, leg)
        print(f"{index + 1}/{coarse.size} epsilon={value:.6g} steady r={steady:.5f}", flush=True)
        if index == 0 and steady > 2 / np.sqrt(config.n):
            _failed_baseline(config, matrix, leg, output)
            raise ValueError(
                "Baseline exceeds twice the finite-size floor; stop before sweep. "
                "The failed baseline and its noise control are saved; "
                "geometric_frustration_report.py plots them."
            )
        legs.append(leg)
    coarse_orders = np.array([_steady(config, leg) for leg in legs])
    _, coarse_lower, coarse_upper = threshold(coarse, coarse_orders)
    epsilon, orders, refined_legs = _refine(
        config, matrix, coarse, coarse_orders, (coarse_lower, coarse_upper), output
    )
    critical, lower, upper = threshold(epsilon, orders)
    summary: dict[str, Any] = {
        "config": asdict(config),
        "epsilon": epsilon.tolist(),
        "steady_order": orders.tolist(),
        "coarse_epsilon": coarse.tolist(),
        "coarse_bracket": [coarse_lower, coarse_upper],
        "critical_epsilon": critical,
        "threshold_bracket": [lower, upper],
        "effective_coupling": critical * config.n,
        "coupling_over_diffusion": critical * config.n / config.diffusion,
        "decay_mm": [0.1, 0.2, 0.3],
        "conditional_field_mV_mm": [
            field_required(critical * config.n, lam) for lam in (0.1, 0.2, 0.3)
        ],
        "row_sum_min_mean_max": [float(rows.min()), float(rows.mean()), float(rows.max())],
        "runtime_seconds": sum(float(leg["runtime_seconds"]) for leg in legs + refined_legs),
        "calibration_limit": (
            "N*shift*f is dimensionless; identifying it with inverse-time K "
            "requires an unspecified rate calibration."
        ),
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def _failed_baseline(config: Config, matrix: Array, leg: dict[str, Array], output: Path) -> None:
    """Preserve the failed assumption and a matched independent-noise control."""
    control = simulate(config, np.zeros_like(matrix), 0.0, config.seed + 1)
    np.savez_compressed(
        output / "noise_control.npz",
        **control,
        metadata=np.array(json.dumps(asdict(config))),
        allow_pickle=False,
    )
    tail = leg["time"] >= config.steps * config.dt / 2
    rows = matrix.sum(axis=1)
    summary = {
        "status": FAILED_BASELINE,
        "config": asdict(config),
        "baseline_order": float(leg["order"][tail].mean()),
        "noise_control_order": float(control["order"][tail].mean()),
        "finite_size_floor": float(1 / np.sqrt(config.n)),
        "baseline_gate": "second-half mean r <= 2/sqrt(N)",
        "row_sum_min_mean_max": [float(rows.min()), float(rows.mean()), float(rows.max())],
        "runtime_seconds": float(leg["runtime_seconds"] + control["runtime_seconds"]),
        "critical_epsilon": None,
        "conditional_field_mV_mm": None,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strength", type=float, default=4.0)
    parser.add_argument("--seed", type=int, default=20260905)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT)
    args = parser.parse_args()
    config = Config(positive_sum=args.strength, seed=args.seed)
    if args.smoke:
        config = Config(
            n=100, steps=2000, probability=0.5, positive_sum=args.strength, seed=args.seed
        )
    summary = run(config, args.output)
    print(
        f"wrote {args.output}/summary.json and {len(summary['epsilon'])} legs; "
        f"geometric_frustration_report.py --output {args.output} builds the figures",
        flush=True,
    )


if __name__ == "__main__":
    main()
