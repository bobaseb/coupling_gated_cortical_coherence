"""Seeded fast/slow plasticity illustration; no E45 or thermodynamic-rate claim.

The objective is half the squared deterministic drift. Its symmetric-edge
partial derivative includes both endpoints. Clip/rescale is a resource
retraction, not an orthogonal projection or a monotonic-descent guarantee.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
from time import perf_counter
from typing import cast

import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]
ROOT = Path(__file__).resolve().parent / "figures" / "structural_resonance"


@dataclass(frozen=True)
class Config:
    n: int = 100
    steps: int = 40000
    dt: float = 0.01
    diffusion: float = 0.1
    row_sum: float = 4.0
    learning_rate: float = 0.001
    update_every: int = 50
    sample_every: int = 50
    seed: int = 20260906


def validate(config: Config) -> None:
    positive = (
        config.dt,
        config.diffusion,
        config.row_sum,
        config.update_every,
        config.sample_every,
        config.steps,
    )
    if config.n < 6 or min(positive) <= 0 or config.learning_rate < 0:
        raise ValueError("Require N>=6, positive scales/cadences and nonnegative learning rate")


def project(coupling: Array, total: float) -> Array:
    """Clip, hollow and rescale a symmetric matrix to the fixed resource total."""
    result = np.maximum((coupling + coupling.T) / 2, 0.0)
    np.fill_diagonal(result, 0.0)
    mass = float(result.sum())
    if mass <= 0 or total <= 0:
        raise ValueError("Resource normalization requires positive mass and budget")
    return result * (total / mass)


def environment(n: int, total: float, seed: int) -> tuple[Array, Array, Array, NDArray[np.int64]]:
    """One-hot cluster covariance template, with a matched label-shuffle control."""
    labels = np.arange(n) * 3 // n
    omega = np.asarray([0.5, 1.0, 1.5])[labels]
    target = project((labels[:, None] == labels[None, :]).astype(float), total)
    permutation = np.random.default_rng(seed + 1).permutation(n)
    return omega, target, target[np.ix_(permutation, permutation)], permutation


def drift(theta: Array, coupling: Array, omega: Array) -> Array:
    return cast(Array, omega + np.sum(coupling * np.sin(theta[None, :] - theta[:, None]), axis=1))


def symmetric_gradient(theta: Array, velocity: Array) -> Array:
    """Derivative of sum(v_i^2)/2 with respect to each independent symmetric edge."""
    return (velocity[:, None] - velocity[None, :]) * np.sin(theta[None, :] - theta[:, None])


def diagnostics(
    theta: Array, coupling: Array, omega: Array, target: Array, shuffled: Array, diffusion: float
) -> list[float]:
    velocity = drift(theta, coupling, omega)
    return [
        float(abs(np.mean(np.exp(1j * theta)))),
        float(velocity @ velocity / diffusion),
        float(np.linalg.norm(coupling - target)),
        float(np.linalg.norm(coupling - shuffled)),
        float(velocity.mean()),
    ]


def simulate(config: Config, adaptive: bool = True) -> dict[str, Array]:
    """Euler--Maruyama with endpoint-inclusive decimation and only final phase state."""
    validate(config)
    rng = np.random.default_rng(config.seed)
    total = config.n * config.row_sum
    omega, target, shuffled, permutation = environment(config.n, total, config.seed)
    theta = rng.normal(0.0, 0.1, config.n)
    coupling = project(rng.uniform(0.0, 1.0, (config.n, config.n)), total)
    initial = coupling.copy()
    times, rows = [0.0], [diagnostics(theta, coupling, omega, target, shuffled, config.diffusion)]
    updates = 0
    for step in range(1, config.steps + 1):
        velocity = drift(theta, coupling, omega)
        theta += config.dt * velocity + np.sqrt(2 * config.diffusion * config.dt) * rng.normal(
            size=config.n
        )
        theta = (theta + np.pi) % (2 * np.pi) - np.pi
        if adaptive and step % config.update_every == 0:
            gradient = symmetric_gradient(theta, drift(theta, coupling, omega))
            coupling = project(
                coupling - config.learning_rate * config.update_every * config.dt * gradient, total
            )
            updates += 1
        if step % config.sample_every == 0 or step == config.steps:
            times.append(step * config.dt)
            rows.append(diagnostics(theta, coupling, omega, target, shuffled, config.diffusion))
    values = np.asarray(rows)
    result = {
        name: values[:, index]
        for index, name in enumerate(
            ("order", "dissipation", "distance", "shuffled_distance", "mean_drift")
        )
    }
    result.update(
        time=np.asarray(times),
        coupling_initial=initial,
        coupling_final=coupling,
        theta_final=theta,
        omega=omega,
        target=target,
        shuffled=shuffled,
        permutation=permutation.astype(float),
        updates=np.asarray(float(updates)),
    )
    return result


def metrics(result: dict[str, Array]) -> dict[str, float | bool]:
    time = result["time"]
    tail = time >= time[-1] / 2
    last = time >= 3 * time[-1] / 4
    previous = (time >= time[-1] / 2) & ~last
    plateau_change = float(
        result["dissipation"][last].mean() / result["dissipation"][previous].mean() - 1
    )
    reductions = [
        float(result[key][0] - result[key][-1]) for key in ("distance", "shuffled_distance")
    ]
    return {
        "tail_order": float(result["order"][tail].mean()),
        "minimum_order_after_ten": float(result["order"][time >= min(10.0, time[-1])].min()),
        "tail_dissipation": float(result["dissipation"][tail].mean()),
        "initial_dissipation": float(result["dissipation"][0]),
        "first_quarter_dissipation": float(result["dissipation"][time <= time[-1] / 4].mean()),
        "last_quarter_dissipation": float(result["dissipation"][last].mean()),
        "plateau_relative_change": plateau_change,
        "plateau_pass": abs(plateau_change) <= 0.05,
        "true_distance_reduction": reductions[0],
        "shuffled_distance_reduction": reductions[1],
        "specificity_advantage": reductions[0] - reductions[1],
        "mean_drive": float(result["mean_drift"].mean()),
    }


def run(output: Path, smoke: bool) -> None:
    output.mkdir(parents=True, exist_ok=True)
    records = []
    seeds = (20260906,) if smoke else (20260906, 20261906, 20262906)
    for seed in seeds:
        config = Config(n=24, steps=2000, seed=seed) if smoke else Config(seed=seed)
        for adaptive in (True, False):
            name = f"{seed}_{'adaptive' if adaptive else 'frozen'}"
            start = perf_counter()
            result = simulate(config, adaptive)
            runtime = perf_counter() - start
            np.savez_compressed(
                output / f"{name}.npz",
                allow_pickle=False,
                **result,
                config=json.dumps(asdict(config)),
            )
            records.append(
                {
                    "name": name,
                    "config": asdict(config),
                    "adaptive": adaptive,
                    "runtime_seconds": runtime,
                    **metrics(result),
                }
            )
            print(f"{name}: {records[-1]}", flush=True)
    (output / "summary.json").write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT)
    args = parser.parse_args()
    run(args.output, args.smoke)


if __name__ == "__main__":
    main()
