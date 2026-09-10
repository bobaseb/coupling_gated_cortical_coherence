"""Seeded fast/slow plasticity illustration; no E45 or thermodynamic-rate claim.

The objective is half the squared deterministic drift. Its symmetric-edge
partial derivative includes both endpoints. Clip/rescale is a resource
retraction, not an orthogonal projection or a monotonic-descent guarantee.

Four arms share one phase-noise stream per seed. The gradient arm descends the
objective; the random arm takes a symmetric step of the same Frobenius norm in a
direction unrelated to it; the permuted arm takes the gradient step itself under
a random node relabelling; the frozen arm holds the kernel fixed. The random arm
separates the gradient's effect from the effect of moving a kernel of that step
size under a fixed total resource at all. Its successive isotropic steps cancel,
so it ends an order of magnitude less deformed than the gradient arm and cannot
separate the gradient direction from comparable cumulative deformation; the
permuted arm can, since a relabelling is an isometry that leaves the step's entry
multiset alone and changes only which edges receive them.

Frobenius distance to a template confounds alignment with kernel norm, which a
fixed resource total does not hold constant. The reported alignment statistics
are the within-over-between cluster coupling ratio and the off-diagonal
correlation with the template; both are invariant under rescaling the kernel.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
from time import perf_counter
from typing import Any, cast

import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]
ROOT = Path(__file__).resolve().parent / "figures" / "structural_resonance"
MODES = ("gradient", "random", "permuted", "frozen")
SWEEP_RATES = (0.001, 0.05, 0.1, 0.2, 0.3, 0.4)
DIAGNOSTIC_NAMES = (
    "order",
    "dissipation",
    "distance",
    "shuffled_distance",
    "mean_drift",
    "alignment_ratio",
    "template_correlation",
)


@dataclass(frozen=True)
class Config:
    n: int = 100
    steps: int = 40000
    dt: float = 0.01
    diffusion: float = 0.1
    row_sum: float = 4.0
    learning_rate: float = 0.2
    update_every: int = 50
    sample_every: int = 50
    permutations: int = 2000
    seed: int = 20260906


@dataclass(frozen=True)
class Environment:
    """Constant frequencies and the diagnostic templates scored against them."""

    omega: Array
    target: Array
    shuffled: Array
    permutation: NDArray[np.int64]
    labels: NDArray[np.int64]


def validate(config: Config, mode: str) -> None:
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
    if mode not in MODES:
        raise ValueError(f"Unknown arm {mode!r}; expected one of {MODES}")


def project(coupling: Array, total: float) -> Array:
    """Clip, hollow and rescale a symmetric matrix to the fixed resource total."""
    result = np.maximum((coupling + coupling.T) / 2, 0.0)
    np.fill_diagonal(result, 0.0)
    mass = float(result.sum())
    if mass <= 0 or total <= 0:
        raise ValueError("Resource normalization requires positive mass and budget")
    return result * (total / mass)


def environment(n: int, total: float, seed: int) -> Environment:
    """One-hot cluster covariance template, with a matched label-shuffle control."""
    labels = np.arange(n) * 3 // n
    omega = np.asarray([0.5, 1.0, 1.5])[labels]
    target = project((labels[:, None] == labels[None, :]).astype(float), total)
    permutation = np.random.default_rng(seed + 1).permutation(n)
    return Environment(omega, target, target[np.ix_(permutation, permutation)], permutation, labels)


def drift(theta: Array, coupling: Array, omega: Array) -> Array:
    return cast(Array, omega + np.sum(coupling * np.sin(theta[None, :] - theta[:, None]), axis=1))


def symmetric_gradient(theta: Array, velocity: Array) -> Array:
    """Derivative of sum(v_i^2)/2 with respect to each independent symmetric edge."""
    return (velocity[:, None] - velocity[None, :]) * np.sin(theta[None, :] - theta[:, None])


def step_direction(
    mode: str, theta: Array, coupling: Array, omega: Array, rng: np.random.Generator
) -> Array:
    """The gradient, a node relabelling of it, or a random matrix of its norm.

    A relabelling preserves the Frobenius norm and the multiset of entries, so
    the permuted arm takes a step of the gradient's size *and* of its shape,
    acting on edges the gradient did not select. The random arm preserves the
    size alone, and its fresh draws cancel across updates.
    """
    gradient = symmetric_gradient(theta, drift(theta, coupling, omega))
    if mode == "gradient":
        return gradient
    if mode == "permuted":
        order = rng.permutation(len(theta))
        return gradient[np.ix_(order, order)]
    noise = rng.normal(size=gradient.shape)
    noise = (noise + noise.T) / 2
    np.fill_diagonal(noise, 0.0)
    return noise * (float(np.linalg.norm(gradient)) / float(np.linalg.norm(noise)))


def offdiagonal(size: int) -> NDArray[np.bool_]:
    return ~np.eye(size, dtype=bool)


def alignment_ratio(coupling: Array, labels: NDArray[np.int64]) -> float:
    """Mean within-cluster over mean between-cluster coupling; invariant under rescaling."""
    within = (labels[:, None] == labels[None, :]) & offdiagonal(len(labels))
    between = labels[:, None] != labels[None, :]
    return float(coupling[within].mean() / coupling[between].mean())


def template_correlation(coupling: Array, target: Array) -> float:
    """Off-diagonal Pearson correlation with the template; invariant under rescaling."""
    mask = offdiagonal(len(coupling))
    return float(np.corrcoef(coupling[mask], target[mask])[0, 1])


def permutation_percentile(coupling: Array, target: Array, count: int, seed: int) -> float:
    """Fraction of node relabellings the true template's distance is worse than."""
    rng = np.random.default_rng(seed)
    true = float(np.linalg.norm(coupling - target))
    draws = (rng.permutation(len(coupling)) for _ in range(count))
    return float(np.mean([np.linalg.norm(coupling - target[np.ix_(p, p)]) < true for p in draws]))


def diagnostics(theta: Array, coupling: Array, world: Environment, diffusion: float) -> list[float]:
    velocity = drift(theta, coupling, world.omega)
    return [
        float(abs(np.mean(np.exp(1j * theta)))),
        float(velocity @ velocity / diffusion),
        float(np.linalg.norm(coupling - world.target)),
        float(np.linalg.norm(coupling - world.shuffled)),
        float(velocity.mean()),
        alignment_ratio(coupling, world.labels),
        template_correlation(coupling, world.target),
    ]


def simulate(config: Config, mode: str) -> dict[str, Array]:
    """Euler--Maruyama with endpoint-inclusive decimation and only final phase state."""
    validate(config, mode)
    rng = np.random.default_rng(config.seed)
    steps = np.random.default_rng(config.seed + 2)
    total = config.n * config.row_sum
    world = environment(config.n, total, config.seed)
    theta = rng.normal(0.0, 0.1, config.n)
    coupling = project(rng.uniform(0.0, 1.0, (config.n, config.n)), total)
    initial = coupling.copy()
    times, rows = [0.0], [diagnostics(theta, coupling, world, config.diffusion)]
    updates = 0
    scale = config.learning_rate * config.update_every * config.dt
    for step in range(1, config.steps + 1):
        velocity = drift(theta, coupling, world.omega)
        theta += config.dt * velocity + np.sqrt(2 * config.diffusion * config.dt) * rng.normal(
            size=config.n
        )
        theta = (theta + np.pi) % (2 * np.pi) - np.pi
        if mode != "frozen" and step % config.update_every == 0:
            direction = step_direction(mode, theta, coupling, world.omega, steps)
            coupling = project(coupling - scale * direction, total)
            updates += 1
        if step % config.sample_every == 0 or step == config.steps:
            times.append(step * config.dt)
            rows.append(diagnostics(theta, coupling, world, config.diffusion))
    values = np.asarray(rows)
    result = {name: values[:, index] for index, name in enumerate(DIAGNOSTIC_NAMES)}
    result.update(
        time=np.asarray(times),
        coupling_initial=initial,
        coupling_final=coupling,
        theta_final=theta,
        omega=world.omega,
        target=world.target,
        shuffled=world.shuffled,
        permutation=world.permutation.astype(float),
        updates=np.asarray(float(updates)),
    )
    return result


def metrics(result: dict[str, Array], config: Config) -> dict[str, float | bool]:
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
    drive = float(result["omega"].mean())
    return {
        "tail_order": float(result["order"][tail].mean()),
        "minimum_order_after_ten": float(result["order"][time >= min(10.0, time[-1])].min()),
        "tail_dissipation": float(result["dissipation"][tail].mean()),
        "initial_dissipation": float(result["dissipation"][0]),
        "first_quarter_dissipation": float(result["dissipation"][time <= time[-1] / 4].mean()),
        "last_quarter_dissipation": float(result["dissipation"][last].mean()),
        "sigma_floor": config.n * drive**2 / config.diffusion,
        "plateau_relative_change": plateau_change,
        "plateau_pass": abs(plateau_change) <= 0.05,
        "true_distance_reduction": reductions[0],
        "shuffled_distance_reduction": reductions[1],
        "specificity_advantage": reductions[0] - reductions[1],
        "initial_alignment_ratio": float(result["alignment_ratio"][0]),
        "tail_alignment_ratio": float(result["alignment_ratio"][tail].mean()),
        "initial_template_correlation": float(result["template_correlation"][0]),
        "final_template_correlation": float(result["template_correlation"][-1]),
        "permutation_percentile": permutation_percentile(
            result["coupling_final"], result["target"], config.permutations, config.seed + 3
        ),
        "kernel_norm_growth": float(
            np.linalg.norm(result["coupling_final"]) / np.linalg.norm(result["coupling_initial"])
        ),
        "mean_drive": float(result["mean_drift"].mean()),
    }


def descent_fractions(records: list[dict[str, Any]]) -> None:
    """Share of the frozen arm's headroom above the drive floor that each arm removes."""
    frozen = {row["seed"]: row["tail_dissipation"] for row in records if row["mode"] == "frozen"}
    for row in records:
        reference = frozen[row["seed"]]
        row["descent_fraction"] = (reference - row["tail_dissipation"]) / (
            reference - row["sigma_floor"]
        )


def sweep_records(config: Config, rates: tuple[float, ...]) -> list[dict[str, Any]]:
    """Learning-rate sweep on one seed, reporting only the rate-selection criteria."""
    records = []
    for rate in rates:
        scored = metrics(simulate(replace_rate(config, rate), "gradient"), config)
        records.append(
            {
                "learning_rate": rate,
                "tail_dissipation": scored["tail_dissipation"],
                "minimum_order_after_ten": scored["minimum_order_after_ten"],
                "plateau_relative_change": scored["plateau_relative_change"],
                "first_quarter_dissipation": scored["first_quarter_dissipation"],
                "sigma_floor": scored["sigma_floor"],
            }
        )
    return records


def replace_rate(config: Config, rate: float) -> Config:
    return Config(**{**asdict(config), "learning_rate": rate})


def run(output: Path, smoke: bool) -> None:
    output.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, Any]] = []
    seeds = (20260906,) if smoke else (20260906, 20261906, 20262906)
    for seed in seeds:
        config = (
            Config(n=24, steps=2000, permutations=200, seed=seed) if smoke else Config(seed=seed)
        )
        for mode in MODES:
            start = perf_counter()
            result = simulate(config, mode)
            runtime = perf_counter() - start
            np.savez_compressed(
                output / f"{seed}_{mode}.npz",
                allow_pickle=False,
                **result,
                config=json.dumps(asdict(config)),
            )
            records.append(
                {
                    "name": f"{seed}_{mode}",
                    "config": asdict(config),
                    "seed": seed,
                    "mode": mode,
                    "runtime_seconds": runtime,
                    **metrics(result, config),
                }
            )
            print(f"{records[-1]['name']}: {records[-1]}", flush=True)
    descent_fractions(records)
    (output / "summary.json").write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")
    rates = (0.001, 0.2) if smoke else SWEEP_RATES
    sweep = sweep_records(Config(n=24, steps=2000) if smoke else Config(), rates)
    (output / "sweep.json").write_text(json.dumps(sweep, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT)
    args = parser.parse_args()
    run(args.output, args.smoke)


if __name__ == "__main__":
    main()
