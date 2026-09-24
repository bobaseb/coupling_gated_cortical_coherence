"""Two-frequency conservative density pilot for the G22 current bound.

Each cohort has normalized periodic density and frequency ±spread. The
aggregate density obeys continuity with its aggregate current, so the G22
bound concerns aggregate current cost. The mean cohort cost is a distinct,
larger account by pointwise Cauchy--Schwarz for the same diffusion constant.
Neither account is heat or metabolic power.
"""

from dataclasses import dataclass
from pathlib import Path

import numpy as np
from numpy.typing import NDArray

from g22_current_sim import Config, Schedule, _validate, coupling_at

FloatArray = NDArray[np.float64]


@dataclass(frozen=True)
class HeteroConfig(Config):
    """Two equally weighted frequency cohorts on the same periodic grid."""

    spread: float = 0.1


@dataclass(frozen=True)
class HeteroResult:
    """Cohort paths and separate aggregate/cohort current-cost ledgers."""

    config: HeteroConfig
    spacing: float
    time: FloatArray
    density: FloatArray
    current: FloatArray
    order: FloatArray
    accumulated_marginal_cost: FloatArray
    accumulated_cohort_cost: FloatArray
    endpoint_bound: float


def _current(
    density: FloatArray,
    coupling: float,
    spread: float,
    diffusion: float,
    centers: FloatArray,
    edges: FloatArray,
    spacing: float,
) -> FloatArray:
    marginal = density.mean(axis=0)
    moment = spacing * np.sum(marginal * np.exp(1j * centers))
    mean_drift = coupling * np.imag(moment * np.exp(-1j * edges))
    drift = mean_drift[None, :] + np.array([-spread, spread])[:, None]
    forward = np.roll(density, -1, axis=1)
    upwind = np.where(drift >= 0, density, forward)
    return np.asarray(drift * upwind - diffusion * (forward - density) / spacing, dtype=np.float64)


def _costs(
    density: FloatArray, current: FloatArray, diffusion: float, spacing: float
) -> tuple[float, float]:
    edge_density = (density + np.roll(density, -1, axis=1)) / 2
    marginal_density = edge_density.mean(axis=0)
    marginal_current = current.mean(axis=0)
    marginal_cost = spacing * np.sum(marginal_current**2 / (diffusion * marginal_density))
    cohort_cost = spacing * np.mean(np.sum(current**2 / (diffusion * edge_density), axis=1))
    return float(marginal_cost), float(cohort_cost)


def run_heterogeneous(config: HeteroConfig) -> HeteroResult:
    """Evolve two normalized cohorts using their shared aggregate order field."""
    _validate(config)
    if not np.isfinite(config.spread) or config.spread < 0:
        raise ValueError("Frequency spread must be finite and nonnegative")
    spacing = 2 * np.pi / config.cells
    centers = np.asarray(-np.pi + (np.arange(config.cells) + 0.5) * spacing, dtype=np.float64)
    edges = np.asarray(centers + spacing / 2, dtype=np.float64)
    max_drift = max(config.start_coupling, config.end_coupling) + config.spread
    max_step = 0.7 * spacing**2 / (2 * config.diffusion + max_drift * spacing)
    steps = max(1, int(np.ceil(config.duration / max_step)))
    step = config.duration / steps
    time = np.linspace(0, config.duration, steps + 1)
    density = np.empty((steps + 1, 2, config.cells))
    current = np.empty_like(density)
    order = np.empty(steps + 1)
    marginal_cost = np.zeros(steps + 1)
    cohort_cost = np.zeros(steps + 1)
    density[0] = (1 + 2 * config.initial_order * np.cos(centers)) / (2 * np.pi)
    previous = (0.0, 0.0)
    for index, instant in enumerate(time):
        current[index] = _current(
            density[index],
            coupling_at(config, float(instant)),
            config.spread,
            config.diffusion,
            centers,
            edges,
            spacing,
        )
        moment = spacing * np.sum(density[index].mean(axis=0) * np.exp(1j * centers))
        order[index] = abs(moment)
        costs = _costs(density[index], current[index], config.diffusion, spacing)
        if index:
            marginal_cost[index] = marginal_cost[index - 1] + step * (previous[0] + costs[0]) / 2
            cohort_cost[index] = cohort_cost[index - 1] + step * (previous[1] + costs[1]) / 2
        if index < steps:
            density[index + 1] = (
                density[index]
                - step * (current[index] - np.roll(current[index], 1, axis=1)) / spacing
            )
        previous = costs
    bound = (np.arcsin(order[-1]) - np.arcsin(order[0])) ** 2 / (config.diffusion * config.duration)
    return HeteroResult(
        config,
        spacing,
        time,
        density,
        current,
        order,
        marginal_cost,
        cohort_cost,
        float(bound),
    )


def save_heterogeneous(path: Path, result: HeteroResult) -> None:
    """Save cohort paths, protocol values, and both cost ledgers."""
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        time=result.time,
        density=result.density,
        current=result.current,
        order=result.order,
        accumulated_marginal_cost=result.accumulated_marginal_cost,
        accumulated_cohort_cost=result.accumulated_cohort_cost,
        endpoint_bound=result.endpoint_bound,
        spacing=result.spacing,
        cells=result.config.cells,
        duration=result.config.duration,
        diffusion=result.config.diffusion,
        spread=result.config.spread,
        initial_order=result.config.initial_order,
        start_coupling=result.config.start_coupling,
        end_coupling=result.config.end_coupling,
        schedule=result.config.schedule,
    )


def run_heterogeneous_grid(
    output: Path,
    *,
    diffusions: tuple[float, ...] = (0.25, 0.5),
    spreads: tuple[float, ...] = (0.0, 0.1, 0.3),
    schedules: tuple[Schedule, ...] = ("early", "linear", "late"),
    cells: int = 64,
) -> list[Path]:
    """Save equal-endpoint ramps across diffusion and two-frequency spread."""
    paths: list[Path] = []
    for diffusion in diffusions:
        for spread in spreads:
            for schedule in schedules:
                config = HeteroConfig(
                    cells=cells,
                    duration=1.0,
                    diffusion=diffusion,
                    initial_order=0.2,
                    start_coupling=0.4,
                    end_coupling=2.0,
                    schedule=schedule,
                    spread=spread,
                )
                path = output / f"D{diffusion:g}_h{spread:g}_{schedule}.npz"
                save_heterogeneous(path, run_heterogeneous(config))
                paths.append(path)
    return paths
