"""Conservative periodic Fokker--Planck pilot for G22 current cost.

The finite-volume flux evolves the density and supplies its measured cost.
This is a homogeneous, deterministic density solver, not an oscillator or
cortical model. Its discretization has numerical error; the continuum bound
is assessed with a declared tolerance rather than imposed by construction.
"""

from dataclasses import dataclass
from pathlib import Path
from typing import Literal

import numpy as np
from numpy.typing import NDArray

Schedule = Literal["linear", "early", "late"]
FloatArray = NDArray[np.float64]


@dataclass(frozen=True)
class Config:
    """Declared density, diffusion and coupling schedule."""

    cells: int = 64
    duration: float = 1.0
    diffusion: float = 0.5
    initial_order: float = 0.2
    start_coupling: float = 0.4
    end_coupling: float = 2.0
    schedule: Schedule = "linear"


@dataclass(frozen=True)
class Result:
    """Full sampled trajectory and its integrated probability-current cost."""

    config: Config
    spacing: float
    time: FloatArray
    density: FloatArray
    current: FloatArray
    order: FloatArray
    coupling: FloatArray
    accumulated_cost: FloatArray
    endpoint_bound: float


def _validate_grid(config: Config) -> None:
    if config.cells < 8 or config.initial_order < 0 or config.initial_order >= 0.5:
        raise ValueError("Need at least 8 cells and initial order in [0, 0.5)")
    if config.schedule not in ("linear", "early", "late"):
        raise ValueError("Unknown coupling schedule")


def _validate_physics(config: Config) -> None:
    values = (config.duration, config.diffusion, config.start_coupling, config.end_coupling)
    if not all(np.isfinite(value) for value in values):
        raise ValueError("Protocol parameters must be finite")
    if config.duration <= 0 or config.diffusion <= 0:
        raise ValueError("Duration and diffusion must be positive")
    if min(config.start_coupling, config.end_coupling) < 0:
        raise ValueError("This pilot uses nonnegative coupling")


def _validate(config: Config) -> None:
    _validate_grid(config)
    _validate_physics(config)


def coupling_at(config: Config, time: float) -> float:
    """Schedules share both endpoint couplings and total duration."""
    fraction = time / config.duration
    if config.schedule == "early":
        fraction = 1 - (1 - fraction) ** 2
    elif config.schedule == "late":
        fraction **= 2
    return config.start_coupling + (config.end_coupling - config.start_coupling) * fraction


def _flux(
    density: FloatArray,
    coupling: float,
    diffusion: float,
    centers: FloatArray,
    edges: FloatArray,
    spacing: float,
) -> FloatArray:
    moment = spacing * np.sum(density * np.exp(1j * centers))
    if abs(moment) < 1e-14:
        drift = np.zeros_like(edges)
    else:
        drift = coupling * np.imag(moment * np.exp(-1j * edges))
    forward = np.roll(density, -1)
    upwind = np.where(drift >= 0, density, forward)
    return np.asarray(drift * upwind - diffusion * (forward - density) / spacing, dtype=np.float64)


def _cost(flux: FloatArray, density: FloatArray, diffusion: float, spacing: float) -> float:
    edge_density = (density + np.roll(density, -1)) / 2
    return float(spacing * np.sum(flux**2 / (diffusion * edge_density)))


def _state(
    config: Config,
    density: FloatArray,
    time: float,
    centers: FloatArray,
    edges: FloatArray,
    spacing: float,
) -> tuple[float, FloatArray, float, float]:
    coupling = coupling_at(config, time)
    flux = _flux(density, coupling, config.diffusion, centers, edges, spacing)
    order = float(abs(spacing * np.sum(density * np.exp(1j * centers))))
    return coupling, flux, order, _cost(flux, density, config.diffusion, spacing)


def run_protocol(config: Config) -> Result:
    """Evolve a positive periodic density under the declared coupling schedule."""
    _validate(config)
    spacing = 2 * np.pi / config.cells
    centers = np.asarray(-np.pi + (np.arange(config.cells) + 0.5) * spacing, dtype=np.float64)
    edges = np.asarray(centers + spacing / 2, dtype=np.float64)
    max_coupling = max(config.start_coupling, config.end_coupling)
    max_step = 0.7 * spacing**2 / (2 * config.diffusion + max_coupling * spacing)
    steps = max(1, int(np.ceil(config.duration / max_step)))
    step = config.duration / steps
    time = np.linspace(0, config.duration, steps + 1)
    density = np.empty((steps + 1, config.cells))
    current = np.empty_like(density)
    order = np.empty(steps + 1)
    coupling = np.empty(steps + 1)
    accumulated = np.zeros(steps + 1)
    density[0] = (1 + 2 * config.initial_order * np.cos(centers)) / (2 * np.pi)
    previous_cost = 0.0
    for index, instant in enumerate(time):
        coupling[index], current[index], order[index], cost = _state(
            config, density[index], float(instant), centers, edges, spacing
        )
        if index:
            accumulated[index] = accumulated[index - 1] + step * (previous_cost + cost) / 2
        if index < steps:
            density[index + 1] = (
                density[index] - step * (current[index] - np.roll(current[index], 1)) / spacing
            )
        previous_cost = cost
    endpoint_bound = float(
        (np.arcsin(order[-1]) - np.arcsin(order[0])) ** 2 / (config.diffusion * config.duration)
    )
    return Result(
        config, spacing, time, density, current, order, coupling, accumulated, endpoint_bound
    )


def save_protocol(path: Path, result: Result) -> None:
    """Save the full trajectory and all parameters needed to inspect the bound."""
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        time=result.time,
        density=result.density,
        current=result.current,
        order=result.order,
        coupling=result.coupling,
        accumulated_cost=result.accumulated_cost,
        endpoint_bound=result.endpoint_bound,
        spacing=result.spacing,
        duration=result.config.duration,
        diffusion=result.config.diffusion,
        cells=result.config.cells,
        initial_order=result.config.initial_order,
        start_coupling=result.config.start_coupling,
        end_coupling=result.config.end_coupling,
        schedule=result.config.schedule,
    )


def run_parameter_grid(
    output: Path,
    *,
    cells: int = 48,
    diffusions: tuple[float, ...] = (0.25, 0.5, 1.0),
    durations: tuple[float, ...] = (0.4, 1.0),
) -> list[Path]:
    """Save prespecified ramps and exact uniform/relaxation controls.

    This runs the solver. Reporting must read the saved files separately.
    Heterogeneous dynamics and operational onset are outside this grid.
    """
    paths: list[Path] = []
    for diffusion in diffusions:
        for duration in durations:
            protocols: tuple[tuple[str, float, float, float, Schedule], ...] = (
                ("early", 0.2, 0.4, 2.0, "early"),
                ("linear", 0.2, 0.4, 2.0, "linear"),
                ("late", 0.2, 0.4, 2.0, "late"),
                ("uniform", 0.0, 0.0, 2.0, "linear"),
                ("relaxation", 0.2, 0.0, 0.0, "linear"),
            )
            for name, initial, start, end, schedule in protocols:
                config = Config(cells, duration, diffusion, initial, start, end, schedule)
                path = output / f"D{diffusion:g}_T{duration:g}_{name}.npz"
                save_protocol(path, run_protocol(config))
                paths.append(path)
    return paths


def run_onset_resolution(
    output: Path, *, cells: tuple[int, ...] = (32, 48, 64, 96, 128, 192, 256)
) -> list[Path]:
    """Save a resolution check for the exploratory D=0.25 early-ramp crossing."""
    paths: list[Path] = []
    for count in cells:
        path = output / f"early_N{count}.npz"
        config = Config(cells=count, duration=1.0, diffusion=0.25, schedule="early")
        save_protocol(path, run_protocol(config))
        paths.append(path)
    return paths


if __name__ == "__main__":
    schedules: tuple[Schedule, ...] = ("linear", "early", "late")
    for schedule_name in schedules:
        run = run_protocol(Config(schedule=schedule_name))
        save_protocol(Path("figures/g22_pilot") / f"{schedule_name}.npz", run)
        print(schedule_name, run.order[-1], run.accumulated_cost[-1], run.endpoint_bound)
    for name, initial in (("uniform", 0.0), ("relaxation", 0.2)):
        control = run_protocol(Config(initial_order=initial, start_coupling=0.0, end_coupling=0.0))
        save_protocol(Path("figures/g22_pilot") / f"{name}.npz", control)
        print(name, control.order[-1], control.accumulated_cost[-1], control.endpoint_bound)
