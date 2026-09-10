"""Finite-sheet evidence for a row-normalized, spatially decaying Kuramoto kernel.

The simulation tests sampled finite systems and proves no phase-transition,
continuum-limit, or biological claim. Non-zero Gaussian natural frequencies are
used, so the identical-frequency von Mises self-consistency curve is not a
validation target.
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

from fermi_estimate_check import FERMI_LAM_MAX, FERMI_LAM_MIN


FloatArray = NDArray[np.float64]
IntArray = NDArray[np.int64]

PRODUCTION_OUTPUT = Path("figures/spatial_kernel")
REFINED_OUTPUT = Path("figures/spatial_kernel_refined")


@dataclass(frozen=True)
class SpatialConfig:
    """Parameters for one independently initialized spatial trajectory."""

    side: int = 128
    extent_mm: float = 2.0
    decay_mm: float = 0.2
    coupling: float = 8.0
    diffusion: float = 0.5
    frequency_sigma: float = 1.5
    dt: float = 0.01
    steps: int = 20_000
    sample_every: int = 100
    seed: int = 20260904


@dataclass(frozen=True)
class SpatialResult:
    """Decimated observables and one final snapshot, without phase history."""

    time: FloatArray
    order: FloatArray
    defect_density: FloatArray
    final_phases: FloatArray
    final_winding: IntArray
    frequency_mean: float
    frequency_std: float
    runtime_seconds: float


@dataclass(frozen=True)
class SweepSummary:
    """Saved steady-state summaries for a physical decay-length sweep."""

    decay_mm: FloatArray
    steady_order: FloatArray
    steady_defect_density: FloatArray
    critical_decay_mm: float | None
    threshold: float
    runtime_seconds: float


def _validate_config(config: SpatialConfig) -> None:
    positive = (
        config.side,
        config.extent_mm,
        config.decay_mm,
        config.coupling,
        config.dt,
        config.steps,
        config.sample_every,
    )
    if any(value <= 0 for value in positive):
        raise ValueError("spatial scales, coupling, step counts, and dt must be positive")
    if config.diffusion < 0.0 or config.frequency_sigma < 0.0:
        raise ValueError("diffusion and frequency spread must be non-negative")


def empirical_lambda_grid_units(side: int, extent_mm: float) -> FloatArray:
    """Convert the shared 0.1, 0.2, and 0.3 mm controls to grid cells."""
    if side <= 0 or extent_mm <= 0.0:
        raise ValueError("side and physical extent must be positive")
    physical = np.array([FERMI_LAM_MIN, 0.2, FERMI_LAM_MAX])
    return physical * side / extent_mm


def build_kernel(side: int, decay_grid: float, coupling: float) -> FloatArray:
    """Build a toroidal exponential kernel whose row sum is ``coupling``."""
    if side <= 1 or decay_grid <= 0.0 or coupling <= 0.0:
        raise ValueError("kernel dimensions, decay, and coupling must be positive")
    coordinate = np.arange(side)
    periodic = np.minimum(coordinate, side - coordinate).astype(float)
    distance = np.hypot(periodic[:, None], periodic[None, :])
    weights = np.exp(-distance / decay_grid)
    weights[0, 0] = 0.0
    return cast(FloatArray, coupling * weights / np.sum(weights))


def coupling_drift(phases: FloatArray, kernel_fft: NDArray[np.complex128]) -> FloatArray:
    """Evaluate the circular convolution form of the sine-coupling drift."""
    unit_phase = np.exp(1j * phases)
    local_field = np.fft.ifft2(kernel_fft * np.fft.fft2(unit_phase))
    return cast(FloatArray, np.imag(np.exp(-1j * phases) * local_field))


def _wrap(angle: FloatArray) -> FloatArray:
    return (angle + np.pi) % (2.0 * np.pi) - np.pi


def defect_winding(phases: FloatArray) -> IntArray:
    """Return integer winding around every periodic 2x2 plaquette."""
    right = np.roll(phases, -1, axis=1)
    down = np.roll(phases, -1, axis=0)
    down_right = np.roll(right, -1, axis=0)
    circulation = (
        _wrap(right - phases)
        + _wrap(down_right - right)
        + _wrap(down - down_right)
        + _wrap(phases - down)
    )
    return np.rint(circulation / (2.0 * np.pi)).astype(np.int64)


def _record(phases: FloatArray) -> tuple[float, float]:
    order = float(np.abs(np.mean(np.exp(1j * phases))))
    density = float(np.count_nonzero(defect_winding(phases)) / phases.size)
    return order, density


def simulate_spatial(config: SpatialConfig) -> SpatialResult:
    """Integrate one Euler--Maruyama trajectory with quenched detuning."""
    _validate_config(config)
    rng = np.random.default_rng(config.seed)
    phases = rng.uniform(-np.pi, np.pi, size=(config.side, config.side))
    frequencies = rng.normal(0.0, config.frequency_sigma, size=phases.shape)
    decay_grid = config.decay_mm * config.side / config.extent_mm
    kernel_fft = np.fft.fft2(build_kernel(config.side, decay_grid, config.coupling))
    noise_scale = np.sqrt(2.0 * config.diffusion * config.dt)
    sampled_steps = set(range(0, config.steps + 1, config.sample_every)) | {config.steps}
    times: list[float] = []
    orders: list[float] = []
    densities: list[float] = []
    started = time.monotonic()
    for step in range(config.steps + 1):
        if step in sampled_steps:
            order, density = _record(phases)
            times.append(step * config.dt)
            orders.append(order)
            densities.append(density)
        if step == config.steps:
            break
        drift = frequencies + coupling_drift(phases, kernel_fft)
        phases += config.dt * drift + noise_scale * rng.standard_normal(phases.shape)
        phases = _wrap(phases)
    return SpatialResult(
        time=np.asarray(times),
        order=np.asarray(orders),
        defect_density=np.asarray(densities),
        final_phases=phases,
        final_winding=defect_winding(phases),
        frequency_mean=float(np.mean(frequencies)),
        frequency_std=float(np.std(frequencies)),
        runtime_seconds=time.monotonic() - started,
    )


def production_decay_lengths() -> FloatArray:
    """Return a log sweep containing all three empirical controls exactly."""
    broad = np.geomspace(0.0078125, 8.0, 12)
    transition_controls = np.linspace(0.0085, 0.0140, 7)
    return np.unique(
        np.concatenate((broad, transition_controls, [FERMI_LAM_MIN, 0.2, FERMI_LAM_MAX]))
    )


def _steady_mean(values: FloatArray) -> float:
    tail = max(1, values.size // 4)
    return float(np.mean(values[-tail:]))


def estimate_critical_decay(
    decay_mm: FloatArray, steady_order: FloatArray, threshold: float
) -> float | None:
    """Interpolate the crossing above which all sampled lengths stay ordered."""
    order = np.argsort(decay_mm)
    x_values = decay_mm[order]
    y_values = steady_order[order]
    for index in range(1, x_values.size):
        low = y_values[index - 1] - threshold
        high = y_values[index] - threshold
        stays_ordered = bool(np.all(y_values[index:] > threshold))
        if low <= 0.0 < high and stays_ordered:
            fraction = -low / (high - low)
            return float(x_values[index - 1] + fraction * (x_values[index] - x_values[index - 1]))
    return None


def spacing_mm(config: SpatialConfig) -> float:
    """Return the physical width of one lattice cell."""
    return config.extent_mm / config.side


def transition_band(
    decay_mm: FloatArray, steady_order: FloatArray, threshold: float, follow: int = 2
) -> FloatArray:
    """Return the sampled lengths up to the first sustained crossing, and ``follow`` past it.

    Below the band every sampled length is incoherent, so the band is the only
    part of a sweep that a change of resolution can move. The lengths past the
    crossing are what make the sustained half of the criterion mean anything: a
    boundary whose coherent side is one sample is a boundary no rerun tests.
    """
    order = np.argsort(decay_mm)
    lengths = decay_mm[order]
    values = steady_order[order]
    index = lengths.size - 1
    while index > 0 and values[index - 1] > threshold:
        index -= 1
    return lengths[: index + 1 + follow]


def refined_decay_lengths(
    band: FloatArray, base: SpatialConfig, refined: SpatialConfig
) -> FloatArray:
    """Sample the band twice, once for each thing the boundary could be.

    A boundary that belongs to the dynamics sits at a fixed physical length and
    is unmoved by the finer sheet, so the refined sweep must sample ``band``
    itself. A boundary that belongs to the discretisation sits at a fixed number
    of lattice spacings, which on the finer sheet is a shorter physical length —
    the same cell counts scaled by the ratio of the two spacings. Running both
    makes the two answers two runs rather than two readings of one run.
    """
    ratio = spacing_mm(refined) / spacing_mm(base)
    return np.unique(np.concatenate((band, band * ratio)))


def _save_run(path: Path, config: SpatialConfig, result: SpatialResult) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        config=np.asarray(json.dumps(asdict(config), sort_keys=True)),
        time=result.time,
        order=result.order,
        defect_density=result.defect_density,
        final_phases=result.final_phases,
        final_winding=result.final_winding,
        frequency_mean=np.asarray(result.frequency_mean),
        frequency_std=np.asarray(result.frequency_std),
        runtime_seconds=np.asarray(result.runtime_seconds),
    )


def _load_run(path: Path) -> SpatialResult:
    with np.load(path, allow_pickle=False) as saved:
        return SpatialResult(
            time=np.asarray(saved["time"]),
            order=np.asarray(saved["order"]),
            defect_density=np.asarray(saved["defect_density"]),
            final_phases=np.asarray(saved["final_phases"]),
            final_winding=np.asarray(saved["final_winding"]),
            frequency_mean=float(saved["frequency_mean"]),
            frequency_std=float(saved["frequency_std"]),
            runtime_seconds=float(saved["runtime_seconds"]),
        )


def _run_path(output: Path, decay_mm: float) -> Path:
    return output / f"spatial_lambda_{decay_mm:.6f}.npz"


def run_sweep(config: SpatialConfig, decay_lengths: FloatArray, output: Path) -> SweepSummary:
    """Run or resume independent lengths and save required compact artifacts."""
    results: list[SpatialResult] = []
    for decay_mm in decay_lengths:
        run_config = SpatialConfig(**{**asdict(config), "decay_mm": float(decay_mm)})
        path = _run_path(output, float(decay_mm))
        result = _load_run(path) if path.exists() else simulate_spatial(run_config)
        if not path.exists():
            _save_run(path, run_config, result)
        results.append(result)
        print(
            f"lambda={decay_mm:.6f} mm r={_steady_mean(result.order):.4f} "
            f"defects={_steady_mean(result.defect_density):.6f}",
            flush=True,
        )
    steady_order = np.asarray([_steady_mean(result.order) for result in results])
    steady_defects = np.asarray([_steady_mean(result.defect_density) for result in results])
    threshold = max(5.0 / config.side, 0.2)
    summary = SweepSummary(
        decay_mm=decay_lengths,
        steady_order=steady_order,
        steady_defect_density=steady_defects,
        critical_decay_mm=estimate_critical_decay(decay_lengths, steady_order, threshold),
        threshold=threshold,
        runtime_seconds=float(sum(result.runtime_seconds for result in results)),
    )
    _save_summary(output, config, summary)
    _plot_outputs(output, config, results, summary)
    return summary


def _save_summary(output: Path, config: SpatialConfig, summary: SweepSummary) -> None:
    output.mkdir(parents=True, exist_ok=True)
    payload = {
        "config": asdict(config),
        "decay_mm": summary.decay_mm.tolist(),
        "steady_order": summary.steady_order.tolist(),
        "steady_defect_density": summary.steady_defect_density.tolist(),
        "critical_decay_mm": summary.critical_decay_mm,
        "order_threshold": summary.threshold,
        "runtime_seconds": summary.runtime_seconds,
        "scope": "finite-N heuristic evidence; no theorem or biological measurement",
    }
    (output / "spatial_kernel_summary.json").write_text(json.dumps(payload, indent=2) + "\n")


def _plot_outputs(
    output: Path,
    config: SpatialConfig,
    results: list[SpatialResult],
    summary: SweepSummary,
) -> None:
    figure, (trace_axis, sweep_axis) = plt.subplots(1, 2, figsize=(12, 4.5))
    for decay, result in zip(summary.decay_mm, results, strict=True):
        trace_axis.plot(result.time, result.order, linewidth=0.8, label=f"{decay:.3g} mm")
    trace_axis.axhline(1.0 / config.side, color="black", linestyle="--", label=r"$1/\sqrt{N}$")
    trace_axis.set(xlabel="time (s)", ylabel="global order r", title="Finite-sheet traces")
    trace_axis.legend(fontsize=6, ncol=2)
    sweep_axis.semilogx(summary.decay_mm, summary.steady_order, "o-", label="steady r")
    sweep_axis.axhline(1.0 / config.side, color="black", linestyle="--", label=r"$1/\sqrt{N}$")
    defect_axis = sweep_axis.twinx()
    defect_axis.semilogx(
        summary.decay_mm, summary.steady_defect_density, "s-", color="tab:red", label="defects"
    )
    sweep_axis.axvspan(FERMI_LAM_MIN, FERMI_LAM_MAX, alpha=0.15, color="tab:green")
    sweep_axis.set(
        xlabel="decay length (mm)", ylabel="steady global order r", title="Geometry sweep"
    )
    defect_axis.set_ylabel("winding-defect density")
    figure.tight_layout()
    figure.savefig(output / "spatial_kernel_sweep.png", dpi=180)
    plt.close(figure)

    columns = 5
    rows = int(np.ceil(len(results) / columns))
    maps, axes = plt.subplots(rows, columns, figsize=(2.6 * columns, 2.4 * rows), squeeze=False)
    for axis, decay, result in zip(axes.flat, summary.decay_mm, results, strict=False):
        image = axis.imshow(result.final_phases, cmap="twilight", vmin=-np.pi, vmax=np.pi)
        defects = np.nonzero(result.final_winding)
        axis.scatter(defects[1], defects[0], s=3, c="black")
        axis.set_title(f"λ={decay:.3g} mm, r={_steady_mean(result.order):.2f}", fontsize=8)
        axis.set_xticks([])
        axis.set_yticks([])
    for axis in list(axes.flat)[len(results) :]:
        axis.set_visible(False)
    maps.colorbar(image, ax=axes.ravel().tolist(), shrink=0.7, label="phase (rad)")
    maps.suptitle("Final phase snapshots: finite sampled trajectories")
    maps.savefig(output / "spatial_kernel_phase_maps.png", dpi=180, bbox_inches="tight")
    plt.close(maps)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="run a reduced deterministic sweep")
    parser.add_argument(
        "--refine",
        action="store_true",
        help="rerun the transition band on a sheet of halved spacing",
    )
    parser.add_argument(
        "--coarse",
        type=Path,
        default=PRODUCTION_OUTPUT,
        help="sweep whose transition band the refinement reruns",
    )
    parser.add_argument("--output", type=Path, default=None)
    return parser.parse_args()


def _saved_band(coarse: Path) -> FloatArray:
    """Read the transition band out of a completed sweep's saved summary."""
    data = json.loads((coarse / "spatial_kernel_summary.json").read_text(encoding="utf-8"))
    return transition_band(
        np.asarray(data["decay_mm"]),
        np.asarray(data["steady_order"]),
        float(data["order_threshold"]),
    )


def _plan(args: argparse.Namespace) -> tuple[SpatialConfig, FloatArray, Path]:
    """Choose the configuration, the lengths, and where the run is saved."""
    base = (
        SpatialConfig(side=24, steps=100, sample_every=20, dt=0.02)
        if args.smoke
        else SpatialConfig()
    )
    if not args.refine:
        lengths = np.array([0.05, 0.2, 2.0]) if args.smoke else production_decay_lengths()
        return base, lengths, args.output or PRODUCTION_OUTPUT
    refined = replace(base, side=2 * base.side)
    band = np.array([0.05, 0.2]) if args.smoke else _saved_band(args.coarse)
    return refined, refined_decay_lengths(band, base, refined), args.output or REFINED_OUTPUT


def main() -> None:
    """Run the reduced, production, or refined sweep and print the operational result."""
    args = _parse_args()
    config, lengths, output = _plan(args)
    summary = run_sweep(config, lengths, output)
    critical = (
        "not bracketed"
        if summary.critical_decay_mm is None
        else f"{summary.critical_decay_mm:.6f} mm "
        f"({summary.critical_decay_mm / spacing_mm(config):.2f} lattice spacings)"
    )
    print(f"operational critical decay length at side {config.side}: {critical}")
    print("scope: finite-N heuristic evidence; no theorem or biological measurement")


if __name__ == "__main__":
    main()
