"""Finite-sheet evidence on what the global order parameter reports for a wave.

The framework's coherence observable is the global resultant
``r = |mean exp(i theta)|``, and a phase field that winds once across the sheet
has ``r = 0`` while every patch of it stays locked. This module measures that
separation on the same sheet, kernel and integrator as ``spatial_kernel``,
adding a patch-local order parameter beside the global one.

Two wave states are run. A *twisted* initial condition imposes winding with
identical frequencies, so it sits inside both hypotheses the Lean convergence
results carry --- positive symmetric coupling and zero detuning --- and asks
whether the sheet relaxes out of it. A *detuned* run adds a periodic frequency
profile, which keeps positivity and drops only the identical-frequency
hypothesis. Neither run measures cortex, and neither establishes a transition.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.axes import Axes
from matplotlib.ticker import FuncFormatter, NullFormatter
from numpy.typing import NDArray

from fermi_estimate_check import FERMI_LAM_MAX, FERMI_LAM_MIN
from spatial_kernel import FIGURES, build_kernel, coupling_drift, defect_winding

FloatArray = NDArray[np.float64]
IntArray = NDArray[np.int64]

PRODUCTION_OUTPUT = FIGURES / "travelling_wave"
DISORDERED_OUTPUT = FIGURES / "travelling_wave_disordered"


@dataclass(frozen=True)
class WaveConfig:
    """Parameters for one sheet carrying an imposed twist or a detuning."""

    side: int = 128
    extent_mm: float = 2.0
    decay_mm: float = 0.2
    coupling: float = 8.0
    diffusion: float = 0.5
    winding_q: int = 0
    detuning_rad_s: float = 0.0
    frequency_sigma: float = 0.0
    patch_mm: float = 0.2
    dt: float = 0.01
    steps: int = 20_000
    sample_every: int = 100
    seed: int = 20260918


@dataclass(frozen=True)
class WaveResult:
    """Decimated observables and one final snapshot, without phase history."""

    time: FloatArray
    global_order: FloatArray
    local_order: FloatArray
    defect_density: FloatArray
    axis_winding: list[tuple[int, int]]
    final_phases: FloatArray
    runtime_seconds: float


@dataclass(frozen=True)
class WaveSummary:
    """Steady observables for one sweep over spatial decay lengths.

    Each length is run twice: once from the imposed twist and once from the
    uniform state, so the control that must show no gap is measured rather than
    assumed.
    """

    decay_mm: FloatArray
    steady_global: FloatArray
    steady_local: FloatArray
    steady_gap: FloatArray
    steady_defect_density: FloatArray
    retained_winding: IntArray
    control_global: FloatArray
    boundary_mm: float | None
    runtime_seconds: float


def _validate(config: WaveConfig) -> None:
    positive = (config.side, config.extent_mm, config.decay_mm, config.coupling, config.dt)
    if any(value <= 0 for value in positive):
        raise ValueError("sheet scales, coupling, and dt must be positive")
    if config.steps <= 0 or config.sample_every <= 0:
        raise ValueError("step counts must be positive")
    if config.diffusion < 0.0 or config.patch_mm <= 0.0:
        raise ValueError("diffusion must be non-negative and the patch radius positive")
    if config.frequency_sigma < 0.0:
        raise ValueError("the quenched frequency spread must be non-negative")


def _wrap(angle: FloatArray) -> FloatArray:
    return (angle + np.pi) % (2.0 * np.pi) - np.pi


def twisted_phases(side: int, winding_q: int) -> FloatArray:
    """Return the phase field winding ``winding_q`` times across the columns.

    On a torus this is an exact stationary state of any isotropic symmetric
    kernel at identical frequencies: the coupling drift sums a term odd in the
    separation against a kernel even in it.
    """
    if side <= 1:
        raise ValueError("a twisted sheet needs at least two columns")
    column = np.arange(side, dtype=float)
    return _wrap(np.broadcast_to(2.0 * np.pi * winding_q * column / side, (side, side)).copy())


def detuning_field(side: int, detuning_rad_s: float) -> FloatArray:
    """Return a zero-mean natural-frequency profile that is periodic across columns.

    A linear ramp is the usual travelling-wave drive, but it is discontinuous on
    a torus, so the seam rather than the gradient would set the result. One
    period of a sinusoid carries the same monotone stretch without the seam.
    """
    if side <= 1:
        raise ValueError("a detuned sheet needs at least two columns")
    column = np.arange(side, dtype=float)
    profile = detuning_rad_s * np.sin(2.0 * np.pi * column / side)
    return np.broadcast_to(profile, (side, side)).copy()


def frequency_field(config: WaveConfig, rng: np.random.Generator) -> FloatArray:
    """Return natural frequencies: the periodic detuning plus quenched disorder.

    Disorder is drawn before the trajectory, so a twisted run and its uniform
    control at one seed see the same frozen frequencies and the same noise.
    Any nonzero spread leaves the identical-frequency hypothesis, under which a
    twist is no longer stationary; whether it survives anyway is the question.
    """
    field = detuning_field(config.side, config.detuning_rad_s)
    if config.frequency_sigma == 0.0:
        return field
    return field + rng.normal(0.0, config.frequency_sigma, size=field.shape)


def patch_cells(config: WaveConfig) -> int:
    """Return the patch radius in lattice cells, clamped to fit on the sheet."""
    cells = int(config.patch_mm * config.side / config.extent_mm)
    return max(1, min(cells, (config.side - 1) // 2))


def global_order(phases: FloatArray) -> float:
    """Return the framework's coherence observable, the global resultant length."""
    return float(np.abs(np.mean(np.exp(1j * phases))))


def _patch_window(side: int, cells: int) -> NDArray[np.complex128]:
    offsets = np.arange(-cells, cells + 1) % side
    window = np.zeros((side, side))
    window[np.ix_(offsets, offsets)] = 1.0
    return np.fft.fft2(window / np.sum(window))


def local_order(phases: FloatArray, cells: int) -> float:
    """Return the mean resultant length of the patches of radius ``cells``.

    The patch means average back to the global mean, so this never falls below
    ``global_order``; the difference is exactly the phase structure the global
    resultant discards.
    """
    side = phases.shape[0]
    cells = max(1, min(cells, (side - 1) // 2))
    smoothed = np.fft.ifft2(_patch_window(side, cells) * np.fft.fft2(np.exp(1j * phases)))
    return float(np.mean(np.abs(smoothed)))


def axis_winding(phases: FloatArray) -> tuple[int, int]:
    """Return the net phase winding down the rows and across the columns.

    Winding is read from wrapped nearest-neighbour differences, so it resolves
    ``|q| < side / 2``. At exactly ``side / 2`` the per-cell step is ``pi``, whose
    sign the lattice does not fix, and above it the twist aliases to a slower one.
    """
    across = _wrap(np.roll(phases, -1, axis=1) - phases).sum(axis=1) / (2.0 * np.pi)
    down = _wrap(np.roll(phases, -1, axis=0) - phases).sum(axis=0) / (2.0 * np.pi)
    return int(np.rint(np.mean(down))), int(np.rint(np.mean(across)))


def _steady_mean(values: FloatArray) -> float:
    tail = max(1, values.size // 4)
    return float(np.mean(values[-tail:]))


def coherence_gap(result: WaveResult) -> float:
    """Return the steady local order less the steady global order."""
    return _steady_mean(result.local_order) - _steady_mean(result.global_order)


def _record(phases: FloatArray, cells: int) -> tuple[float, float, float, tuple[int, int]]:
    defects = float(np.count_nonzero(defect_winding(phases)) / phases.size)
    return global_order(phases), local_order(phases, cells), defects, axis_winding(phases)


def simulate_wave(config: WaveConfig) -> WaveResult:
    """Integrate one Euler--Maruyama trajectory from an imposed twist."""
    _validate(config)
    rng = np.random.default_rng(config.seed)
    phases = twisted_phases(config.side, config.winding_q)
    frequencies = frequency_field(config, rng)
    decay_grid = config.decay_mm * config.side / config.extent_mm
    kernel_fft = np.fft.fft2(build_kernel(config.side, decay_grid, config.coupling))
    noise_scale = np.sqrt(2.0 * config.diffusion * config.dt)
    cells = patch_cells(config)
    sampled = set(range(0, config.steps + 1, config.sample_every)) | {config.steps}
    records: list[tuple[float, float, float, tuple[int, int]]] = []
    times: list[float] = []
    started = time.monotonic()
    for step in range(config.steps + 1):
        if step in sampled:
            records.append(_record(phases, cells))
            times.append(step * config.dt)
        if step == config.steps:
            break
        drift = frequencies + coupling_drift(phases, kernel_fft)
        phases = _wrap(phases + config.dt * drift + noise_scale * rng.standard_normal(phases.shape))
    return WaveResult(
        time=np.asarray(times),
        global_order=np.asarray([entry[0] for entry in records]),
        local_order=np.asarray([entry[1] for entry in records]),
        defect_density=np.asarray([entry[2] for entry in records]),
        axis_winding=[entry[3] for entry in records],
        final_phases=phases,
        runtime_seconds=time.monotonic() - started,
    )


def _run_path(output: Path, decay_mm: float, winding_q: int) -> Path:
    return output / f"wave_lambda_{decay_mm:.6f}_q{winding_q}.npz"


def _save_run(path: Path, config: WaveConfig, result: WaveResult) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        config=np.asarray(json.dumps(asdict(config), sort_keys=True)),
        time=result.time,
        global_order=result.global_order,
        local_order=result.local_order,
        defect_density=result.defect_density,
        axis_winding=np.asarray(result.axis_winding, dtype=np.int64),
        final_phases=result.final_phases,
        runtime_seconds=np.asarray(result.runtime_seconds),
    )


def _load_run(path: Path) -> WaveResult:
    with np.load(path, allow_pickle=False) as saved:
        winding = np.asarray(saved["axis_winding"])
        return WaveResult(
            time=np.asarray(saved["time"]),
            global_order=np.asarray(saved["global_order"]),
            local_order=np.asarray(saved["local_order"]),
            defect_density=np.asarray(saved["defect_density"]),
            axis_winding=[(int(row[0]), int(row[1])) for row in winding],
            final_phases=np.asarray(saved["final_phases"]),
            runtime_seconds=float(saved["runtime_seconds"]),
        )


def _resume(config: WaveConfig, output: Path) -> WaveResult:
    path = _run_path(output, config.decay_mm, config.winding_q)
    if path.exists():
        return _load_run(path)
    result = simulate_wave(config)
    _save_run(path, config, result)
    return result


def retention_boundary(decay_mm: FloatArray, retained: IntArray) -> float | None:
    """Interpolate the decay length above which no sampled length holds the twist.

    Retention is a short-range property, so the sweep runs from held to lost as
    the length grows. The crossing counts only if every longer length also loses
    it, on the sustained-crossing rule ``spatial_kernel`` uses for coherence.
    """
    order = np.argsort(decay_mm)
    lengths, held = decay_mm[order], retained[order] != 0
    for index in range(1, lengths.size):
        if held[index - 1] and not np.any(held[index:]):
            return float(np.sqrt(lengths[index - 1] * lengths[index]))
    return None


def _run_pair(config: WaveConfig, decay_mm: float, output: Path) -> tuple[WaveResult, WaveResult]:
    fields = {**asdict(config), "decay_mm": decay_mm}
    wave = _resume(WaveConfig(**{**fields, "winding_q": config.winding_q}), output)
    control = _resume(WaveConfig(**{**fields, "winding_q": 0}), output)
    return wave, control


def run_sweep(config: WaveConfig, decay_lengths: FloatArray, output: Path) -> WaveSummary:
    """Run the twist and its uniform control at each decay length."""
    waves: list[WaveResult] = []
    controls: list[WaveResult] = []
    for decay_mm in decay_lengths:
        wave, control = _run_pair(config, float(decay_mm), output)
        waves.append(wave)
        controls.append(control)
        print(
            f"lambda={decay_mm:.4f} mm kept={wave.axis_winding[-1][1]:+d} "
            f"r_global={_steady_mean(wave.global_order):.4f} "
            f"r_local={_steady_mean(wave.local_order):.4f} "
            f"gap={coherence_gap(wave):.4f} "
            f"control_r={_steady_mean(control.global_order):.4f} "
            f"defects={_steady_mean(wave.defect_density):.6f}",
            flush=True,
        )
    retained = np.asarray([item.axis_winding[-1][1] for item in waves], dtype=np.int64)
    summary = WaveSummary(
        decay_mm=np.asarray(decay_lengths, dtype=float),
        steady_global=np.asarray([_steady_mean(item.global_order) for item in waves]),
        steady_local=np.asarray([_steady_mean(item.local_order) for item in waves]),
        steady_gap=np.asarray([coherence_gap(item) for item in waves]),
        steady_defect_density=np.asarray([_steady_mean(item.defect_density) for item in waves]),
        retained_winding=retained,
        control_global=np.asarray([_steady_mean(item.global_order) for item in controls]),
        boundary_mm=retention_boundary(np.asarray(decay_lengths, dtype=float), retained),
        runtime_seconds=float(sum(item.runtime_seconds for item in waves + controls)),
    )
    _save_summary(output, config, summary)
    _plot_outputs(output, summary, waves)
    return summary


def run_seed_control(
    config: WaveConfig, decay_lengths: FloatArray, seeds: list[int], output: Path
) -> dict[str, object]:
    """Repeat the twisted runs over frozen disorder realisations.

    Quenched frequencies are drawn once per seed, so with a nonzero spread each
    seed is a different frozen landscape and retention could belong to one
    sample rather than to the model. Each seed checkpoints in its own directory,
    leaving the single-seed sweep's paths untouched.
    """
    retained: list[list[int]] = []
    orders: list[list[float]] = []
    for seed in seeds:
        fields = {**asdict(config), "seed": int(seed)}
        results = [
            _resume(WaveConfig(**{**fields, "decay_mm": float(decay)}), output / f"seed_{seed}")
            for decay in decay_lengths
        ]
        retained.append([item.axis_winding[-1][1] for item in results])
        orders.append([_steady_mean(item.global_order) for item in results])
        print(f"seed={seed} kept={retained[-1]}", flush=True)
    payload: dict[str, object] = {
        "config": asdict(config),
        "decay_mm": np.asarray(decay_lengths, dtype=float).tolist(),
        "seeds": list(seeds),
        "retained_winding": retained,
        "steady_global_order": orders,
        "retained_total": sum(1 for row in retained for value in row if value != 0),
        "run_total": len(seeds) * len(decay_lengths),
        "scope": "finite-N heuristic evidence; no theorem or biological measurement",
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "travelling_wave_seeds.json").write_text(json.dumps(payload, indent=2) + "\n")
    return payload


def _save_summary(output: Path, config: WaveConfig, summary: WaveSummary) -> None:
    output.mkdir(parents=True, exist_ok=True)
    payload = {
        "config": asdict(config),
        "decay_mm": summary.decay_mm.tolist(),
        "steady_global_order": summary.steady_global.tolist(),
        "steady_local_order": summary.steady_local.tolist(),
        "steady_coherence_gap": summary.steady_gap.tolist(),
        "steady_defect_density": summary.steady_defect_density.tolist(),
        "retained_winding": summary.retained_winding.tolist(),
        "control_global_order": summary.control_global.tolist(),
        "retention_boundary_mm": summary.boundary_mm,
        "runtime_seconds": summary.runtime_seconds,
        "scope": "finite-N heuristic evidence; no theorem or biological measurement",
    }
    (output / "travelling_wave_summary.json").write_text(json.dumps(payload, indent=2) + "\n")


def replot(output: Path) -> None:
    """Redraw a finished sweep's figures from its saved artifacts.

    Every quantity the figure draws is already on disk: the summary carries the
    boundary panel and each length's twisted checkpoint carries its traces.
    Redrawing therefore integrates nothing, so adjusting a legend or an axis
    never puts the published numbers back through the integrator.
    """
    data = json.loads((output / "travelling_wave_summary.json").read_text(encoding="utf-8"))
    summary = WaveSummary(
        decay_mm=np.asarray(data["decay_mm"]),
        steady_global=np.asarray(data["steady_global_order"]),
        steady_local=np.asarray(data["steady_local_order"]),
        steady_gap=np.asarray(data["steady_coherence_gap"]),
        steady_defect_density=np.asarray(data["steady_defect_density"]),
        retained_winding=np.asarray(data["retained_winding"], dtype=np.int64),
        control_global=np.asarray(data["control_global_order"]),
        boundary_mm=data["retention_boundary_mm"],
        runtime_seconds=float(data["runtime_seconds"]),
    )
    winding_q = int(data["config"]["winding_q"])
    waves = []
    for decay_mm in summary.decay_mm:
        path = _run_path(output, float(decay_mm), winding_q)
        if not path.exists():
            raise FileNotFoundError(f"no saved run for decay length {decay_mm:.6f} mm: {path}")
        waves.append(_load_run(path))
    _plot_outputs(output, summary, waves)


def _trace_subset(summary: WaveSummary, count: int = 6) -> list[int]:
    """Pick evenly spaced lengths so the trace legend stays readable."""
    span = np.linspace(0, summary.decay_mm.size - 1, count)
    return sorted(set(span.round().astype(int).tolist()))


def _plot_traces(axis: Axes, summary: WaveSummary, waves: list[WaveResult]) -> None:
    for index in _trace_subset(summary):
        result = waves[index]
        line = axis.plot(
            result.time,
            result.global_order,
            linewidth=1.0,
            label=f"{summary.decay_mm[index]:.3g} mm",
        )
        axis.plot(
            result.time,
            result.local_order,
            linewidth=1.0,
            linestyle="--",
            color=line[0].get_color(),
        )
    axis.set(xlabel="time (s)", ylabel="order", title="Global (solid) and local (dashed)")
    axis.legend(fontsize=7, ncol=2, title="decay length", title_fontsize=7)


def _plot_sweep(axis: Axes, summary: WaveSummary) -> None:
    axis.semilogx(summary.decay_mm, summary.steady_global, "o-", label="global r (twisted)")
    axis.semilogx(summary.decay_mm, summary.steady_local, "s-", label="local r (twisted)")
    axis.semilogx(summary.decay_mm, summary.control_global, "^--", label="global r (uniform)")
    band = axis.axvspan(FERMI_LAM_MIN, FERMI_LAM_MAX, alpha=0.15, color="tab:green")
    band.set_label("empirical decay-length band")
    if summary.boundary_mm is not None:
        axis.axvline(summary.boundary_mm, color="black", linestyle=":", label="retention boundary")
    axis.set(xlabel="decay length (mm)", ylabel="steady order", title="Where the twist survives")
    axis.set_xticks([0.0125, 0.025, 0.05, 0.1, 0.2, 0.4, 0.8])
    # Four decimals on every tick of a decade-wide log axis reads as noise;
    # the lengths differ in their leading digits, which is what a reader needs.
    axis.xaxis.set_major_formatter(FuncFormatter(lambda value, _: f"{value:g}"))
    axis.xaxis.set_minor_formatter(NullFormatter())
    axis.legend(fontsize=7, loc="center left")


def _plot_outputs(output: Path, summary: WaveSummary, waves: list[WaveResult]) -> None:
    figure, (trace_axis, sweep_axis) = plt.subplots(1, 2, figsize=(12, 4.5))
    _plot_traces(trace_axis, summary, waves)
    _plot_sweep(sweep_axis, summary)
    figure.tight_layout()
    figure.savefig(output / "travelling_wave_sweep.png", dpi=180)
    plt.close(figure)


def production_decay_lengths() -> FloatArray:
    """Sample the empirical band densely enough to place the boundary inside it."""
    return np.unique(
        np.concatenate(
            (
                np.geomspace(0.0125, 0.8, 8),
                np.linspace(0.10, 0.30, 9),
                [FERMI_LAM_MIN, 0.2, FERMI_LAM_MAX],
            )
        )
    )


def seed_control_lengths() -> FloatArray:
    """Sample the lengths that retain the twist under the published spread."""
    return np.asarray([FERMI_LAM_MIN, 0.125, 0.134590])


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="run a reduced deterministic sweep")
    parser.add_argument("--detuning", type=float, default=0.0, help="periodic detuning amplitude")
    parser.add_argument(
        "--frequency-sigma",
        type=float,
        default=0.0,
        help="quenched Gaussian frequency spread, in rad/s",
    )
    parser.add_argument(
        "--seeds",
        type=int,
        nargs="+",
        default=None,
        help="run the seed control over these seeds instead of the decay sweep",
    )
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument(
        "--replot",
        action="store_true",
        help="redraw the figures from saved artifacts, running no integration",
    )
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    fields = {
        "winding_q": 1,
        "detuning_rad_s": args.detuning,
        "frequency_sigma": args.frequency_sigma,
    }
    config = (
        WaveConfig(side=32, steps=2_000, sample_every=200, **fields)
        if args.smoke
        else WaveConfig(**fields)
    )
    default = DISORDERED_OUTPUT if args.frequency_sigma > 0.0 else PRODUCTION_OUTPUT
    output = args.output or default
    if args.replot:
        replot(output)
        print(f"redrew figures in {output} from saved artifacts")
        return
    if args.seeds:
        run_seed_control(config, seed_control_lengths(), args.seeds, output)
        return
    run_sweep(config, production_decay_lengths(), output)


if __name__ == "__main__":
    main()
