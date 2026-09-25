"""How phase agreement between two sites of a noisy sheet decays with distance (U3).

At identical natural frequencies the sheet ``dθ_i = Σ_j K_ij sin(θ_j − θ_i) dt +
sqrt(2D) dW_i`` is a gradient system, and in the harmonic approximation its
stationary phase differences are Gaussian with ``Var(θ_a − θ_b) = D·R_eff(a, b)``,
where ``R_eff`` is the effective resistance of the network whose conductances are
the couplings ``K_ij``. The resistance is exact and cheap on a torus; the
simulation measures how far the nonlinear, finite-time sheet follows it.

The question the run answers is the one the physical-unity outline gates on:
whether discrepancy grows with the logarithm of distance under short-range
coupling, and whether a kernel tail slower than ``r^-4`` makes it distance
independent. Kernels share one row sum, so only their shape differs.

Scope: finite sheets, finite time, identical frequencies. No theorem, and no
biological measurement.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, cast

import matplotlib.pyplot as plt
from matplotlib.axes import Axes
import numpy as np
from numpy.typing import NDArray

from spatial_kernel import build_kernel, coupling_drift

FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_agreement"

# Exponential decay length in lattice spacings: short range, but not nearest.
EXPONENTIAL_DECAY = 2.0
KERNEL_SHAPES = ("nearest", "exponential", "power_sigma1", "power_sigma3")
# Sheet sides for the resistance scaling, beyond what the simulation reaches.
SCALING_SIDES = (128, 512, 1024)


@dataclass(frozen=True)
class SheetConfig:
    """One identical-frequency trajectory, started from the synchronized state."""

    side: int = 64
    coupling: float = 4.0
    noise: float = 0.1
    dt: float = 0.05
    burn_in: int = 2_000
    steps: int = 10_000
    sample_every: int = 10
    seed: int = 20260925


@dataclass(frozen=True)
class SheetResult:
    """Time- and site-averaged discrepancy at each axial separation ``0..side//2``."""

    variance: FloatArray
    discrepancy: FloatArray
    runtime_seconds: float


@dataclass(frozen=True)
class GrowthFit:
    """Least-squares fits ``a + b·ln d`` and ``a + c·d``, and which fits better."""

    log_slope: float
    linear_slope: float
    log_rss: float
    linear_rss: float
    better: str


def _torus_distance(side: int) -> FloatArray:
    coordinate = np.arange(side)
    periodic = np.minimum(coordinate, side - coordinate).astype(float)
    return cast(FloatArray, np.hypot(periodic[:, None], periodic[None, :]))


def _power_kernel(side: int, sigma: float, coupling: float) -> FloatArray:
    distance = _torus_distance(side)
    distance[0, 0] = np.inf
    weights = distance ** -(2.0 + sigma)
    normalized: FloatArray = coupling * weights / np.sum(weights)
    return normalized


def _nearest_kernel(side: int, coupling: float) -> FloatArray:
    kernel = np.zeros((side, side))
    kernel[0, 1] = kernel[1, 0] = kernel[0, -1] = kernel[-1, 0] = coupling / 4.0
    return kernel


def build_shape_kernel(shape: str, side: int, coupling: float) -> FloatArray:
    """Return a displacement-array kernel of the named shape with row sum ``coupling``."""
    if shape == "nearest":
        return _nearest_kernel(side, coupling)
    if shape == "exponential":
        return build_kernel(side, EXPONENTIAL_DECAY, coupling)
    if shape == "power_sigma1":
        return _power_kernel(side, 1.0, coupling)
    if shape == "power_sigma3":
        return _power_kernel(side, 3.0, coupling)
    raise ValueError(f"unknown kernel shape {shape!r}; expected one of {KERNEL_SHAPES}")


def effective_resistance(kernel: FloatArray) -> FloatArray:
    """Resistance between site (0, 0) and (0, d) for ``d = 0..side//2``, by Fourier sum.

    The coupling Laplacian of a translation-invariant kernel is diagonal in
    Fourier space with eigenvalue ``λ(k) = Σ_r K(r)(1 − cos k·r)``, so
    ``R(0, r) = (1/N) Σ_{k≠0} (2 − 2 cos k·r) / λ(k)``.
    """
    eigenvalue = float(np.sum(kernel)) - np.real(np.fft.fft2(kernel))
    inverse = np.zeros_like(eigenvalue)
    nonzero = np.ones(eigenvalue.shape, dtype=bool)
    nonzero[0, 0] = False
    inverse[nonzero] = 1.0 / eigenvalue[nonzero]
    green = np.real(np.fft.ifft2(inverse))
    return cast(FloatArray, 2.0 * (green[0, 0] - green[0, : kernel.shape[0] // 2 + 1]))


def stiffness(kernel: FloatArray) -> float:
    """Half the kernel's second moment along one axis, ``½ Σ_r K(r) x_r²``.

    The coefficient of the short-range logarithm is ``1/(π s)``; a tail slower
    than ``r^-4`` has a second moment that grows without bound with the sheet.
    """
    coordinate = np.arange(kernel.shape[1])
    axial = np.minimum(coordinate, kernel.shape[1] - coordinate).astype(float)
    return float(0.5 * np.sum(kernel * axial[None, :] ** 2))


def resistance_scaling(sides: tuple[int, ...], coupling: float) -> dict[str, Any]:
    """Resistance at half the side for every shape and side, and each shape's stiffness.

    Exact Fourier sums, no integration: this is how the kernels differ at sheet
    sizes the simulation cannot reach. Stiffness is read at the largest side.
    """
    far = {
        shape: [
            float(effective_resistance(build_shape_kernel(shape, side, coupling))[side // 2])
            for side in sides
        ]
        for shape in KERNEL_SHAPES
    }
    return {
        "sides": list(sides),
        "coupling": coupling,
        "far_resistance": far,
        "stiffness": {
            shape: stiffness(build_shape_kernel(shape, max(sides), coupling))
            for shape in KERNEL_SHAPES
        },
    }


def _axial_moments(phases: FloatArray, half: int) -> tuple[FloatArray, FloatArray]:
    """Mean squared and chord discrepancy at each axial separation, both axes pooled."""
    squared = np.empty(half + 1)
    chord = np.empty(half + 1)
    for separation in range(half + 1):
        difference = np.concatenate(
            (
                (phases - np.roll(phases, separation, axis=0)).ravel(),
                (phases - np.roll(phases, separation, axis=1)).ravel(),
            )
        )
        squared[separation] = np.mean(difference**2)
        chord[separation] = np.mean(1.0 - np.cos(difference))
    return squared, chord


def simulate_sheet(shape: str, config: SheetConfig) -> SheetResult:
    """Integrate one Euler--Maruyama trajectory; phases are left unwrapped."""
    rng = np.random.default_rng(config.seed)
    kernel_fft = np.fft.fft2(build_shape_kernel(shape, config.side, config.coupling))
    phases = np.zeros((config.side, config.side))
    noise_scale = np.sqrt(2.0 * config.noise * config.dt)
    half = config.side // 2
    squared_sum = np.zeros(half + 1)
    chord_sum = np.zeros(half + 1)
    samples = 0
    started = time.monotonic()
    for step in range(config.burn_in + config.steps):
        phases += config.dt * coupling_drift(phases, kernel_fft)
        phases += noise_scale * rng.standard_normal(phases.shape)
        if step >= config.burn_in and (step - config.burn_in) % config.sample_every == 0:
            squared, chord = _axial_moments(phases, half)
            squared_sum += squared
            chord_sum += chord
            samples += 1
    return SheetResult(
        variance=squared_sum / samples,
        discrepancy=chord_sum / samples,
        runtime_seconds=time.monotonic() - started,
    )


def _rss(design: FloatArray, values: FloatArray) -> tuple[float, float]:
    coefficients, *_ = np.linalg.lstsq(design, values, rcond=None)
    residual = values - design @ coefficients
    return float(coefficients[1]), float(residual @ residual)


def growth_fit(distance: FloatArray, values: FloatArray) -> GrowthFit:
    """Compare logarithmic and linear growth of ``values`` over ``distance``."""
    ones = np.ones_like(distance)
    log_slope, log_rss = _rss(np.column_stack((ones, np.log(distance))), values)
    linear_slope, linear_rss = _rss(np.column_stack((ones, distance)), values)
    better = "logarithmic" if log_rss <= linear_rss else "linear"
    return GrowthFit(log_slope, linear_slope, log_rss, linear_rss, better)


def _run_record(shape: str, config: SheetConfig) -> dict[str, object]:
    result = simulate_sheet(shape, config)
    predicted = config.noise * effective_resistance(
        build_shape_kernel(shape, config.side, config.coupling)
    )
    fit_range = np.arange(2, config.side // 4 + 1)
    fit = growth_fit(fit_range.astype(float), result.variance[fit_range])
    return {
        "shape": shape,
        "config": asdict(config),
        "variance": result.variance.tolist(),
        "discrepancy": result.discrepancy.tolist(),
        "harmonic_variance": predicted.tolist(),
        # The growth fit reads unwrapped phase differences, which stop meaning
        # anything once phase slips occur; this ratio says whether they have.
        "harmonic_ratio_max": float(np.max(result.variance[1:] / predicted[1:])),
        "fit_distance": [int(fit_range[0]), int(fit_range[-1])],
        "fit": asdict(fit),
        "runtime_seconds": result.runtime_seconds,
    }


def production_configs(smoke: bool) -> list[SheetConfig]:
    """Two sheet sizes, and noise below, near and above the short-range BKT point.

    With four neighbours of bond ``K/4`` the nearest-neighbour sheet is the XY
    model at temperature ``D`` and bond ``K/4``, whose BKT point is near
    ``0.89·K/4 ≈ 0.9`` at ``K = 4``.
    """
    if smoke:
        return [SheetConfig(side=16, burn_in=50, steps=200)]
    base = SheetConfig()
    return [
        replace(base, side=side, noise=noise) for side in (64, 128) for noise in (0.1, 0.4, 1.2)
    ]


def run(configs: list[SheetConfig], output: Path) -> dict[str, object]:
    """Run every shape at every configuration and save the compact summary."""
    output.mkdir(parents=True, exist_ok=True)
    records = [_run_record(shape, config) for config in configs for shape in KERNEL_SHAPES]
    summary: dict[str, object] = {
        "runs": records,
        "scope": "finite sheets, identical frequencies; no theorem or biological measurement",
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def _plot_panel(axis: Axes, records: list[dict[str, Any]], chord: bool) -> None:
    """One noise level: measured discrepancy solid, harmonic prediction dotted.

    The chord prediction is ``1 − exp(−D·R_eff/2)``, the Gaussian value of
    ``⟨1 − cos Δθ⟩``; unlike the unwrapped variance it stays meaningful after
    phase slips, which is what the high-noise column shows.
    """
    for record in records:
        distance = np.arange(len(record["variance"]))[1:]
        harmonic = np.asarray(record["harmonic_variance"][1:])
        measured = record["discrepancy" if chord else "variance"][1:]
        (line,) = axis.semilogx(distance, measured, label=str(record["label"]))
        predicted = 1.0 - np.exp(-harmonic / 2.0) if chord else harmonic
        axis.semilogx(distance, predicted, ":", color=line.get_color())
    ylabel = (
        r"$\langle 1-\cos(\theta_a-\theta_b)\rangle$"
        if chord
        else r"$\langle(\theta_a-\theta_b)^2\rangle$"
    )
    axis.set(xlabel="separation (sites)", ylabel=ylabel)


def plot(output: Path) -> None:
    """Draw discrepancy against distance from the saved summary, integrating nothing."""
    runs = json.loads((output / "summary.json").read_text(encoding="utf-8"))["runs"]
    for record in runs:
        record["label"] = f"{record['shape']}, N={record['config']['side']}²"
    noises = sorted({run["config"]["noise"] for run in runs})
    figure, axes = plt.subplots(2, len(noises), figsize=(4.4 * len(noises), 7.2), squeeze=False)
    for column, noise in enumerate(noises):
        records = [r for r in runs if r["config"]["noise"] == noise]
        _plot_panel(axes[0, column], records, chord=False)
        _plot_panel(axes[1, column], records, chord=True)
        axes[0, column].set_title(f"D = {noise} (dotted: harmonic, D·R_eff)")
    axes[0, 0].legend(fontsize=6)
    figure.tight_layout()
    figure.savefig(output / "unity_agreement.png", dpi=160)
    plt.close(figure)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="U3: phase agreement against distance")
    parser.add_argument("--smoke", action="store_true", help="one small, short run")
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument(
        "--resistance",
        action="store_true",
        help="save the far resistance at large sheet sizes, integrating nothing",
    )
    parser.add_argument(
        "--replot", action="store_true", help="redraw from the saved summary, integrating nothing"
    )
    return parser.parse_args()


def main() -> None:
    """Run the sweep (or redraw it) and print each run's growth classification."""
    args = _parse_args()
    output = args.output or (OUTPUT.with_name("unity_agreement_smoke") if args.smoke else OUTPUT)
    if args.resistance:
        output.mkdir(parents=True, exist_ok=True)
        scaling = resistance_scaling(SCALING_SIDES, SheetConfig().coupling)
        (output / "resistance.json").write_text(json.dumps(scaling, indent=2) + "\n")
        return
    if not args.replot:
        summary = cast(list[dict[str, object]], run(production_configs(args.smoke), output)["runs"])
        for record in summary:
            config = cast(dict[str, object], record["config"])
            fit = cast(dict[str, object], record["fit"])
            print(
                f"{record['shape']:>13} N={config['side']} D={config['noise']}: "
                f"{fit['better']}, max variance / harmonic {record['harmonic_ratio_max']:.2f}"
            )
    plot(output)


if __name__ == "__main__":
    main()
