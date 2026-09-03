"""Finite-N simulation of a noisy Kuramoto system under a linear coupling ramp.

This supplies heuristic numerical evidence about bifurcation delay. It proves no
trajectory theorem and does not discharge the manuscript's adiabatic assumption.
Natural frequencies are identically zero because the comparison target is the
identical-frequency von Mises stationary curve with critical coupling ``2D``.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import numpy as np
from numpy.typing import NDArray


FloatArray = NDArray[np.float64]


@dataclass(frozen=True)
class RampConfig:
    """Numerical parameters for an ensemble of independent ramp trajectories."""

    n_oscillators: int = 256
    n_replicas: int = 4
    diffusion: float = 1.0
    ramp_speed: float = 0.1
    coupling_half_window: float = 0.5
    dt: float = 0.01
    sample_every: int = 10
    concentration_bins: int = 36
    seed: int = 20260903

    @property
    def critical_coupling(self) -> float:
        """Return the identical-frequency threshold ``K_c = 2D``."""
        return 2.0 * self.diffusion


@dataclass(frozen=True)
class RampResult:
    """Decimated ensemble summaries; no phase histories are retained."""

    time: FloatArray
    coupling: FloatArray
    order_mean: FloatArray
    order_std: FloatArray
    concentration_mean: FloatArray
    steps: int
    phase_snapshots: int = 0


def _validate_config(config: RampConfig) -> None:
    positive = (
        config.n_oscillators,
        config.n_replicas,
        config.diffusion,
        config.ramp_speed,
        config.coupling_half_window,
        config.dt,
        config.sample_every,
        config.concentration_bins,
    )
    if any(value <= 0 for value in positive):
        raise ValueError("all ramp configuration scales must be positive")


def estimate_log_density_concentration(phases: FloatArray, bins: int = 36) -> float:
    """Estimate von Mises concentration from an unweighted log-density slope.

    The phase centre is the circular mean. Regressing histogram log counts on
    ``cos(theta - psi)`` uses distribution shape rather than inverting the
    observed resultant length, avoiding a tautological collapse test.
    """
    if bins < 3:
        raise ValueError("at least three phase bins are required")
    centre = float(np.angle(np.mean(np.exp(1j * phases))))
    counts, edges = np.histogram(phases, bins=bins, range=(-np.pi, np.pi))
    midpoints = 0.5 * (edges[:-1] + edges[1:])
    predictor = np.cos(midpoints - centre)
    response = np.log(counts.astype(float) + 0.5)
    centred_predictor = predictor - np.mean(predictor)
    centred_response = response - np.mean(response)
    denominator = float(np.dot(centred_predictor, centred_predictor))
    return float(np.dot(centred_predictor, centred_response) / denominator)


def _summarize(phases: FloatArray, bins: int) -> tuple[float, float, float]:
    complex_order = np.mean(np.exp(1j * phases), axis=1)
    order = np.abs(complex_order)
    concentration = np.array(
        [estimate_log_density_concentration(replica, bins) for replica in phases],
        dtype=float,
    )
    return float(np.mean(order)), float(np.std(order)), float(np.mean(concentration))


def _sample_steps(steps: int, sample_every: int) -> list[int]:
    sampled = list(range(0, steps + 1, sample_every))
    if sampled[-1] != steps:
        sampled.append(steps)
    return sampled


def simulate_ramp(config: RampConfig) -> RampResult:
    """Integrate the ensemble by Euler-Maruyama and retain decimated summaries."""
    _validate_config(config)
    duration = 2.0 * config.coupling_half_window / config.ramp_speed
    steps = int(round(duration / config.dt))
    if not np.isclose(steps * config.dt, duration):
        raise ValueError("ramp duration must be an integer multiple of dt")

    sampled_steps = _sample_steps(steps, config.sample_every)
    sampled_lookup = set(sampled_steps)
    rng = np.random.default_rng(config.seed)
    phases = rng.uniform(-np.pi, np.pi, (config.n_replicas, config.n_oscillators))
    noise_scale = np.sqrt(2.0 * config.diffusion * config.dt)
    coupling_start = config.critical_coupling - config.coupling_half_window

    times: list[float] = []
    coupling_values: list[float] = []
    order_means: list[float] = []
    order_stds: list[float] = []
    concentrations: list[float] = []

    for step in range(steps + 1):
        time = step * config.dt
        coupling = coupling_start + config.ramp_speed * time
        if step in sampled_lookup:
            order_mean, order_std, concentration = _summarize(phases, config.concentration_bins)
            times.append(time)
            coupling_values.append(coupling)
            order_means.append(order_mean)
            order_stds.append(order_std)
            concentrations.append(concentration)
        if step == steps:
            continue
        complex_order = np.mean(np.exp(1j * phases), axis=1)
        order = np.abs(complex_order)[:, None]
        mean_phase = np.angle(complex_order)[:, None]
        drift = coupling * order * np.sin(mean_phase - phases)
        phases += config.dt * drift + noise_scale * rng.standard_normal(phases.shape)
        phases = (phases + np.pi) % (2.0 * np.pi) - np.pi

    return RampResult(
        time=np.asarray(times),
        coupling=np.asarray(coupling_values),
        order_mean=np.asarray(order_means),
        order_std=np.asarray(order_stds),
        concentration_mean=np.asarray(concentrations),
        steps=steps,
    )


def detect_escape_coupling(
    coupling: FloatArray,
    order: FloatArray,
    n_oscillators: int,
    floor_multiple: float = 2.0,
    critical_coupling: float = 2.0,
) -> float | None:
    """Return the first post-critical coupling above a multiple of ``1/sqrt(N)``."""
    threshold = floor_multiple / np.sqrt(n_oscillators)
    crossings = np.flatnonzero((coupling >= critical_coupling) & (order > threshold))
    return None if len(crossings) == 0 else float(coupling[crossings[0]])


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260903)
    return parser.parse_args()


def main() -> None:
    """Run the reduced deterministic smoke configuration."""
    args = _parse_args()
    config = RampConfig(seed=args.seed)
    result = simulate_ramp(config)
    escape = detect_escape_coupling(
        result.coupling,
        result.order_mean,
        config.n_oscillators,
        critical_coupling=config.critical_coupling,
    )
    print(
        f"smoke seed={config.seed} steps={result.steps} samples={len(result.time)} "
        f"escape_K={escape} final_r={result.order_mean[-1]:.4f}"
    )


if __name__ == "__main__":
    main()
