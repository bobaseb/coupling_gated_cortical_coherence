"""Finite-N simulation of a noisy Kuramoto system under a linear coupling ramp.

This supplies heuristic numerical evidence about bifurcation delay. It proves no
trajectory theorem and does not discharge the manuscript's adiabatic assumption.
The default has identical natural frequencies for comparison with the von Mises
stationary curve. A quenched Lorentzian spread is available as a separate control.
"""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

import numpy as np
from numpy.typing import NDArray


FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
FIGURES = Path(__file__).resolve().parent / "figures"


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
    frequency_halfwidth: float = 0.0

    @property
    def critical_coupling(self) -> float:
        """Return the threshold ``K_c = 2(D + gamma)``."""
        return 2.0 * (self.diffusion + self.frequency_halfwidth)


@dataclass(frozen=True)
class RampResult:
    """Decimated ensemble summaries; no phase histories are retained."""

    time: FloatArray
    coupling: FloatArray
    order_mean: FloatArray
    order_std: FloatArray
    concentration_mean: FloatArray
    order_replicas: FloatArray
    concentration_replicas: FloatArray
    steps: int
    phase_snapshots: int = 0


@dataclass
class _RampState:
    phases: FloatArray
    rng: np.random.Generator
    step: int = 0
    natural_frequencies: FloatArray | None = None
    times: list[float] = field(default_factory=list)
    couplings: list[float] = field(default_factory=list)
    order_means: list[float] = field(default_factory=list)
    order_stds: list[float] = field(default_factory=list)
    concentrations: list[float] = field(default_factory=list)
    order_replicas: list[FloatArray] = field(default_factory=list)
    concentration_replicas: list[FloatArray] = field(default_factory=list)


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
    if not np.isfinite(config.frequency_halfwidth) or config.frequency_halfwidth < 0:
        raise ValueError("frequency half-width must be finite and non-negative")


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


def _summarize(phases: FloatArray, bins: int) -> tuple[FloatArray, FloatArray]:
    complex_order = np.mean(np.exp(1j * phases), axis=1)
    order = np.abs(complex_order)
    concentration = np.array(
        [estimate_log_density_concentration(replica, bins) for replica in phases],
        dtype=float,
    )
    return order, concentration


def _sample_steps(steps: int, sample_every: int) -> list[int]:
    sampled = list(range(0, steps + 1, sample_every))
    if sampled[-1] != steps:
        sampled.append(steps)
    return sampled


def _total_steps(config: RampConfig) -> int:
    duration = 2.0 * config.coupling_half_window / config.ramp_speed
    steps = int(round(duration / config.dt))
    if not np.isclose(steps * config.dt, duration):
        raise ValueError("ramp duration must be an integer multiple of dt")
    return steps


def _new_state(config: RampConfig) -> _RampState:
    rng = np.random.default_rng(config.seed)
    phases = rng.uniform(-np.pi, np.pi, (config.n_replicas, config.n_oscillators))
    if config.frequency_halfwidth > 0.0:
        natural_frequencies = (
            rng.standard_cauchy((config.n_replicas, config.n_oscillators))
            * config.frequency_halfwidth
        )
    else:
        natural_frequencies = None
    return _RampState(phases=phases, rng=rng, natural_frequencies=natural_frequencies)


def _record(state: _RampState, config: RampConfig) -> None:
    time = state.step * config.dt
    coupling = config.critical_coupling - config.coupling_half_window + config.ramp_speed * time
    order, concentration = _summarize(state.phases, config.concentration_bins)
    state.times.append(time)
    state.couplings.append(coupling)
    state.order_means.append(float(np.mean(order)))
    state.order_stds.append(float(np.std(order)))
    state.concentrations.append(float(np.mean(concentration)))
    state.order_replicas.append(order)
    state.concentration_replicas.append(concentration)


def _advance(state: _RampState, config: RampConfig) -> None:
    time = state.step * config.dt
    coupling = config.critical_coupling - config.coupling_half_window + config.ramp_speed * time
    complex_order = np.mean(np.exp(1j * state.phases), axis=1)
    order = np.abs(complex_order)[:, None]
    mean_phase = np.angle(complex_order)[:, None]
    drift = coupling * order * np.sin(mean_phase - state.phases)
    if state.natural_frequencies is not None:
        drift += state.natural_frequencies
    noise_scale = np.sqrt(2.0 * config.diffusion * config.dt)
    state.phases += config.dt * drift + noise_scale * state.rng.standard_normal(state.phases.shape)
    state.phases = (state.phases + np.pi) % (2.0 * np.pi) - np.pi
    state.step += 1


def _to_result(state: _RampState, steps: int) -> RampResult:
    return RampResult(
        time=np.asarray(state.times),
        coupling=np.asarray(state.couplings),
        order_mean=np.asarray(state.order_means),
        order_std=np.asarray(state.order_stds),
        concentration_mean=np.asarray(state.concentrations),
        order_replicas=np.asarray(state.order_replicas),
        concentration_replicas=np.asarray(state.concentration_replicas),
        steps=steps,
    )


def _config_json(config: RampConfig) -> str:
    values = asdict(config)
    if config.frequency_halfwidth == 0.0:
        # Existing identical-frequency checkpoints predate this control.
        values.pop("frequency_halfwidth")
    return json.dumps(values, sort_keys=True)


def _save_checkpoint(path: Path, config: RampConfig, state: _RampState) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, suffix=".npz", delete=False) as temporary:
        temporary_path = Path(temporary.name)
        kwargs: dict[str, Any] = dict(
            config=np.asarray(_config_json(config)),
            rng_state=np.asarray(json.dumps(state.rng.bit_generator.state)),
            step=np.asarray(state.step),
            phases=state.phases,
            time=np.asarray(state.times),
            coupling=np.asarray(state.couplings),
            order_mean=np.asarray(state.order_means),
            order_std=np.asarray(state.order_stds),
            concentration_mean=np.asarray(state.concentrations),
            order_replicas=np.asarray(state.order_replicas),
            concentration_replicas=np.asarray(state.concentration_replicas),
        )
        if state.natural_frequencies is not None:
            kwargs["natural_frequencies"] = state.natural_frequencies
        np.savez_compressed(temporary, **kwargs)
    os.replace(temporary_path, path)


def _load_checkpoint(path: Path, config: RampConfig) -> _RampState:
    with np.load(path, allow_pickle=False) as saved:
        saved_config = str(saved["config"])
        if saved_config != _config_json(config):
            raise ValueError("checkpoint configuration does not match requested ramp")
        rng = np.random.default_rng()
        rng_state: dict[str, Any] = json.loads(str(saved["rng_state"]))
        rng.bit_generator.state = rng_state
        natural_frequencies = None
        if "natural_frequencies" in saved:
            natural_frequencies = np.asarray(saved["natural_frequencies"])
        return _RampState(
            phases=np.asarray(saved["phases"]),
            rng=rng,
            step=int(saved["step"]),
            natural_frequencies=natural_frequencies,
            times=np.asarray(saved["time"]).tolist(),
            couplings=np.asarray(saved["coupling"]).tolist(),
            order_means=np.asarray(saved["order_mean"]).tolist(),
            order_stds=np.asarray(saved["order_std"]).tolist(),
            concentrations=np.asarray(saved["concentration_mean"]).tolist(),
            order_replicas=list(np.asarray(saved["order_replicas"])),
            concentration_replicas=list(np.asarray(saved["concentration_replicas"])),
        )


def _record_if_due(state: _RampState, config: RampConfig, sampled_lookup: set[int]) -> None:
    time = state.step * config.dt
    already_recorded = bool(state.times) and state.times[-1] == time
    if state.step in sampled_lookup and not already_recorded:
        _record(state, config)


def _checkpoint_if_due(
    state: _RampState,
    config: RampConfig,
    checkpoint: Path | None,
    checkpoint_every: int,
    steps: int,
    report_progress: bool,
) -> None:
    if checkpoint is None or state.step % checkpoint_every != 0:
        return
    _save_checkpoint(checkpoint, config, state)
    if report_progress:
        percent = 100.0 * state.step / steps
        print(f"checkpoint step={state.step}/{steps} ({percent:.1f}%)", flush=True)


def _finish_run(
    state: _RampState, config: RampConfig, checkpoint: Path | None, steps: int
) -> RampResult:
    if checkpoint is not None:
        _save_checkpoint(checkpoint, config, state)
    return _to_result(state, steps)


def _run(
    config: RampConfig,
    state: _RampState,
    checkpoint: Path | None = None,
    checkpoint_every: int = 0,
    max_steps: int | None = None,
    report_progress: bool = False,
) -> RampResult | None:
    steps = _total_steps(config)
    sampled_lookup = set(_sample_steps(steps, config.sample_every))
    stop_step = steps if max_steps is None else min(max_steps, steps)
    while state.step <= stop_step:
        _record_if_due(state, config, sampled_lookup)
        if state.step == steps:
            return _finish_run(state, config, checkpoint, steps)
        if state.step == stop_step:
            break
        _advance(state, config)
        _checkpoint_if_due(state, config, checkpoint, checkpoint_every, steps, report_progress)
    if checkpoint is not None:
        _save_checkpoint(checkpoint, config, state)
    return None


def simulate_ramp(config: RampConfig) -> RampResult:
    """Integrate the ensemble by Euler-Maruyama and retain decimated summaries."""
    _validate_config(config)
    result = _run(config, _new_state(config))
    if result is None:
        raise RuntimeError("uncheckpointed ramp stopped before completion")
    return result


def run_checkpointed(
    config: RampConfig,
    checkpoint: Path,
    checkpoint_every: int,
    max_steps: int | None = None,
    report_progress: bool = False,
) -> RampResult | None:
    """Run or resume one ramp leg, atomically saving its current state."""
    _validate_config(config)
    if checkpoint_every <= 0:
        raise ValueError("checkpoint_every must be positive")
    state = _load_checkpoint(checkpoint, config) if checkpoint.exists() else _new_state(config)
    return _run(config, state, checkpoint, checkpoint_every, max_steps, report_progress)


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


def production_config(speed: float, seed: int, n_oscillators: int = 2000) -> RampConfig:
    """Build the prescribed production configuration with useful decimation."""
    steps = int(round(1.0 / (speed * 0.01)))
    sample_every = max(1, min(1000, steps // 100))
    return RampConfig(
        n_oscillators=n_oscillators,
        n_replicas=32,
        diffusion=1.0,
        ramp_speed=speed,
        coupling_half_window=0.5,
        dt=0.01,
        sample_every=sample_every,
        concentration_bins=36,
        seed=seed,
    )


def production_config_heterogeneous(
    speed: float, seed: int, frequency_halfwidth: float, n_oscillators: int = 2000
) -> RampConfig:
    """Build a heterogeneous production configuration with useful decimation."""
    steps = int(round(1.0 / (speed * 0.01)))
    sample_every = max(1, min(1000, steps // 100))
    return RampConfig(
        n_oscillators=n_oscillators,
        n_replicas=32,
        diffusion=1.0,
        ramp_speed=speed,
        coupling_half_window=0.5,
        dt=0.01,
        sample_every=sample_every,
        concentration_bins=36,
        seed=seed,
        frequency_halfwidth=frequency_halfwidth,
    )


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260903)
    parser.add_argument("--speed", type=float)
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument("--n-oscillators", type=int, default=2000)
    return parser.parse_args()


def main() -> None:
    """Run the smoke configuration or one checkpointed production-speed leg."""
    args = _parse_args()
    if args.speed is None:
        config = RampConfig(seed=args.seed)
        result = simulate_ramp(config)
    else:
        config = production_config(args.speed, args.seed, args.n_oscillators)
        checkpoint = args.checkpoint
        if checkpoint is None:
            checkpoint = FIGURES / f"dynamic_ramp_v{args.speed:.0e}.npz"
        checkpoint_result = run_checkpointed(
            config,
            checkpoint,
            checkpoint_every=5000,
            report_progress=True,
        )
        if checkpoint_result is None:
            raise RuntimeError("production ramp stopped before completion")
        result = checkpoint_result
    escape = detect_escape_coupling(
        result.coupling,
        result.order_mean,
        config.n_oscillators,
        critical_coupling=config.critical_coupling,
    )
    mode = "smoke" if args.speed is None else f"production v={config.ramp_speed:g}"
    print(
        f"{mode} seed={config.seed} steps={result.steps} samples={len(result.time)} "
        f"escape_K={escape} final_r={result.order_mean[-1]:.4f}"
    )


if __name__ == "__main__":
    main()
