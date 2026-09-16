"""A fluctuating coupling, and which of its statistics controls coherence.

No coupling anywhere else in this repository fluctuates: every one is a constant
scalar, a linear deterministic ramp, or a deterministically updated matrix. The
threshold `K_c = 2D` is proved for a constant coupling, and using it for a
coupling that varies means substituting some statistic of `K(t)` for `K`. This
module asks which statistic that may be, on two declared noise processes.

**The processes.** Both have mean `mean_coupling`, stationary standard deviation
`amplitude` and correlation time `correlation_time`, and both are updated by
their exact stationary transition over a step, so the step size does not set the
correlation time:

* *telegraph* -- `K` takes the two values `mean +- amplitude`, switching with
  probability `(1 - exp(-dt / tau)) / 2` per step. Its excursions are of one
  size and it spends no time near its mean.
* *Ornstein--Uhlenbeck* -- `K` relaxes to the mean at rate `1/tau` under
  Gaussian noise, so its excursions are of every size and its tails are
  unbounded. Negative couplings are not clipped, because clipping would move the
  mean, which is the statistic under test; the fraction of time spent there is
  reported instead.

**The dynamics** are `quasistatic_error`'s mean-field harmonic ladder, driven
along a replica axis so that each replica carries its own `K(t)`. The observable
is the time average of `r` over the measurement window, averaged over replicas.

**The two candidate substitutions.**

* *mean coupling* -- `r_ss(mean)`, which is what using `K_c = 2D` on an averaged
  coupling asserts. It is exact when the coupling fluctuates faster than the
  phases relax, because the density then sees only the average drift.
* *quasi-static average* -- `E[r_ss(K)]` over the coupling's own stationary law,
  which is what the density tracks when the coupling fluctuates slowly.

`r_ss` is identically zero below threshold and leaves the axis with infinite
slope above it, so it is convex there: a subcritical mean with supercritical
excursions has `E[r_ss(K)] > 0 = r_ss(mean)`, and the two substitutions do not
merely differ in accuracy, they disagree about whether there is any order at
all. That disagreement is the rejection this module exists to retain.

**Scope.** A scalar coupling driven by a declared noise process, and nothing
else. No mechanism is offered for what would make a cortical coupling fluctuate,
no amplitude or correlation time is fitted to data, and no dynamical mean-field
limit is supplied: this is the mean-field equation already in use, driven.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import cast

import numpy as np
from numpy.typing import NDArray

from quasistatic_error import Propagator, advance, propagator, stationary_order, von_mises_harmonics
from quasistatic_error import concentration_for_order


FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
FIGURES = Path(__file__).resolve().parent / "figures"
PRODUCTION_OUTPUT = FIGURES / "fluctuating_coupling"

PROCESSES: tuple[str, ...] = ("telegraph", "ornstein_uhlenbeck")
AMPLITUDES: tuple[float, ...] = (0.25, 0.5, 1.0)
CORRELATION_TIMES: tuple[float, ...] = (0.03, 0.3, 3.0, 30.0)
MEAN_COUPLINGS: tuple[float, ...] = (1.4, 1.6, 1.8, 2.0, 2.2, 2.4, 2.6)

# Nodes and weights for `E[f(K)]` under a Gaussian coupling law.
_HERMITE_NODES = 41


@dataclass(frozen=True)
class NoiseConfig:
    """Declared numerical parameters. None of them is fitted to anything."""

    diffusion: float = 1.0
    n_harmonics: int = 20
    dt: float = 0.01
    replicas: int = 32
    seed_order: float = 0.02
    burn_fraction: float = 1.0 / 3.0
    horizon_factor: float = 60.0
    min_horizon: float = 100.0
    seed: int = 20260916

    @property
    def critical_coupling(self) -> float:
        """Return the identical-frequency threshold ``K_c = 2D``."""
        return 2.0 * self.diffusion


@dataclass(frozen=True)
class Drive:
    """One declared coupling process."""

    process: str
    mean: float
    amplitude: float
    correlation_time: float


@dataclass(frozen=True)
class DriveRun:
    """What one drive produced, against both candidate substitutions."""

    measured_order: float
    order_spread: float
    mean_substitution: float
    quasi_static_average: float
    negative_fraction: float
    horizon: float


def initial_coupling(drive: Drive, config: NoiseConfig, rng: np.random.Generator) -> FloatArray:
    """Draw the coupling from its own stationary law, so no burn-in is spent
    reaching it and the reported mean is the declared one."""
    if drive.process == "telegraph":
        signs = rng.choice((-1.0, 1.0), size=config.replicas)
        return np.asarray(drive.mean + drive.amplitude * signs, dtype=float)
    if drive.process == "ornstein_uhlenbeck":
        return np.asarray(
            drive.mean + drive.amplitude * rng.standard_normal(config.replicas), dtype=float
        )
    raise ValueError(f"Unknown coupling process: {drive.process}")


def step_coupling(
    coupling: FloatArray, drive: Drive, dt: float, rng: np.random.Generator
) -> FloatArray:
    """Advance the coupling by its exact stationary transition over `dt`."""
    relaxation = float(np.exp(-dt / drive.correlation_time))
    if drive.process == "telegraph":
        flip = rng.random(coupling.shape) < 0.5 * (1.0 - relaxation)
        signs = np.sign(coupling - drive.mean)
        return np.asarray(drive.mean + drive.amplitude * np.where(flip, -signs, signs), dtype=float)
    noise = drive.amplitude * np.sqrt(1.0 - relaxation**2) * rng.standard_normal(coupling.shape)
    return np.asarray(drive.mean + (coupling - drive.mean) * relaxation + noise, dtype=float)


def quasi_static_average(drive: Drive, diffusion: float) -> float:
    """Return `E[r_ss(K)]` under the coupling's own stationary law."""
    if drive.process == "telegraph":
        low = stationary_order(drive.mean - drive.amplitude, diffusion)
        high = stationary_order(drive.mean + drive.amplitude, diffusion)
        return 0.5 * (low + high)
    nodes, weights = np.polynomial.hermite.hermgauss(_HERMITE_NODES)
    couplings = drive.mean + np.sqrt(2.0) * drive.amplitude * nodes
    orders = np.array([stationary_order(float(value), diffusion) for value in couplings])
    return float(np.dot(weights, orders) / np.sqrt(np.pi))


def horizon(drive: Drive, config: NoiseConfig) -> float:
    """The measured window: many correlation times, and never shorter than the
    declared floor. It is a declared horizon, not a limit."""
    return max(config.min_horizon, config.horizon_factor * drive.correlation_time)


@dataclass(frozen=True)
class _Accumulator:
    harmonics: FloatArray
    coupling: FloatArray
    factors: Propagator


def _seeded(config: NoiseConfig, drive: Drive, rng: np.random.Generator) -> _Accumulator:
    seed = von_mises_harmonics(concentration_for_order(config.seed_order), config.n_harmonics)
    return _Accumulator(
        harmonics=np.tile(seed, (config.replicas, 1)),
        coupling=initial_coupling(drive, config, rng),
        factors=propagator(config.n_harmonics, config.diffusion, config.dt),
    )


def run_drive(drive: Drive, config: NoiseConfig, total_time: float | None = None) -> DriveRun:
    """Drive the mean-field equation with one declared coupling process."""
    window = horizon(drive, config) if total_time is None else total_time
    steps = max(int(round(window / config.dt)), 1)
    burn = int(round(config.burn_fraction * steps))
    rng = np.random.default_rng(config.seed)
    state = _seeded(config, drive, rng)
    coupling, harmonics = state.coupling, state.harmonics
    orders: list[FloatArray] = []
    negative = 0
    for index in range(steps):
        harmonics = advance(harmonics, coupling, state.factors)
        coupling = step_coupling(coupling, drive, config.dt, rng)
        if index >= burn:
            orders.append(harmonics[:, 0].copy())
            negative += int(np.count_nonzero(coupling < 0.0))
    sampled = np.asarray(orders)
    return DriveRun(
        measured_order=float(np.mean(sampled)),
        order_spread=float(np.std(np.mean(sampled, axis=0))),
        mean_substitution=stationary_order(drive.mean, config.diffusion),
        quasi_static_average=quasi_static_average(drive, config.diffusion),
        negative_fraction=float(negative) / float(sampled.size),
        horizon=window,
    )


def crosses_threshold(drive: Drive, config: NoiseConfig) -> bool:
    """Whether the coupling's declared excursion band spans the threshold. For
    the Gaussian process the band is two standard deviations, which is where the
    process spends the overwhelming majority of its time and not a support."""
    reach = drive.amplitude if drive.process == "telegraph" else 2.0 * drive.amplitude
    return drive.mean - reach < config.critical_coupling < drive.mean + reach


def _closer(run: DriveRun) -> str:
    mean_gap = abs(run.measured_order - run.mean_substitution)
    quasi_gap = abs(run.measured_order - run.quasi_static_average)
    return "quasi_static" if quasi_gap < mean_gap else "mean"


def _drive_payload(drive: Drive, run: DriveRun, config: NoiseConfig) -> dict[str, object]:
    return {
        **asdict(drive),
        **asdict(run),
        "crosses_threshold": crosses_threshold(drive, config),
        "closer": _closer(run),
        "self_averaging": run.order_spread <= 0.1 * run.measured_order,
        "visits_negative_coupling": run.negative_fraction > 0.0,
        "orders_below_mean_threshold": run.mean_substitution == 0.0
        and run.measured_order > config.seed_order,
    }


def build_drives() -> list[Drive]:
    """Every declared combination of process, amplitude, correlation time and
    mean coupling."""
    return [
        Drive(process, mean, amplitude, tau)
        for process in PROCESSES
        for amplitude in AMPLITUDES
        for tau in CORRELATION_TIMES
        for mean in MEAN_COUPLINGS
    ]


def _limit_gap(rows: list[dict[str, object]], key: str) -> float | None:
    gaps = [abs(cast(float, row["measured_order"]) - cast(float, row[key])) for row in rows]
    return max(gaps) if gaps else None


def _fast_limit(rows: list[dict[str, object]]) -> dict[str, object]:
    fastest = min(CORRELATION_TIMES)
    selected = [row for row in rows if row["correlation_time"] == fastest]
    return {
        "correlation_time": fastest,
        "worst_mean_substitution_gap": _limit_gap(selected, "mean_substitution"),
        "worst_quasi_static_gap": _limit_gap(selected, "quasi_static_average"),
    }


def _slow_limit(rows: list[dict[str, object]]) -> dict[str, object]:
    """The slow limit is read on the drives that never cross the threshold. A
    crossing drive collapses its order on every subcritical excursion and has to
    rebuild it, which is a third regime and not the quasi-static one."""
    slowest = max(CORRELATION_TIMES)
    selected = [
        row
        for row in rows
        if row["correlation_time"] == slowest and not cast(bool, row["crosses_threshold"])
    ]
    return {
        "correlation_time": slowest,
        "drives": len(selected),
        "worst_mean_substitution_gap": _limit_gap(selected, "mean_substitution"),
        "worst_quasi_static_gap": _limit_gap(selected, "quasi_static_average"),
    }


def _crossover(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    """The smallest correlation time at which the quasi-static average is the
    closer of the two substitutions, one entry per family."""
    families = sorted(
        {
            (cast(str, r["process"]), cast(float, r["amplitude"]), cast(float, r["mean"]))
            for r in rows
        }
    )
    entries: list[dict[str, object]] = []
    for process, amplitude, mean in families:
        taus = [
            cast(float, row["correlation_time"])
            for row in rows
            if (row["process"], row["amplitude"], row["mean"]) == (process, amplitude, mean)
            and row["closer"] == "quasi_static"
        ]
        entries.append(
            {
                "process": process,
                "amplitude": amplitude,
                "mean": mean,
                "crossover_correlation_time": min(taus) if taus else None,
            }
        )
    return entries


def _rejection(rows: list[dict[str, object]], config: NoiseConfig) -> dict[str, object]:
    ordering = [row for row in rows if row["orders_below_mean_threshold"]]
    strongest = max(ordering, key=lambda row: cast(float, row["measured_order"]), default=None)
    return {
        "criterion": "the mean coupling is at or below K_c, so r_ss(mean) is exactly zero, "
        f"and the measured mean order exceeds the seed {config.seed_order} the run started from",
        "count": len(ordering),
        "strongest": strongest,
        "rejected": bool(ordering),
    }


def _controls(rows: list[dict[str, object]], config: NoiseConfig) -> dict[str, object]:
    reference = Drive("telegraph", 2.4, 0.25, max(CORRELATION_TIMES))
    coarse = run_drive(reference, config)
    fine = run_drive(reference, NoiseConfig(**{**asdict(config), "dt": config.dt / 2.0}))
    rejection = cast(dict[str, object] | None, _rejection(rows, config)["strongest"])
    extended: dict[str, object] | None = None
    if rejection is not None:
        drive = Drive(
            cast(str, rejection["process"]),
            cast(float, rejection["mean"]),
            cast(float, rejection["amplitude"]),
            cast(float, rejection["correlation_time"]),
        )
        run = run_drive(drive, config, total_time=4.0 * horizon(drive, config))
        extended = {"horizon": run.horizon, "measured_order": run.measured_order}
    return {
        "step_halving": abs(coarse.measured_order - fine.measured_order),
        "step_halving_drive": asdict(reference),
        "extended_horizon": extended,
    }


def run_sweep(config: NoiseConfig, drives: list[Drive], output: Path) -> dict[str, object]:
    """Run every declared drive and write one summary."""
    rows = [_drive_payload(drive, run_drive(drive, config), config) for drive in drives]
    summary: dict[str, object] = {
        "source": "fluctuating_coupling.py",
        "config": asdict(config),
        "processes": list(PROCESSES),
        "amplitudes": list(AMPLITUDES),
        "correlation_times": list(CORRELATION_TIMES),
        "mean_couplings": list(MEAN_COUPLINGS),
        "drives": rows,
        "fast_limit": _fast_limit(rows),
        "slow_limit": _slow_limit(rows),
        "crossover": _crossover(rows),
        "mean_substitution_rejection": _rejection(rows, config),
        "controls": _controls(rows, config),
        "scope": "a scalar coupling driven by two declared noise processes; no cortical "
        "fluctuation mechanism, amplitude or correlation time is supplied",
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "fluctuating_coupling_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return summary


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="run a reduced deterministic sweep")
    parser.add_argument("--output", type=Path, default=None)
    return parser.parse_args()


def _smoke_drives() -> list[Drive]:
    """Both processes at both ends of the correlation-time range, and on both
    sides of the threshold, so the reduced run exercises every branch."""
    return [
        Drive(process, mean, amplitude, tau)
        for process in PROCESSES
        for amplitude in (0.25, 1.0)
        for tau in (min(CORRELATION_TIMES), max(CORRELATION_TIMES))
        for mean in (1.8, 2.4)
    ]


def main() -> None:
    args = _parse_args()
    config = (
        NoiseConfig(n_harmonics=10, replicas=4, min_horizon=20.0, horizon_factor=10.0)
        if args.smoke
        else NoiseConfig()
    )
    drives = _smoke_drives() if args.smoke else build_drives()
    summary = run_sweep(config, drives, args.output or PRODUCTION_OUTPUT)
    print(f"fast limit: {summary['fast_limit']}")
    print(f"slow limit: {summary['slow_limit']}")
    rejection = cast(dict[str, object], summary["mean_substitution_rejection"])
    print(f"mean substitution rejected: {rejection['rejected']} in {rejection['count']} drives")
    print("scope: a declared scalar noise process; no cortical fluctuation mechanism is supplied")


if __name__ == "__main__":
    main()
