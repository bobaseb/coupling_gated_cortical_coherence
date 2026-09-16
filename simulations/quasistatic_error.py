"""The error of the quasi-static reduction, as a function of rate.

`Phase8` proves a *stationary* statement: at a fixed scalar coupling `K` the
self-consistent order parameter is `r_ss(K)`, zero at or below `K_c = 2D` and on
a unique coherent branch above it. Every use of that result for a coupling that
moves assumes the density tracks `r_ss(K(t))`, and `main.tex` motivates the
assumption with the words "coupling that evolves more slowly than phase
dynamics". Nothing in this repository says what "more slowly" has to mean, and
no module computes the residual `r(t) - r_ss(K(t))` at all.

This module measures it.

**The dynamics.** The mean-field Fokker--Planck equation for identical natural
frequencies, in the frame where the mean direction is zero, is

    d rho / dt = - d/dtheta [ K r sin(-theta) rho ] + D d^2 rho / dtheta^2 ,

with `r` the first harmonic of `rho`. In Fourier coordinates `h_k = <e^{-ik
theta}>`, with `h_0 = 1` and `r = h_1`, that is the closed system

    dh_k/dt = - D k^2 h_k + (K r k / 2) (h_{k-1} - h_{k+1}) ,

truncated at `n_harmonics`. This is a deterministic equation, so the residual it
measures is the error of the *reduction* and not a finite-population
fluctuation: `dynamic_ramp.py` measures the second, at finite `N`, and cannot
separate the two. There is no shared integrator in this repository, and this one
is written here rather than imported from `dynamic_ramp`, whose `_advance` is a
finite-`N` Langevin step on phases.

**The protocol.** Every leg starts at the stationary density for its initial
coupling, displaced by a declared `start_offset` in `r`, and ramps `K` linearly
at a declared speed. The displacement is what makes a subcritical leg carry any
information at all: below threshold `r_ss` is identically zero and the uniform
density solves the time-dependent equation exactly, so a leg started exactly on
the branch has zero residual at every rate, and the question below threshold is
how fast a departure decays rather than how well a moving branch is tracked.
Above threshold the residual is both: the decayed displacement and the lag.

**The criterion.** For each leg the reported number is the terminal residual
`|r(T) - r_ss(K(T))|`, and the *admissible speed* is the largest scanned speed
at which that residual stays under `tolerance`. Legs are indexed by their
distance `delta` from `K_c` -- for a subcritical leg the distance of its upper
end, for a supercritical leg the distance of its lower end -- so the admissible
speed is a function of distance from threshold, and its collapse as `delta -> 0`
is the quantity the manuscript sentence needs.

**What this is not.** No cortical coupling trajectory is calibrated, and a rate
that cortex is claimed to satisfy is not among the outputs. The comparison in
`REPORT` terms is a ratio of declared time scales against a measured admissible
ratio, which is a statement about what would have to be true, not a measurement
that it is.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import cast

import numpy as np
from numpy.typing import NDArray
from scipy.optimize import brentq
from scipy.special import i0e, i1e, ive

from recovery_mechanisms import branch_concentration


FloatArray = NDArray[np.float64]

# Anchored on this file, not the working directory: simulations/README.md.
FIGURES = Path(__file__).resolve().parent / "figures"
PRODUCTION_OUTPUT = FIGURES / "quasistatic_error"

# Distances from threshold at which the admissible speed is measured. The
# smallest is where critical slowing down is expected to bite; the largest is
# far enough out that the quasi-static reduction should be comfortable.
OFFSETS: tuple[float, ...] = (0.05, 0.1, 0.2, 0.4, 0.8)

# The three legs the item names, as (name, offset, side).
HEADLINE: tuple[str, ...] = ("subcritical", "supercritical", "crossing")


@dataclass(frozen=True)
class ErrorConfig:
    """Declared numerical parameters. None of them is fitted to anything."""

    diffusion: float = 1.0
    n_harmonics: int = 24
    dt: float = 5e-3
    leg_width: float = 0.2
    start_offset: float = 0.02
    tolerance: float = 5e-3
    samples: int = 200
    delay_span: float = 1.5

    @property
    def critical_coupling(self) -> float:
        """Return the identical-frequency threshold ``K_c = 2D``."""
        return 2.0 * self.diffusion


@dataclass(frozen=True)
class Leg:
    """One ramp: a name, its endpoints in `K` and its distance from threshold."""

    name: str
    start: float
    end: float
    delta: float


@dataclass(frozen=True)
class LegRun:
    """What one leg at one speed produced."""

    speed: float
    terminal_error: float
    max_error: float
    max_error_coupling: float


def stationary_order(coupling: float, diffusion: float) -> float:
    """Return `r_ss(K)`: zero at or below `K_c = 2D`, the coherent branch above.

    `branch_concentration` solves `R(a)/a = D/K` on the unique coherent branch,
    which is `Phase8_SelfConsistency`'s `coherent_iff_sRatio_eq`; the order
    parameter is `r = a D / K`. Inverting a measured resultant length would be
    the tautology `recovery_mechanisms` avoids, and is not done here either.
    """
    if coupling <= 0.0:
        return 0.0
    ratio = coupling / diffusion
    return float(branch_concentration(ratio) / ratio)


def bessel_ratio(concentration: float) -> float:
    """Return `I_1(a) / I_0(a)`, the order parameter of a von Mises density."""
    if concentration <= 0.0:
        return 0.0
    return float(i1e(concentration) / i0e(concentration))


def concentration_for_order(order: float) -> float:
    """Invert `I_1(a)/I_0(a) = r` for the von Mises concentration `a`."""
    if order <= 0.0:
        return 0.0
    if order >= 1.0:
        raise ValueError("a von Mises order parameter is strictly below one")
    return float(brentq(lambda a: bessel_ratio(a) - order, 1e-12, 1e4, xtol=1e-13))


def von_mises_harmonics(concentration: float, n_harmonics: int) -> FloatArray:
    """Return `h_k = I_k(a) / I_0(a)` for `k = 1 .. n_harmonics`."""
    if n_harmonics < 2:
        raise ValueError("at least two harmonics are required")
    orders = np.arange(1, n_harmonics + 1)
    return np.asarray(ive(orders, concentration) / ive(0, concentration), dtype=float)


def nonlinear_term(harmonics: FloatArray, coupling: FloatArray | float) -> FloatArray:
    """Return the coupling term `(K r k / 2)(h_{k-1} - h_{k+1})` of the ladder.

    The last axis of `harmonics` indexes the harmonic; any leading axes are
    independent copies, and `coupling` broadcasts against them. One trajectory
    and an ensemble driven by different couplings are therefore the same code.
    """
    leading = harmonics[..., :1]
    extended = np.concatenate((np.ones_like(leading), harmonics, np.zeros_like(leading)), axis=-1)
    orders = np.arange(1, harmonics.shape[-1] + 1, dtype=float)
    strength = np.asarray(coupling, dtype=float)[..., None]
    return 0.5 * strength * leading * orders * (extended[..., :-2] - extended[..., 2:])


@dataclass(frozen=True)
class Propagator:
    """Integrating factors for the diffusive part, precomputed once per run."""

    decay: FloatArray
    phi_one: FloatArray
    phi_two: FloatArray


def propagator(n_harmonics: int, diffusion: float, dt: float) -> Propagator:
    orders = np.arange(1, n_harmonics + 1, dtype=float)
    rate = -diffusion * orders**2
    decay = np.exp(rate * dt)
    phi_one = (decay - 1.0) / rate
    phi_two = (decay - 1.0 - rate * dt) / (rate**2 * dt)
    return Propagator(decay, phi_one, phi_two)


def advance(harmonics: FloatArray, coupling: FloatArray | float, factors: Propagator) -> FloatArray:
    """One exponential-Heun step. The diffusive part is integrated exactly, so
    the step is stable at every harmonic and the truncation order is two."""
    slope = nonlinear_term(harmonics, coupling)
    predicted = factors.decay * harmonics + factors.phi_one * slope
    corrected = nonlinear_term(predicted, coupling)
    return predicted + factors.phi_two * (corrected - slope)


def _initial_harmonics(leg: Leg, config: ErrorConfig) -> FloatArray:
    start = stationary_order(leg.start, config.diffusion) + config.start_offset
    return von_mises_harmonics(concentration_for_order(start), config.n_harmonics)


def run_leg(leg: Leg, speed: float, config: ErrorConfig) -> LegRun:
    """Ramp one leg at one speed and report its quasi-static residual."""
    duration = (leg.end - leg.start) / speed
    steps = max(int(round(duration / config.dt)), 1)
    factors = propagator(config.n_harmonics, config.diffusion, config.dt)
    harmonics = _initial_harmonics(leg, config)
    record_every = max(steps // config.samples, 1)
    best = (0.0, leg.start)
    for index in range(steps):
        coupling = leg.start + speed * index * config.dt
        harmonics = advance(harmonics, coupling, factors)
        if index % record_every == 0:
            residual = abs(harmonics[0] - stationary_order(coupling, config.diffusion))
            best = max(best, (residual, coupling))
    terminal = abs(harmonics[0] - stationary_order(leg.end, config.diffusion))
    return LegRun(speed, float(terminal), float(best[0]), float(best[1]))


def admissible_speed(runs: list[LegRun], tolerance: float) -> float | None:
    """Return the largest scanned speed whose terminal residual is within
    `tolerance`, or `None` when no scanned speed is."""
    passing = [run.speed for run in runs if run.terminal_error <= tolerance]
    return max(passing) if passing else None


def build_legs(config: ErrorConfig) -> list[Leg]:
    """The scanned legs: one pair per offset, plus the crossing leg."""
    critical, width = config.critical_coupling, config.leg_width
    legs = [Leg("crossing", critical - width, critical + width, 0.0)]
    for offset in OFFSETS:
        legs.append(
            Leg(f"subcritical_{offset:g}", critical - offset - width, critical - offset, offset)
        )
        legs.append(
            Leg(f"supercritical_{offset:g}", critical + offset, critical + offset + width, offset)
        )
    return legs


# Declared for comparison with the finite-`N` ramp already in this repository.
# `dynamic_ramp_report` fixes the escape level and the speeds, and
# `dynamic_ramp.production_config` fixes the population; `report` sits above
# `simulation` in `tach.toml`, so the numbers are restated here rather than
# imported, and `\rampDelayExponent` is the published fit they produced.
RAMP_SPEEDS: tuple[float, ...] = (1e-1, 1e-2, 1e-3, 1e-4)
# The finite-`N` ensemble is right-censored at the fastest speed -- not every
# replica escapes before the leg ends -- so the published fit uses the other
# three. The comparison below is made over the same three, and over all four.
RAMP_UNCENSORED: tuple[float, ...] = RAMP_SPEEDS[1:]
RAMP_ESCAPE = 0.2
RAMP_OSCILLATORS = 2000
RAMP_DELAY_EXPONENT = 0.443

# Declared time scales for the manuscript reading, both as ranges and neither
# measured here. The first is the sleep-wake transition the extracellular-space
# study works over; the second is the phase-coherence time of the cortical bands
# the recovery section discusses.
GEOMETRY_SECONDS: tuple[float, float] = (60.0, 600.0)
PHASE_SECONDS: tuple[float, float] = (0.01, 0.1)


def required_ratio(speed: float, config: ErrorConfig) -> float:
    """Return the coupling-to-phase time-scale ratio a given ramp speed is.

    The coupling time scale is `K_c / |dK/dt|` and the phase time scale is the
    free relaxation time `1/D`, so the ratio is `K_c D / speed`. "Evolves more
    slowly than phase dynamics" is a statement about this number.
    """
    if speed <= 0.0:
        raise ValueError("a ramp speed must be positive")
    return float(config.critical_coupling * config.diffusion / speed)


def fit_exponent(speeds: FloatArray, delays: FloatArray) -> float:
    """Least-squares slope of `log delay` on `log speed`."""
    if speeds.size < 2 or speeds.shape != delays.shape:
        raise ValueError("an exponent fit needs at least two matching points")
    if np.any(speeds <= 0.0) or np.any(delays <= 0.0):
        raise ValueError("an exponent fit needs strictly positive points")
    slope = np.polyfit(np.log(speeds), np.log(delays), 1)[0]
    return float(slope)


def _seeded_delay_leg(config: ErrorConfig) -> Leg:
    critical = config.critical_coupling
    return Leg("threshold_delay", critical, critical + config.delay_span, 0.0)


def threshold_delay(speed: float, config: ErrorConfig) -> float | None:
    """Return the coupling excess at which a threshold-seeded run escapes.

    The seed is the finite-population fluctuation floor `1/sqrt(N)` and the
    escape level is the one `dynamic_ramp_report` uses, so this is the
    deterministic idealization of the same measurement: a run that enters the
    threshold at the floor rather than one whose seed decayed to a point.
    """
    leg = _seeded_delay_leg(config)
    seed = 1.0 / np.sqrt(RAMP_OSCILLATORS)
    harmonics = von_mises_harmonics(concentration_for_order(float(seed)), config.n_harmonics)
    factors = propagator(config.n_harmonics, config.diffusion, config.dt)
    steps = max(int(round((leg.end - leg.start) / speed / config.dt)), 1)
    for index in range(steps):
        coupling = leg.start + speed * index * config.dt
        harmonics = advance(harmonics, coupling, factors)
        if harmonics[0] >= RAMP_ESCAPE:
            return float(coupling - leg.start)
    return None


def stationary_control(config: ErrorConfig, coupling: float = 3.0) -> float:
    """Hold `K` fixed on the coherent branch and report the drift in `r`.

    A positive control: the von Mises density at the branch concentration is an
    exact stationary solution, so an integrator that moves it is wrong, and a
    residual measured against a branch this run could not hold would be an
    artefact of the integrator rather than of the rate.
    """
    order = stationary_order(coupling, config.diffusion)
    harmonics = von_mises_harmonics(concentration_for_order(order), config.n_harmonics)
    factors = propagator(config.n_harmonics, config.diffusion, config.dt)
    for _ in range(config.samples):
        harmonics = advance(harmonics, coupling, factors)
    return float(abs(harmonics[0] - order))


def frozen_comparison(leg: Leg, speed: float, config: ErrorConfig) -> float:
    """Residual against `r_ss` at the leg's *initial* coupling rather than its
    current one. The design is required to fail this comparison: a quasi-static
    reduction that held the branch fixed would report a residual that does not
    fall as the rate falls, which is how a silently frozen branch would look."""
    duration = (leg.end - leg.start) / speed
    steps = max(int(round(duration / config.dt)), 1)
    factors = propagator(config.n_harmonics, config.diffusion, config.dt)
    harmonics = _initial_harmonics(leg, config)
    for index in range(steps):
        harmonics = advance(harmonics, leg.start + speed * index * config.dt, factors)
    return float(abs(harmonics[0] - stationary_order(leg.start, config.diffusion)))


def step_halving_control(leg: Leg, speed: float, config: ErrorConfig) -> float:
    """Return how much the terminal residual moves when `dt` is halved."""
    coarse = run_leg(leg, speed, config)
    fine = run_leg(leg, speed, ErrorConfig(**{**asdict(config), "dt": config.dt / 2.0}))
    return float(abs(coarse.terminal_error - fine.terminal_error))


def _leg_payload(leg: Leg, runs: list[LegRun], config: ErrorConfig) -> dict[str, object]:
    speed = admissible_speed(runs, config.tolerance)
    worst = max(runs, key=lambda run: run.max_error)
    return {
        "start": leg.start,
        "end": leg.end,
        "delta": leg.delta,
        "admissible_speed": speed,
        "required_ratio": None if speed is None else required_ratio(speed, config),
        "worst_residual": worst.max_error,
        "worst_residual_coupling": worst.max_error_coupling,
        "worst_residual_speed": worst.speed,
        "runs": [asdict(run) for run in runs],
    }


def _criterion(legs: dict[str, dict[str, object]]) -> list[dict[str, object]]:
    """The admissible speed as a function of distance from threshold, one point
    per scanned leg, sorted by that distance."""
    points = [
        {
            "leg": name,
            "delta": payload["delta"],
            "admissible_speed": payload["admissible_speed"],
            "required_ratio": payload["required_ratio"],
        }
        for name, payload in legs.items()
    ]
    return sorted(points, key=lambda point: (cast(float, point["delta"]), cast(str, point["leg"])))


def _worst_ratio(points: list[dict[str, object]], delta: float) -> float | None:
    """The largest required ratio among the legs at one distance. `None` when
    any leg there has no admissible speed at all, which is a stronger failure
    than a large requirement."""
    at_delta = [point for point in points if cast(float, point["delta"]) == delta]
    if any(point["required_ratio"] is None for point in at_delta):
        return None
    return max(cast(float, point["required_ratio"]) for point in at_delta)


def _trackable_delta(points: list[dict[str, object]], ratio: float) -> float | None:
    """The smallest scanned distance from threshold at which *every* leg meets a
    declared time-scale ratio. One leg failing is the reduction failing: the
    criterion is about the distance, not about the direction of approach."""
    deltas = sorted({cast(float, point["delta"]) for point in points})
    meeting = [
        delta
        for delta in deltas
        if (worst := _worst_ratio(points, delta)) is not None and worst <= ratio
    ]
    return min(meeting) if meeting else None


def _manuscript_payload(points: list[dict[str, object]]) -> dict[str, object]:
    slow = GEOMETRY_SECONDS[0] / PHASE_SECONDS[1]
    fast = GEOMETRY_SECONDS[1] / PHASE_SECONDS[0]
    return {
        "geometry_seconds": list(GEOMETRY_SECONDS),
        "phase_seconds": list(PHASE_SECONDS),
        "cited_ratio_range": [slow, fast],
        "trackable_delta_at_slow_end": _trackable_delta(points, slow),
        "trackable_delta_at_fast_end": _trackable_delta(points, fast),
        "worst_ratio_by_delta": {
            f"{delta:g}": _worst_ratio(points, delta)
            for delta in sorted({cast(float, point["delta"]) for point in points})
        },
        "reading": "the cited ratio is what 'evolves more slowly than phase dynamics' would "
        "have to mean; the trackable distance is how close to threshold it reaches",
    }


def _exponent_of(pairs: list[tuple[float, float]]) -> float | None:
    """The fitted exponent of a speed/delay set, or `None` when a run did not
    escape and there is nothing to fit."""
    if len(pairs) < 2:
        return None
    return fit_exponent(
        np.array([speed for speed, _ in pairs]), np.array([delay for _, delay in pairs])
    )


def _delay_payload(config: ErrorConfig) -> dict[str, object]:
    excess = [threshold_delay(speed, config) for speed in RAMP_SPEEDS]
    measured = [(s, d) for s, d in zip(RAMP_SPEEDS, excess, strict=True) if d is not None]
    uncensored = [(s, d) for s, d in measured if s in RAMP_UNCENSORED]
    return {
        "speeds": list(RAMP_SPEEDS),
        "coupling_excess": excess,
        "exponent": _exponent_of(measured),
        "uncensored_speeds": list(RAMP_UNCENSORED),
        "uncensored_exponent": _exponent_of(uncensored),
        "published_exponent": RAMP_DELAY_EXPONENT,
        "seed_order": 1.0 / float(np.sqrt(RAMP_OSCILLATORS)),
        "escape_level": RAMP_ESCAPE,
    }


def _controls_payload(
    legs: list[Leg], speeds: FloatArray, config: ErrorConfig
) -> dict[str, object]:
    reference = next(leg for leg in legs if leg.name == f"supercritical_{OFFSETS[3]:g}")
    frozen = {f"{speed:g}": frozen_comparison(reference, float(speed), config) for speed in speeds}
    return {
        "stationary_drift": stationary_control(config),
        "step_halving": step_halving_control(reference, float(speeds[len(speeds) // 2]), config),
        "frozen_leg": reference.name,
        "frozen_comparison": frozen,
        "frozen_rejected": all(value > config.tolerance for value in frozen.values()),
    }


def run_sweep(config: ErrorConfig, speeds: FloatArray, output: Path) -> dict[str, object]:
    """Run every leg at every speed and write one summary."""
    legs = build_legs(config)
    payloads = {
        leg.name: _leg_payload(leg, [run_leg(leg, float(s), config) for s in speeds], config)
        for leg in legs
    }
    points = _criterion(payloads)
    summary: dict[str, object] = {
        "source": "quasistatic_error.py",
        "config": asdict(config),
        "speeds": [float(speed) for speed in speeds],
        "headline_legs": list(HEADLINE),
        "legs": payloads,
        "criterion": points,
        "bifurcation_delay": _delay_payload(config),
        "controls": _controls_payload(legs, speeds, config),
        "manuscript": _manuscript_payload(points),
        "scope": "mean-field quasi-static residual of one declared ramp family; "
        "no cortical coupling trajectory is calibrated",
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "quasistatic_error_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return summary


def production_speeds() -> FloatArray:
    """The scanned ramp speeds, four decades wide."""
    return np.geomspace(1e-4, 1.0, 9)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="run a reduced deterministic sweep")
    parser.add_argument("--output", type=Path, default=None)
    return parser.parse_args()


def main() -> None:
    args = _parse_args()
    config = ErrorConfig(n_harmonics=12, samples=40) if args.smoke else ErrorConfig()
    speeds = np.geomspace(1e-2, 1.0, 3) if args.smoke else production_speeds()
    summary = run_sweep(config, speeds, args.output or PRODUCTION_OUTPUT)
    delay = cast(dict[str, object], summary["bifurcation_delay"])
    print(f"delay exponent {delay['exponent']} against published {delay['published_exponent']}")
    for point in cast(list[dict[str, object]], summary["criterion"]):
        print(f"{point['leg']}: admissible speed {point['admissible_speed']}")
    print("scope: mean-field quasi-static residual; no cortical trajectory is calibrated")


if __name__ == "__main__":
    main()
