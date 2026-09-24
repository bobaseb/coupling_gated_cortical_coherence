"""Exact two-state phase/register process with a finite work store.

The installed action sets the phase energy landscape. Phase flips obey local
detailed balance against a named unit-temperature bath. Sensing and reset
have declared work prices; installation changes a declared actuator mode
energy. The full sensor/register channel is not asserted to satisfy detailed
balance, so bath heat covers phase flips only. No continuous phase current is
defined for this two-state model.
"""

from dataclasses import asdict, dataclass
import json
from pathlib import Path
from typing import Literal

import numpy as np
from numpy.typing import NDArray

from followup_foundations import (
    feedback_expected_costs,
    feedback_laws,
    feedback_prediction_accuracy,
    feedback_store,
    feedback_transition,
)

FloatArray = NDArray[np.float64]
Control = Literal["informed", "blind", "frozen", "replayed"]


@dataclass(frozen=True)
class FeedbackConfig:
    """Declared bath, measurement, actuator and work-store parameters."""

    beta: float = 1.0
    field: float = 0.4
    flip_attempt: float = 0.2
    sensor_accuracy: float = 0.9
    sensing_work: float = 0.2
    reset_work: float = 0.1
    mode_gap: float = 0.1
    initial_store: float = 3.0
    preparation: float = 0.1
    horizon: int = 8


@dataclass(frozen=True)
class ControlResult:
    """Joint law and distinct predictive, work and bath-heat measurements."""

    control: Control
    joint_law: FloatArray
    phase_marginal: FloatArray
    prediction_accuracy: FloatArray
    work_cost: FloatArray
    installation_work: FloatArray
    bath_heat: FloatArray
    installed_energy: FloatArray
    available_store: FloatArray
    current_cost: None


def _validate(config: FeedbackConfig) -> None:
    values = (
        config.beta,
        config.field,
        config.flip_attempt,
        config.sensor_accuracy,
        config.sensing_work,
        config.reset_work,
        config.mode_gap,
        config.initial_store,
        config.preparation,
    )
    if not np.isfinite(values).all() or config.horizon < 0:
        raise ValueError("Feedback parameters must be finite with nonnegative horizon")
    if config.beta <= 0 or config.field < 0 or config.flip_attempt <= 0:
        raise ValueError("Bath scale, field and flip attempt are outside the model domain")
    if not 0.5 <= config.sensor_accuracy <= 1:
        raise ValueError("Sensor accuracy must be in [0.5, 1]")
    if min(config.sensing_work, config.reset_work, config.mode_gap) < 0:
        raise ValueError("Declared work prices must be nonnegative")
    if config.flip_attempt * np.exp(config.beta * config.field) >= 1:
        raise ValueError("Flip attempt is too large for a supported stochastic channel")


def _energy(config: FeedbackConfig) -> FloatArray:
    spin = np.array([-1.0, 1.0])
    return np.asarray(-installed_coupling(config)[:, None] * spin[None, :])


def installed_coupling(config: FeedbackConfig) -> FloatArray:
    """Signed coupling between the actuator orientation and binary phase."""
    return np.array([-config.field, config.field], dtype=np.float64)


def phase_channel(config: FeedbackConfig) -> FloatArray:
    """Positive two-state channel with P01/P10 = exp(-beta ΔE)."""
    _validate(config)
    energy = _energy(config)
    channel = np.empty((2, 2, 2), dtype=np.float64)
    for action in range(2):
        for phase in range(2):
            other = 1 - phase
            delta = energy[action, other] - energy[action, phase]
            channel[action, phase, other] = config.flip_attempt * np.exp(-config.beta * delta / 2)
            channel[action, phase, phase] = 1 - channel[action, phase, other]
    return channel


def _sensor(config: FeedbackConfig, control: Control) -> FloatArray:
    if control == "blind":
        return np.full((2, 2), 0.5)
    accuracy = config.sensor_accuracy
    return np.array([[accuracy, 1 - accuracy], [1 - accuracy, accuracy]])


def _update() -> FloatArray:
    return np.array([[[1.0, 0.0], [1.0, 0.0]], [[0.0, 1.0], [0.0, 1.0]]])


def _install(control: Control) -> NDArray[np.int64]:
    return np.array([0, 0] if control == "frozen" else [0, 1], dtype=np.int64)


def _installation_price(config: FeedbackConfig, install: NDArray[np.int64]) -> FloatArray:
    modes = np.array([0, config.mode_gap])
    energy = _energy(config)
    price = np.empty((2, 2, 2, 2), dtype=np.float64)
    for phase in range(2):
        for register in range(2):
            for next_phase in range(2):
                for next_register in range(2):
                    old_action, new_action = install[register], install[next_register]
                    price[phase, register, next_phase, next_register] = (
                        energy[new_action, next_phase]
                        - energy[old_action, next_phase]
                        + modes[new_action]
                        - modes[old_action]
                    )
    return price


def _installed_energy(
    config: FeedbackConfig, install: NDArray[np.int64], laws: FloatArray
) -> FloatArray:
    modes = np.array([0, config.mode_gap])
    energy = _energy(config)[install].T + modes[install][None, :]
    return np.asarray(np.einsum("tpr,pr->t", laws, energy), dtype=np.float64)


def _bath_heat(config: FeedbackConfig, install: NDArray[np.int64]) -> FloatArray:
    energy = _energy(config)
    # Return heat to the bath E(old phase) - E(new phase), on each old action.
    heat = np.empty((2, 2, 2, 2), dtype=np.float64)
    for phase in range(2):
        for register in range(2):
            for next_phase in range(2):
                heat[phase, register, next_phase, :] = (
                    energy[install[register], phase] - energy[install[register], next_phase]
                )
    return heat


def safe_steps(config: FeedbackConfig, replenishment: float = 0.0) -> int:
    """Conservative pathwise stop horizon under the maximum possible work cost."""
    _validate(config)
    if not np.isfinite(replenishment) or replenishment < 0:
        raise ValueError("Replenishment must be finite and nonnegative")
    maximum = config.sensing_work + config.reset_work + config.mode_gap + 2 * config.field
    available = config.initial_store - config.preparation
    steps = 0
    while steps < config.horizon and available + replenishment >= maximum:
        available += replenishment - maximum
        steps += 1
    return steps


def _replayed_result(config: FeedbackConfig, *, replenishment: float, steps: int) -> ControlResult:
    """Yoke register marginals to feedback while severing phase observations.

    This counterfactual uses the informed process's register marginals as an
    externally supplied schedule. It is a matched diagnostic, not an autonomous
    controller or a thermodynamic implementation of that external schedule.
    """
    evolve = phase_channel(config)
    install = _install("informed")
    informed_transition = feedback_transition(
        evolve, _sensor(config, "informed"), _update(), install
    )
    informed = feedback_laws(np.full((2, 2), 0.25), informed_transition, steps)
    laws = np.empty_like(informed)
    laws[0] = informed[0]
    installation_price = _installation_price(config, install)
    heat_price = _bath_heat(config, install)
    work = np.empty(steps)
    installation_work = np.empty(steps)
    heat = np.empty(steps)
    for index in range(steps):
        next_register = informed[index + 1].sum(axis=0)
        transition = evolve[install].transpose(1, 0, 2)[:, :, :, None] * next_register
        laws[index + 1] = np.einsum("pr,prqs->qs", laws[index], transition)
        installation_work[index] = np.einsum(
            "pr,prqs,prqs->", laws[index], transition, installation_price
        )
        heat[index] = np.einsum("pr,prqs,prqs->", laws[index], transition, heat_price)
        work[index] = installation_work[index] + config.sensing_work + config.reset_work
    store = feedback_store(
        config.initial_store, config.preparation, work, np.full(steps, replenishment)
    )
    return ControlResult(
        "replayed",
        laws,
        laws.sum(axis=2),
        feedback_prediction_accuracy(laws, evolve, install, np.array([0, 1])),
        work,
        installation_work,
        heat,
        _installed_energy(config, install, laws),
        store,
        None,
    )


def control_result(
    config: FeedbackConfig,
    control: Control,
    *,
    replenishment: float = 0.0,
    stop_when_unfunded: bool = False,
) -> ControlResult:
    """Propagate one matched control and its expected path ledgers."""
    if control not in ("informed", "blind", "frozen", "replayed"):
        raise ValueError("Unknown feedback control")
    evolve = phase_channel(config)
    steps = safe_steps(config, replenishment) if stop_when_unfunded else config.horizon
    if control == "replayed":
        return _replayed_result(config, replenishment=replenishment, steps=steps)
    install = _install(control)
    transition = feedback_transition(evolve, _sensor(config, control), _update(), install)
    laws = feedback_laws(np.full((2, 2), 0.25), transition, steps)
    installation_price = _installation_price(config, install)
    installation_work = feedback_expected_costs(laws, transition, installation_price)
    work_price = installation_price + config.sensing_work + config.reset_work
    work = feedback_expected_costs(laws, transition, work_price)
    heat = np.einsum("tpr,prqs,prqs->t", laws[:-1], transition, _bath_heat(config, install))
    store = feedback_store(
        config.initial_store, config.preparation, work, np.full(steps, replenishment)
    )
    return ControlResult(
        control,
        laws,
        laws.sum(axis=2),
        feedback_prediction_accuracy(laws, evolve, install, np.array([0, 1])),
        work,
        installation_work,
        np.asarray(heat, dtype=np.float64),
        _installed_energy(config, install, laws),
        store,
        None,
    )


def save_controls(output: Path, config: FeedbackConfig) -> None:
    """Save all model channels, joint laws, ledgers and a compact summary."""
    output.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, str | float | int | None]] = []
    protocols: tuple[tuple[str, Control, float], ...] = (
        ("informed", "informed", 0.0),
        ("blind", "blind", 0.0),
        ("replayed", "replayed", 0.0),
        ("frozen", "frozen", 0.0),
        ("informed_replenished", "informed", 1.3),
    )
    for name, control, replenishment in protocols:
        result = control_result(
            config, control, replenishment=replenishment, stop_when_unfunded=True
        )
        np.savez_compressed(
            output / f"{name}.npz",
            installed_coupling=installed_coupling(config),
            joint_law=result.joint_law,
            phase_marginal=result.phase_marginal,
            prediction_accuracy=result.prediction_accuracy,
            work_cost=result.work_cost,
            installation_work=result.installation_work,
            bath_heat=result.bath_heat,
            installed_energy=result.installed_energy,
            available_store=result.available_store,
        )
        rows.append(
            {
                "control": name,
                "executed_steps": int(result.work_cost.size),
                "replenishment_per_step": replenishment,
                "prediction_accuracy_final": float(result.prediction_accuracy[-1]),
                "cumulative_work": float(result.work_cost.sum()),
                "cumulative_phase_heat_to_bath": float(result.bath_heat.sum()),
                "cumulative_installation_work": float(result.installation_work.sum()),
                "installed_energy_change": float(
                    result.installed_energy[-1] - result.installed_energy[0]
                ),
                "available_store_final": float(result.available_store[-1]),
                "continuous_current_cost": None,
            }
        )
    summary = {"source": "g23_closed_loop.py", "config": asdict(config), "controls": rows}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
