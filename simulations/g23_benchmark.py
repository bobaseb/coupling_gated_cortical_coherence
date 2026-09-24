"""Held-out finite-state episodes for the coupled phase/register witness.

The task is to predict the next binary phase from the register. The register
readout is fit once on an independently sampled training family and frozen for
all held-out bath-field families and controls. Phase/register symbol agreement
is a toy shared-content proxy; it is not an independently decoded cortical
content measurement. Bath heat covers phase flips only. The finite model has
no continuous angular probability current.
"""

from dataclasses import replace
import json
from pathlib import Path

import numpy as np
from numpy.typing import NDArray

from g23_closed_loop import Control, ControlResult, FeedbackConfig, control_result, phase_channel

IntArray = NDArray[np.int64]


def fit_readout(register: IntArray, next_phase: IntArray) -> IntArray:
    """Fit a binary next-phase decoder from training episodes alone."""
    if register.shape != next_phase.shape or register.ndim != 1 or register.size == 0:
        raise ValueError("Training episode arrays must match and be nonempty")
    if not np.isin(register, (0, 1)).all() or not np.isin(next_phase, (0, 1)).all():
        raise ValueError("Training episodes must contain binary states")
    if not np.isin((0, 1), register).all():
        raise ValueError("Both register values need training support")
    return np.asarray(
        [int(np.mean(next_phase[register == value]) > 0.5) for value in (0, 1)],
        dtype=np.int64,
    )


def sample_final_episodes(
    config: FeedbackConfig, result: ControlResult, count: int, *, seed: int
) -> dict[str, IntArray]:
    """Draw independent held-out final states and one actual phase transition."""
    if not isinstance(count, int) or count < 1:
        raise ValueError("Episode count must be positive")
    rng = np.random.default_rng(seed)
    sample = rng.choice(4, size=count, p=result.joint_law[-1].reshape(4))
    phase = np.asarray(sample // 2, dtype=np.int64)
    register = np.asarray(sample % 2, dtype=np.int64)
    action = np.zeros(count, dtype=np.int64) if result.control == "frozen" else register
    probability_one = phase_channel(config)[action, phase, 1]
    next_phase = np.asarray(rng.random(count) < probability_one, dtype=np.int64)
    return {"phase": phase, "register": register, "next_phase": next_phase}


def _score(
    config: FeedbackConfig,
    result: ControlResult,
    episodes: dict[str, IntArray],
    readout: IntArray,
) -> dict[str, float | None]:
    phase, register, next_phase = (episodes["phase"], episodes["register"], episodes["next_phase"])
    predicted = readout[register]
    phase_marginal = result.phase_marginal[-1]
    return {
        "heldout_accuracy": float(np.mean(predicted == next_phase)),
        "shared_content_agreement_proxy": float(np.mean(phase == register)),
        "phase_reconstruction_error": float(np.mean((phase - predicted) ** 2)),
        "phase_order": float(abs(phase_marginal[0] - phase_marginal[1])),
        "installed_energy": float(result.installed_energy[-1]),
        "cumulative_work": float(result.work_cost.sum()),
        "cumulative_phase_heat_to_bath": float(result.bath_heat.sum()),
        "available_store": float(result.available_store[-1]),
        "continuous_current_cost": None,
        "bath_inverse_temperature": config.beta,
    }


def _save_episodes(path: Path, episodes: dict[str, IntArray]) -> None:
    np.savez_compressed(
        path,
        phase=episodes["phase"],
        register=episodes["register"],
        next_phase=episodes["next_phase"],
    )


def run_benchmark(
    output: Path,
    *,
    train_episodes: int = 4096,
    test_episodes: int = 4096,
    seed: int = 230,
) -> None:
    """Save disjoint training and held-out episodes with fixed control budgets."""
    base = FeedbackConfig(horizon=6)
    charger = 1.3
    training = sample_final_episodes(
        base,
        control_result(base, "informed", replenishment=charger),
        train_episodes,
        seed=seed,
    )
    readout = fit_readout(training["register"], training["next_phase"])
    output.mkdir(parents=True, exist_ok=True)
    _save_episodes(output / "training_episodes.npz", training)
    rows: list[dict[str, str | float | None]] = []
    controls: tuple[Control, ...] = ("informed", "blind", "replayed", "frozen")
    for family_index, (name, field) in enumerate((("field_0p25", 0.25), ("field_0p55", 0.55))):
        config = replace(base, field=field)
        for control_index, control in enumerate(controls):
            result = control_result(config, control, replenishment=charger)
            episodes = sample_final_episodes(
                config,
                result,
                test_episodes,
                seed=seed + 1 + 4 * family_index + control_index,
            )
            _save_episodes(output / f"{name}_{control}.npz", episodes)
            rows.append(
                {
                    "family": name,
                    "control": control,
                    **_score(config, result, episodes, readout),
                }
            )
    summary = {
        "source": "g23_benchmark.py",
        "seed": seed,
        "train_family": "field_0p4",
        "train_episodes": train_episodes,
        "test_episodes_per_control_and_family": test_episodes,
        "trained_readout": readout.tolist(),
        "initial_joint_law": [[0.25, 0.25], [0.25, 0.25]],
        "initial_prior": "uninformative_phase_register_product",
        "external_charger_per_step": charger,
        "content_scope": "phase/register binary-symbol agreement proxy",
        "rows": rows,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
