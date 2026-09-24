"""Fixed synthetic G24 task for a measured linear bottleneck baseline.

The latent state has two scene bits and two self bits. Two local views overlap
on scene bit 1 and self bit 0; their measurement noise is independent. Even
parity combinations train the decoder and odd parity combinations test it.
Flipping self bit 0 holds the scene fixed and crosses the split. This module
does not implement the nonlinear transformer or phase-network candidates.
"""

from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path
from time import perf_counter
from typing import Literal

import numpy as np
from numpy.typing import NDArray

from followup_foundations import covariance_rank_tail, covariance_rank_truncation

FloatArray = NDArray[np.float64]
Split = Literal["parity", "scene_pair"]


@dataclass(frozen=True)
class SharedTask:
    """Declared local inputs, global targets, and disjoint state combinations."""

    train_input: FloatArray
    train_target: FloatArray
    train_state: FloatArray
    test_input: FloatArray
    test_target: FloatArray
    test_state: FloatArray
    target_operator: FloatArray


def _target_operator() -> FloatArray:
    return np.array(
        [
            [1, 0, 0, 0, 0, 0],
            [0, 0.5, 0, 0.5, 0, 0],
            [0, 0, 0.5, 0, 0.5, 0],
            [0, 0, 0, 0, 0, 1],
            [0, -0.5, 0.5, -0.5, 0.5, 0],
        ],
        dtype=np.float64,
    )


def _observations(states: FloatArray, noise: float, rng: np.random.Generator) -> FloatArray:
    local = states[:, [0, 1, 2, 1, 2, 3]]
    return np.asarray(local + rng.normal(0, noise, local.shape), dtype=np.float64)


def _targets(states: FloatArray) -> FloatArray:
    return np.column_stack((states, states[:, 2] - states[:, 1]))


def build_task(
    repeats: int = 16,
    noise: float = 0.0,
    seed: int = 24,
    split: Split = "parity",
) -> SharedTask:
    """Build declared training states and disjoint held-out combinations."""
    if not isinstance(repeats, int) or repeats < 1:
        raise ValueError("Repeats must be a positive integer")
    if not np.isfinite(noise) or noise < 0:
        raise ValueError("Observation noise must be finite and nonnegative")
    if split not in ("parity", "scene_pair"):
        raise ValueError("Unknown state-family split")
    states = np.asarray(list(product((-1.0, 1.0), repeat=4)), dtype=np.float64)
    mask = np.prod(states, axis=1) == 1 if split == "parity" else states[:, 0] == states[:, 1]
    train = np.repeat(states[mask], repeats, axis=0)
    test = np.repeat(states[~mask], repeats, axis=0)
    rng = np.random.default_rng(seed)
    return SharedTask(
        _observations(train, noise, rng),
        _targets(train),
        train,
        _observations(test, noise, rng),
        _targets(test),
        test,
        _target_operator(),
    )


def intervention_set(
    task: SharedTask, *, distance: float, noise: float, seed: int
) -> tuple[FloatArray, FloatArray]:
    """Shift held-out self bit 0 while preserving both external scene bits."""
    if not np.isfinite(distance) or distance < 0:
        raise ValueError("Intervention distance must be finite and nonnegative")
    if not np.isfinite(noise) or noise < 0:
        raise ValueError("Observation noise must be finite and nonnegative")
    states = task.test_state.copy()
    states[:, 2] += distance
    return _observations(states, noise, np.random.default_rng(seed)), _targets(states)


def overlap_disagreement_set(task: SharedTask, *, distance: float) -> tuple[FloatArray, FloatArray]:
    """Perturb second-view copies of shared quantities, holding the world fixed.

    The result is an incompatible observation pair. The target stays the
    unperturbed global state so the score measures decoder robustness to a
    declared local disagreement, not reconstruction of a different world.
    """
    if not np.isfinite(distance) or distance < 0:
        raise ValueError("Overlap disagreement must be finite and nonnegative")
    inputs = task.test_input.copy()
    inputs[:, 3:5] += distance
    return inputs, task.test_target.copy()


def fit_reduced_rank(inputs: FloatArray, targets: FloatArray, rank: int) -> FloatArray:
    """Fit least squares, then optimally compress its empirical linear map."""
    if inputs.ndim != 2 or targets.ndim != 2 or inputs.shape[0] != targets.shape[0]:
        raise ValueError("Inputs and targets must have matching sample rows")
    if not np.isfinite(inputs).all() or not np.isfinite(targets).all():
        raise ValueError("Training arrays must be finite")
    if inputs.shape[0] == 0 or inputs.shape[1] == 0 or targets.shape[1] == 0:
        raise ValueError("Training arrays must be nonempty")
    fitted = np.asarray(np.linalg.lstsq(inputs, targets, rcond=None)[0].T, dtype=np.float64)
    covariance = inputs.T @ inputs / len(inputs)
    return covariance_rank_truncation(fitted, covariance, rank)


def reconstruction_scores(
    inputs: FloatArray, targets: FloatArray, decoder: FloatArray
) -> dict[str, float]:
    """Mean squared global-state error and self-relation component error."""
    if (
        inputs.ndim != 2
        or targets.ndim != 2
        or decoder.shape != (targets.shape[1], inputs.shape[1])
    ):
        raise ValueError("Decoder and task arrays have incompatible dimensions")
    if inputs.shape[0] != targets.shape[0] or inputs.shape[0] == 0:
        raise ValueError("Scoring arrays must have matching nonempty rows")
    residual = inputs @ decoder.T - targets
    return {
        "squared_error": float(np.mean(np.sum(residual**2, axis=1))),
        "self_relation_squared_error": float(np.mean(residual[:, -1] ** 2)),
    }


def save_linear_baseline(
    output: Path,
    *,
    repeats: int = 16,
    noise: float = 0.0,
    seed: int = 24,
    split: Split = "parity",
) -> None:
    """Save fixed splits, fitted decoders, and analytical rank-floor checks.

    This is the linear candidate only. It makes no claim about a transformer,
    phase network, hardware energy, or physical reconstruction.
    """
    started = perf_counter()
    task = build_task(repeats, noise, seed, split)
    covariance = task.train_input.T @ task.train_input / len(task.train_input)
    full = fit_reduced_rank(task.train_input, task.train_target, 5)
    full_error = reconstruction_scores(task.train_input, task.train_target, full)["squared_error"]
    rows: list[dict[str, float | int]] = []
    decoders: dict[str, FloatArray] = {}
    for rank in range(5):
        decoder = fit_reduced_rank(task.train_input, task.train_target, rank)
        decoders[f"rank_{rank}"] = decoder
        train = reconstruction_scores(task.train_input, task.train_target, decoder)
        test = reconstruction_scores(task.test_input, task.test_target, decoder)
        rows.append(
            {
                "rank": rank,
                "effective_rank": int(np.linalg.matrix_rank(decoder, tol=1e-10)),
                "stored_parameter_count": int(decoder.size),
                "decoder_bytes": int(decoder.nbytes),
                "predicted_train_floor": full_error + covariance_rank_tail(full, covariance, rank),
                "train_squared_error": train["squared_error"],
                "test_squared_error": test["squared_error"],
                "test_self_relation_squared_error": test["self_relation_squared_error"],
            }
        )
    fit_seconds = perf_counter() - started
    output.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        output / "dataset.npz",
        train_input=task.train_input,
        train_target=task.train_target,
        train_state=task.train_state,
        test_input=task.test_input,
        test_target=task.test_target,
        test_state=task.test_state,
        target_operator=task.target_operator,
    )
    np.savez_compressed(
        output / "decoders.npz",
        rank_0=decoders["rank_0"],
        rank_1=decoders["rank_1"],
        rank_2=decoders["rank_2"],
        rank_3=decoders["rank_3"],
        rank_4=decoders["rank_4"],
    )
    summary = {
        "source": "g24_shared_task.py",
        "seed": seed,
        "repeats": repeats,
        "noise": noise,
        "train_family": "even_parity" if split == "parity" else "scene_equal",
        "test_family": "odd_parity" if split == "parity" else "scene_opposite",
        "fit_seconds": fit_seconds,
        "runtime_budget_seconds": 2.0,
        "ranks": rows,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
