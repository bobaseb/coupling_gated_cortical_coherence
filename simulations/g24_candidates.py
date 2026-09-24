"""Small CPU nonlinear controls on the fixed G24 local-observation task.

The transformer has two causal tokens, width four, one attention head with
query/key dimension one, and a tanh feedforward block. Its attention and
feedforward parameters are optimized on training states; the linear output
head is refitted at each step. The phase candidate has two coupled oscillators
on a declared one-edge graph. Its readout sees node 1 only after the declared
communication rounds. Both are finite synthetic controls, not physical or
consciousness models.
"""

from dataclasses import dataclass
import json
from pathlib import Path
from time import perf_counter
from typing import Callable

import numpy as np
from numpy.typing import NDArray
from scipy.optimize import minimize

from g24_shared_task import (
    build_task,
    fit_reduced_rank,
    intervention_set,
    overlap_disagreement_set,
    Split,
)

FloatArray = NDArray[np.float64]


def _head(code: FloatArray, targets: FloatArray) -> FloatArray:
    features = np.column_stack((code, np.ones(len(code))))
    return np.asarray(np.linalg.lstsq(features, targets, rcond=None)[0], dtype=np.float64)


def _predict(code: FloatArray, head: FloatArray) -> FloatArray:
    return np.asarray(np.column_stack((code, np.ones(len(code)))) @ head, dtype=np.float64)


def _squared_error(prediction: FloatArray, target: FloatArray) -> float:
    return float(np.mean(np.sum((prediction - target) ** 2, axis=1)))


def _transformer_code(inputs: FloatArray, params: FloatArray) -> FloatArray:
    if inputs.ndim != 2 or inputs.shape[1] != 6 or params.shape != (100,):
        raise ValueError("Transformer expects two three-value tokens and 100 parameters")
    embedding = params[:12].reshape(3, 4)
    position = params[12:20].reshape(2, 4)
    query, key = params[20:24], params[24:28]
    value = params[28:44].reshape(4, 4)
    output = params[44:60].reshape(4, 4)
    feed_in, bias_in = params[60:76].reshape(4, 4), params[76:80]
    feed_out, bias_out = params[80:96].reshape(4, 4), params[96:100]
    tokens = inputs.reshape(-1, 2, 3)
    hidden = tokens @ embedding + position
    scores = (hidden[:, 1, :] @ query)[:, None] * (hidden @ key)
    weights = np.exp(scores - scores.max(axis=1, keepdims=True))
    weights /= weights.sum(axis=1, keepdims=True)
    context = np.sum(weights[:, :, None] * (hidden @ value), axis=1)
    state = np.tanh(hidden[:, 1, :] + context @ output)
    return np.asarray(state + np.tanh(state @ feed_in + bias_in) @ feed_out + bias_out)


@dataclass(frozen=True)
class TransformerModel:
    """Trained causal attention parameters and fitted real-valued output head."""

    params: FloatArray
    head: FloatArray
    fit_seconds: float
    query_key_dim: int = 1
    causal_past_tokens: int = 2
    communication_rounds: int = 1

    def code(self, inputs: FloatArray) -> FloatArray:
        return _transformer_code(inputs, self.params)

    def predict(self, inputs: FloatArray) -> FloatArray:
        return _predict(self.code(inputs), self.head)


def _phase_evolve(inputs: FloatArray, params: FloatArray, rounds: int) -> FloatArray:
    if inputs.ndim != 2 or inputs.shape[1] != 6 or params.shape != (7,):
        raise ValueError("Phase model expects two local views and seven parameters")
    phases = np.sum(inputs.reshape(-1, 2, 3) * params[:6].reshape(2, 3), axis=2)
    coupling = 0.5 * np.tanh(params[6])
    for _ in range(rounds):
        exchange = 0.2 * coupling * np.sin(phases[:, 1] - phases[:, 0])
        phases = phases + np.column_stack((exchange, -exchange))
    return np.asarray(phases, dtype=np.float64)


def _phase_code(phases: FloatArray) -> FloatArray:
    """Read the encoding region at node 1 through five phase harmonics."""
    encoded = phases[:, 1]
    return np.asarray(
        np.column_stack(
            (
                np.cos(encoded),
                np.sin(encoded),
                np.cos(2 * encoded),
                np.sin(2 * encoded),
                np.cos(3 * encoded),
                np.sin(3 * encoded),
                np.cos(4 * encoded),
                np.sin(4 * encoded),
                np.cos(5 * encoded),
                np.sin(5 * encoded),
            )
        ),
        dtype=np.float64,
    )


@dataclass(frozen=True)
class PhaseModel:
    """Two-node phase graph and fitted readout after fixed communication rounds."""

    params: FloatArray
    head: FloatArray
    fit_seconds: float
    communication_rounds: int = 3

    def phases(self, inputs: FloatArray) -> FloatArray:
        return _phase_evolve(inputs, self.params, self.communication_rounds)

    def code(self, inputs: FloatArray) -> FloatArray:
        return _phase_code(self.phases(inputs))

    def predict(self, inputs: FloatArray) -> FloatArray:
        return _predict(self.code(inputs), self.head)


def _fit_params(
    inputs: FloatArray,
    targets: FloatArray,
    initial: FloatArray,
    encoder: object,
    iterations: int,
) -> tuple[FloatArray, FloatArray, float]:
    if iterations < 0:
        raise ValueError("Iterations must be nonnegative")
    started = perf_counter()

    def objective(parameters: FloatArray) -> float:
        code = encoder(inputs, parameters)  # type: ignore[operator]
        head = _head(code, targets)
        return _squared_error(_predict(code, head), targets) + 1e-8 * float(parameters @ parameters)

    result = minimize(
        objective,
        initial,
        method="L-BFGS-B",
        options={"maxiter": iterations, "maxfun": max(1, iterations * (initial.size + 1))},
    )
    parameters = np.asarray(result.x, dtype=np.float64)
    head = _head(encoder(inputs, parameters), targets)  # type: ignore[operator]
    return parameters, head, perf_counter() - started


def fit_transformer(
    inputs: FloatArray, targets: FloatArray, *, seed: int = 24, iterations: int = 20
) -> TransformerModel:
    """Fit all nonlinear block parameters and the output head on training data."""
    initial = np.asarray(np.random.default_rng(seed).normal(0, 0.2, 100), dtype=np.float64)
    params, head, duration = _fit_params(inputs, targets, initial, _transformer_code, iterations)
    return TransformerModel(params, head, duration)


def fit_phase_network(
    inputs: FloatArray,
    targets: FloatArray,
    *,
    seed: int = 24,
    iterations: int = 30,
    rounds: int = 3,
) -> PhaseModel:
    """Fit the two local phase encoders and edge coupling on training data."""
    if rounds < 0:
        raise ValueError("Communication rounds must be nonnegative")
    initial = np.asarray(
        [0.3, 0.7, 1.1, 0.3, 0.7, 1.1, 0.2] + np.random.default_rng(seed).normal(0, 0.01, 7),
        dtype=np.float64,
    )

    def encoder(x: FloatArray, p: FloatArray) -> FloatArray:
        return _phase_code(_phase_evolve(x, p, rounds))

    params, head, duration = _fit_params(inputs, targets, initial, encoder, iterations)
    return PhaseModel(params, head, duration, rounds)


def _candidate_row(
    name: str,
    train_code: FloatArray,
    test_code: FloatArray,
    train_target: FloatArray,
    test_target: FloatArray,
    test_input: FloatArray,
    head: FloatArray,
    params: FloatArray,
    fit_seconds: float,
    rounds: int,
    causal_past: int,
    inference_ms_per_sample: float,
) -> dict[str, str | int | float | bool]:
    train_error = _squared_error(_predict(train_code, head), train_target)
    test_prediction = _predict(test_code, head)
    test_error = _squared_error(test_prediction, test_target)
    shift = max(1, len(train_code) // 8)
    shuffled = _squared_error(_predict(np.roll(train_code, shift, axis=0), head), train_target)
    incompatible_head = _head(train_code, np.roll(train_target, shift, axis=0))
    incompatible = _squared_error(_predict(test_code, incompatible_head), test_target)
    centered = train_code - train_code.mean(axis=0)
    singular = np.linalg.svd(centered, compute_uv=False)
    effective_rank = int(np.sum(singular > 1e-6 * singular[0])) if singular.size else 0
    shared_error = np.mean(
        (
            (test_prediction[:, 1] - test_input[:, 1]) ** 2
            + (test_prediction[:, 1] - test_input[:, 3]) ** 2
            + (test_prediction[:, 2] - test_input[:, 2]) ** 2
            + (test_prediction[:, 2] - test_input[:, 4]) ** 2
        )
        / 4
    )
    return {
        "candidate": name,
        "train_squared_error": train_error,
        "test_squared_error": test_error,
        "test_self_relation_error": float(
            np.mean((test_prediction[:, -1] - test_target[:, -1]) ** 2)
        ),
        "shared_content_error": float(shared_error),
        "shuffled_code_error": shuffled,
        "incompatible_decoder_error": incompatible,
        "effective_code_rank_tol_1e_6": effective_rank,
        "code_dimension": int(train_code.shape[1]),
        "parameter_count": int(params.size + head.size),
        "code_and_parameter_bytes": int(train_code.nbytes + params.nbytes + head.nbytes),
        "fit_seconds": fit_seconds,
        "inference_ms_per_sample": inference_ms_per_sample,
        "runtime_budget_seconds": 120.0,
        "within_budget": fit_seconds <= 120.0,
        "communication_rounds": rounds,
        "causal_past_tokens": causal_past,
        "output_scalars": int(train_target.shape[1]),
    }


def _intervention_scores(
    encode: Callable[[FloatArray], FloatArray],
    head: FloatArray,
    half: tuple[FloatArray, FloatArray],
    full: tuple[FloatArray, FloatArray],
) -> dict[str, float]:
    return {
        "intervention_error_d0p5": _squared_error(_predict(encode(half[0]), head), half[1]),
        "intervention_error_d1p0": _squared_error(_predict(encode(full[0]), head), full[1]),
    }


def _overlap_scores(
    encode: Callable[[FloatArray], FloatArray],
    head: FloatArray,
    half: tuple[FloatArray, FloatArray],
    full: tuple[FloatArray, FloatArray],
) -> dict[str, float]:
    return {
        "overlap_disagreement_error_d0p5": _squared_error(_predict(encode(half[0]), head), half[1]),
        "overlap_disagreement_error_d1p0": _squared_error(_predict(encode(full[0]), head), full[1]),
    }


def save_candidate_comparison(
    output: Path,
    *,
    repeats: int = 16,
    noise: float = 0.0,
    seed: int = 24,
    iterations: int = 20,
    split: Split = "parity",
) -> None:
    """Train and save linear, causal attention, and phase graph candidates."""
    task = build_task(repeats, noise, seed, split)
    half = intervention_set(task, distance=0.5, noise=noise, seed=seed + 1)
    full = intervention_set(task, distance=1.0, noise=noise, seed=seed + 2)
    overlap_half = overlap_disagreement_set(task, distance=0.5)
    overlap_full = overlap_disagreement_set(task, distance=1.0)
    transformer = fit_transformer(
        task.train_input, task.train_target, seed=seed, iterations=iterations
    )
    started = perf_counter()
    linear = fit_reduced_rank(task.train_input, task.train_target, 4)
    linear_fit_seconds = perf_counter() - started
    linear_head = np.vstack((linear.T, np.zeros((1, task.train_target.shape[1]))))
    started = perf_counter()
    linear_test_code = task.test_input
    _predict(linear_test_code, linear_head)
    linear_latency = 1000 * (perf_counter() - started) / len(linear_test_code)
    transformer_train_code = transformer.code(task.train_input)
    started = perf_counter()
    transformer_test_code = transformer.code(task.test_input)
    _predict(transformer_test_code, transformer.head)
    transformer_latency = 1000 * (perf_counter() - started) / len(transformer_test_code)
    rows = [
        _candidate_row(
            "linear_full",
            task.train_input,
            task.test_input,
            task.train_target,
            task.test_target,
            task.test_input,
            linear_head,
            np.empty(0),
            linear_fit_seconds,
            1,
            2,
            linear_latency,
        ),
        _candidate_row(
            "transformer",
            transformer_train_code,
            transformer_test_code,
            task.train_target,
            task.test_target,
            task.test_input,
            transformer.head,
            transformer.params,
            transformer.fit_seconds,
            1,
            2,
            transformer_latency,
        ),
    ]
    rows[0].update(_intervention_scores(lambda x: x, linear_head, half, full))
    rows[1].update(_intervention_scores(transformer.code, transformer.head, half, full))
    rows[0].update(_overlap_scores(lambda x: x, linear_head, overlap_half, overlap_full))
    rows[1].update(_overlap_scores(transformer.code, transformer.head, overlap_half, overlap_full))
    output.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        output / "dataset.npz",
        train_input=task.train_input,
        train_target=task.train_target,
        train_state=task.train_state,
        test_input=task.test_input,
        test_target=task.test_target,
        test_state=task.test_state,
        intervention_d0p5_input=half[0],
        intervention_d0p5_target=half[1],
        intervention_d1p0_input=full[0],
        intervention_d1p0_target=full[1],
        overlap_disagreement_d0p5_input=overlap_half[0],
        overlap_disagreement_d1p0_input=overlap_full[0],
    )
    np.savez_compressed(
        output / "transformer.npz",
        params=transformer.params,
        head=transformer.head,
        train_code=transformer_train_code,
        test_code=transformer_test_code,
    )
    np.savez_compressed(
        output / "linear_full.npz",
        head=linear_head,
        train_code=task.train_input,
        test_code=task.test_input,
    )
    phase_models: dict[int, PhaseModel] = {}
    for rounds in (0, 1, 3):
        phase = fit_phase_network(
            task.train_input,
            task.train_target,
            seed=seed,
            iterations=iterations,
            rounds=rounds,
        )
        phase_models[rounds] = phase
        train_code = phase.code(task.train_input)
        started = perf_counter()
        test_code = phase.code(task.test_input)
        _predict(test_code, phase.head)
        latency = 1000 * (perf_counter() - started) / len(test_code)
        name = "phase_network" if rounds == 3 else f"phase_round{rounds}"
        rows.append(
            _candidate_row(
                name,
                train_code,
                test_code,
                task.train_target,
                task.test_target,
                task.test_input,
                phase.head,
                phase.params,
                phase.fit_seconds,
                rounds,
                2 if rounds else 1,
                latency,
            )
        )
        rows[-1].update(_intervention_scores(phase.code, phase.head, half, full))
        rows[-1].update(_overlap_scores(phase.code, phase.head, overlap_half, overlap_full))
        np.savez_compressed(
            output / f"{name}.npz",
            params=phase.params,
            head=phase.head,
            train_code=train_code,
            test_code=test_code,
        )
    phase = phase_models[3]
    first = phase.phases(task.test_input[:1])
    opposite = phase.phases(-task.test_input[:1])
    order_difference = abs(abs(np.exp(1j * first).mean()) - abs(np.exp(1j * opposite).mean()))
    code_distance = float(np.linalg.norm(_phase_code(first) - _phase_code(opposite)))
    summary = {
        "source": "g24_candidates.py",
        "seed": seed,
        "repeats": repeats,
        "noise": noise,
        "train_family": "even_parity" if split == "parity" else "scene_equal",
        "test_family": "odd_parity" if split == "parity" else "scene_opposite",
        "phase_graph_edges": [[0, 1]],
        "transformer_query_key_dim": 1,
        "intervention_distances": [0.5, 1.0],
        "overlap_disagreement_distances": [0.5, 1.0],
        "phase_same_order_control": {
            "order_difference": float(order_difference),
            "code_distance": code_distance,
        },
        "candidates": rows,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
