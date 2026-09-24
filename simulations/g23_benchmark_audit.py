"""Recompute held-out G23 episode scores from saved arrays without dynamics."""

import json
from pathlib import Path
from typing import Any, cast

import numpy as np
from numpy.typing import NDArray

from g23_benchmark import fit_readout

IntArray = NDArray[np.int64]


def _episodes(path: Path) -> tuple[IntArray, IntArray, IntArray]:
    with np.load(path, allow_pickle=False) as saved:
        phase = np.asarray(saved["phase"], dtype=np.int64)
        register = np.asarray(saved["register"], dtype=np.int64)
        next_phase = np.asarray(saved["next_phase"], dtype=np.int64)
    if phase.ndim != 1 or phase.size == 0 or phase.shape != register.shape:
        raise ValueError("Invalid saved episode shapes")
    if next_phase.shape != phase.shape:
        raise ValueError("Invalid saved episode shapes")
    if not all(np.isin(value, (0, 1)).all() for value in (phase, register, next_phase)):
        raise ValueError("Saved episode states must be binary")
    return phase, register, next_phase


def audit_benchmark(output: Path) -> None:
    """Fail if the frozen readout or any sampled held-out score has drifted."""
    summary = cast(dict[str, Any], json.loads((output / "summary.json").read_text()))
    _, train_register, train_next = _episodes(output / "training_episodes.npz")
    readout = fit_readout(train_register, train_next)
    if readout.tolist() != summary["trained_readout"]:
        raise ValueError("Training readout drift")
    rows: list[dict[str, str | float]] = []
    for row in summary["rows"]:
        family, control = str(row["family"]), str(row["control"])
        phase, register, next_phase = _episodes(output / f"{family}_{control}.npz")
        prediction = readout[register]
        accuracy = float(np.mean(prediction == next_phase))
        agreement = float(np.mean(phase == register))
        reconstruction = float(np.mean((phase - prediction) ** 2))
        if (
            not np.isclose(accuracy, row["heldout_accuracy"], atol=1e-12)
            or not np.isclose(agreement, row["shared_content_agreement_proxy"], atol=1e-12)
            or not np.isclose(reconstruction, row["phase_reconstruction_error"], atol=1e-12)
        ):
            raise ValueError(f"{family}/{control} held-out score drift")
        rows.append(
            {
                "family": family,
                "control": control,
                "heldout_accuracy": accuracy,
                "shared_content_agreement_proxy": agreement,
                "phase_reconstruction_error": reconstruction,
            }
        )
    audit = {"source": "g23_benchmark_audit.py", "trained_readout": readout.tolist(), "rows": rows}
    (output / "audit.json").write_text(json.dumps(audit, indent=2) + "\n")
