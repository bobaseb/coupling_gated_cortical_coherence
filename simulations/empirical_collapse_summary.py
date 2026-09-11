"""Save reproducible summary statistics for the exploratory EEG analysis.

This command reads cached or public ds005620 recordings and writes compact
statistics for the manuscript.  It never runs a production simulation sweep.
`simulation_tex.py` is the only consumer of the saved JSON when it writes
publication macros.
"""

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np
from numpy.typing import NDArray

import empirical_collapse as collapse


ROOT = Path(__file__).resolve().parent
DEFAULT_OUTPUT = ROOT / "figures" / "empirical_collapse_summary.json"


def _residual(a_trace: np.ndarray, r_trace: np.ndarray) -> NDArray[np.float64]:
    predicted = np.array([collapse.bessel_ratio(a) for a in a_trace])
    return np.asarray(r_trace - predicted, dtype=np.float64)


def _load_bipolar(subject: str) -> tuple[np.ndarray, float]:
    old_subject = collapse.SUBJECT
    try:
        collapse.SUBJECT = subject
        data, fs = collapse.read_brainvision(
            "sed", "rest", 1, max_seconds=20.0, pad_seconds=collapse.PAD_SECONDS
        )
    finally:
        collapse.SUBJECT = old_subject
    return collapse.extract_phase_bipolar(data, fs, pad_seconds=collapse.PAD_SECONDS), fs


def _cross_subject_summary() -> dict[str, float | int]:
    subject_rows: list[tuple[float, float, np.ndarray]] = []
    for subject in collapse.MULTI_SUBJECTS:
        phase, _ = _load_bipolar(subject)
        a_trace, r_trace = collapse.compute_ar_trace(phase)
        subject_rows.append(
            (float(np.nanmean(a_trace)), float(np.nanmean(r_trace)), _residual(a_trace, r_trace))
        )
    means_a = np.array([row[0] for row in subject_rows])
    means_r = np.array([row[1] for row in subject_rows])
    residual = np.concatenate([row[2] for row in subject_rows])
    return {
        "count": len(subject_rows),
        "a_mean": float(np.mean(means_a)),
        "a_min": float(np.min(means_a)),
        "a_max": float(np.max(means_a)),
        "r_mean": float(np.mean(means_r)),
        "r_min": float(np.min(means_r)),
        "r_max": float(np.max(means_r)),
        "residual_mean": float(np.mean(residual)),
        "residual_rmse": float(np.sqrt(np.mean(residual**2))),
        "residual_abs_max": float(np.max(np.abs(residual))),
    }


def _band_summary(phase_data: np.ndarray, fs: float) -> dict[str, float]:
    results: dict[str, float] = {}
    for band, (low, high) in collapse.BANDS.items():
        phase = collapse.extract_phase_bipolar(
            phase_data, fs, low, high, pad_seconds=collapse.PAD_SECONDS
        )
        a_trace, r_trace = collapse.compute_ar_trace(phase)
        results[band] = float(np.nanmean(_residual(a_trace, r_trace)))
    return results


def _small_sample_calibration() -> dict[str, float | int]:
    samples = 100
    replicas = 500
    concentration = 2.0
    rng = np.random.default_rng(20260911)
    draws = [rng.vonmises(0.0, concentration, samples) for _ in range(replicas)]
    estimates = np.array(
        [(collapse.concentration_a(draw), collapse.order_parameter_r(draw)) for draw in draws]
    )
    residual = estimates[:, 1] - np.array([collapse.bessel_ratio(a) for a in estimates[:, 0]])
    return {
        "samples": samples,
        "replicas": replicas,
        "concentration": concentration,
        "a_mean": float(np.mean(estimates[:, 0])),
        "residual_mean": float(np.mean(residual)),
        "residual_sd": float(np.std(residual)),
    }


def build_summary() -> dict[str, Any]:
    """Recompute every exploratory EEG statistic reported by the manuscript."""
    phase, fs = _load_bipolar("1016")
    window_rows = collapse.compute_window_sensitivity(phase, fs)
    collapse.make_window_sensitivity_figure(window_rows)
    return {
        "source": "empirical_collapse_summary.py",
        "dataset": "OpenNeuro ds005620",
        "configuration": {
            "subject": "1016",
            "task": "sed",
            "acquisition": "rest",
            "run": 1,
            "duration_seconds": 20.0,
            "padding_seconds": collapse.PAD_SECONDS,
            "montage": "adjacent bipolar pairs",
            "pooling_window_ms": 100,
        },
        "cross_subject": _cross_subject_summary(),
        "bands": _band_summary(
            collapse.read_brainvision(
                "sed", "rest", 1, max_seconds=20.0, pad_seconds=collapse.PAD_SECONDS
            )[0],
            fs,
        ),
        "window_sensitivity": [row.__dict__ for row in window_rows],
        "small_sample_calibration": _small_sample_calibration(),
    }


def main() -> None:
    """Write the compact summary, without regenerating publication macros."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    contents = json.dumps(build_summary(), indent=2, sort_keys=True) + "\n"
    args.output.write_text(contents, encoding="utf-8")
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
