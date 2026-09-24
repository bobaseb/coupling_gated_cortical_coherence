"""Pass constructed signals through the exploratory EEG pipeline.

The reported statistic pools bipolar Hilbert phases over 61 pairs and 100 ms
without removing their common rotation. This module builds signals whose
instantaneous spatial coherence is known and reads them through the same
filter, Hilbert transform, bipolar montage and 100 ms bins
(`empirical_collapse.extract_phase_bipolar`, `compute_ar_trace`). It compares
the pooled estimand with the instantaneous spatial resultant of the raw channels
and of the bipolar pairs, and with the pooled distribution after each sample is
centred on its circular mean.

The command writes a compact summary and nothing else. It reads no recording
and runs no production sweep; `simulation_tex.py` reads the saved JSON.
"""

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

import numpy as np
from numpy.typing import NDArray

import empirical_collapse as collapse

ROOT = Path(__file__).resolve().parent
DEFAULT_OUTPUT = ROOT / "figures" / "eeg_pipeline_check" / "eeg_pipeline_check_summary.json"

FS = 5000.0
PAD_SECONDS = collapse.PAD_SECONDS
N_CHANNELS = 62
SEED = 20260924

FloatArray = NDArray[np.float64]


def _time(seconds: float) -> FloatArray:
    """Sample times for a block plus the pipeline's padding on each side."""
    n = int(round((seconds + 2.0 * PAD_SECONDS) * FS))
    return np.arange(n, dtype=float) / FS


def locked_rotation(seconds: float, freq: float) -> FloatArray:
    """Every channel at one phase, with amplitude falling along the montage.

    Falling amplitudes keep each adjacent difference nonzero and of one sign, so
    the bipolar pairs are exactly phase-locked as well.
    """
    t = _time(seconds)
    amplitudes = np.linspace(2.0, 1.0, N_CHANNELS)[:, None]
    return np.asarray(amplitudes * np.sin(2.0 * np.pi * freq * t)[None, :], dtype=float)


def noisy_field(
    seconds: float, freq: float, kappa: float, noise_sd: float, rng: np.random.Generator
) -> FloatArray:
    """A rotating field with fixed von Mises spatial offsets and white noise."""
    t = _time(seconds)
    offsets = rng.vonmises(0.0, kappa, size=N_CHANNELS)[:, None]
    amplitudes = np.linspace(2.0, 1.0, N_CHANNELS)[:, None]
    clean = amplitudes * np.sin(2.0 * np.pi * freq * t[None, :] + offsets)
    return np.asarray(clean + noise_sd * rng.standard_normal(clean.shape), dtype=float)


def instantaneous_order(phase: FloatArray, width: int) -> FloatArray:
    """Per-bin mean of the spatial resultant length at each sample."""
    spatial = np.abs(np.mean(np.exp(1j * phase), axis=0))
    n_bins = phase.shape[1] // width
    return np.asarray(spatial[: n_bins * width].reshape(n_bins, width).mean(axis=1), dtype=float)


def centred_phase(phase: FloatArray) -> FloatArray:
    """Phases measured from their circular mean at the same sample."""
    mean = np.angle(np.mean(np.exp(1j * phase), axis=0))
    return np.asarray(np.angle(np.exp(1j * (phase - mean[None, :]))), dtype=float)


def quadratic_variation_rate(data: FloatArray, step: int) -> float:
    """Squared increments of unwrapped bipolar phase per second, drift removed.

    For an Ito phase with diffusion D the rate is 2D at every step. A band-limited
    analytic phase is smooth below its correlation time, so its rate depends on
    the sampling step.
    """
    phase = collapse.extract_phase_bipolar(data, FS, pad_seconds=PAD_SECONDS)
    increments = np.diff(np.unwrap(phase, axis=1)[:, ::step], axis=1)
    detrended = increments - increments.mean(axis=1, keepdims=True)
    return float(np.mean(detrended**2) * FS / step)


@dataclass(frozen=True)
class PipelineRow:
    """One constructed signal read through the reported and centred estimands.

    The centred estimand reports only its resultant: the log-density estimator
    is not defined for the degenerate distribution a locked signal centres to.
    """

    case: str
    raw_instantaneous_r: float
    instantaneous_r: float
    pooled_r: float
    pooled_a: float
    pooled_residual: float
    centred_r: float


def _mean_residual(a_trace: FloatArray, r_trace: FloatArray) -> float:
    predicted = np.array([collapse.bessel_ratio(float(a)) for a in a_trace])
    return float(np.nanmean(r_trace - predicted))


def evaluate(case: str, data: FloatArray) -> PipelineRow:
    """Read one signal through the pipeline and through its centred variant."""
    phase = collapse.extract_phase_bipolar(data, FS, pad_seconds=PAD_SECONDS)
    raw = collapse.extract_phase(data, FS, pad_seconds=PAD_SECONDS)[:N_CHANNELS]
    width = collapse.DECIMATE_FACTOR
    a_pooled, r_pooled = collapse.compute_ar_trace(phase, decimate=width)
    _, r_centred = collapse.compute_ar_trace(centred_phase(phase), decimate=width)
    return PipelineRow(
        case=case,
        raw_instantaneous_r=float(np.mean(instantaneous_order(raw, width))),
        instantaneous_r=float(np.mean(instantaneous_order(phase, width))),
        pooled_r=float(np.nanmean(r_pooled)),
        pooled_a=float(np.nanmean(a_pooled)),
        pooled_residual=_mean_residual(a_pooled, r_pooled),
        centred_r=float(np.nanmean(r_centred)),
    )


def build_summary(seconds: float = 2.0) -> dict[str, Any]:
    """Evaluate a locked rotation and noisy fields at alpha frequency."""
    rng = np.random.default_rng(SEED)
    rows = [evaluate("locked_rotation", locked_rotation(seconds, 10.0))]
    for kappa in (1.0, 4.0):
        field = noisy_field(seconds, 10.0, kappa, noise_sd=0.5, rng=rng)
        rows.append(evaluate(f"noisy_field_kappa_{kappa:g}", field))
    qv_field = noisy_field(seconds, 10.0, 4.0, noise_sd=0.5, rng=rng)
    steps = (1, 10, 100)
    return {
        "source": "eeg_pipeline_check.py",
        "seed": SEED,
        "seconds": seconds,
        "frequency_hz": 10.0,
        "noise_sd": 0.5,
        "rows": [asdict(row) for row in rows],
        "quadratic_variation_rate": {
            str(step): quadratic_variation_rate(qv_field, step) for step in steps
        },
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
