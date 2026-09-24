"""Compare delay exponents at two escape levels and oscillator counts.

Only completed checkpoint files are read. This command never runs a sweep.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import TypeAlias

import numpy as np

from dynamic_ramp import FIGURES
from dynamic_ramp_analysis import (
    bootstrap_delay_exponent,
    fit_power_law,
    replica_escape_couplings,
)

SPEEDS = (0.1, 0.02, 0.01, 0.005, 0.002, 0.001, 0.0002, 0.0001)

MATCHED_SPEEDS = (0.01, 0.005, 0.002, 0.001, 0.0002, 0.0001)


ExponentSummary: TypeAlias = dict[str, bool | int | float | list[float] | None]


def fit_diagnostics(speeds: np.ndarray, delays: np.ndarray) -> dict[str, float | list[float]]:
    """Inspect log-fit residuals and sensitivity to any one speed leg."""
    if speeds.shape != delays.shape or speeds.size < 3:
        raise ValueError("Fit diagnostics require at least three matched speed legs")
    fit = fit_power_law(speeds, delays)
    residuals = np.log(delays) - np.log(fit.prefactor * speeds**fit.exponent)
    slopes = [
        fit_power_law(
            speeds[np.arange(speeds.size) != index], delays[np.arange(delays.size) != index]
        ).exponent
        for index in range(speeds.size)
    ]
    return {
        "log_residuals": residuals.tolist(),
        "rms_log_residual": float(np.sqrt(np.mean(residuals**2))),
        "leave_one_out_exponents": slopes,
    }


def _path(n_oscillators: int, speed: float, figure_dir: Path) -> Path:
    stem = "dynamic_ramp_replicas" if n_oscillators == 2000 else f"dynamic_ramp_N{n_oscillators}"
    return figure_dir / f"{stem}_v{speed:.0e}.npz"


def _read_completed(path: Path) -> tuple[np.ndarray, np.ndarray, float] | None:
    if not path.exists():
        return None
    with np.load(path, allow_pickle=False) as saved:
        config = json.loads(str(saved["config"]))
        steps = round(2 * config["coupling_half_window"] / config["ramp_speed"] / config["dt"])
        if int(saved["step"]) != steps:
            return None
        critical = 2.0 * (config["diffusion"] + config.get("frequency_halfwidth", 0.0))
        return np.asarray(saved["coupling"]), np.asarray(saved["order_replicas"]), critical


def compute_exponent(
    n_oscillators: int,
    level: float,
    *,
    figure_dir: Path = FIGURES,
    speeds: tuple[float, ...] = SPEEDS,
    matched_speeds_subset: tuple[float, ...] = MATCHED_SPEEDS,
    n_boot: int = 10_000,
) -> ExponentSummary:
    """Fit uncensored legs and disclose any missing production artifacts."""
    fit_speeds: list[float] = []
    replica_delays: list[np.ndarray] = []
    missing: list[float] = []
    artifact_count = 0
    largest_precritical_order = 0.0
    largest_coupling_step = 0.0
    largest_initial_order = 0.0
    censored_replicas = 0
    precritical_max_by_speed: list[float] = []
    censored_count_by_speed: list[float] = []
    for speed in speeds:
        leg = _read_completed(_path(n_oscillators, speed, figure_dir))
        if leg is None:
            missing.append(speed)
            continue
        artifact_count += 1
        coupling, order, critical = leg
        largest_precritical_order = max(
            largest_precritical_order, float(np.max(order[coupling < critical]))
        )
        precritical_max_by_speed.append(float(np.max(order[coupling < critical])))
        largest_coupling_step = max(largest_coupling_step, float(np.max(np.diff(coupling))))
        largest_initial_order = max(largest_initial_order, float(np.max(order[0])))
        escape = replica_escape_couplings(
            coupling, order, level=level, sustain=3, critical_coupling=critical
        )
        delays = escape - critical
        censored_replicas += int(np.sum(~np.isfinite(delays)))
        censored_count_by_speed.append(float(np.sum(~np.isfinite(delays))))
        if np.all(np.isfinite(delays)) and float(np.mean(delays)) > 0:
            fit_speeds.append(speed)
            replica_delays.append(delays)

    result: ExponentSummary = {
        "complete": not missing,
        "n_artifacts": artifact_count,
        "n_fit_legs": len(fit_speeds),
        "fit_speeds": fit_speeds,
        "missing_speeds": missing,
        "exponent_ols": None,
        "exponent_ols_low": None,
        "exponent_ols_high": None,
        "exponent_boot_low": None,
        "exponent_boot_high": None,
        "p_above_05": None,
        "zero_delay_resamples": None,
        "matched_exponent_ols": None,
        "fit_log_residuals": None,
        "rms_log_residual": None,
        "leave_one_out_exponents": None,
        "largest_precritical_order": largest_precritical_order,
        "largest_coupling_step": largest_coupling_step,
        "largest_initial_order": largest_initial_order,
        "censored_replicas": censored_replicas,
        "precritical_max_by_speed": precritical_max_by_speed,
        "censored_count_by_speed": censored_count_by_speed,
    }
    if len(fit_speeds) >= 3:
        x = np.asarray(fit_speeds)
        y = np.asarray([float(np.mean(delays)) for delays in replica_delays])
        ols = fit_power_law(x, y)
        boot = bootstrap_delay_exponent(x, replica_delays, n_boot=n_boot)
        result["exponent_ols"] = ols.exponent
        result["exponent_ols_low"] = ols.exponent_low
        result["exponent_ols_high"] = ols.exponent_high
        result["exponent_boot_low"] = boot.ci_low
        result["exponent_boot_high"] = boot.ci_high
        result["p_above_05"] = boot.p_above
        result["zero_delay_resamples"] = boot.n_invalid
        diagnostics = fit_diagnostics(x, y)
        result["fit_log_residuals"] = diagnostics["log_residuals"]
        result["rms_log_residual"] = diagnostics["rms_log_residual"]
        result["leave_one_out_exponents"] = diagnostics["leave_one_out_exponents"]

        # Compute matched exponent
        matched_indices = [i for i, v in enumerate(fit_speeds) if v in matched_speeds_subset]
        if len(matched_indices) >= 3:
            matched_x = x[matched_indices]
            matched_y = y[matched_indices]
            matched_ols = fit_power_law(matched_x, matched_y)
            result["matched_exponent_ols"] = matched_ols.exponent

    return result


def main() -> None:
    summary = {
        "N2000_r0.20": compute_exponent(2000, 0.20),
        "N2000_r0.05": compute_exponent(2000, 0.05),
        "N8000_r0.05": compute_exponent(8000, 0.05),
    }
    path = FIGURES / "tighter_threshold_summary.json"
    path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
