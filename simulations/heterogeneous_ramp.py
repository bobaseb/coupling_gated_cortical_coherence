"""Run or analyze quenched Lorentzian-frequency ramp controls.

Analysis reads completed checkpoint files and never starts a simulation.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import TypeAlias

import numpy as np

from dynamic_ramp import FIGURES, production_config_heterogeneous, run_checkpointed
from dynamic_ramp_analysis import (
    bootstrap_delay_exponent,
    fit_power_law,
    replica_escape_couplings,
)

SPEEDS = (0.1, 0.01, 0.001, 0.0001)
HALFWIDTHS = (0.5, 1.0, 1.5)
OUTPUT_DIR = FIGURES / "hetero"


HeterogeneousSummary: TypeAlias = dict[str, bool | int | float | list[float] | None]


def _path(output_dir: Path, speed: float, gamma: float, n_oscillators: int) -> Path:
    return output_dir / f"hetero_N{n_oscillators}_v{speed:.0e}_g{gamma:.1f}.npz"


def _seed(speed: float, gamma: float, seed_base: int) -> int:
    return seed_base + int(speed * 1e5) + int(gamma * 10)


def read_completed_leg(
    path: Path, *, n_oscillators: int, gamma: float
) -> tuple[np.ndarray, np.ndarray, float] | None:
    """Reject absent, partial, and smoke-run checkpoints."""
    if not path.exists():
        return None
    with np.load(path, allow_pickle=False) as saved:
        config = json.loads(str(saved["config"]))
        steps = round(2 * config["coupling_half_window"] / config["ramp_speed"] / config["dt"])
        if (
            int(saved["step"]) != steps
            or config["n_oscillators"] != n_oscillators
            or config.get("frequency_halfwidth") != gamma
            or config["n_replicas"] != 32
        ):
            return None
        critical = 2.0 * (config["diffusion"] + gamma)
        return np.asarray(saved["coupling"]), np.asarray(saved["order_replicas"]), critical


def summarize_halfwidth(
    gamma: float,
    *,
    output_dir: Path = OUTPUT_DIR,
    speeds: tuple[float, ...] = SPEEDS,
    n_oscillators: int = 2000,
    n_boot: int = 10_000,
) -> HeterogeneousSummary:
    fit_speeds: list[float] = []
    replica_delays: list[np.ndarray] = []
    missing: list[float] = []
    n_artifacts = 0
    for speed in speeds:
        leg = read_completed_leg(
            _path(output_dir, speed, gamma, n_oscillators),
            n_oscillators=n_oscillators,
            gamma=gamma,
        )
        if leg is None:
            missing.append(speed)
            continue
        n_artifacts += 1
        coupling, order, critical = leg
        escape = replica_escape_couplings(
            coupling, order, level=0.2, sustain=3, critical_coupling=critical
        )
        delays = escape - critical
        if np.all(np.isfinite(delays)) and float(np.mean(delays)) > 0:
            fit_speeds.append(speed)
            replica_delays.append(delays)

    result: HeterogeneousSummary = {
        "complete": not missing,
        "n_artifacts": n_artifacts,
        "n_fit_legs": len(fit_speeds),
        "missing_speeds": missing,
        "fit_speeds": fit_speeds,
        "exponent": None,
        "exponent_low": None,
        "exponent_high": None,
        "bootstrap_low": None,
        "bootstrap_high": None,
        "zero_delay_resamples": None,
    }
    if len(fit_speeds) >= 3:
        x = np.asarray(fit_speeds)
        means = np.asarray([float(np.mean(delays)) for delays in replica_delays])
        fit = fit_power_law(x, means)
        boot = bootstrap_delay_exponent(x, replica_delays, n_boot=n_boot)
        result["exponent"] = fit.exponent
        result["exponent_low"] = fit.exponent_low
        result["exponent_high"] = fit.exponent_high
        result["bootstrap_low"] = boot.ci_low
        result["bootstrap_high"] = boot.ci_high
        result["zero_delay_resamples"] = boot.n_invalid
    return result


def run_leg(speed: float, gamma: float, n_oscillators: int = 2000) -> None:
    """Run or resume a single production checkpoint."""
    config = production_config_heterogeneous(
        speed, _seed(speed, gamma, 42), gamma, n_oscillators=n_oscillators
    )
    path = _path(OUTPUT_DIR, speed, gamma, n_oscillators)
    result = run_checkpointed(config, path, checkpoint_every=5000, report_progress=True)
    if result is None:
        raise RuntimeError(f"heterogeneous ramp v={speed:g}, gamma={gamma:g} did not finish")
    print(f"completed v={speed:g}, gamma={gamma:g}: {len(result.time)} samples")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true", help="run selected production legs")
    parser.add_argument("--speeds", nargs="+", type=float, choices=SPEEDS, default=SPEEDS)
    parser.add_argument(
        "--halfwidths", nargs="+", type=float, choices=HALFWIDTHS, default=HALFWIDTHS
    )
    args = parser.parse_args()
    if args.run:
        for gamma in args.halfwidths:
            for speed in args.speeds:
                run_leg(speed, gamma)
        return
    summary = {str(gamma): summarize_halfwidth(gamma) for gamma in HALFWIDTHS}
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    path = OUTPUT_DIR / "hetero_summary.json"
    path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
