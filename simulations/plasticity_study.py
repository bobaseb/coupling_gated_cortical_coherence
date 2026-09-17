"""Execute the bounded F5 design in tasks/f5_f6_design.md; never tune on alignment."""

from __future__ import annotations

import argparse
from dataclasses import asdict, replace
import hashlib
import json
from pathlib import Path
from time import perf_counter
from typing import Any

import numpy as np

from repo_root import REPO
from structural_resonance import (
    Array,
    Config,
    cluster_labels,
    partition_percentile,
    simulate,
)

ROOT = Path(__file__).resolve().parent / "figures" / "plasticity_study"
DESIGN = REPO / "tasks" / "f5_f6_design.md"
RATES = (0.01, 0.05, 0.2)
INTERVALS = (0.05, 0.5)
TUNING_SEED = 20260910
HELD_OUT_SEEDS = (20261910, 20262910, 20263910)
Row = dict[str, Any]


def physical_config(seed: int, rate: float, interval: float, dt: float) -> Config:
    """Refine integration while holding physical duration and update cadence fixed."""
    if min(dt, interval) <= 0:
        raise ValueError("dt and update interval must be positive")
    counts = (400.0 / dt, interval / dt)
    if any(abs(value - round(value)) > 1e-9 for value in counts):
        raise ValueError("Duration and update interval must be integral multiples of dt")
    return Config(
        seed=seed,
        learning_rate=rate,
        dt=dt,
        steps=round(counts[0]),
        update_every=round(counts[1]),
        sample_every=round(counts[1]),
    )


def quarter_means(result: dict[str, Array], name: str, duration: float) -> list[float]:
    """Both assessment windows are unions of complete, equally weighted intervals."""
    times = result["interval_time"]
    return [
        float(result[name][(times >= start * duration) & (times < stop * duration)].mean())
        for start, stop in ((0.5, 0.75), (0.75, 1.0))
    ]


def score_pair(result: dict[str, Array], frozen: dict[str, Array], config: Config) -> Row:
    duration = config.steps * config.dt
    objective = quarter_means(result, "interval_objective", duration)
    reference = quarter_means(frozen, "interval_objective", duration)
    order = quarter_means(result, "interval_order", duration)
    ratios = [value / base for value, base in zip(objective, reference, strict=True)]
    return {
        "quarter_objective": objective,
        "quarter_frozen_objective": reference,
        "quarter_objective_ratios": ratios,
        "quarter_order": order,
        "quarter_frozen_order": quarter_means(frozen, "interval_order", duration),
        "worst_objective_ratio": max(ratios),
        "objective_pass": max(ratios) <= 0.95,
        "coherence_pass": min(order) >= 0.8,
        "tail_alignment": float(np.mean(quarter_means(result, "interval_alignment", duration))),
        "frozen_alignment": float(np.mean(quarter_means(frozen, "interval_alignment", duration))),
    }


def select_candidate(records: list[Row]) -> tuple[float, float] | None:
    """Rank eligible cases on objective and coherence alone; alignment is never read."""
    ranked = [
        (row["worst_objective_ratio"], row["learning_rate"], row["update_interval"])
        for row in records
        if row["objective_pass"] and row["coherence_pass"]
    ]
    if not ranked:
        return None
    _, rate, interval = min(ranked)
    return float(rate), float(interval)


def alignment_score(result: dict[str, Array], config: Config, scored: Row) -> Row:
    percentile = partition_percentile(
        result["coupling_final"], cluster_labels(config.n), config.permutations, config.seed + 5
    )
    return {
        "blind_partition_percentile": percentile,
        "alignment_pass": scored["tail_alignment"] <= 0.8
        and scored["tail_alignment"] <= scored["frozen_alignment"] - 0.1
        and percentile <= 0.05,
        "post_update_tail_objective": float(
            result["dissipation"][result["time"] >= config.steps * config.dt / 2].mean()
        ),
    }


def trajectory(output: Path, config: Config, mode: str, started: float) -> dict[str, Array]:
    if perf_counter() - started > 1800:
        raise TimeoutError("F5 budget exhausted: study incomplete; do not expand the design")
    name = f"{config.seed}_{mode}_rate{config.learning_rate:g}_dt{config.dt:g}"
    name += f"_interval{config.update_every * config.dt:g}"
    tick = perf_counter()
    result = simulate(config, mode)
    np.savez_compressed(
        output / f"{name}.npz", allow_pickle=False, **result, config=json.dumps(asdict(config))
    )
    print(f"{name}: saved ({perf_counter() - tick:.1f}s)", flush=True)
    return result


def comparison(output: Path, config: Config, frozen: dict[str, Array], started: float) -> Row:
    result = trajectory(output, config, "gradient", started)
    scored = score_pair(result, frozen, config)
    scored.update(alignment_score(result, config, scored))
    scored.update(
        config=asdict(config),
        seed=config.seed,
        learning_rate=config.learning_rate,
        update_interval=config.update_every * config.dt,
        dt=config.dt,
    )
    scored["coexistence_pass"] = all(
        scored[key] for key in ("objective_pass", "coherence_pass", "alignment_pass")
    )
    print(json.dumps(scored, sort_keys=True), flush=True)
    return scored


def confirmations(output: Path, candidate: tuple[float, float], started: float) -> list[Row]:
    rate, interval = candidate
    records = []
    for seed in HELD_OUT_SEEDS:
        for dt in (0.01, 0.005):
            config = physical_config(seed, rate, interval, dt)
            frozen = trajectory(output, config, "frozen", started)
            records.append(comparison(output, config, frozen, started))
    return records


def tuning_runs(output: Path, smoke: bool, started: float) -> list[Row]:
    baseline = physical_config(TUNING_SEED, 0.0, 0.5, 0.01)
    if smoke:
        baseline = replace(baseline, n=12, steps=200, permutations=100)
    frozen = trajectory(output, baseline, "frozen", started)
    tuning = []
    for rate in (0.05,) if smoke else RATES:
        for interval in (0.5,) if smoke else INTERVALS:
            cadence = round(interval / baseline.dt)
            config = replace(
                baseline, learning_rate=rate, update_every=cadence, sample_every=cadence
            )
            tuning.append(comparison(output, config, frozen, started))
    return tuning


def run(output: Path, smoke: bool = False) -> Row:
    output.mkdir(parents=True, exist_ok=True)
    started = perf_counter()
    tuning = tuning_runs(output, smoke, started)
    candidate = select_candidate(tuning)
    held_out = confirmations(output, candidate, started) if candidate and not smoke else []
    summary: Row = {
        "status": "smoke" if smoke else "complete",
        "design_sha256": hashlib.sha256(DESIGN.read_bytes()).hexdigest(),
        "tuning_seed": TUNING_SEED,
        "held_out_seeds": list(HELD_OUT_SEEDS),
        "tuning": tuning,
        "selected_candidate": candidate,
        "confirmation": held_out,
        "confirmed": bool(held_out) and all(row["coexistence_pass"] for row in held_out),
        "trajectory_count": 1 + len(tuning) + 2 * len(held_out),
        "runtime_seconds": perf_counter() - started,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT)
    parser.add_argument("--smoke", action="store_true")
    args = parser.parse_args()
    run(args.output, args.smoke)


if __name__ == "__main__":
    main()
