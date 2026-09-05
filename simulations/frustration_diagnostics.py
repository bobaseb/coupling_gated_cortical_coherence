"""Predeclared S5 size/strength controls; compact cached outputs, no phase histories."""

from __future__ import annotations

import argparse
from dataclasses import asdict, replace
import json
from pathlib import Path
from typing import Any

import numpy as np

from geometric_frustration import Array, Config, ROOT, _leg, balanced_network, run

SEEDS = (20261905, 20262905, 20263905)


def order_statistics(leg: dict[str, Array], n: int) -> tuple[float, float]:
    """Return second-half mean r and N mean(r^2), without treating times as replicas."""
    tail = leg["order"][leg["time"] >= leg["time"][-1] / 2]
    return float(tail.mean()), float(n * np.square(tail).mean())


def baseline_controls(output: Path) -> None:
    records = []
    for n in (250, 500, 1000):
        for strength in (0.0, 1.0, 2.0, 4.0):
            for seed in SEEDS:
                config = Config(n=n, positive_sum=strength, seed=seed)
                path = output / f"N{n}_g{strength:g}_seed{seed}"
                path.mkdir(parents=True, exist_ok=True)
                matrix = balanced_network(n, config.probability, strength, seed)
                leg = _leg(config, matrix, 0, 0, path)
                mean, scaled = order_statistics(leg, n)
                records.append(
                    {
                        "config": asdict(config),
                        "mean_order": mean,
                        "scaled_second_moment": scaled,
                        "runtime_seconds": float(leg["runtime_seconds"]),
                    }
                )
                print(
                    f"N={n} g={strength:g} seed={seed}: r={mean:.5f}, N<r²>={scaled:.3f}",
                    flush=True,
                )
    (output / "summary.json").write_text(json.dumps(records, indent=2) + "\n")


def timestep_controls(output: Path) -> None:
    records: list[dict[str, Any]] = []
    for seed in SEEDS:
        for coupling in (1.6, 2.0, 2.4):
            for dt in (0.01, 0.005):
                config = Config(positive_sum=1, seed=seed)
                config = replace(config, dt=dt, steps=round(100 / dt), sample_every=round(0.1 / dt))
                path = output / f"seed{seed}_K{coupling:g}_dt{dt:g}"
                path.mkdir(parents=True, exist_ok=True)
                matrix = balanced_network(config.n, config.probability, 1, seed)
                leg = _leg(config, matrix, coupling / config.n, 0, path)
                mean, scaled = order_statistics(leg, config.n)
                records.append(
                    {
                        "config": asdict(config),
                        "coupling": coupling,
                        "mean_order": mean,
                        "scaled_second_moment": scaled,
                        "runtime_seconds": float(leg["runtime_seconds"]),
                    }
                )
                print(f"dt control seed={seed} K={coupling:g} dt={dt:g} r={mean:.5f}", flush=True)
    (output / "summary.json").write_text(json.dumps(records, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("baseline", "rescue", "timestep"))
    args = parser.parse_args()
    if args.mode == "baseline":
        baseline_controls(ROOT / "diagnostics")
    elif args.mode == "timestep":
        timestep_controls(ROOT / "timestep")
    else:
        for seed in SEEDS:
            run(Config(positive_sum=1, seed=seed), ROOT / f"weak_seed{seed}")


if __name__ == "__main__":
    main()
