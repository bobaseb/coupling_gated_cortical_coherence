"""Resume the N=8000 dynamic-ramp legs one at a time.

Each leg is checkpointed. The analysis command reads completed artifacts and
never starts a production sweep.
"""

from __future__ import annotations

import argparse

from dynamic_ramp import FIGURES, production_config, run_checkpointed

SPEEDS = (0.1, 0.02, 0.01, 0.005, 0.002, 0.001, 0.0002, 0.0001)


def run_speed(speed: float, seed: int = 20260903) -> None:
    """Resume one production leg at N=8000."""
    config = production_config(speed, seed, n_oscillators=8000)
    path = FIGURES / f"dynamic_ramp_N8000_v{speed:.0e}.npz"
    result = run_checkpointed(config, path, checkpoint_every=5000, report_progress=True)
    if result is None:
        raise RuntimeError(f"N=8000 ramp at v={speed:g} stopped before completion")
    print(f"completed N=8000 v={speed:g}: {len(result.time)} samples")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--speeds", nargs="+", type=float, choices=SPEEDS, default=SPEEDS)
    parser.add_argument("--seed", type=int, default=20260903)
    args = parser.parse_args()
    for speed in args.speeds:
        run_speed(speed, args.seed)


if __name__ == "__main__":
    main()
