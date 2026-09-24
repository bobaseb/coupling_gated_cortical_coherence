#!/usr/bin/env python3
import multiprocessing
import subprocess  # nosec B404
import sys

SPEEDS = (0.1, 0.02, 0.01, 0.005, 0.002, 0.001, 0.0002, 0.0001)


def run_speed(speed: float) -> None:
    print(f"Starting N=8000, v={speed}")
    subprocess.run(  # noqa: S603  # nosec B603
        [
            sys.executable,
            "dynamic_ramp.py",
            "--n-oscillators",
            "8000",
            "--speed",
            str(speed),
        ],
        check=True,
    )
    print(f"Finished N=8000, v={speed}")


def main() -> None:
    with multiprocessing.Pool(min(8, multiprocessing.cpu_count())) as pool:
        pool.map(run_speed, SPEEDS)


if __name__ == "__main__":
    main()
