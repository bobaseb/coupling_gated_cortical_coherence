"""Fast-tail and spike-threshold checks for the recorded-membrane rate mismatch.

This reads the original deposit without fitting a new twin. Its output is a
machine-readable diagnosis, separate from the production occupancy summary.
"""

from __future__ import annotations

import json
import math
import multiprocessing
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from typing import Any

import numpy as np
from numpy.typing import NDArray
from scipy.stats import spearmanr

import unity_recordings as ur

FloatArray = NDArray[np.float64]
SUMMARY = ur.OUTPUT / "recordings.json"
OUTPUT = ur.OUTPUT / "recording_diagnostics.json"


def fast_shape(samples: FloatArray) -> dict[str, float]:
    """Standardised skew and mass above three SD, relative to a Gaussian tail."""
    centred = samples - samples.mean()
    scaled = centred / centred.std()
    return {
        "skew": float(np.mean(scaled**3)),
        "upper_tail_ratio": float(np.mean(scaled > 3) / (math.erfc(3 / math.sqrt(2)) / 2)),
    }


def threshold_spread(thresholds: FloatArray) -> float:
    """Across-spike threshold standard deviation in millivolts."""
    return float(1000 * np.std(thresholds, ddof=1))


def slow_histogram(slow: FloatArray) -> list[list[float | int]]:
    """Empirical slow levels in quarter-millivolt bins, with sample counts."""
    levels, counts = np.unique(np.rint(slow * 4000).astype(np.int64), return_counts=True)
    return [[float(level / 4), int(count)] for level, count in zip(levels, counts, strict=True)]


def measure_cell(path: Path, rows: list[int]) -> dict[str, Any]:
    """Diagnostics for one cell, using the same detection and epoch cuts as U100."""
    deposit = ur.Deposit(path)
    pooled = {state: ur._Pooled([], []) for state in ur.STATES}
    thresholds: list[FloatArray] = []
    for row in rows:
        ur._pool_sweep(deposit, row, pooled, thresholds)
    result: dict[str, Any] = {"cell": deposit.text("Cell_ID", rows[0])}
    all_thresholds = np.concatenate(thresholds)
    result["threshold_sd_mv"] = threshold_spread(all_thresholds)
    result["states"] = {}
    for state, pool in pooled.items():
        if sum(map(len, pool.volts)) * ur.DT_MS < ur.MIN_STATE_MS:
            continue
        voltage = np.concatenate(pool.volts)
        failing = np.concatenate(pool.failing)
        smooth = ur._interpolated(voltage, failing)
        slow = ur._slow_part(smooth, pool.epochs(), ur.DT_MS, ur.SLOW_MS)
        fast = smooth - slow
        shape: dict[str, Any] = dict(fast_shape(fast[~failing]))
        shape["slow_sd_mv"] = float(1000 * np.std(slow))
        shape["slow_histogram"] = slow_histogram(slow)
        result["states"][state] = shape
    return result


def _worker(path: Path, rows: list[int]) -> dict[str, Any]:
    return measure_cell(path, rows)


def correlation(rows: list[dict[str, float]], key: str) -> float:
    """Rank correlation of a candidate cause with the twin/recorded rate ratio."""
    return float(spearmanr([r[key] for r in rows], [r["rate_ratio"] for r in rows]).statistic)


def _group_rows(path: Path, wanted: dict[str, Any]) -> dict[str, list[int]]:
    """Find deposit sweeps for saved cells."""
    deposit = ur.Deposit(path)
    by_cell: dict[str, list[int]] = {}
    for row in range(deposit.rows()):
        cell = deposit.text("Cell_ID", row)
        if cell in wanted:
            by_cell.setdefault(cell, []).append(row)
    return by_cell


def run(path: Path = ur.CACHE / Path(ur.DATA_MEMBER).name) -> dict[str, Any]:
    """Measure the cells present in the saved occupancy analysis."""
    saved = json.loads(SUMMARY.read_text())
    wanted = {c["cell"]: c for c in saved["cells"] if "quiet" in c.get("states", {})}
    by_cell = _group_rows(path, wanted)
    with ProcessPoolExecutor(4, mp_context=multiprocessing.get_context("spawn")) as pool:
        measured = list(pool.map(_worker, [path] * len(by_cell), by_cell.values()))
    joined = []
    for result in measured:
        quiet = result["states"].get("quiet")
        if quiet is None:
            continue
        original = wanted[result["cell"]]["states"]["quiet"]
        joined.append(
            {
                "cell": result["cell"],
                "type": wanted[result["cell"]]["type"],
                "rate_ratio": original["twin_rate_hz"] / original["rate_hz"],
                "threshold_sd_mv": result["threshold_sd_mv"],
                **quiet,
            }
        )
    keys = ("skew", "upper_tail_ratio", "threshold_sd_mv", "slow_sd_mv")
    excitatory = [row for row in joined if row["type"] == "EXC"]
    return {
        "source": str(SUMMARY.relative_to(ur.OUTPUT)),
        "cells": joined,
        "exc_spearman_with_rate_ratio": {k: correlation(excitatory, k) for k in keys},
    }


if __name__ == "__main__":
    OUTPUT.write_text(json.dumps(run(), indent=2) + "\n")
