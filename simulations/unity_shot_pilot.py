"""Rate-only screening of a sparse-jump twin from saved cell summaries.

The slow levels use quarter-millivolt histograms from the original paths.
This screening cannot replace the original paths or determine passing states.
The jump rate is fixed before looking at firing rates; its scale comes only
from an unthresholded stationary-skew approximation to the measured fast skew.
A second jump input takes both its rate and scale from the fast skew and
three-SD tail excess, again without spike counts.
"""

from __future__ import annotations

import json
import math
from typing import Any

import numpy as np
from numpy.polynomial.hermite import hermgauss

import unity_occupancy as uo
import unity_recording_diagnostics as diag
import unity_recordings as ur
from unity_shot import ShotInput, stationary_rate, two_moment

RATE_PER_MS = 0.01
OUTPUT = ur.OUTPUT / "shot_pilot.json"


def threshold_rate(grid: uo.Grid, membrane: uo.Membrane, dt_ms: float, spread: float) -> float:
    """Static Gaussian threshold heterogeneity at its measured across-spike SD."""
    nodes, weights = hermgauss(3)
    total = 0.0
    for node, weight in zip(nodes, weights, strict=True):
        offset = math.sqrt(2) * spread * node
        shifted = uo.Membrane(
            membrane.tau_ms,
            membrane.mean - offset,
            membrane.reset - offset,
            membrane.refractory_ms,
        )
        total += float(weight) * uo.stationary(grid, shifted, dt_ms)[2]
    return total / math.sqrt(math.pi)


def predict(
    state: dict[str, float], shape: dict[str, Any], threshold_mv: float
) -> tuple[float, float, float, float]:
    """OU, jump, threshold-mixture and two-moment jump rates under empirical slow levels."""
    tau = state["tau_ms"]
    scale = (max(shape["skew"], 0) / (2 * RATE_PER_MS * tau)) ** (1 / 3)
    matched, _ = two_moment(shape["skew"], shape["upper_tail_ratio"], tau)
    low = -max(8, math.ceil(state["distance"] + 8))
    grid = uo.Grid(low, ur.GRID_STEP)
    histogram = shape["slow_histogram"]
    total = sum(count for _, count in histogram)
    levels = np.array([(level - threshold_mv) / state["sigma_mv"] for level, _ in histogram])
    fit = ur.Calibration(grid, state["sigma_mv"] / 1000, tau)
    model_means = ur.twin_means(fit, levels, ur.DT_MS)
    by_mean: dict[float, int] = {}
    for mean, (_, count) in zip(model_means, histogram, strict=True):
        rounded = min(-0.2, round(mean / ur.MEAN_STEP) * ur.MEAN_STEP)
        by_mean[rounded] = by_mean.get(rounded, 0) + count
    original = changed = threshold = both = 0.0
    threshold_sd = shape["threshold_sd_mv"] / state["sigma_mv"]
    for mean, count in by_mean.items():
        weight = count / total
        membrane = uo.Membrane(tau, mean, mean, uo.REFRACTORY_MS)
        original += weight * uo.stationary(grid, membrane, ur.DT_MS)[2]
        changed += weight * stationary_rate(grid, membrane, ur.DT_MS, ShotInput(RATE_PER_MS, scale))
        threshold += weight * threshold_rate(grid, membrane, ur.DT_MS, threshold_sd)
        both += weight * stationary_rate(grid, membrane, ur.DT_MS, matched)
    return original, changed, threshold, both


def run() -> dict[str, Any]:
    """Screen the 86 quiet excitatory cells without using their rates as fit targets."""
    saved = json.loads(diag.SUMMARY.read_text())
    shapes = json.loads(diag.OUTPUT.read_text())
    by_cell = {row["cell"]: row for row in shapes["cells"] if row["type"] == "EXC"}
    rows = []
    for cell in saved["cells"]:
        if cell["type"] != "EXC" or "quiet" not in cell.get("states", {}):
            continue
        state = cell["states"]["quiet"]
        shape = by_cell[cell["cell"]]
        baseline, changed, threshold, both = predict(state, shape, cell["threshold_mv"])
        _, reachable = two_moment(shape["skew"], shape["upper_tail_ratio"], state["tau_ms"])
        rows.append(
            {
                "cell": cell["cell"],
                "recorded_hz": state["rate_hz"],
                "saved_ou_hz": state["twin_rate_hz"],
                "pilot_ou_hz": baseline,
                "pilot_shot_hz": changed,
                "pilot_threshold_hz": threshold,
                "pilot_two_moment_hz": both,
                "two_moment_tail_reachable": reachable,
            }
        )
    return {"jump_rate_per_ms": RATE_PER_MS, "cells": rows}


if __name__ == "__main__":
    OUTPUT.write_text(json.dumps(run(), indent=2) + "\n")
