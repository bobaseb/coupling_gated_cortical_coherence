"""Read saved two-frequency G22 paths without executing the density solver."""

import json
from pathlib import Path

import numpy as np

SummaryRow = dict[str, str | int | float]


def _required(files: list[str]) -> None:
    names = {
        "time",
        "density",
        "current",
        "order",
        "accumulated_marginal_cost",
        "accumulated_cohort_cost",
        "endpoint_bound",
        "spacing",
        "cells",
        "duration",
        "diffusion",
        "spread",
        "initial_order",
        "schedule",
    }
    if not names.issubset(files):
        raise ValueError("Incomplete heterogeneous G22 artifact")


def _validate_paths(
    time: np.ndarray,
    density: np.ndarray,
    current: np.ndarray,
    order: np.ndarray,
    marginal: np.ndarray,
    cohort: np.ndarray,
    cells: int,
    spacing: float,
) -> float:
    if density.shape != (time.size, 2, cells) or current.shape != density.shape:
        raise ValueError("Inconsistent heterogeneous G22 path shapes")
    if any(vector.shape != time.shape for vector in (order, marginal, cohort)):
        raise ValueError("Inconsistent heterogeneous G22 time series")
    vectors = (time, density, current, order, marginal, cohort)
    if not all(np.isfinite(vector).all() for vector in vectors):
        raise ValueError("Nonfinite heterogeneous G22 path")
    mass_error = float(np.max(np.abs(density.sum(axis=2) * spacing - 1)))
    if density.min() <= 0 or mass_error > 1e-8:
        raise ValueError("Heterogeneous G22 densities must be positive and normalized")
    if not np.all(np.diff(time) > 0):
        raise ValueError("Heterogeneous G22 times must increase")
    return mass_error


def _validate_current_path(
    time: np.ndarray,
    density: np.ndarray,
    current: np.ndarray,
    marginal: np.ndarray,
    cohort: np.ndarray,
    spacing: float,
    diffusion: float,
) -> None:
    step = np.diff(time)
    expected_density = (
        density[:-1]
        - step[:, None, None] * (current[:-1] - np.roll(current[:-1], 1, axis=2)) / spacing
    )
    if not np.allclose(density[1:], expected_density, rtol=1e-9, atol=1e-10):
        raise ValueError("Heterogeneous G22 discrete continuity failed")
    edge_density = (density + np.roll(density, -1, axis=2)) / 2
    aggregate_density = edge_density.mean(axis=1)
    aggregate_current = current.mean(axis=1)
    marginal_rate = spacing * np.sum(aggregate_current**2 / (diffusion * aggregate_density), axis=1)
    cohort_rate = spacing * np.mean(np.sum(current**2 / (diffusion * edge_density), axis=2), axis=1)
    for saved, rate in ((marginal, marginal_rate), (cohort, cohort_rate)):
        expected = np.concatenate(([0.0], np.cumsum(step * (rate[:-1] + rate[1:]) / 2)))
        if not np.allclose(saved, expected, rtol=1e-9, atol=1e-10):
            raise ValueError("Heterogeneous G22 current cost drift")


def summarize_heterogeneous(path: Path) -> SummaryRow:
    """Validate and summarize separate aggregate and cohort current costs."""
    with np.load(path, allow_pickle=False) as data:
        _required(data.files)
        time, density, current, order = (
            data["time"],
            data["density"],
            data["current"],
            data["order"],
        )
        marginal = data["accumulated_marginal_cost"]
        cohort = data["accumulated_cohort_cost"]
        cells, spacing = int(data["cells"]), float(data["spacing"])
        mass_error = _validate_paths(
            time, density, current, order, marginal, cohort, cells, spacing
        )
        duration, diffusion = float(data["duration"]), float(data["diffusion"])
        bound = float(data["endpoint_bound"])
        if not np.isfinite([duration, diffusion, bound]).all() or duration <= 0 or diffusion <= 0:
            raise ValueError("Invalid heterogeneous G22 parameters")
        _validate_current_path(time, density, current, marginal, cohort, spacing, diffusion)
        expected = (np.arcsin(order[-1]) - np.arcsin(order[0])) ** 2 / (diffusion * duration)
        if not np.isclose(bound, expected, rtol=1e-10, atol=1e-12):
            raise ValueError("Incorrect heterogeneous G22 endpoint bound")
        if cohort[-1] + 1e-8 < marginal[-1] or marginal[-1] + 2e-3 < bound:
            raise ValueError("Heterogeneous G22 current inequality failed")
        return {
            "artifact": path.name,
            "cells": cells,
            "diffusion": diffusion,
            "spread": float(data["spread"]),
            "schedule": str(data["schedule"].item()),
            "initial_order": float(order[0]),
            "final_order": float(order[-1]),
            "marginal_cost": float(marginal[-1]),
            "cohort_cost": float(cohort[-1]),
            "endpoint_bound": bound,
            "marginal_slack": float(marginal[-1] - bound),
            "mass_error_max": mass_error,
            "density_min": float(density.min()),
        }


def write_heterogeneous_summary(path: Path, artifacts: list[Path]) -> None:
    """Write a compact report from saved two-frequency artifacts only."""
    rows = [summarize_heterogeneous(artifact) for artifact in artifacts]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"source": "g22_heterogeneous_report.py", "protocols": rows}, indent=2) + "\n"
    )
