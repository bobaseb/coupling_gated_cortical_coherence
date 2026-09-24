"""Summarize saved G22 density trajectories without running the solver."""

import json
from pathlib import Path

import numpy as np


SummaryRow = dict[str, str | int | float | None]


def _validate_onset_input(time: np.ndarray, order: np.ndarray, threshold: float) -> None:
    if time.ndim != 1 or order.shape != time.shape or time.size < 2:
        raise ValueError("Onset arrays must be matching nonempty trajectories")
    if not np.isfinite(time).all() or not np.isfinite(order).all() or not 0 < threshold < 1:
        raise ValueError("Onset arrays and threshold must be finite and valid")
    if np.any(np.diff(time) <= 0):
        raise ValueError("Onset times must increase")


def first_upcrossing(time: np.ndarray, order: np.ndarray, threshold: float) -> float | None:
    """Linearly interpolate the first order upcrossing on saved samples.

    The 0.3 threshold used below is exploratory, selected after the grid was
    generated. A crossing is an operational statistic, not a phase transition.
    """
    _validate_onset_input(time, order, threshold)
    if order[0] >= threshold:
        return float(time[0])
    crossings = np.flatnonzero((order[:-1] < threshold) & (order[1:] >= threshold))
    if crossings.size == 0:
        return None
    index = int(crossings[0])
    fraction = (threshold - order[index]) / (order[index + 1] - order[index])
    return float(time[index] + fraction * (time[index + 1] - time[index]))


def onset_cost_summary(
    time: np.ndarray,
    order: np.ndarray,
    accumulated: np.ndarray,
    *,
    diffusion: float,
    threshold: float,
) -> dict[str, float] | None:
    """Evaluate the finite-time floor at the first interpolated upcrossing."""
    crossing = first_upcrossing(time, order, threshold)
    if accumulated.shape != time.shape or not np.isfinite(accumulated).all():
        raise ValueError("Onset cost must match finite time samples")
    if not np.isfinite(diffusion) or diffusion <= 0:
        raise ValueError("Onset diffusion must be positive")
    if crossing is None:
        return None
    cost = float(np.interp(crossing, time, accumulated))
    if crossing == time[0]:
        return {"time": crossing, "cost": 0.0, "bound": 0.0, "slack": 0.0}
    bound = float(
        (np.arcsin(threshold) - np.arcsin(order[0])) ** 2 / (diffusion * (crossing - time[0]))
    )
    return {"time": crossing, "cost": cost, "bound": bound, "slack": cost - bound}


def _required_present(files: list[str]) -> bool:
    required = {
        "time",
        "density",
        "current",
        "order",
        "coupling",
        "accumulated_cost",
        "endpoint_bound",
        "spacing",
        "duration",
        "diffusion",
        "cells",
        "initial_order",
        "start_coupling",
        "end_coupling",
        "schedule",
    }
    return required.issubset(files)


def _valid_shape(
    time: np.ndarray,
    density: np.ndarray,
    current: np.ndarray,
    order: np.ndarray,
    coupling: np.ndarray,
    accumulated: np.ndarray,
    cells: int,
) -> bool:
    return (
        time.ndim == 1
        and density.shape == current.shape
        and density.shape == (time.size, cells)
        and all(vector.shape == time.shape for vector in (order, coupling, accumulated))
    )


def _validate_density(density: np.ndarray, spacing: float) -> None:
    if not np.isfinite(spacing) or spacing <= 0:
        raise ValueError("Invalid G22 physical parameters")
    if density.min() <= 0 or np.max(np.abs(density.sum(axis=1) * spacing - 1)) > 1e-8:
        raise ValueError("G22 density must be positive and normalized")


def _validate_time_order_cost(
    time: np.ndarray, order: np.ndarray, accumulated: np.ndarray, duration: float
) -> None:
    if np.any(order < 0) or np.any(order >= 1) or np.any(np.diff(accumulated) < -1e-12):
        raise ValueError("Invalid G22 order or accumulated cost")
    if not np.isclose(time[0], 0) or not np.isclose(time[-1], duration):
        raise ValueError("G22 time endpoints do not match duration")
    if np.any(np.diff(time) <= 0):
        raise ValueError("G22 times must increase")


def _validate_trajectory(
    time: np.ndarray,
    density: np.ndarray,
    order: np.ndarray,
    accumulated: np.ndarray,
    spacing: float,
    duration: float,
    diffusion: float,
    bound: float,
) -> None:
    if not np.isfinite([duration, diffusion, bound]).all() or duration <= 0 or diffusion <= 0:
        raise ValueError("Invalid G22 physical parameters")
    _validate_density(density, spacing)
    _validate_time_order_cost(time, order, accumulated, duration)
    expected = (np.arcsin(order[-1]) - np.arcsin(order[0])) ** 2 / (diffusion * duration)
    if not np.isclose(bound, expected, rtol=1e-10, atol=1e-12):
        raise ValueError("Inconsistent G22 endpoint bound")


def _validate_current_path(
    time: np.ndarray,
    density: np.ndarray,
    current: np.ndarray,
    accumulated: np.ndarray,
    spacing: float,
    diffusion: float,
) -> None:
    step = np.diff(time)
    expected_density = (
        density[:-1] - step[:, None] * (current[:-1] - np.roll(current[:-1], 1, axis=1)) / spacing
    )
    if not np.allclose(density[1:], expected_density, rtol=1e-9, atol=1e-10):
        raise ValueError("Saved G22 density violates discrete continuity")
    edge_density = (density + np.roll(density, -1, axis=1)) / 2
    instantaneous = spacing * np.sum(current**2 / (diffusion * edge_density), axis=1)
    expected_cost = np.concatenate(
        ([0.0], np.cumsum(step * (instantaneous[:-1] + instantaneous[1:]) / 2))
    )
    if not np.allclose(accumulated, expected_cost, rtol=1e-9, atol=1e-10):
        raise ValueError("Saved G22 current cost does not match saved flux")


def summarize_artifact(path: Path) -> SummaryRow:
    """Read one saved artifact; fail if key arrays or dimensions are missing."""
    with np.load(path, allow_pickle=False) as data:
        if not _required_present(data.files):
            raise ValueError(f"Incomplete G22 artifact: {path}")
        time, density = data["time"], data["density"]
        current, order = data["current"], data["order"]
        coupling, accumulated = data["coupling"], data["accumulated_cost"]
        if not _valid_shape(
            time, density, current, order, coupling, accumulated, int(data["cells"])
        ):
            raise ValueError(f"Inconsistent G22 artifact dimensions: {path}")
        if not all(
            np.isfinite(vector).all()
            for vector in (time, density, current, order, coupling, accumulated)
        ):
            raise ValueError(f"Nonfinite G22 artifact: {path}")
        cost = float(accumulated[-1])
        bound = float(data["endpoint_bound"])
        _validate_trajectory(
            time,
            density,
            order,
            accumulated,
            float(data["spacing"]),
            float(data["duration"]),
            float(data["diffusion"]),
            bound,
        )
        _validate_current_path(
            time,
            density,
            current,
            accumulated,
            float(data["spacing"]),
            float(data["diffusion"]),
        )
        onset = onset_cost_summary(
            time, order, accumulated, diffusion=float(data["diffusion"]), threshold=0.3
        )
        return {
            "artifact": path.name,
            "schedule": str(data["schedule"].item()),
            "cells": int(data["cells"]),
            "duration": float(data["duration"]),
            "diffusion": float(data["diffusion"]),
            "initial_order": float(order[0]),
            "final_order": float(order[-1]),
            "start_coupling": float(coupling[0]),
            "end_coupling": float(coupling[-1]),
            "cost": cost,
            "endpoint_bound": bound,
            "slack": cost - bound,
            "slack_ratio": cost / bound if bound > 0 else None,
            "exploratory_onset_time_r0p3": first_upcrossing(time, order, 0.3),
            "exploratory_onset_cost_r0p3": onset["cost"] if onset else None,
            "exploratory_onset_bound_r0p3": onset["bound"] if onset else None,
            "exploratory_onset_slack_r0p3": onset["slack"] if onset else None,
            "density_min": float(density.min()),
            "mass_error_max": float(
                np.max(np.abs(density.sum(axis=1) * float(data["spacing"]) - 1))
            ),
        }


def write_summary(path: Path, artifacts: list[Path]) -> None:
    """Write a compact JSON report from existing artifacts only."""
    rows = [summarize_artifact(artifact) for artifact in artifacts]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"source": "g22_current_report.py", "protocols": rows}, indent=2) + "\n"
    )


if __name__ == "__main__":
    pilot = Path("figures/g22_pilot")
    names = ("uniform", "relaxation", "early", "linear", "late")
    write_summary(pilot / "summary.json", [pilot / f"{name}.npz" for name in names])
