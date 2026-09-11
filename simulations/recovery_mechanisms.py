"""F6 ideal stationary observations: analytic ambiguity precedes observation noise.

For q=K/D, p(theta) is von Mises with a=q*r(q). Scaling K and D together
preserves this stationary density but changes the physical clock. Independent
oscillators forced by -h*sin(theta-psi) have the same density when h/D=a.
Successive stationary windows discard the increments that could reveal the
clock. This pilot tests that observation protocol, not continuous phase paths.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from time import perf_counter
from typing import Any, cast

import numpy as np
from numpy.typing import NDArray
from scipy.optimize import brentq, minimize_scalar
from scipy.special import i0e, i1e

Array = NDArray[np.float64]
ROOT = Path(__file__).resolve().parent / "figures" / "recovery_mechanisms"
DESIGN = Path(__file__).resolve().parents[1] / "tasks" / "f5_f6_design.md"
FAMILIES = ("coupling", "diffusion", "shared_drive")
Fits = dict[str, dict[str, float]]


def branch_concentration(q: float) -> float:
    """Solve R(a)/a=1/q on the unique coherent branch; do not invert measured r."""
    if q <= 2:
        return 0.0
    return float(brentq(lambda a: i1e(a) / (a * i0e(a)) - 1 / q, 1e-7, q, xtol=1e-13))


def parameters(family: str, endpoint: float, windows: Array) -> tuple[Array, Array, Array]:
    """Declared generating parameters, kept outside the observation passed to inference."""
    q = 1.5 + (endpoint - 1.5) * windows
    ones, zeros = np.ones_like(q), np.zeros_like(q)
    if family == "coupling":
        return q, ones, zeros
    if family == "diffusion":
        return ones * endpoint, endpoint / q, zeros
    if family == "shared_drive":
        return zeros, ones, np.asarray([branch_concentration(float(value)) for value in q])
    raise ValueError(f"Unknown family: {family}")


def predicted_concentration(family: str, endpoint: float, windows: Array) -> Array:
    coupling, diffusion, drive = parameters(family, endpoint, windows)
    return np.asarray(
        [
            branch_concentration(float(k / d)) if k > 0 else h / d
            for k, d, h in zip(coupling, diffusion, drive, strict=True)
        ]
    )


def ideal_observation(family: str, endpoint: float, phase: float, windows: Array) -> Array:
    """Exact stationary density on a periodic quadrature grid; no individual paths."""
    theta = np.linspace(-np.pi, np.pi, 4096, endpoint=False)
    concentration = predicted_concentration(family, endpoint, windows)
    density = np.exp(concentration[:, None] * (np.cos(theta - phase) - 1))
    return cast(Array, density / (density.mean(axis=1, keepdims=True) * 2 * np.pi))


def observe_density(density: Array) -> dict[str, Array]:
    """Independent concentration regression and circular integral, with unknown orientation."""
    theta = np.linspace(-np.pi, np.pi, density.shape[1], endpoint=False)
    design = np.column_stack([np.ones_like(theta), np.cos(theta), np.sin(theta)])
    coefficients = np.linalg.lstsq(design, np.log(density).T, rcond=None)[0]
    concentration = np.hypot(coefficients[1], coefficients[2])
    order = np.abs((density * np.exp(1j * theta)).mean(axis=1) * 2 * np.pi)
    return {"concentration": concentration, "order": order}


def fit_family(family: str, concentration: Array, windows: Array) -> dict[str, float]:
    def squared_error(endpoint: float) -> float:
        residual = predicted_concentration(family, endpoint, windows) - concentration
        return float(residual @ residual)

    fitted = minimize_scalar(
        squared_error, bounds=(2.6, 4.0), method="bounded", options={"xatol": 1e-12}
    )
    if not fitted.success:
        raise RuntimeError(f"Concentration fit failed: {fitted.message}")
    return {"endpoint_ratio": float(fitted.x), "squared_error": float(fitted.fun)}


def fit_models(density: Array, windows: Array) -> Fits:
    """Inference interface accepts observations and window coordinates, no hidden parameters."""
    concentration = observe_density(density)["concentration"]
    return {family: fit_family(family, concentration, windows) for family in FAMILIES}


def tie_weights(fits: Fits) -> Array:
    """Expected tie allocation, not sampled correct classifications."""
    errors = np.asarray([fits[name]["squared_error"] for name in FAMILIES])
    tied = (errors <= errors.min() + 1e-10).astype(float)
    return cast(Array, tied / tied.sum())


def evaluate_case(family: str, endpoint: float, phase: float, windows: Array) -> dict[str, Any]:
    density = ideal_observation(family, endpoint, phase, windows)
    # No generating metadata crosses this call boundary.
    fits = fit_models(density, windows)
    observed = observe_density(density)
    coupling, diffusion, drive = parameters(family, endpoint, windows)
    return {
        "family": family,
        "endpoint_ratio": endpoint,
        "phase": phase,
        "coupling": coupling.tolist(),
        "diffusion": diffusion.tolist(),
        "shared_drive": drive.tolist(),
        "concentration": observed["concentration"].tolist(),
        "order": observed["order"].tolist(),
        "fits": fits,
        "tie_weights": tie_weights(fits).tolist(),
    }


def confusion_summary(cases: list[dict[str, Any]]) -> dict[str, Any]:
    confusion = np.zeros((3, 3))
    unique = np.zeros(3, dtype=int)
    counts = np.zeros(3, dtype=int)
    for case in cases:
        index = FAMILIES.index(case["family"])
        weights = np.asarray(case["tie_weights"])
        confusion[index] += weights
        unique[index] += int(weights[index] == 1.0)
        counts[index] += 1
    return {
        "families": list(FAMILIES),
        "case_counts": counts.tolist(),
        "confusion_expected_counts": confusion.tolist(),
        "confusion_row_fractions": (confusion / counts[:, None]).tolist(),
        "uniquely_correct": unique.tolist(),
        "unique_recovery_pass": bool(np.all(unique / counts >= 0.8)),
    }


def run(output: Path) -> dict[str, Any]:
    started = perf_counter()
    windows = np.linspace(0.0, 1.0, 9)
    cases = [
        evaluate_case(family, endpoint, phase, windows)
        for family in FAMILIES
        for endpoint in (2.6, 3.2, 4.0)
        for phase in (0.0, 0.7)
    ]
    summary = {
        "status": "complete_ideal_stop",
        "design_sha256": hashlib.sha256(DESIGN.read_bytes()).hexdigest(),
        "observation": "exact stationary density; no within-window phase increments",
        "windows": windows.tolist(),
        "phase_grid_points": 4096,
        "cases": cases,
        **confusion_summary(cases),
        "runtime_seconds": perf_counter() - started,
    }
    if summary["unique_recovery_pass"]:
        raise RuntimeError("Recovery contradicts analytic equivalence; inspect numerical fitting")
    output.mkdir(parents=True, exist_ok=True)
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in summary.items() if key != "cases"}, indent=2))
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT)
    args = parser.parse_args()
    run(args.output)


if __name__ == "__main__":
    main()
