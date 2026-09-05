"""Generate publication TeX macros from saved simulation outputs, without integration."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import cast

import numpy as np

from dynamic_ramp_analysis import fit_power_law, replica_escape_couplings
from dynamic_ramp_report import SPEEDS, _load_leg, _metrics
from propagation_of_chaos import Summary, write_tex_macros


JsonObject = dict[str, object]
ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"


def _macro(name: str, value: object) -> str:
    return f"\\newcommand{{\\{name}}}{{{value}}}"


def _read_json(path: Path) -> JsonObject:
    return cast(JsonObject, json.loads(path.read_text(encoding="utf-8")))


def _ramp_n_delays() -> list[float]:
    paths = [
        FIGURES / "dynamic_ramp_N500_v1e-02.npz",
        FIGURES / "dynamic_ramp_replicas_v1e-02.npz",
        FIGURES / "dynamic_ramp_N8000_v1e-02.npz",
    ]
    legs = [_load_leg(path) for path in paths]
    return [
        float(np.nanmean(replica_escape_couplings(leg.coupling, leg.order_replicas)) - 2.0)
        for leg in legs
    ]


def _indexed_macros(prefix: str, values: list[float], precision: int) -> list[str]:
    words = ("One", "Two", "Three", "Four")
    return [
        _macro(f"{prefix}{words[index]}", f"{value:.{precision}f}")
        for index, value in enumerate(values)
    ]


def _ramp_macros() -> list[str]:
    legs = [_load_leg(FIGURES / f"dynamic_ramp_replicas_v{speed:.0e}.npz") for speed in SPEEDS]
    metrics = [_metrics(leg) for leg in legs]
    uncensored = [item for item in metrics if item.escaped == 32]
    delay_fit = fit_power_law(
        np.asarray([item.speed for item in uncensored]),
        np.asarray([item.delay_mean for item in uncensored]),
    )
    floor = metrics[-1].collapse_deviation
    return [
        _macro("rampFastEscaped", metrics[0].escaped),
        _macro("rampReplicas", 32),
        _macro("rampDelaySlowOne", f"{metrics[1].delay_mean:.4f}"),
        _macro("rampDelaySlowTwo", f"{metrics[2].delay_mean:.4f}"),
        _macro("rampDelaySlowThree", f"{metrics[3].delay_mean:.4f}"),
        _macro("rampDelayExponent", f"{delay_fit.exponent:.3f}"),
        *_indexed_macros("rampNDelay", _ramp_n_delays(), 4),
        *_indexed_macros("rampOnset", [item.onset_exponent for item in metrics], 3),
        *_indexed_macros("rampCollapse", [item.collapse_deviation for item in metrics], 5),
        _macro("rampCollapseThreshold", f"{2.0 * floor:.5f}"),
    ]


def _spatial_macros() -> list[str]:
    data = _read_json(FIGURES / "spatial_kernel" / "spatial_kernel_summary.json")
    decays = cast(list[float], data["decay_mm"])
    orders = cast(list[float], data["steady_order"])
    defects = cast(list[float], data["steady_defect_density"])
    indices = [decays.index(value) for value in (0.1, 0.2, 0.3)]
    mantissa, exponent = f"{max(defects[position] for position in indices):.1e}".split("e")
    return [
        _macro("spatialCriticalDecay", f"{cast(float, data['critical_decay_mm']):.4f}"),
        *[
            _macro(f"spatialOrder{('One', 'Two', 'Three')[index]}", f"{orders[position]:.4f}")
            for index, position in enumerate(indices)
        ],
        _macro("spatialDefectMaximum", rf"{mantissa}\times10^{{{int(exponent)}}}"),
    ]


def _selection_macros() -> list[str]:
    data = _read_json(FIGURES / "dynamical_selection" / "dynamical_selection_summary.json")
    orders = cast(list[float], data["regime_final_order"])
    theory = cast(list[float], data["regime_theory_order"])
    return [
        _macro("selectionSubOrder", f"{orders[0]:.5f}"),
        _macro("selectionCriticalOrder", f"{orders[1]:.5f}"),
        _macro("selectionSuperOrder", f"{orders[2]:.5f}"),
        _macro("selectionTheoryOrder", f"{theory[2]:.5f}"),
        _macro("selectionStaticResidual", f"{orders[2] - theory[2]:.5f}"),
        _macro("selectionRateSlope", f"{cast(float, data['rate_fit_slope']):.5f}"),
        _macro("selectionRateIntercept", f"{cast(float, data['rate_fit_intercept']):.5f}"),
    ]


def _frustration_macros() -> list[str]:
    data = _read_json(FIGURES / "geometric_frustration" / "followup_summary.json")
    lines = []
    for key, prefix in (("baseline_range", "Baseline"), ("coupling_range", "Coupling")):
        values = cast(list[float], data[key])
        for suffix, value in zip(("Min", "Max"), values, strict=True):
            lines.append(_macro(f"frustration{prefix}{suffix}", f"{value:.4f}"))
    for suffix in ("min", "max"):
        values = cast(list[float], data[f"conditional_field_{suffix}"])
        for word, value in zip(("One", "Two", "Three"), values, strict=True):
            lines.append(_macro(f"frustrationField{word}{suffix.title()}", f"{value:.4f}"))
    return lines


def generate_simulation_tex(output: Path) -> None:
    """Write all completed simulation macros from compact saved results."""
    chaos_summary = cast(
        Summary,
        json.loads(
            (FIGURES / "propagation_of_chaos" / "propagation_of_chaos_summary.json").read_text(
                encoding="utf-8"
            )
        ),
    )
    temporary = output.with_suffix(".chaos.tmp")
    write_tex_macros(chaos_summary, temporary)
    chaos_lines = temporary.read_text(encoding="utf-8").splitlines()[2:]
    temporary.unlink()
    lines = [
        "%% Auto-generated by simulations/simulation_tex.py",
        "%% Do not edit manually. Run: uv run --directory simulations python simulation_tex.py",
        "",
        "% S1: dynamic ramp",
        *_ramp_macros(),
        "",
        "% S2: spatial kernel",
        *_spatial_macros(),
        "",
        "% S3: dynamical selection",
        *_selection_macros(),
        "",
        "% S4: propagation of chaos",
        *chaos_lines,
        "",
        "% S5: conditional frustration rescue",
        *_frustration_macros(),
    ]
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    """Parse the output path and generate macros without running any simulation."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "simulation_results.tex")
    args = parser.parse_args()
    generate_simulation_tex(args.output)
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
