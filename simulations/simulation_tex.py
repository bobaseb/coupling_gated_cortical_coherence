"""Generate publication TeX macros from saved simulation outputs, without integration."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import cast
from typing import Any

import numpy as np

from dynamic_ramp_analysis import fit_power_law
from dynamic_ramp_report import SPEEDS, _load_leg, _metrics, _size_metrics
from empirical_collapse import tangent_separation
from propagation_of_chaos import Summary, write_tex_macros


JsonObject = dict[str, object]
ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"


def _macro(name: str, value: object) -> str:
    return f"\\newcommand{{\\{name}}}{{{value}}}"


def _read_json(path: Path) -> JsonObject:
    return cast(JsonObject, json.loads(path.read_text(encoding="utf-8")))


def _ramp_size_macros() -> list[str]:
    sizes = _size_metrics()
    return [
        *_indexed_macros("rampNDelay", [item.delay_mean for item in sizes], 4),
        *_indexed_macros("rampNScaledDelay", [item.scaled_delay for item in sizes], 4),
        *_indexed_macros("rampNPrecriticalMax", [item.precritical_order_max for item in sizes], 3),
    ]


def _indexed_macros(prefix: str, values: list[float], precision: int) -> list[str]:
    words = ("One", "Two", "Three", "Four")
    return [
        _macro(f"{prefix}{words[index]}", f"{value:.{precision}f}")
        for index, value in enumerate(values)
    ]


def _ramp_onset_macros(metrics: list[Any]) -> list[str]:
    res = []
    words = ["One", "Two", "Three", "Four"]
    for i in range(4):
        val = "true" if metrics[i].onset.onset_pinned else "false"
        res.append(_macro(f"rampOnsetPinned{words[i]}", val))

    res.extend(_indexed_macros("rampOnset", [item.onset.exponent for item in metrics], 3))
    res.extend(_indexed_macros("rampOnsetReference", [item.onset_reference for item in metrics], 3))
    res.extend(_indexed_macros("rampOnsetOrderMin", [item.onset.order_min for item in metrics], 3))
    res.extend(_indexed_macros("rampOnsetOrderMax", [item.onset.order_max for item in metrics], 3))
    res.extend(
        _indexed_macros("rampOnsetExcessMin", [item.onset.excess_min for item in metrics], 2)
    )
    res.extend(
        _indexed_macros("rampOnsetExcessMax", [item.onset.excess_max for item in metrics], 2)
    )
    res.extend(_indexed_macros("rampOnsetSamples", [item.onset.samples for item in metrics], 0))
    return res


def _ramp_macros() -> list[str]:
    legs = []
    for speed in SPEEDS:
        legs.append(_load_leg(FIGURES / f"dynamic_ramp_replicas_v{speed:.0e}.npz"))

    metrics = []
    for leg in legs:
        metrics.append(_metrics(leg))

    uncensored = [item for item in metrics if item.escaped == 32]
    delay_fit = fit_power_law(
        np.asarray([item.speed for item in uncensored]),
        np.asarray([item.delay_mean for item in uncensored]),
    )
    floor = metrics[-1].collapse_deviation

    res = [
        _macro("rampFastEscaped", metrics[0].escaped),
        _macro("rampReplicas", 32),
        _macro("rampDelaySlowOne", f"{metrics[1].delay_mean:.4f}"),
        _macro("rampDelaySlowTwo", f"{metrics[2].delay_mean:.4f}"),
        _macro("rampDelaySlowThree", f"{metrics[3].delay_mean:.4f}"),
        _macro("rampDelayExponent", f"{delay_fit.exponent:.3f}"),
    ]
    res.extend(_ramp_size_macros())
    res.extend(_ramp_onset_macros(metrics))
    res.extend(_indexed_macros("rampCollapse", [item.collapse_deviation for item in metrics], 5))
    res.append(_macro("rampCollapseThreshold", f"{2.0 * floor:.5f}"))
    return res


def _spatial_macros() -> list[str]:
    data = _read_json(FIGURES / "spatial_kernel" / "spatial_kernel_summary.json")
    decays = cast(list[float], data["decay_mm"])
    orders = cast(list[float], data["steady_order"])
    defects = cast(list[float], data["steady_defect_density"])
    config = cast(JsonObject, data["config"])
    side = cast(int, config["side"])
    extent_mm = cast(float, config["extent_mm"])

    indices = [decays.index(value) for value in (0.1, 0.2, 0.3)]
    mantissa, exponent = f"{max(defects[position] for position in indices):.1e}".split("e")

    critical_decay_mm = cast(float, data["critical_decay_mm"])
    critical_decay_cells = critical_decay_mm * side / extent_mm
    plateau_max_mm = decays[-1]

    return [
        _macro("spatialCriticalDecay", f"{critical_decay_mm:.4f}"),
        _macro("spatialCriticalDecayCells", f"{critical_decay_cells:.2f}"),
        _macro("spatialPlateauMax", f"{plateau_max_mm:.1f}"),
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

    bracket = cast(list[float], data["threshold_bracket"])
    lines.append(_macro("frustrationBracketMin", f"{bracket[0]*500:.3f}"))
    lines.append(_macro("frustrationBracketMax", f"{bracket[1]*500:.3f}"))
    lines.append(_macro("frustrationGridRatio", f"{bracket[1]/bracket[0]:.3f}"))

    for suffix in ("min", "max"):
        values = cast(list[float], data[f"conditional_field_{suffix}"])
        for word, value in zip(("One", "Two", "Three"), values, strict=True):
            lines.append(_macro(f"frustrationField{word}{suffix.title()}", f"{value:.4f}"))
    return lines


_PLASTICITY_RANGES = (
    ("gradient", "tail_order", "Order"),
    ("gradient", "tail_dissipation", "Dissipation"),
    ("gradient", "descent_fraction", "Descent"),
    ("gradient", "initial_alignment_ratio", "RatioInitial"),
    ("gradient", "tail_alignment_ratio", "Ratio"),
    ("gradient", "permutation_percentile", "Percentile"),
    ("gradient", "kernel_norm_growth", "NormGrowth"),
    ("gradient", "true_distance_reduction", "Reduction"),
    ("gradient", "final_template_correlation", "Correlation"),
    ("random", "descent_fraction", "RandomDescent"),
    ("random", "tail_alignment_ratio", "RandomRatio"),
    ("random", "kernel_norm_growth", "RandomNormGrowth"),
    ("frozen", "tail_dissipation", "FrozenDissipation"),
    ("frozen", "permutation_percentile", "FrozenPercentile"),
)


def _plasticity_records(name: str) -> list[JsonObject]:
    path = FIGURES / "structural_resonance" / name
    return cast(list[JsonObject], json.loads(path.read_text(encoding="utf-8")))


def _plasticity_macros() -> list[str]:
    data = _plasticity_records("summary.json")
    lines = []
    for mode, key, name in _PLASTICITY_RANGES:
        values = [cast(float, row[key]) for row in data if row["mode"] == mode]
        for suffix, value in (("Min", min(values)), ("Max", max(values))):
            lines.append(_macro(f"plasticity{name}{suffix}", f"{value:.4f}"))
    config = cast(JsonObject, data[0]["config"])
    lines.append(_macro("plasticitySigmaFloor", f"{cast(float, data[0]['sigma_floor']):.0f}"))
    lines.append(_macro("plasticityLearningRate", f"{cast(float, config['learning_rate']):g}"))
    return lines + _sweep_macros()


def _sweep_macros() -> list[str]:
    sweep = sorted(
        _plasticity_records("sweep.json"), key=lambda row: cast(float, row["learning_rate"])
    )
    best = min(sweep, key=lambda row: cast(float, row["tail_dissipation"]))
    return [
        _macro("plasticitySweepLowRate", f"{cast(float, sweep[0]['learning_rate']):g}"),
        _macro("plasticitySweepHighRate", f"{cast(float, sweep[-1]['learning_rate']):g}"),
        _macro("plasticitySweepBestRate", f"{cast(float, best['learning_rate']):g}"),
        _macro(
            "plasticitySweepLowDissipation",
            f"{cast(float, sweep[0]['tail_dissipation']):.4f}",
        ),
        _macro(
            "plasticitySweepHighDissipation",
            f"{cast(float, sweep[-1]['tail_dissipation']):.4f}",
        ),
    ]


def _collapse_macros() -> list[str]:
    """Emit the Bessel-curve separations that set what the EEG range can discriminate."""
    separation = tangent_separation()
    return [
        _macro("collapseLinearDeviation", f"{separation.linear_deviation:.4f}"),
        _macro("collapseTanhDeviation", f"{separation.tanh_deviation:.4f}"),
        _macro("collapseProbe", f"{separation.probe:g}"),
        _macro("collapseProbeSeparation", f"{separation.probe_separation:.3f}"),
        _macro("collapseTarget", f"{separation.target:g}"),
        _macro("collapseTargetConcentration", f"{separation.target_concentration:.2f}"),
    ]


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
        "",
        "% S6: joint phase/plasticity dynamics",
        *_plasticity_macros(),
        "",
        "% Empirical (a, r) collapse: what the observed range discriminates",
        *_collapse_macros(),
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
