"""Generate publication TeX macros from saved simulation outputs, without integration."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, cast

import numpy as np

from dynamic_ramp_analysis import fit_power_law
from dynamic_ramp_report import SPEEDS, LegMetrics, _load_leg, _metrics, _size_metrics
from empirical_collapse import tangent_separation
from propagation_of_chaos import Summary, write_tex_macros


JsonObject = dict[str, object]
ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"

# The spatial sweep's declared operational coherence gate.
_COHERENCE_CRITERION = 0.2


def _macro(name: str, value: object) -> str:
    return f"\\newcommand{{\\{name}}}{{{value}}}"


def _read_json(path: Path) -> JsonObject:
    return cast(JsonObject, json.loads(path.read_text(encoding="utf-8")))


def _effective_coupling(epsilon: float, config: JsonObject) -> float:
    """Convert a per-pair term to the mean-field ratio ``K_eff/D = N*eps/D``."""
    return epsilon * cast(int, config["n"]) / cast(float, config["diffusion"])


def _geometric_grid_ratio(values: list[float]) -> float:
    """Return the common ratio of a geometric grid, ignoring a leading zero.

    Taken from the grid itself rather than from the bracket it produced: the two
    agree only while the bracket happens to be a single grid step wide.
    """
    positive = [value for value in values if value > 0.0]
    return float(np.median([later / earlier for earlier, later in zip(positive, positive[1:])]))


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


def _ramp_onset_macros(metrics: list[LegMetrics]) -> list[str]:
    """Emit each leg's exponent with the reference and window it was read from.

    The shift ``K0`` returning at its lower bound is a property of the fit, not
    of one leg, so it is emitted as a count over the legs rather than per leg:
    a reader needs to know whether pinning separates the fast fit from the rest.
    """
    return [
        _macro("rampLegCount", len(metrics)),
        _macro("rampOnsetPinnedCount", sum(item.onset.onset_pinned for item in metrics)),
        *_indexed_macros("rampOnset", [item.onset.exponent for item in metrics], 3),
        *_indexed_macros("rampOnsetReference", [item.onset_reference for item in metrics], 3),
        *_indexed_macros("rampOnsetOrderMin", [item.onset.order_min for item in metrics], 3),
        *_indexed_macros("rampOnsetOrderMax", [item.onset.order_max for item in metrics], 3),
        *_indexed_macros("rampOnsetExcessMin", [item.onset.excess_min for item in metrics], 2),
        *_indexed_macros("rampOnsetExcessMax", [item.onset.excess_max for item in metrics], 2),
        *_indexed_macros("rampOnsetSamples", [float(item.onset.samples) for item in metrics], 0),
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
        *_ramp_size_macros(),
        *_ramp_onset_macros(metrics),
        *_indexed_macros("rampCollapse", [item.collapse_deviation for item in metrics], 5),
        _macro("rampCollapseThreshold", f"{2.0 * floor:.5f}"),
    ]


def _first_sustained_index(values: list[float], threshold: float) -> int:
    """Return the first index from which every later value stays above ``threshold``.

    This is the criterion the sweep's own boundary estimate is built on, so an
    isolated early excursion above the threshold does not open the coherent
    range.
    """
    index = len(values) - 1
    while index > 0 and values[index - 1] > threshold:
        index -= 1
    return index


def _spatial_refinement_macros(critical_decay_mm: float) -> list[str]:
    """Emit what the halved-spacing rerun does to the boundary.

    The boundary is a property of the discretisation exactly to the extent that
    it moves with the spacing, so the ratio of the two boundaries is the result
    and the two lengths are what it is read from.
    """
    data = _read_json(FIGURES / "spatial_kernel_refined" / "spatial_kernel_summary.json")
    config = cast(JsonObject, data["config"])
    refined_mm = data["critical_decay_mm"]
    if refined_mm is None:
        raise ValueError("the refined sweep does not bracket a crossing; widen its band")
    refined_mm = cast(float, refined_mm)
    spacing_mm = cast(float, config["extent_mm"]) / cast(int, config["side"])
    return [
        _macro("spatialRefinedSide", cast(int, config["side"])),
        _macro("spatialRefinedCriticalDecay", f"{refined_mm:.5f}"),
        _macro("spatialRefinedCriticalDecayCells", f"{refined_mm / spacing_mm:.2f}"),
        _macro("spatialRefinedBoundaryRatio", f"{refined_mm / critical_decay_mm:.2f}"),
    ]


def _spatial_macros() -> list[str]:
    data = _read_json(FIGURES / "spatial_kernel" / "spatial_kernel_summary.json")
    decays = cast(list[float], data["decay_mm"])
    orders = cast(list[float], data["steady_order"])
    defects = cast(list[float], data["steady_defect_density"])
    config = cast(JsonObject, data["config"])
    spacing_mm = cast(float, config["extent_mm"]) / cast(int, config["side"])

    indices = [decays.index(value) for value in (0.1, 0.2, 0.3)]
    mantissa, exponent = f"{max(defects[position] for position in indices):.1e}".split("e")

    critical_decay_mm = cast(float, data["critical_decay_mm"])
    resolved_mm = decays[_first_sustained_index(orders, _COHERENCE_CRITERION)]
    plateau = orders[indices[0] :]

    return [
        _macro("spatialCriticalDecay", f"{critical_decay_mm:.4f}"),
        _macro("spatialCriticalDecayCells", f"{critical_decay_mm / spacing_mm:.2f}"),
        _macro("spatialResolvedDecayCells", f"{resolved_mm / spacing_mm:.2f}"),
        _macro("spatialPlateauMax", f"{decays[-1]:.1f}"),
        _macro("spatialPlateauSpread", f"{max(plateau) - min(plateau):.5f}"),
        _macro("spatialPlateauExtentRatio", f"{decays[-1] / cast(float, config['extent_mm']):.1f}"),
        *[
            _macro(f"spatialOrder{('One', 'Two', 'Three')[index]}", f"{orders[position]:.4f}")
            for index, position in enumerate(indices)
        ],
        _macro("spatialDefectMaximum", rf"{mantissa}\times10^{{{int(exponent)}}}"),
        *_spatial_refinement_macros(critical_decay_mm),
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
        *_selection_step_macros(data, theory[2]),
        _macro("selectionRateSlope", f"{cast(float, data['rate_fit_slope']):.5f}"),
        _macro("selectionRateIntercept", f"{cast(float, data['rate_fit_intercept']):.5f}"),
        *_selection_window_macros(data),
    ]


def _selection_step_macros(data: JsonObject, static_order: float) -> list[str]:
    """Emit the step-size series and what its last refinement still moves.

    ``selectionDtLastChange`` is what separates a bound from a measurement: the
    residual at the finest step is the finite-size part only to the extent that
    halving the step again would not move it.
    """
    steps = cast(list[float], data["dt_control_dt"])
    series = cast(list[float], data["dt_control_order"])
    return [
        _macro("selectionDtRefinement", f"{round(steps[0] / steps[-1])}"),
        _macro("selectionSuperOrderDtFine", f"{series[-1]:.5f}"),
        _macro("selectionStaticResidualDtFine", f"{series[-1] - static_order:.5f}"),
        _macro("selectionDtLastChange", f"{series[-1] - series[-2]:.5f}"),
    ]


def _selection_window_macros(data: JsonObject) -> list[str]:
    """Emit the growth-fit window, whose upper bound moves with the coupling."""
    lower = cast(list[float], data["growth_window_lower"])
    upper = cast(list[float], data["growth_window_upper"])
    return [
        _macro("selectionWindowLower", f"{lower[0]:.5f}"),
        _macro("selectionWindowUpperMin", f"{min(upper):.5f}"),
        _macro("selectionWindowUpperMax", f"{max(upper):.5f}"),
    ]


def _frustration_macros() -> list[str]:
    data = _read_json(FIGURES / "geometric_frustration" / "followup_summary.json")
    lines = []
    for key, prefix, precision in (
        ("baseline_range", "Baseline", 4),
        ("coupling_range", "Coupling", 2),
    ):
        values = cast(list[float], data[key])
        for suffix, value in zip(("Min", "Max"), values, strict=True):
            lines.append(_macro(f"frustration{prefix}{suffix}", f"{value:.{precision}f}"))

    config = cast(JsonObject, data["config"])
    bracket = cast(list[float], data["threshold_bracket"])
    lines.append(_macro("frustrationBracketMin", f"{_effective_coupling(bracket[0], config):.3f}"))
    lines.append(_macro("frustrationBracketMax", f"{_effective_coupling(bracket[1], config):.3f}"))
    coarse = cast(list[float], data["coarse_bracket"])
    lines.append(_macro("frustrationCoarseMin", f"{_effective_coupling(coarse[0], config):.3f}"))
    lines.append(_macro("frustrationCoarseMax", f"{_effective_coupling(coarse[1], config):.3f}"))
    step = _effective_coupling(cast(float, data["refinement_step"]), config)
    lines.append(_macro("frustrationRefinementStep", f"{step:.3f}"))
    ratio = _geometric_grid_ratio(cast(list[float], data["coarse_epsilon"]))
    lines.append(_macro("frustrationGridRatio", f"{ratio:.3f}"))

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
    ("gradient", "tail_crossed_alignment_ratio", "CrossedRatio"),
    ("gradient", "blind_partition_percentile", "BlindPercentile"),
    ("gradient", "kernel_norm_growth", "NormGrowth"),
    ("gradient", "true_distance_reduction", "Reduction"),
    ("gradient", "final_template_correlation", "Correlation"),
    ("random", "descent_fraction", "RandomDescent"),
    ("random", "tail_alignment_ratio", "RandomRatio"),
    ("random", "kernel_norm_growth", "RandomNormGrowth"),
    ("permuted", "tail_order", "PermutedOrder"),
    ("permuted", "descent_fraction", "PermutedDescent"),
    ("permuted", "tail_alignment_ratio", "PermutedRatio"),
    ("permuted", "kernel_norm_growth", "PermutedNormGrowth"),
    ("permuted", "permutation_percentile", "PermutedPercentile"),
    ("frozen", "tail_dissipation", "FrozenDissipation"),
    ("frozen", "permutation_percentile", "FrozenPercentile"),
    ("frozen", "blind_partition_percentile", "FrozenBlindPercentile"),
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


def _plasticity_study_rows(tuning: list[dict[str, Any]]) -> str:
    return "\n".join(
        f"{row['learning_rate']:g} & {row['update_interval']:g} & "
        f"{row['quarter_objective_ratios'][0]:.4f} & "
        f"{row['quarter_objective_ratios'][1]:.4f} & "
        f"{min(row['quarter_order']):.3f} & {row['tail_alignment']:.3f} & "
        f"{row['blind_partition_percentile']:.4f} \\\\"
        for row in tuning
    )


def _scientific_upper_bound(value: float, digits: int = 1) -> str:
    """Round a magnitude upward, so a macro quoted as ``at most`` is never overclaimed."""
    if value <= 0.0:
        return "0"
    exponent = int(np.floor(np.log10(value)))
    mantissa = np.ceil(value / 10.0**exponent * 10**digits) / 10**digits
    if mantissa >= 10.0:
        mantissa, exponent = mantissa / 10.0, exponent + 1
    return f"{mantissa:.{digits}f}\\times10^{{{exponent}}}"


def _production_study_row(tuning: list[dict[str, Any]]) -> dict[str, Any]:
    """The grid cell run at the production plasticity rate and update cadence."""
    production = cast(
        list[JsonObject], _read_json(FIGURES / "structural_resonance" / "summary.json")
    )
    config = cast(dict[str, Any], production[0]["config"])
    cadence = config["update_every"] * config["dt"]
    matches = [
        row
        for row in tuning
        if row["learning_rate"] == config["learning_rate"] and row["update_interval"] == cadence
    ]
    if len(matches) != 1:
        raise ValueError("The F5 grid must contain the production rate and cadence exactly once")
    return matches[0]


def _plasticity_study_macros(plasticity: JsonObject) -> list[str]:
    tuning = cast(list[dict[str, Any]], plasticity["tuning"])
    best = min(tuning, key=lambda row: row["worst_objective_ratio"])
    improvements = [100 * (1 - ratio) for ratio in best["quarter_objective_ratios"]]
    matched = _production_study_row(tuning)
    ratios = cast(list[float], matched["quarter_objective_ratios"])
    return [
        _macro("plasticityStudyCaseCount", len(tuning)),
        _macro(
            "plasticityStudyEligibleCount",
            sum(row["objective_pass"] and row["coherence_pass"] for row in tuning),
        ),
        _macro("plasticityStudyBestRate", f"{best['learning_rate']:g}"),
        _macro("plasticityStudyBestInterval", f"{best['update_interval']:g}"),
        _macro("plasticityStudyImprovementMin", f"{min(improvements):.2f}"),
        _macro("plasticityStudyImprovementMax", f"{max(improvements):.2f}"),
        _macro("plasticityStudyOrderMin", f"{min(best['quarter_order']):.3f}"),
        _macro("plasticityStudyOrderMax", f"{max(best['quarter_order']):.3f}"),
        _macro("plasticityStudyAlignment", f"{best['tail_alignment']:.3f}"),
        _macro("plasticityStudyPercentile", f"{best['blind_partition_percentile']:.3f}"),
        _macro(
            "plasticityStudyProductionPostUpdate", f"{matched['post_update_tail_objective']:.2f}"
        ),
        _macro(
            "plasticityStudyProductionInterval",
            f"{float(np.mean(matched['quarter_objective'])):.2f}",
        ),
        _macro(
            "plasticityStudyProductionFrozen",
            f"{float(np.mean(matched['quarter_frozen_objective'])):.2f}",
        ),
        _macro("plasticityStudyProductionRatioMin", f"{min(ratios):.3f}"),
        _macro("plasticityStudyProductionRatioMax", f"{max(ratios):.3f}"),
        _macro("plasticityStudyRows", _plasticity_study_rows(tuning)),
    ]


def _recovery_study_macros(recovery: JsonObject) -> list[str]:
    cases = cast(list[dict[str, Any]], recovery["cases"])
    families = cast(list[str], recovery["families"])
    fitted = [[case["fits"][name]["endpoint_ratio"] for name in families] for case in cases]
    errors = [case["fits"][name]["squared_error"] for case in cases for name in families]
    return [
        _macro("recoveryStudyCaseCount", sum(cast(list[int], recovery["case_counts"]))),
        _macro("recoveryStudyUniqueCount", sum(cast(list[int], recovery["uniquely_correct"]))),
        _macro("recoveryStudyFitSpread", _scientific_upper_bound(max(map(np.ptp, fitted)))),
        _macro("recoveryStudyMaxSquaredError", _scientific_upper_bound(max(errors))),
    ]


def _followup_macros() -> list[str]:
    return [
        *_plasticity_study_macros(_read_json(FIGURES / "plasticity_study" / "summary.json")),
        *_recovery_study_macros(_read_json(FIGURES / "recovery_mechanisms" / "summary.json")),
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
        "",
        "% F5/F6: bounded follow-up studies",
        *_followup_macros(),
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
