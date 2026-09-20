"""Generate publication TeX macros from saved simulation outputs, without integration."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, cast

import numpy as np

from dynamic_ramp_analysis import fit_power_law, split_span_exponents
from dynamic_ramp_report import (
    DELAY_SPEEDS,
    SPEEDS,
    LegMetrics,
    _load_leg,
    _metrics,
    _size_metrics,
)
from empirical_collapse import tangent_separation
from fermi_estimate_check import FERMI_LAM_MIN
from propagation_of_chaos import Summary, write_tex_macros
from travelling_wave import WaveConfig, patch_cells


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


def _ramp_delay_macros(delays: list[LegMetrics]) -> list[str]:
    """The delay scaling, over every leg the sweep ran.

    The exponent travels with an interval and with the two half-span fits,
    because a single number over three decades cannot say whether its shortfall
    from the predicted 1/2 is the estimator's or a drift with rate.
    """
    uncensored = [item for item in delays if item.escaped == 32]
    speeds = np.asarray([item.speed for item in uncensored])
    means = np.asarray([item.delay_mean for item in uncensored])
    delay_fit = fit_power_law(speeds, means)
    fast_fit, slow_fit = split_span_exponents(speeds, means)
    return [
        _macro("rampDelaySpeedCount", len(delays)),
        _macro("rampDelayUncensoredCount", len(uncensored)),
        _macro("rampDelayCensoredCount", len(delays) - len(uncensored)),
        _macro("rampDelaySpeedFastest", f"{max(item.speed for item in delays):g}"),
        _macro("rampDelaySpeedSlowest", f"{min(item.speed for item in delays):g}"),
        _macro("rampDelayExponent", f"{delay_fit.exponent:.3f}"),
        _macro("rampDelayExponentLow", f"{delay_fit.exponent_low:.3f}"),
        _macro("rampDelayExponentHigh", f"{delay_fit.exponent_high:.3f}"),
        _macro("rampDelayExponentFast", f"{fast_fit.exponent:.3f}"),
        _macro("rampDelayExponentFastLow", f"{fast_fit.exponent_low:.3f}"),
        _macro("rampDelayExponentFastHigh", f"{fast_fit.exponent_high:.3f}"),
        _macro("rampDelayExponentSlow", f"{slow_fit.exponent:.3f}"),
        _macro("rampDelayExponentSlowLow", f"{slow_fit.exponent_low:.3f}"),
        _macro("rampDelayExponentSlowHigh", f"{slow_fit.exponent_high:.3f}"),
    ]


def _ramp_macros() -> list[str]:
    delays = [
        _metrics(_load_leg(FIGURES / f"dynamic_ramp_replicas_v{speed:.0e}.npz"))
        for speed in DELAY_SPEEDS
    ]
    metrics = [item for item in delays if item.speed in SPEEDS]
    floor = metrics[-1].collapse_deviation
    return [
        _macro("rampFastEscaped", metrics[0].escaped),
        _macro("rampReplicas", 32),
        _macro("rampDelaySlowOne", f"{metrics[1].delay_mean:.4f}"),
        _macro("rampDelaySlowTwo", f"{metrics[2].delay_mean:.4f}"),
        _macro("rampDelaySlowThree", f"{metrics[3].delay_mean:.4f}"),
        *_ramp_delay_macros(delays),
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


def _sustained_bracket(
    decays: list[float], orders: list[float], threshold: float = _COHERENCE_CRITERION
) -> tuple[float, float]:
    """The two sampled lengths the operational crossing falls between.

    An interpolated crossing is a number read between the sweep's samples rather
    than one it measured, and two of them can differ while lying in the same
    grid cell. The pair returned here is what the grid itself says, so a
    comparison of two crossings can be checked against the resolution it was
    read at.
    """
    index = _first_sustained_index(orders, threshold)
    if index == 0:
        raise ValueError("the sweep is already coherent at its shortest length; widen its band")
    return decays[index - 1], decays[index]


def _shared_coherent_length(
    coarse_decays: list[float],
    coarse_orders: list[float],
    refined_decays: list[float],
    refined_orders: list[float],
) -> float:
    """The shortest sampled length from which both sheets stay above the coherence gate.

    Two threshold interpolants agreeing says nothing about the trajectories the
    interpolation runs between, so this is the length at which the sheets can be
    compared on a steady order both of them call coherent.
    """
    length = max(
        decays[_first_sustained_index(orders, _COHERENCE_CRITERION)]
        for decays, orders in ((coarse_decays, coarse_orders), (refined_decays, refined_orders))
    )
    if length not in coarse_decays or length not in refined_decays:
        raise ValueError("the sheets' coherent ranges open at no commonly sampled length")
    return length


def _spatial_refinement_macros(
    critical_decay_mm: float, coarse_decays: list[float], coarse_orders: list[float]
) -> list[str]:
    """Emit what the halved-spacing rerun does to the boundary and to the sheet near it.

    The boundary moves with the spacing exactly to the extent that it is a
    property of the discretisation, so the ratio of the two boundaries is the
    result and the two lengths are what it is read from. The near-boundary
    steady orders are reported beside it because a stable interpolated crossing
    is not a converged trajectory on either side of it.
    """
    data = _read_json(FIGURES / "spatial_kernel_refined" / "spatial_kernel_summary.json")
    config = cast(JsonObject, data["config"])
    refined_mm = data["critical_decay_mm"]
    if refined_mm is None:
        raise ValueError("the refined sweep does not bracket a crossing; widen its band")
    refined_mm = cast(float, refined_mm)
    spacing_mm = cast(float, config["extent_mm"]) / cast(int, config["side"])
    refined_decays = cast(list[float], data["decay_mm"])
    refined_orders = cast(list[float], data["steady_order"])
    if _sustained_bracket(refined_decays, refined_orders) != _sustained_bracket(
        coarse_decays, coarse_orders
    ):
        raise ValueError("the two sheets no longer cross inside one pair of sampled lengths")
    shared_mm = _shared_coherent_length(
        coarse_decays, coarse_orders, refined_decays, refined_orders
    )
    coarse_order = coarse_orders[coarse_decays.index(shared_mm)]
    refined_order = refined_orders[refined_decays.index(shared_mm)]
    return [
        _macro("spatialRefinedSide", cast(int, config["side"])),
        _macro("spatialRefinedCriticalDecay", f"{refined_mm:.5f}"),
        _macro("spatialRefinedCriticalDecayCells", f"{refined_mm / spacing_mm:.2f}"),
        _macro("spatialRefinedBoundaryRatio", f"{refined_mm / critical_decay_mm:.2f}"),
        _macro("spatialSharedCoherentDecay", f"{shared_mm:.5f}"),
        _macro("spatialSharedCoarseOrder", f"{coarse_order:.4f}"),
        _macro("spatialSharedRefinedOrder", f"{refined_order:.4f}"),
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
    bracket = _sustained_bracket(decays, orders)
    resolved_mm = decays[_first_sustained_index(orders, _COHERENCE_CRITERION)]
    plateau = orders[indices[0] :]

    return [
        _macro("spatialCriticalDecay", f"{critical_decay_mm:.4f}"),
        _macro("spatialBracketLow", f"{bracket[0]:.4f}"),
        _macro("spatialBracketHigh", f"{bracket[1]:.4f}"),
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
        *_spatial_refinement_macros(critical_decay_mm, decays, orders),
    ]


def _wave_macros() -> list[str]:
    """Read the twisted-state sweep: where a winding field survives, and what r reports."""
    data = _read_json(FIGURES / "travelling_wave" / "travelling_wave_summary.json")
    decays = cast(list[float], data["decay_mm"])
    retained = cast(list[int], data["retained_winding"])
    twisted = cast(list[float], data["steady_global_order"])
    local = cast(list[float], data["steady_local_order"])
    control = cast(list[float], data["control_global_order"])
    gaps = cast(list[float], data["steady_coherence_gap"])
    defects = cast(list[float], data["steady_defect_density"])
    config = cast(JsonObject, data["config"])
    spacing_mm = cast(float, config["extent_mm"]) / cast(int, config["side"])

    boundary_mm = cast(float, data["retention_boundary_mm"])
    held = [index for index, value in enumerate(retained) if value != 0]
    lost = [index for index, value in enumerate(retained) if value == 0]
    band = decays.index(FERMI_LAM_MIN)

    return [
        _macro("waveBoundary", f"{boundary_mm:.4f}"),
        _macro("waveBoundaryCells", f"{boundary_mm / spacing_mm:.1f}"),
        _macro("waveRetainedMax", f"{decays[held[-1]]:.4f}"),
        _macro("waveLostMin", f"{decays[lost[0]]:.4f}"),
        _macro("waveRetainedCount", len(held)),
        _macro("waveSampleCount", len(decays)),
        _macro("waveBandOrder", f"{twisted[band]:.4f}"),
        _macro("waveBandLocalOrder", f"{local[band]:.4f}"),
        _macro("waveBandControlOrder", f"{control[band]:.4f}"),
        _macro("waveGapMax", f"{max(gaps):.4f}"),
        _macro("waveControlGapMax", f"{max(gaps[index] for index in lost):.4f}"),
        _macro("waveDefectMaximum", f"{max(defects):.6f}"),
    ]


def _wave_content_macros() -> list[str]:
    """Read the coherence-to-content bound at the two grains the same sweep fixes.

    Eq. (main-content-coherence) bounds a chord by ``L*sqrt(2)*N*sqrt(1-r^2)``,
    and a chord never exceeds 2, so the estimate says something only where the
    population is small enough. The winding sweep fixes both ends on one sheet:
    its own patch is a square of ``2*cells+1`` sites at the measured patch-local
    order, and a nearest-neighbour pair of the same winding is the smallest
    patch there is, where the bound is exactly ``2*sqrt(2)*|sin psi|``.
    """
    data = _read_json(FIGURES / "travelling_wave" / "travelling_wave_summary.json")
    config = WaveConfig(**cast(dict[str, Any], data["config"]))
    band = cast(list[float], data["decay_mm"]).index(FERMI_LAM_MIN)
    order = cast(list[float], data["steady_local_order"])[band]
    sites = (2 * patch_cells(config) + 1) ** 2
    spread = math.sqrt(2.0) * math.sqrt(1.0 - order**2)
    advance = 2.0 * math.pi * config.winding_q / config.side
    return [
        _macro("wavePatchSites", sites),
        _macro("wavePatchChordBound", f"{sites * spread:.1f}"),
        _macro("wavePatchInformativeSites", int(2.0 / spread)),
        _macro("waveNeighbourChordBound", f"{2.0 * math.sqrt(2.0) * abs(math.sin(advance)):.4f}"),
    ]


def _wave_disordered_macros() -> list[str]:
    """Read the same sweep under the published quenched frequency spread."""
    output = FIGURES / "travelling_wave_disordered"
    data = _read_json(output / "travelling_wave_summary.json")
    seeds = _read_json(output / "travelling_wave_seeds.json")
    decays = cast(list[float], data["decay_mm"])
    retained = cast(list[int], data["retained_winding"])
    twisted = cast(list[float], data["steady_global_order"])
    local = cast(list[float], data["steady_local_order"])
    control = cast(list[float], data["control_global_order"])
    defects = cast(list[float], data["steady_defect_density"])
    config = cast(JsonObject, data["config"])

    held = [index for index, value in enumerate(retained) if value != 0]
    band = decays.index(FERMI_LAM_MIN)
    mantissa, exponent = f"{max(defects[index] for index in held):.1e}".split("e")
    orders = [
        value for row in cast(list[list[float]], seeds["steady_global_order"]) for value in row
    ]

    return [
        _macro("waveSpread", f"{cast(float, config['frequency_sigma']):.1f}"),
        _macro("waveSpreadBoundary", f"{cast(float, data['retention_boundary_mm']):.4f}"),
        _macro("waveSpreadRetainedCount", len(held)),
        _macro("waveSpreadBandOrder", f"{twisted[band]:.4f}"),
        _macro("waveSpreadBandLocalOrder", f"{local[band]:.4f}"),
        _macro("waveSpreadBandControlOrder", f"{control[band]:.4f}"),
        _macro("waveSpreadDefectMaximum", rf"{mantissa}\times10^{{{int(exponent)}}}"),
        _macro("waveSpreadShortDecay", f"{decays[0]:.4f}"),
        _macro("waveSpreadShortControl", f"{control[0]:.4f}"),
        _macro("waveSeedCount", len(cast(list[int], seeds["seeds"]))),
        _macro("waveSeedRetained", cast(int, seeds["retained_total"])),
        _macro("waveSeedTotal", cast(int, seeds["run_total"])),
        _macro("waveSeedOrderMin", f"{min(orders):.4f}"),
        _macro("waveSeedOrderMax", f"{max(orders):.4f}"),
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


def _eeg_macros() -> list[str]:
    """Emit exploratory EEG values from its compact, separately generated summary."""
    data = _read_json(FIGURES / "empirical_collapse_summary.json")
    cross = cast(JsonObject, data["cross_subject"])
    calibration = cast(JsonObject, data["small_sample_calibration"])
    bands = cast(JsonObject, data["bands"])
    windows = cast(list[JsonObject], data["window_sensitivity"])
    pooled_samples = next(
        cast(int, row["pooled_samples"]) for row in windows if cast(int, row["window_ms"]) == 100
    )
    return [
        _macro("eegCrossSubjectCount", cross["count"]),
        _macro("eegAMean", f"{cast(float, cross['a_mean']):.3f}"),
        _macro("eegAMin", f"{cast(float, cross['a_min']):.3f}"),
        _macro("eegAMax", f"{cast(float, cross['a_max']):.3f}"),
        _macro("eegRMean", f"{cast(float, cross['r_mean']):.3f}"),
        _macro("eegResidualMean", f"{cast(float, cross['residual_mean']):+.4f}"),
        _macro("eegResidualRmse", f"{cast(float, cross['residual_rmse']):.4f}"),
        _macro("eegResidualMax", f"{cast(float, cross['residual_abs_max']):.4f}"),
        _macro("eegPooledSamples", pooled_samples),
        _macro("eegCalibrationSmallSamples", calibration["samples"]),
        _macro("eegCalibrationReplicas", calibration["replicas"]),
        _macro("eegCalibrationConcentration", f"{cast(float, calibration['concentration']):.1f}"),
        _macro("eegCalibrationAMean", f"{cast(float, calibration['a_mean']):.3f}"),
        _macro("eegCalibrationResidualMean", f"{cast(float, calibration['residual_mean']):+.3f}"),
        _macro("eegCalibrationResidualSd", f"{cast(float, calibration['residual_sd']):.3f}"),
        *[
            _macro(
                f"eegBand{band.title()}",
                f"{cast(float, bands[band]):+.4f}",
            )
            for band in ("theta", "alpha", "beta", "gamma", "broad")
        ],
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


def _largest_usable_bin_count(rows: list[JsonObject], dependence: float) -> tuple[int, float]:
    """Return the coarsest-passing bin count at a dependence, with its concentration floor.

    The estimator is usable at a bin count when some scanned concentration clears
    the floor rule; the published count clears none, so what the protocol needs is
    the largest count that does. Reading the largest rather than the smallest keeps
    the answer a relaxation of the current design rather than a different design.
    """
    usable = [
        (cast(int, row["bins"]), cast(float, row["a_min"]))
        for row in rows
        if row["a_min"] is not None and cast(float, row["dependence"]) == dependence
    ]
    if not usable:
        raise ValueError(f"no scanned bin count is usable at dependence {dependence}")
    return max(usable, key=lambda pair: pair[0])


def _design_macros() -> list[str]:
    """Emit what the proposed site count and bin count can discriminate (N7)."""
    data = _read_json(FIGURES / "collapse_design" / "collapse_design_summary.json")
    observed = cast(JsonObject, data["observed_range"])
    rejection = cast(JsonObject, data["rejection_cases"])
    required = cast(dict[str, int], observed["sites_required_by_dependence"])
    bins, floor = _largest_usable_bin_count(cast(list[JsonObject], data["bin_sensitivity"]), 0.0)
    if rejection["protocol_sites_independent_a_min"] is not None:
        raise ValueError("the protocol site count now clears the floor; rewrite the sentence")
    return [
        _macro("designProtocolSites", observed["protocol_sites"]),
        _macro("designPublishedBins", data["bins"]),
        _macro("designUsableBins", bins),
        _macro("designUsableConcentration", f"{floor:.1f}"),
        _macro("designObservedMax", f"{cast(float, observed['observed_max']):.3f}"),
        _macro("designSitesIndependent", required["0"]),
        _macro("designSitesHalfClustered", required["0.5"]),
        _macro("designSitesClustered", required["1"]),
        _macro("designSitesPerCluster", data["sites_per_cluster"]),
    ]


def _spatial_and_heterogeneous_legs(
    legs: dict[str, JsonObject],
) -> tuple[list[JsonObject], list[JsonObject]]:
    """Split the reduction's legs into the spatial kernels and the detuned controls.

    The uniform leg carries no decay length and is the control the spatial ones
    are read against, so it belongs to neither group.
    """
    spatial = [
        leg
        for leg in legs.values()
        if leg["decay_mm"] is not None and cast(float, leg["frequency_sigma"]) == 0.0
    ]
    heterogeneous = [leg for leg in legs.values() if cast(float, leg["frequency_sigma"]) > 0.0]
    return spatial, heterogeneous


def _reduction_macros() -> list[str]:
    """Emit the aggregation rule's measured accuracy and what displaces it (N8)."""
    data = _read_json(FIGURES / "spatial_reduction" / "spatial_reduction_summary.json")
    legs = cast(dict[str, JsonObject], data["legs"])
    validation = cast(JsonObject, data["mean_field_validation"])
    control = cast(float, legs["mean_field"]["threshold_ratio"])
    spatial, heterogeneous = _spatial_and_heterogeneous_legs(legs)
    ratios = [cast(float, leg["threshold_ratio"]) for leg in spatial]
    decays = [cast(float, leg["decay_mm"]) for leg in spatial]
    neighbours = [cast(float, leg["effective_neighbours"]) for leg in spatial]
    windows = [cast(float, leg["threshold_ratio_low"]) for leg in spatial]
    detuned = [cast(float, leg["threshold_ratio"]) for leg in heterogeneous]
    spread = max(abs(ratio - control) for ratio in ratios)
    return [
        _macro("reductionDecayMin", f"{min(decays):.1f}"),
        _macro("reductionDecayMax", f"{max(decays):.1f}"),
        _macro("reductionNeighbourMin", f"{min(neighbours):.0f}"),
        _macro("reductionNeighbourMax", f"{max(neighbours):.0f}"),
        _macro("reductionRatioMin", f"{min(ratios):.3f}"),
        _macro("reductionRatioMax", f"{max(ratios):.3f}"),
        _macro("reductionMeanFieldRatio", f"{control:.3f}"),
        _macro("reductionRuleSpread", f"{spread:.3f}"),
        _macro("reductionWindowLow", f"{min(windows):.3f}"),
        _macro("reductionFrequencySd", f"{cast(float, heterogeneous[0]['frequency_sigma']):.1f}"),
        _macro("reductionHeterogeneousRatio", f"{min(detuned):.2f}"),
        _macro("reductionBranchResidual", f"{cast(float, validation['residual_max_abs']):.4f}"),
        _macro("reductionBranchPoints", validation["supercritical_points"]),
    ]


def _auc_macros(prefix: str, row: JsonObject) -> list[str]:
    """Emit a separation score with the interval the run resampled for it.

    A score quoted alone invites the reader to compare two of them by eye; the
    interval is what says whether that comparison is available.
    """
    return [
        _macro(prefix, f"{cast(float, row['auc_against_null']):.3f}"),
        _macro(f"{prefix}Low", f"{cast(float, row['auc_low']):.3f}"),
        _macro(f"{prefix}High", f"{cast(float, row['auc_high']):.3f}"),
    ]


def _compatibility_macros() -> list[str]:
    """Emit the overlap estimator's separation, its two silent failures and its limit (N9)."""
    data = _read_json(FIGURES / "compatibility_estimator" / "compatibility_estimator_summary.json")
    baseline = {
        cast(str, row["configuration"]): row for row in cast(list[JsonObject], data["baseline"])
    }
    controls = {
        cast(str, row["control"]): row
        for row in cast(list[JsonObject], data["silent_failure_controls"])
    }
    if not all(row["statistic_alone_is_fooled"] for row in controls.values()):
        raise ValueError("a silent failure no longer fools the statistic; rewrite the sentence")
    if not all(row["rejected_by_diagnostic"] for row in controls.values()):
        raise ValueError("a diagnostic no longer catches its silent failure; rewrite the sentence")
    phase = cast(JsonObject, data["phase_carried_content"])
    if phase["bound_separates_the_models"]:
        raise ValueError("the phase bound now separates the models; rewrite the sentence")
    compatible = baseline["single_valued"]
    incompatible = baseline["disagreeing"]
    shrinkage = cast(JsonObject, controls["shrinkage_toward_shared_prior"]["assessment"])
    bias = cast(JsonObject, controls["independent_per_region_bias"]["assessment"])
    honest = cast(float, controls["shrinkage_toward_shared_prior"]["honest_null_statistic"])
    return [
        _macro("overlapTrials", data["trials"]),
        _macro("overlapSites", data["overlap"]),
        _macro("overlapDecodingError", f"{cast(float, data['decoding_error']):.1f}"),
        *_auc_macros("overlapCompatibleAuc", compatible),
        *_auc_macros("overlapIncompatibleAuc", incompatible),
        _macro("overlapIncompatibleZ", f"{cast(float, incompatible['z_against_null']):.0f}"),
        _macro("overlapShrinkageStatistic", f"{cast(float, shrinkage['statistic']):.4f}"),
        _macro("overlapBiasStatistic", f"{cast(float, bias['statistic']):.4f}"),
        _macro("overlapHonestStatistic", f"{honest:.4f}"),
        _macro("overlapPhaseShareBuilt", f"{cast(float, phase['phase_derived_share']):.3f}"),
        _macro("overlapPhaseShareFree", f"{cast(float, phase['phase_free_share']):.3f}"),
        _macro("overlapPhaseBoundBuilt", f"{cast(float, phase['phase_derived_bound']):.3f}"),
        _macro("overlapPhaseBoundFree", f"{cast(float, phase['phase_free_bound']):.3f}"),
        _macro("overlapWorstUsableError", f"{cast(float, data['worst_usable_error']):.1f}"),
        _macro("overlapSmallestTerritory", data["smallest_usable_overlap"]),
    ]


def _scan_exponent(delay: JsonObject, entry: JsonObject) -> float:
    """Fit one escape level over the legs the finite-`N` delay fit uses.

    ``fit_power_law`` is the estimator that produced ``\rampDelayExponent``, so
    the reference and the measurement it is a reference for are one function of
    one set of legs, differing only in the ensemble the delays came from. A
    second estimator here would leave the comparison reading two things.
    """
    uncensored = cast(list[float], delay["uncensored_speeds"])
    excess = cast(list[float | None], entry["coupling_excess"])
    pairs = [
        (speed, value)
        for speed, value in zip(cast(list[float], delay["speeds"]), excess, strict=True)
        if speed in uncensored and value is not None
    ]
    speeds = np.array([speed for speed, _ in pairs])
    delays = np.array([value for _, value in pairs])
    return fit_power_law(speeds, delays).exponent


def _quasistatic_macros() -> list[str]:
    """Emit the rate the quasi-static reading requires and where it is unavailable (N12)."""
    data = _read_json(FIGURES / "quasistatic_error" / "quasistatic_error_summary.json")
    manuscript = cast(JsonObject, data["manuscript"])
    delay = cast(JsonObject, data["bifurcation_delay"])
    crossing = cast(JsonObject, cast(JsonObject, data["legs"])["crossing"])
    runs = cast(list[JsonObject], crossing["runs"])
    cited = cast(list[float], manuscript["cited_ratio_range"])
    if crossing["admissible_speed"] is not None:
        raise ValueError("the crossing leg now admits a speed; rewrite the sentence")
    scan = cast(list[JsonObject], delay["criterion_scan"])
    if len(scan) != 3:
        raise ValueError("the criterion scan is no longer three levels; rewrite the sentence")
    published, mid, tight = scan
    terminal = [cast(float, run["terminal_error"]) for run in runs]
    speeds = [cast(float, run["speed"]) for run in runs]
    return [
        _macro("quasistaticRatioMin", f"{cited[0]:.0f}"),
        _macro("quasistaticRatioMax", rf"{cited[1] / 1000:.0f}\times10^{{3}}"),
        _macro(
            "quasistaticTrackableAtMaxRatio",
            f"{cast(float, manuscript['trackable_delta_at_fast_end']):g}",
        ),
        _macro(
            "quasistaticTrackableAtMinRatio",
            f"{cast(float, manuscript['trackable_delta_at_slow_end']):g}",
        ),
        _macro("quasistaticCrossingSpeedMin", f"{min(speeds):g}"),
        _macro("quasistaticCrossingSpeedMax", f"{max(speeds):g}"),
        _macro("quasistaticCrossingResidualMin", f"{min(terminal):.3f}"),
        _macro("quasistaticCrossingResidualMax", f"{max(terminal):.3f}"),
        _macro("quasistaticSeedOrder", f"{cast(float, delay['seed_order']):.4f}"),
        _macro("quasistaticDelayExponent", f"{_scan_exponent(delay, published):.3f}"),
        _macro("quasistaticEscapeMid", f"{cast(float, mid['escape']):g}"),
        _macro("quasistaticEscapeMidExponent", f"{_scan_exponent(delay, mid):.3f}"),
        _macro("quasistaticEscapeTight", f"{cast(float, tight['escape']):g}"),
        _macro("quasistaticEscapeTightExponent", f"{_scan_exponent(delay, tight):.3f}"),
        _macro("quasistaticSpeedCount", len(cast(list[float], delay["speeds"]))),
        _macro("quasistaticUncensoredCount", len(cast(list[float], delay["uncensored_speeds"]))),
    ]


def _fluctuating_macros() -> list[str]:
    """Emit which statistic of a varying coupling the threshold is read against (N13)."""
    data = _read_json(FIGURES / "fluctuating_coupling" / "fluctuating_coupling_summary.json")
    fast = cast(JsonObject, data["fast_limit"])
    slow = cast(JsonObject, data["slow_limit"])
    rejection = cast(JsonObject, data["mean_substitution_rejection"])
    strongest = cast(JsonObject, rejection["strongest"])
    config = cast(JsonObject, data["config"])
    return [
        _macro("noiseFastTau", f"{cast(float, fast['correlation_time']):g}"),
        _macro("noiseSlowTau", f"{cast(float, slow['correlation_time']):g}"),
        _macro("noiseFastMeanGap", f"{cast(float, fast['worst_mean_substitution_gap']):.3f}"),
        _macro("noiseFastQuasiGap", f"{cast(float, fast['worst_quasi_static_gap']):.3f}"),
        _macro("noiseSlowMeanGap", f"{cast(float, slow['worst_mean_substitution_gap']):.3f}"),
        _macro("noiseSlowQuasiGap", f"{cast(float, slow['worst_quasi_static_gap']):.3f}"),
        _macro("noiseSlowDrives", slow["drives"]),
        _macro("noiseRefusals", rejection["count"]),
        _macro("noiseStrongestMean", f"{cast(float, strongest['mean']):g}"),
        _macro("noiseStrongestAmplitude", f"{cast(float, strongest['amplitude']):g}"),
        _macro("noiseStrongestTau", f"{cast(float, strongest['correlation_time']):g}"),
        _macro("noiseStrongestOrder", f"{cast(float, strongest['measured_order']):.4f}"),
        _macro("noiseStrongestSpread", f"{cast(float, strongest['order_spread']):.4f}"),
        _macro("noiseSeedOrder", f"{cast(float, config['seed_order']):g}"),
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
        "% S2b: a winding state on the same sheet",
        *_wave_macros(),
        "",
        "% S2b': the same sweep read against the coherence-to-content bound",
        *_wave_content_macros(),
        "",
        "% S2c: the same winding state under the published frequency spread",
        *_wave_disordered_macros(),
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
        *_eeg_macros(),
        "",
        "% F5/F6: bounded follow-up studies",
        *_followup_macros(),
        "",
        "% N7: what the collapse design can discriminate",
        *_design_macros(),
        "",
        "% N8: the spatial reduction of the scalar threshold",
        *_reduction_macros(),
        "",
        "% N9: the overlap-compatibility estimator",
        *_compatibility_macros(),
        "",
        "% N12: the quasi-static residual as a function of rate",
        *_quasistatic_macros(),
        "",
        "% N13: a fluctuating coupling and the threshold",
        *_fluctuating_macros(),
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
