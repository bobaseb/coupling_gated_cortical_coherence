"""Figures and a written report for N7--N9, built from their saved summaries.

Reads the three JSON artifacts the numerical extensions leave behind and writes
the figures and `NUMERICAL_EXTENSIONS_REPORT.md` beside them. It integrates
nothing, draws no sample and recomputes no estimator: a restyled figure costs a
second of plotting rather than the run behind it, which is the direction
`tach.toml` enforces by placing `report` above `simulation`.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import matplotlib.pyplot as plt
import numpy as np

from collapse_design import bessel_ratio


FIGURES = Path(__file__).resolve().parent / "figures"
DESIGN_DIR = FIGURES / "collapse_design"
REDUCTION_DIR = FIGURES / "spatial_reduction"
COMPATIBILITY_DIR = FIGURES / "compatibility_estimator"

Row = dict[str, Any]


def load(directory: Path, name: str) -> Row:
    """Read one saved summary, failing loudly when the run has not been done."""
    path = directory / name
    if not path.exists():
        raise FileNotFoundError(f"{path} is missing; run the sweep that writes it first")
    return dict(json.loads(path.read_text(encoding="utf-8")))


# ── N7: the concentration range that makes the collapse a test ─────────────


def _curve_panel(axis: Any, summary: Row) -> None:
    """The Bessel ratio, its tangent, and the range a recording actually saw."""
    grid = np.linspace(0.0, 4.5, 200)
    observed = summary["observed_range"]
    axis.plot(grid, [bessel_ratio(a) for a in grid], "k-", lw=2.2, label=r"$I_1(a)/I_0(a)$")
    axis.plot(grid, grid / 2, "--", color="tab:red", lw=1.8, label=r"tangent $a/2$")
    axis.axvspan(
        observed["observed_min"],
        observed["observed_max"],
        color="tab:green",
        alpha=0.2,
        label="observed ds005620 range",
    )
    axis.set(xlabel="concentration $a$", ylabel="$r$", ylim=(0.0, 1.05))
    axis.legend(fontsize=8)
    axis.grid(alpha=0.3)


def _floor_panel(axis: Any, rows: list[Row]) -> None:
    """Each site count's usable separation against its own residual floor.

    The two curves of a colour are the same calibration read twice: where the
    solid one is above the dashed one a measurement at that count can tell the
    curve from its tangent, and where it is below it cannot.
    """
    grouped: dict[int, list[Row]] = {}
    for row in sorted(rows, key=lambda row: row["concentration"]):
        grouped.setdefault(int(row["n_sites"]), []).append(row)
    for index, (count, group) in enumerate(sorted(grouped.items())):
        colour = f"C{index}"
        concentrations = [row["concentration"] for row in group]
        axis.plot(
            concentrations,
            [row["separation"] for row in group],
            "-o",
            ms=3,
            color=colour,
            label=f"separation, {count} sites",
        )
        axis.plot(
            concentrations, [row["floor"] for row in group], "--", color=colour, label="_floor"
        )
    axis.set(xlabel="concentration $a$", ylabel="separation and estimator floor", yscale="log")
    axis.legend(fontsize=7)
    axis.grid(alpha=0.3)


def collapse_figure(summary: Row, out: Path) -> None:
    """The curve against its tangent, and the separation against the floor."""
    rows = [row for row in summary["calibration"] if row["dependence"] == 0.0]
    figure, (curve_axis, floor_axis) = plt.subplots(1, 2, figsize=(11.5, 4.3))
    _curve_panel(curve_axis, summary)
    _floor_panel(floor_axis, rows)
    figure.tight_layout()
    figure.savefig(out, dpi=180)
    plt.close(figure)


def collapse_section(summary: Row) -> list[str]:
    observed = summary["observed_range"]
    lines = [
        "## N7 — the concentration range that makes the collapse a test",
        "",
        f"Dependence model: {summary['dependence_model']}, "
        f"{summary['sites_per_cluster']} sites per cluster.",
        f"Floor rule: {summary['floor_rule']}. "
        f"Estimator trusted up to a = {summary['estimator_valid_max_concentration']}.",
        "",
        "| sites | a_min, independent | a_min, dependence 0.5 | a_min, dependence 1 |"
        " max tolerable dependence |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in summary["specification"]:
        lines.append(
            f"| {row['n_sites']} | {row['a_min_at_dependence_0']} | "
            f"{row['a_min_at_dependence_0.5']} | {row['a_min_at_dependence_1']} | "
            f"{row['maximum_tolerable_dependence']} |"
        )
    lines += [
        "",
        "| bins at 100 sites | dependence | a_min |",
        "|---:|---:|---:|",
        *[
            f"| {row['bins']} | {row['dependence']} | {row['a_min']} |"
            for row in summary["bin_sensitivity"]
        ],
        "",
        f"At the observed ceiling a = {observed['observed_max']} the curve stands "
        f"{observed['gap_at_observed_max']:.4f} from its tangent. Independent sites "
        f"required: {observed['sites_required_by_dependence']}; the proposed protocol "
        f"permits {observed['protocol_sites']} and the exploratory bins pool "
        f"{observed['pooled_sites']}.",
        "",
    ]
    return lines


# ── N8: sensitivity of the threshold to the spatial reduction ──────────────


def _branch_panel(axis: Any, summary: Row) -> None:
    """Every leg's steady order against the coupling it reduces to."""
    legs = summary["legs"]
    for name, payload in legs.items():
        axis.plot(payload["coupling"], payload["steady_order"], "o-", ms=3, label=name)
    axis.plot(
        legs["mean_field"]["coupling"],
        summary["mean_field_validation"]["reference_order"],
        "k--",
        lw=1.6,
        label="self-consistency",
    )
    axis.axvline(summary["scalar_threshold"], color="0.4", ls=":", lw=1.4)
    axis.set(xlabel="reduced coupling (row sum)", ylabel="steady order $r$", xscale="log")
    axis.legend(fontsize=7)
    axis.grid(alpha=0.3)


def _threshold_panel(axis: Any, legs: dict[str, Row]) -> None:
    """Both threshold estimates, against the value the scalar model proves."""
    names = [name for name, payload in legs.items() if payload["threshold"] is not None]
    axis.errorbar(
        range(len(names)),
        [legs[name]["threshold_ratio"] for name in names],
        yerr=[
            [legs[name]["threshold_ratio"] - legs[name]["threshold_ratio_low"] for name in names],
            [legs[name]["threshold_ratio_high"] - legs[name]["threshold_ratio"] for name in names],
        ],
        fmt="o",
        capsize=4,
        color="tab:blue",
        label="extrapolated intercept",
    )
    crossings = [name for name in names if legs[name]["crossing"] is not None]
    axis.plot(
        [names.index(name) for name in crossings],
        [legs[name]["crossing_ratio"] for name in crossings],
        "D",
        color="tab:red",
        label="two-size crossing",
    )
    axis.axhline(1.0, color="0.4", ls=":", lw=1.4)
    axis.set_xticks(range(len(names)))
    axis.set_xticklabels(names, rotation=30, ha="right", fontsize=7)
    axis.set(ylabel="measured threshold / $2D$")
    axis.legend(fontsize=7)
    axis.grid(alpha=0.3)


def reduction_figure(summary: Row, out: Path) -> None:
    """Steady order against reduced coupling, and where each leg's threshold sits."""
    figure, (sweep_axis, threshold_axis) = plt.subplots(1, 2, figsize=(11.5, 4.3))
    _branch_panel(sweep_axis, summary)
    _threshold_panel(threshold_axis, summary["legs"])
    figure.tight_layout()
    figure.savefig(out, dpi=180)
    plt.close(figure)


def reduction_section(summary: Row) -> list[str]:
    validation = summary["mean_field_validation"]
    lines = [
        "## N8 — sensitivity of the threshold to the spatial reduction",
        "",
        f"Aggregation rule: {summary['aggregation_rule']}.",
        f"Scalar threshold under test: {summary['scalar_threshold']}. "
        f"Fit windows: {summary['fit_windows']}; coarse sheet side divided by "
        f"{summary['finite_size_ratio']}.",
        "",
        "| leg | decay (mm) | frequency sd | effective neighbours | extrapolated / 2D |"
        " window bracket / 2D | size crossing / 2D |",
        "|---|---:|---:|---:|---:|---|---:|",
    ]
    for name, payload in summary["legs"].items():
        threshold = payload["threshold"]
        crossing = payload["crossing"]
        extrapolated = "—" if threshold is None else f"{payload['threshold_ratio']:.3f}"
        bracket = (
            "—"
            if threshold is None
            else f"{payload['threshold_ratio_low']:.3f}–{payload['threshold_ratio_high']:.3f}"
        )
        crossed = "—" if crossing is None else f"{payload['crossing_ratio']:.3f}"
        lines.append(
            f"| {name} | {payload['decay_mm']} | {payload['frequency_sigma']} | "
            f"{payload['effective_neighbours']:.1f} | {extrapolated} | {bracket} | {crossed} |"
        )
    lines += [
        "",
        f"Mean-field validation against the self-consistency branch over "
        f"{validation['supercritical_points']} supercritical couplings: "
        f"largest absolute residual {validation['residual_max_abs']:.4f}, "
        f"mean {validation['residual_mean']:+.4f}.",
        "",
    ]
    return lines


# ── N9: a compatibility estimator validated against constructed answers ────


def compatibility_figure(summary: Row, out: Path) -> None:
    """The statistic on each constructed answer, and how it degrades."""
    baseline = summary["baseline"]
    figure, (bar_axis, sweep_axis) = plt.subplots(1, 2, figsize=(11.5, 4.3))
    names = [row["configuration"] for row in baseline]
    values = [row["statistic"] for row in baseline]
    errors = [2.0 * row["trial_sd"] for row in baseline]
    bar_axis.bar(range(len(names)), values, yerr=errors, capsize=3, color="tab:blue")
    bar_axis.set_xticks(range(len(names)))
    bar_axis.set_xticklabels(names, rotation=35, ha="right", fontsize=7)
    bar_axis.set(ylabel="mean overlap total variation")
    bar_axis.grid(alpha=0.3, axis="y")

    errors_sweep = summary["error_degradation"]
    coverage = summary["coverage_degradation"]
    sweep_axis.plot(
        [row["error"] for row in errors_sweep],
        [row["assessment"]["auc_against_null"] for row in errors_sweep],
        "o-",
        label="decoding error",
    )
    twin = sweep_axis.twiny()
    twin.plot(
        [row["overlap"] for row in coverage],
        [row["assessment"]["auc_against_null"] for row in coverage],
        "s--",
        color="tab:red",
        label="shared sites",
    )
    sweep_axis.set(xlabel="per-site decoding error", ylabel="AUC against the constructed null")
    twin.set_xlabel("shared sites (overlap)")
    sweep_axis.grid(alpha=0.3)
    figure.legend(fontsize=8, loc="lower left", bbox_to_anchor=(0.56, 0.16))
    figure.tight_layout()
    figure.savefig(out, dpi=180)
    plt.close(figure)


def compatibility_section(summary: Row) -> list[str]:
    phase = summary["phase_carried_content"]
    lines = [
        "## N9 — a compatibility estimator validated against constructed answers",
        "",
        f"Restriction map: {summary['restriction_map']}.",
        f"Thresholds: {summary['thresholds']}. Trials: {summary['trials']}; "
        f"overlap: {summary['overlap']} sites.",
        "",
        "| configuration | statistic | z | AUC | phase bound | phase share | admitted |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for row in summary["baseline"]:
        lines.append(
            f"| {row['configuration']} | {row['statistic']:.4f} | "
            f"{row['z_against_null']:.1f} | {row['auc_against_null']:.3f} | "
            f"{row['phase_bound']:.4f} | {row['phase_share']:.3f} | {row['admitted']} |"
        )
    lines += [
        "",
        "| control | manufactures | statistic | fooled the statistic |"
        " information | accuracy | calibration |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for control in summary["silent_failure_controls"]:
        lines.append(
            f"| {control['control']} | {control['manufactures']} | "
            f"{control['assessment']['statistic']:.4f} | "
            f"{control['statistic_alone_is_fooled']} | "
            f"{control['rejected_by_information']} | {control['rejected_by_accuracy']} | "
            f"{control['rejected_by_calibration']} |"
        )
    lines += [
        "",
        f"Phase-derived statistic on the constructed counterexample: "
        f"{summary['phase_observable_control']['required_failure_observed']}.",
        f"Share of content entropy the phase carries: "
        f"{phase['phase_derived_share']:.3f} when the content is built from the phase and "
        f"{phase['phase_free_share']:.3f} when it is not; the phase bound reads "
        f"{phase['phase_derived_bound']:.3f} and {phase['phase_free_bound']:.3f}, so it "
        f"separates the two models: {phase['bound_separates_the_models']}.",
        "",
        f"Worst decoding error still admitted and separated: {summary['worst_usable_error']}. "
        f"Smallest shared territory still usable: {summary['smallest_usable_overlap']} sites.",
        "",
    ]
    return lines


# ── assembly ───────────────────────────────────────────────────────────────


def build_report(design: Row, reduction: Row, compatibility: Row) -> str:
    """The three sections, with the header that says where they came from."""
    lines = [
        "# N7–N9: the numerical extensions",
        "",
        "Generated by simulations/numerical_extensions_report.py from the saved",
        "summaries; do not edit manually. Every number here is read from a JSON",
        "artifact a run left behind, and nothing in this file integrates, samples",
        "or estimates.",
        "",
        *collapse_section(design),
        *reduction_section(reduction),
        *compatibility_section(compatibility),
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=FIGURES)
    args = parser.parse_args()
    design = load(DESIGN_DIR, "collapse_design_summary.json")
    reduction = load(REDUCTION_DIR, "spatial_reduction_summary.json")
    compatibility = load(COMPATIBILITY_DIR, "compatibility_estimator_summary.json")
    collapse_figure(design, DESIGN_DIR / "collapse_design.png")
    reduction_figure(reduction, REDUCTION_DIR / "spatial_reduction.png")
    compatibility_figure(compatibility, COMPATIBILITY_DIR / "compatibility_estimator.png")
    report = args.output / "NUMERICAL_EXTENSIONS_REPORT.md"
    report.write_text(build_report(design, reduction, compatibility), encoding="utf-8")
    print(f"wrote {report}")


if __name__ == "__main__":
    main()
