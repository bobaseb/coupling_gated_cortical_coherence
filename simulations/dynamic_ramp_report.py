"""Generate the S1 dynamic-ramp figures and numerical report from checkpoints."""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.figure import Figure
from numpy.typing import NDArray

from bifurcation import bessel_ratio, coherent_r
from dynamic_ramp_analysis import (
    OnsetFit,
    PowerLawFit,
    collapse_deviation,
    fit_onset_exponent,
    fit_power_law,
    replica_escape_couplings,
    split_span_exponents,
    bootstrap_delay_exponent,
)


FloatArray = NDArray[np.float64]
# Anchored on this file, not the working directory: simulations/README.md.
FIGURE_DIR = Path(__file__).resolve().parent / "figures"
# The legs whose per-leg onset and collapse fits the publication reports, at
# decade spacing.
SPEEDS = (0.1, 0.01, 0.001, 0.0001)
# Every leg the delay measurement uses. The delay is one number per leg, so it
# can carry a denser sweep than the per-leg fits can; the extra speeds are
# placed inside the physiologically converted window and on either side of it.
DELAY_SPEEDS = (0.1, 0.02, 0.01, 0.005, 0.002, 0.001, 0.0002, 0.0001)
ESCAPE_LEVEL = 0.2
SUSTAIN = 3
# How close the two half-span exponents must be for the report to call the
# shortfall stable. A tenth of the shortfall itself, so agreement means the
# halves are closer to each other than either is to the predicted 1/2.
_SPLIT_AGREEMENT = 0.05


@dataclass(frozen=True)
class Leg:
    speed: float
    n_oscillators: int
    coupling: FloatArray
    order_mean: FloatArray
    order_std: FloatArray
    order_replicas: FloatArray
    concentration_mean: FloatArray
    concentration_replicas: FloatArray


@dataclass(frozen=True)
class LegMetrics:
    speed: float
    escaped: int
    delay_mean: float
    delay_sd: float
    collapse_deviation: float
    onset: OnsetFit
    onset_reference: float


@dataclass(frozen=True)
class SizeMetrics:
    """One leg of the fixed-speed population-size control."""

    n_oscillators: int
    delay_mean: float
    delay_error: float
    precritical_order_max: float

    @property
    def scaled_delay(self) -> float:
        """Delay divided by the predicted ``sqrt(log N)`` dependence."""
        return self.delay_mean / math.sqrt(math.log(self.n_oscillators))


def adiabatic_onset_exponent(coupling: FloatArray) -> float:
    """Return what the onset estimator reports for the exact stationary branch.

    The estimator's window runs well past threshold, so it recovers something
    short of the asymptotic 1/2 even on the branch whose exponent is exactly
    1/2. That value, sampled on a leg's own coupling grid, is the reference a
    ramped exponent measured on that grid has to be read against; the residual
    bias is a property of the window rather than of the drive.
    """
    branch = np.array([coherent_r(float(value)) for value in coupling])
    return fit_onset_exponent(coupling, branch).exponent


def _load_leg(path: Path) -> Leg:
    with np.load(path, allow_pickle=False) as saved:
        config = json.loads(str(saved["config"]))
        return Leg(
            speed=float(config["ramp_speed"]),
            n_oscillators=int(config["n_oscillators"]),
            coupling=np.asarray(saved["coupling"]),
            order_mean=np.asarray(saved["order_mean"]),
            order_std=np.asarray(saved["order_std"]),
            order_replicas=np.asarray(saved["order_replicas"]),
            concentration_mean=np.asarray(saved["concentration_mean"]),
            concentration_replicas=np.asarray(saved["concentration_replicas"]),
        )


def _speed_path(speed: float) -> Path:
    return FIGURE_DIR / f"dynamic_ramp_replicas_v{speed:.0e}.npz"


def _load_legs(speeds: tuple[float, ...]) -> list[Leg]:
    return [_load_leg(_speed_path(speed)) for speed in speeds]


def _metrics(leg: Leg) -> LegMetrics:
    escape = replica_escape_couplings(leg.coupling, leg.order_replicas, ESCAPE_LEVEL, SUSTAIN)
    finite = escape[np.isfinite(escape)]
    postcritical = leg.coupling >= 2.0
    deviation = collapse_deviation(
        leg.concentration_replicas[postcritical].ravel(),
        leg.order_replicas[postcritical].ravel(),
    )
    return LegMetrics(
        speed=leg.speed,
        escaped=int(finite.size),
        delay_mean=float(np.mean(finite) - 2.0),
        delay_sd=float(np.std(finite, ddof=1)) if finite.size > 1 else float("nan"),
        collapse_deviation=deviation,
        onset=fit_onset_exponent(leg.coupling, leg.order_mean),
        onset_reference=adiabatic_onset_exponent(leg.coupling),
    )


def _save_figure(fig: Figure, name: str) -> None:
    fig.tight_layout()
    fig.savefig(FIGURE_DIR / name, dpi=200)
    plt.close(fig)


def _plot_bifurcation(legs: list[Leg]) -> None:
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    static_k = np.linspace(1.5, 2.5, 180)
    static_r = np.array([coherent_r(float(value)) for value in static_k])
    ax.plot(static_k, static_r, color="black", lw=2.0, label="stationary coherent branch")
    for leg_index, leg in enumerate(legs):
        (mean_line,) = ax.plot(leg.coupling, leg.order_mean, lw=1.7, label=rf"$v={leg.speed:g}$")
        sem = leg.order_std / np.sqrt(leg.order_replicas.shape[1])
        ax.fill_between(
            leg.coupling,
            leg.order_mean - sem,
            leg.order_mean + sem,
            alpha=0.12,
        )
        escape = replica_escape_couplings(leg.coupling, leg.order_replicas, ESCAPE_LEVEL, SUSTAIN)
        valid = np.isfinite(escape)
        if np.any(valid):
            sample_index = np.searchsorted(leg.coupling, escape[valid])
            replica_index = np.flatnonzero(valid)
            ax.scatter(
                escape[valid],
                leg.order_replicas[sample_index, replica_index],
                color=mean_line.get_color(),
                edgecolors="white",
                linewidths=0.3,
                s=18,
                alpha=0.8,
                label="replica escapes" if leg_index == 0 else "_nolegend_",
                zorder=4,
            )
    ax.axhline(ESCAPE_LEVEL, color="0.6", ls="-.", lw=0.8)
    ax.axhline(1.0 / np.sqrt(2000), color="0.4", ls=":", label=r"$1/\sqrt{2000}$")
    ax.axvline(2.0, color="0.5", ls="--", lw=1.0)
    ax.set(xlabel=r"coupling $K$", ylabel=r"phase order $r$", ylim=(0.0, 0.7))
    ax.legend(fontsize=8, ncol=2)
    ax.grid(alpha=0.25)
    _save_figure(fig, "dynamic_ramp_bifurcation_delay.png")


def _delay_arrays(metrics: list[LegMetrics]) -> tuple[FloatArray, FloatArray, FloatArray]:
    uncensored = [item for item in metrics if item.escaped == 32]
    speeds = np.array([item.speed for item in uncensored])
    delays = np.array([item.delay_mean for item in uncensored])
    errors = np.array([item.delay_sd / np.sqrt(item.escaped) for item in uncensored])
    return speeds, delays, errors


def _size_leg_metrics(leg: Leg) -> SizeMetrics:
    escape = replica_escape_couplings(leg.coupling, leg.order_replicas)
    return SizeMetrics(
        n_oscillators=leg.n_oscillators,
        delay_mean=float(np.nanmean(escape) - 2.0),
        delay_error=float(np.nanstd(escape, ddof=1) / np.sqrt(np.isfinite(escape).sum())),
        precritical_order_max=float(leg.order_replicas[leg.coupling < 2.0].max()),
    )


def _size_metrics() -> list[SizeMetrics]:
    """Metrics for the three population sizes run at the same ramp speed.

    ``precritical_order_max`` is the largest order any replica reaches before
    threshold. The escape level is a fixed absolute number, so where that
    maximum approaches it the measured delay is set by the critical
    fluctuation floor rather than by the ramp.
    """
    paths = (
        FIGURE_DIR / "dynamic_ramp_N500_v1e-02.npz",
        _speed_path(0.01),
        FIGURE_DIR / "dynamic_ramp_N8000_v1e-02.npz",
    )
    return [_size_leg_metrics(_load_leg(path)) for path in paths]


def _plot_delay_scaling(metrics: list[LegMetrics]) -> None:
    speeds, delays, errors = _delay_arrays(metrics)
    fit = fit_power_law(speeds, delays)
    grid = np.geomspace(speeds.min(), speeds.max(), 100)
    fig, axes = plt.subplots(1, 2, figsize=(10.0, 4.2))
    axes[0].fill_between(
        grid,
        fit.prefactor * grid**fit.exponent_low,
        fit.prefactor * grid**fit.exponent_high,
        color="tab:orange",
        alpha=0.18,
        label="95% slope interval",
    )
    axes[0].errorbar(speeds, delays, yerr=errors, fmt="o", capsize=3, label="measured")
    axes[0].plot(grid, fit.prefactor * grid**fit.exponent, label=rf"fit $v^{{{fit.exponent:.3f}}}$")
    axes[0].plot(grid, np.sqrt(2.0 * grid * np.log(2000)), ls="--", label=r"$\sqrt{2v\ln N}$")
    axes[0].set(xscale="log", yscale="log", xlabel=r"ramp speed $v$", ylabel=r"delay $\Delta K$")
    axes[0].legend(fontsize=8)
    sizes = _size_metrics()
    axes[1].errorbar(
        [math.sqrt(math.log(item.n_oscillators)) for item in sizes],
        [item.delay_mean for item in sizes],
        yerr=[item.delay_error for item in sizes],
        fmt="o-",
        capsize=3,
    )
    axes[1].set(xlabel=r"$\sqrt{\ln N}$", ylabel=r"delay $\Delta K$ at $v=10^{-2}$")
    for axis in axes:
        axis.grid(alpha=0.25)
    _save_figure(fig, "dynamic_ramp_delay_scaling.png")


def _plot_collapse(legs: list[Leg], metrics: list[LegMetrics]) -> None:
    fig, ax = plt.subplots(figsize=(6.6, 4.8))
    concentration_grid = np.linspace(0.0, 2.5, 240)
    curve = np.array([bessel_ratio(float(value)) for value in concentration_grid])
    ax.plot(concentration_grid, curve, color="black", lw=2.0, label=r"$I_1(a)/I_0(a)$")
    for leg, metric in zip(legs, metrics, strict=True):
        ax.plot(
            leg.concentration_mean,
            leg.order_mean,
            lw=1.3,
            label=rf"$v={leg.speed:g}$, Dev={metric.collapse_deviation:.4f}",
        )
    ax.set(xlabel=r"log-density concentration $a$", ylabel=r"order parameter $r$")
    ax.legend(fontsize=8)
    ax.grid(alpha=0.25)
    _save_figure(fig, "dynamic_ramp_collapse.png")


def _plot_onset(metrics: list[LegMetrics]) -> None:
    speeds = np.array([item.speed for item in metrics])
    exponents = np.array([item.onset.exponent for item in metrics])
    references = np.array([item.onset_reference for item in metrics])
    fig, ax = plt.subplots(figsize=(6.6, 4.4))
    ax.plot(speeds, exponents, "o-", lw=1.7)
    ax.plot(speeds, references, "s--", color="green", lw=1.3, label="stationary branch, same grid")
    ax.axhline(0.5, color="0.5", ls="--", label=r"asymptotic $\beta=1/2$")
    ax.axhline(1.0, color="red", ls=":", label=r"linear $\beta=1$")
    ax.set(xscale="log", xlabel=r"ramp speed $v$", ylabel=r"effective onset exponent $\beta$")
    ax.legend(fontsize=8)
    ax.grid(alpha=0.25)
    _save_figure(fig, "dynamic_ramp_onset_exponent.png")


def _table_rows(metrics: list[LegMetrics]) -> str:
    return "\n".join(
        f"| {item.speed:g} | {item.escaped}/32 | {item.delay_mean:.4f} | "
        f"{item.delay_sd:.4f} | {item.collapse_deviation:.5f} | {item.onset.exponent:.3f} |"
        for item in metrics
    )


def _fit_text(fit: PowerLawFit) -> str:
    return f"{fit.exponent:.3f} [{fit.exponent_low:.3f}, {fit.exponent_high:.3f}]"


def _delay_paragraph(metrics: list[LegMetrics]) -> str:
    """The delay scaling, its interval, and the split-span consistency check."""
    speeds, delays, _ = _delay_arrays(metrics)
    delay_fit = fit_power_law(speeds, delays)
    fast_fit, slow_fit = split_span_exponents(speeds, delays)
    censored = ", ".join(f"v={item.speed:g}" for item in metrics if item.escaped != 32)
    agree = abs(fast_fit.exponent - slow_fit.exponent) < _SPLIT_AGREEMENT
    resolved = delay_fit.exponent_high < 0.5
    return f"""The delay fit uses the {speeds.size} uncensored legs of {len(metrics)}, excluding
{censored}, and gives exponent {_fit_text(delay_fit)} against the predicted 0.5,
which the interval {"excludes" if resolved else "does not exclude"}.

Split at the median speed, the faster half returns {_fit_text(fast_fit)} and the
slower half {_fit_text(slow_fit)}. The point estimates
{"agree" if agree else "disagree"} to within {_SPLIT_AGREEMENT}, but each half is
three legs over one decade and its own interval is far wider than the shortfall
being tested, so the split is a consistency check and not a second measurement:
it does not resolve drift across the span, and neither half
resolves the shortfall by itself."""


def _bootstrap_paragraph(legs: list[Leg], metrics: list[LegMetrics]) -> str:
    """The replica-bootstrap interval and fraction above one-half."""
    speeds = []
    replica_delays = []
    for leg, metric in zip(legs, metrics, strict=True):
        if metric.escaped == 32:
            escape = replica_escape_couplings(
                leg.coupling, leg.order_replicas, ESCAPE_LEVEL, SUSTAIN
            )
            speeds.append(leg.speed)
            replica_delays.append(escape - 2.0)

    result = bootstrap_delay_exponent(np.array(speeds), replica_delays)

    return (
        f"Bootstrapping the {result.n_boot} resamples over replicas within each of the "
        f"{len(speeds)}\nuncensored legs gives a 95% CI of [{result.ci_low:.3f}, "
        f"{result.ci_high:.3f}] for the exponent. The\nfraction of bootstrap samples "
        f"with an exponent at or above 0.5 is {result.p_above:.3f}."
    )


def _collapse_paragraph(metrics: list[LegMetrics], diagnostics: list[LegMetrics]) -> str:
    """The Bessel-collapse floor, and whether any leg reaches twice it."""
    floor = next(item.collapse_deviation for item in diagnostics if item.speed == min(SPEEDS))
    threshold = 2.0 * floor
    bracketed = any(item.collapse_deviation >= threshold for item in metrics)
    legs = ", ".join(f"{speed:g}" for speed in SPEEDS)
    return f"""Collapse deviations and onset exponents are read on the decade-spaced legs
v={legs}. The slowest-ramp deviation floor is Dev_0={floor:.5f};
2 Dev_0={threshold:.5f}. The critical-speed crossing is
{"bracketed" if bracketed else "not bracketed"} by the sweep."""


def _followup_row(label: str, item: dict[str, Any]) -> str:
    exponent = item.get("exponent_ols", item.get("exponent"))
    display = "—" if exponent is None else f"{exponent:.3f}"
    boot_low = item.get("exponent_boot_low", item.get("bootstrap_low"))
    boot_high = item.get("exponent_boot_high", item.get("bootstrap_high"))
    interval = "—"
    if boot_low is not None and boot_high is not None:
        interval = f"[{boot_low:.3f}, {boot_high:.3f}]"
    invalid = item.get("zero_delay_resamples")
    status = "complete" if item["complete"] else "pending"
    if item["complete"] and exponent is None:
        status = "fit censored"
    missing = ", ".join(f"{value:g}" for value in item["missing_speeds"])
    return (
        f"| {label} | {status} | {item['n_artifacts']} | "
        f"{item['n_fit_legs']} | {display} | {interval} | "
        f"{'—' if invalid is None else invalid} | {missing or '—'} |"
    )


def _residual_diagnostics(data: dict[str, dict[str, Any]], names: tuple[str, ...]) -> str:
    """Read saved fit residuals and deletion sensitivity."""
    if all(data[name].get("rms_log_residual") is not None for name in names):
        rms = [float(data[name]["rms_log_residual"]) for name in names]
        ranges = [
            (min(data[name]["leave_one_out_exponents"]), max(data[name]["leave_one_out_exponents"]))
            for name in names
        ]
        return (
            "In table order, log-residual RMS is "
            + ", ".join(f"{value:.3f}" for value in rms)
            + "; leave-one-speed-out slopes span "
            + ", ".join(f"[{low:.3f}, {high:.3f}]" for low, high in ranges)
            + ". The N=8000 low-threshold fit has material log scatter, so a single "
            "power law is not established across these settings. "
        )
    return "Fit residual diagnostics are unavailable. "


def _threshold_diagnostics(data: dict[str, dict[str, Any]], names: tuple[str, ...]) -> str:
    """Read threshold placement, initialization, resolution and censoring."""
    if all(data[name].get("largest_precritical_order") is not None for name in names):
        peak = [float(data[name]["largest_precritical_order"]) for name in names]
        initial = [float(data[name]["largest_initial_order"]) for name in names]
        step = max(float(data[name]["largest_coupling_step"]) for name in names)
        censored = [int(data[name]["censored_replicas"]) for name in names]
        return (
            "In table order, maximum precritical order is "
            + ", ".join(f"{value:.3f}" for value in peak)
            + "; maximum initial order is "
            + ", ".join(f"{value:.3f}" for value in initial)
            + f"; largest saved coupling step is {step:.3f}; censored replica legs total "
            + ", ".join(str(value) for value in censored)
            + ". A postcritical threshold crossing can therefore be immediate "
            "when the trace is already above the absolute criterion before Kc. "
        )
    return ""


def _delay_comparison(data: dict[str, dict[str, Any]]) -> str:
    """State what the three saved delay fits say about approach to one half."""
    names = ("N2000_r0.20", "N2000_r0.05", "N8000_r0.05")
    if any(name not in data or data[name].get("exponent_ols") is None for name in names):
        return ""
    baseline, tight, large = (float(data[name]["exponent_ols"]) for name in names)
    matched_baseline, matched_tight, matched_large = (
        float(data[name]["matched_exponent_ols"]) for name in names
    )
    matched_errors = [
        abs(value - 0.5) for value in (matched_baseline, matched_tight, matched_large)
    ]
    matched_direction = (
        "moves toward 0.5"
        if matched_errors[2] < matched_errors[1] < matched_errors[0]
        else "does not show convergence toward 0.5"
    )
    return (
        f"The three delay exponents are {baseline:.3f}, {tight:.3f}, and {large:.3f} "
        f"in table order on all eligible legs. Over the matched six-leg subset "
        f"v=0.01--0.0001, the exponents are {matched_baseline:.3f}, "
        f"{matched_tight:.3f}, and {matched_large:.3f}. "
        f"On the matched subset, the sequence {matched_direction}. "
        + _residual_diagnostics(data, names)
        + _threshold_diagnostics(data, names)
        + "The tighter criterion produces zero-delay crossings. These finite-sweep estimates "
        "do not establish an asymptotic exponent. Do not assume tightening the criterion "
        "restores one-half."
    )


def _heterogeneous_limit(data: dict[str, dict[str, Any]]) -> str:
    """Disclose completed frequency sweeps whose exponent remains unidentifiable."""
    censored = [
        label for label, item in data.items() if item["complete"] and item.get("exponent") is None
    ]
    if not censored:
        return ""
    widths = ", ".join(censored)
    return (
        f"At Lorentzian half-width {widths}, the completed sweep has too few uncensored "
        "speed legs for an exponent interval. The control therefore cannot decide "
        "whether heterogeneity changes only the prefactor or the exponent. "
        "A lower, predeclared escape criterion or wider coupling window is needed."
    )


def _followup_report(threshold_path: Path, hetero_path: Path) -> str:
    """Summarize saved follow-up analyses, marking incomplete sweeps explicitly."""
    rows: list[str] = []
    conclusions: list[str] = []
    for path in (threshold_path, hetero_path):
        if path.exists():
            data: dict[str, dict[str, Any]] = json.loads(path.read_text(encoding="utf-8"))
            rows.extend(_followup_row(label, item) for label, item in data.items())
            conclusion = (
                _delay_comparison(data) if path == threshold_path else _heterogeneous_limit(data)
            )
            if conclusion:
                conclusions.append(conclusion)
    if not rows:
        return ""
    return "\n".join(
        [
            "## Follow-up controls",
            "",
            "Only completed checkpoints enter these fits. Pending rows are provisional. "
            "Zero-delay resamples cannot enter a log fit; the reported bootstrap "
            "intervals condition on a positive mean delay at every speed.",
            "",
            "| condition | status | artifacts | fit legs | OLS exponent | "
            "bootstrap 95% CI | zero draws | missing speeds |",
            "|:--|:--|--:|--:|--:|:--|--:|:--|",
            *rows,
            "",
            "\n\n".join(conclusions),
        ]
    )


def _write_report(
    legs: list[Leg], metrics: list[LegMetrics], diagnostics: list[LegMetrics]
) -> None:
    followup = _followup_report(
        FIGURE_DIR / "tighter_threshold_summary.json", FIGURE_DIR / "hetero" / "hetero_summary.json"
    )
    report = f"""# Dynamic-ramp numerical report

Finite-N heuristic evidence only; these runs prove no trajectory theorem and do
not discharge the adiabatic assumption. Seed 20260903, 32 replicas, N=2000,
D=1, dt=0.01. Escape is the first of three consecutive decimated samples with
r >= {ESCAPE_LEVEL}; pre-critical crossings are excluded.

| v | escaped | mean delay | replica SD | collapse Dev | beta_eff |
|---:|---:|---:|---:|---:|---:|
{_table_rows(metrics)}

{_delay_paragraph(metrics)}

{_bootstrap_paragraph(legs, metrics)}

{_collapse_paragraph(metrics, diagnostics)}

{followup}

Using D_phys=1.5 rad/s, v_phys=v D_phys^2. A 100--1000 s crossing of a coupling
window of width 1.5 rad/s corresponds to v=0.000667--0.00667 in simulation
units, inside the tested range. This conversion compares scales; it is not a
measurement of astrocytic coupling dynamics.
"""
    (FIGURE_DIR / "DYNAMIC_RAMP_REPORT.md").write_text(report, encoding="utf-8")


def main() -> None:
    """Generate all required S1 summary artifacts."""
    delay_legs = _load_legs(DELAY_SPEEDS)
    delay_metrics = [_metrics(leg) for leg in delay_legs]
    diagnostic_legs = [leg for leg in delay_legs if leg.speed in SPEEDS]
    diagnostic_metrics = [item for item in delay_metrics if item.speed in SPEEDS]
    _plot_bifurcation(diagnostic_legs)
    _plot_delay_scaling(delay_metrics)
    _plot_collapse(diagnostic_legs, diagnostic_metrics)
    _plot_onset(diagnostic_metrics)
    _write_report(delay_legs, delay_metrics, diagnostic_metrics)
    print("wrote dynamic-ramp figures and DYNAMIC_RAMP_REPORT.md")


if __name__ == "__main__":
    main()
