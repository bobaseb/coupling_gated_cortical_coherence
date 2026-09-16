"""Figures and a written report for N12--N13, built from their saved summaries.

Reads the two JSON artifacts the rate extensions leave behind and writes the
figures and `COUPLING_RATE_REPORT.md` beside them. It integrates nothing and
recomputes no residual: a restyled figure costs a second of plotting rather than
the sweep behind it, which is the direction `tach.toml` enforces by placing
`report` above `simulation`.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import matplotlib.pyplot as plt
import numpy as np


FIGURES = Path(__file__).resolve().parent / "figures"
ERROR_DIR = FIGURES / "quasistatic_error"
NOISE_DIR = FIGURES / "fluctuating_coupling"

Row = dict[str, Any]


def load(directory: Path, name: str) -> Row:
    """Read one saved summary, failing loudly when the run has not been done."""
    path = directory / name
    if not path.exists():
        raise FileNotFoundError(f"{path} is missing; run the sweep that writes it first")
    return dict(json.loads(path.read_text(encoding="utf-8")))


def _format(value: object, digits: int = 4) -> str:
    """Numbers to a fixed width; `None` says the quantity does not exist, which
    is a result rather than a missing entry."""
    if value is None:
        return "none"
    if isinstance(value, float):
        return f"{value:.{digits}g}"
    return str(value)


# ── N12: the quasi-static residual ─────────────────────────────────────────


def _residual_panel(axis: Any, summary: Row) -> None:
    """Terminal residual against ramp speed, one line per leg."""
    for name, payload in sorted(summary["legs"].items()):
        speeds = [run["speed"] for run in payload["runs"]]
        errors = [run["terminal_error"] for run in payload["runs"]]
        style = "--" if name.startswith("sub") else "-"
        width = 2.4 if name == "crossing" else 1.2
        axis.loglog(speeds, errors, style, lw=width, label=name)
    axis.axhline(summary["config"]["tolerance"], color="k", ls=":", lw=1.4)
    axis.set(xlabel=r"ramp speed $\dot K$", ylabel=r"$|r(T)-r_{ss}(K(T))|$")
    axis.legend(fontsize=6, ncol=2)
    axis.grid(alpha=0.3)


def _criterion_panel(axis: Any, summary: Row) -> None:
    """The admissible time-scale ratio against distance from threshold."""
    points = [p for p in summary["criterion"] if p["required_ratio"] is not None]
    deltas = [p["delta"] for p in points]
    ratios = [p["required_ratio"] for p in points]
    axis.semilogy(deltas, ratios, "o", color="tab:blue")
    cited = summary["manuscript"]["cited_ratio_range"]
    axis.axhspan(cited[0], cited[1], color="tab:green", alpha=0.2, label="cited time-scale ratio")
    axis.set(xlabel=r"$|K-K_c|$ at the leg's near end", ylabel=r"required $\tau_K/\tau_\varphi$")
    axis.legend(fontsize=8)
    axis.grid(alpha=0.3)


def _delay_panel(axis: Any, summary: Row) -> None:
    """The threshold-seeded bifurcation delay against the published fit."""
    delay = summary["bifurcation_delay"]
    speeds = np.asarray(delay["speeds"], dtype=float)
    excess = np.asarray([value for value in delay["coupling_excess"]], dtype=float)
    axis.loglog(speeds, excess, "o", color="tab:red", label="measured")
    reference = excess[0] * (speeds / speeds[0]) ** delay["published_exponent"]
    axis.loglog(speeds, reference, "k--", lw=1.4, label=f"$v^{{{delay['published_exponent']}}}$")
    axis.set(xlabel=r"ramp speed $\dot K$", ylabel=r"$\Delta K$ at escape")
    axis.legend(fontsize=8)
    axis.grid(alpha=0.3)


def error_figure(summary: Row, path: Path) -> None:
    """Three panels: the residual, the criterion it gives, and the delay."""
    figure, axes = plt.subplots(1, 3, figsize=(13.5, 4.0))
    _residual_panel(axes[0], summary)
    _criterion_panel(axes[1], summary)
    _delay_panel(axes[2], summary)
    figure.tight_layout()
    figure.savefig(path, dpi=180)
    plt.close(figure)


def error_section(summary: Row) -> list[str]:
    """The N12 section of the report."""
    manuscript = summary["manuscript"]
    delay = summary["bifurcation_delay"]
    controls = summary["controls"]
    lines = [
        "## N12 — the quasi-static residual as a function of rate",
        "",
        f"Mean-field harmonic ladder, `D = {summary['config']['diffusion']}`, "
        f"tolerance `{summary['config']['tolerance']}`, "
        f"start offset `{summary['config']['start_offset']}`.",
        "",
        "The worst residual is the largest excursion anywhere on the leg, over every",
        "scanned speed; on a slow leg it is the initial displacement rather than a lag,",
        "which is why the criterion is read off the terminal residual instead.",
        "",
        "| leg | Δ from K_c | admissible speed | required τ_K/τ_φ | worst residual "
        "| at K | at speed |",
        "| :--- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for point in summary["criterion"]:
        payload = summary["legs"][point["leg"]]
        lines.append(
            f"| {point['leg']} | {_format(point['delta'])} | "
            f"{_format(point['admissible_speed'])} | {_format(point['required_ratio'])} | "
            f"{_format(payload['worst_residual'])} | "
            f"{_format(payload['worst_residual_coupling'])} | "
            f"{_format(payload['worst_residual_speed'])} |"
        )
    lines += [
        "",
        f"Bifurcation delay, seeded at threshold at the finite-`N` fluctuation floor "
        f"`{_format(delay['seed_order'])}`: exponent **{_format(delay['exponent'])}** over all "
        f"four speeds and **{_format(delay['uncensored_exponent'])}** over the three the "
        f"published fit used, against that fit's `{delay['published_exponent']}`.",
        "",
        f"Controls: stationary drift `{_format(controls['stationary_drift'], 3)}`, "
        f"step halving `{_format(controls['step_halving'], 3)}`, frozen-branch comparison "
        f"rejected at every speed: `{controls['frozen_rejected']}`.",
        "",
        f"Manuscript reading: the cited geometry and phase time scales give a ratio between "
        f"`{_format(manuscript['cited_ratio_range'][0])}` and "
        f"`{_format(manuscript['cited_ratio_range'][1])}`. Every scanned leg meets that "
        f"requirement from `|K-K_c| = {_format(manuscript['trackable_delta_at_slow_end'])}` "
        f"at the slow end and `{_format(manuscript['trackable_delta_at_fast_end'])}` at the "
        "fast end.",
        "",
    ]
    return lines


# ── N13: a fluctuating coupling ────────────────────────────────────────────


def _substitution_lines(axis: Any, rows: list[Row]) -> None:
    """The two candidate substitutions, as curves the measurement is read against."""
    reference = sorted(rows, key=lambda row: row["mean"])
    means = [row["mean"] for row in reference]
    axis.plot(
        means,
        [row["mean_substitution"] for row in reference],
        "k--",
        lw=1.6,
        label=r"$r_{ss}(\bar K)$",
    )
    axis.plot(
        means,
        [row["quasi_static_average"] for row in reference],
        "k:",
        lw=1.6,
        label=r"$E[r_{ss}(K)]$",
    )


def _order_panel(axis: Any, summary: Row, process: str) -> None:
    """Measured mean order against mean coupling, one line per correlation time."""
    rows = [
        row for row in summary["drives"] if row["process"] == process and row["amplitude"] == 1.0
    ]
    for tau in summary["correlation_times"]:
        selected = sorted(
            (row for row in rows if row["correlation_time"] == tau), key=lambda row: row["mean"]
        )
        axis.plot(
            [row["mean"] for row in selected],
            [row["measured_order"] for row in selected],
            "o-",
            lw=1.2,
            label=rf"$\tau={tau:g}$",
        )
    _substitution_lines(axis, rows)
    axis.set(xlabel=r"mean coupling $\bar K$", ylabel="mean order", title=process)
    axis.legend(fontsize=7)
    axis.grid(alpha=0.3)


def _gap_panel(axis: Any, summary: Row) -> None:
    """Which substitution is closer, against correlation time."""
    for amplitude in summary["amplitudes"]:
        rows = [row for row in summary["drives"] if row["amplitude"] == amplitude]
        taus = sorted({row["correlation_time"] for row in rows})
        share = [
            float(
                np.mean(
                    [
                        row["closer"] == "quasi_static"
                        for row in rows
                        if row["correlation_time"] == tau
                    ]
                )
            )
            for tau in taus
        ]
        axis.semilogx(taus, share, "o-", label=f"amplitude {amplitude:g}")
    axis.set(
        xlabel=r"correlation time $\tau$",
        ylabel="share where the quasi-static average is closer",
        ylim=(-0.05, 1.05),
    )
    axis.legend(fontsize=8)
    axis.grid(alpha=0.3)


def noise_figure(summary: Row, path: Path) -> None:
    """Three panels: both processes' order curves and the crossover."""
    figure, axes = plt.subplots(1, 3, figsize=(13.5, 4.0))
    _order_panel(axes[0], summary, "telegraph")
    _order_panel(axes[1], summary, "ornstein_uhlenbeck")
    _gap_panel(axes[2], summary)
    figure.tight_layout()
    figure.savefig(path, dpi=180)
    plt.close(figure)


def noise_section(summary: Row) -> list[str]:
    """The N13 section of the report."""
    fast, slow = summary["fast_limit"], summary["slow_limit"]
    rejection = summary["mean_substitution_rejection"]
    controls = summary["controls"]
    lines = [
        "## N13 — a fluctuating coupling and the threshold",
        "",
        f"Two declared processes, amplitudes {summary['amplitudes']}, correlation times "
        f"{summary['correlation_times']}, mean couplings {summary['mean_couplings']}.",
        "",
        "| limit | τ | worst gap to r_ss(mean) | worst gap to E[r_ss(K)] |",
        "| :--- | ---: | ---: | ---: |",
        f"| fast | {_format(fast['correlation_time'])} | "
        f"{_format(fast['worst_mean_substitution_gap'])} | "
        f"{_format(fast['worst_quasi_static_gap'])} |",
        f"| slow, no crossing ({slow['drives']} drives) | {_format(slow['correlation_time'])} | "
        f"{_format(slow['worst_mean_substitution_gap'])} | "
        f"{_format(slow['worst_quasi_static_gap'])} |",
        "",
        f"Mean-coupling substitution refused in **{rejection['count']}** drives. The "
        f"criterion: {rejection['criterion']}.",
        "",
    ]
    strongest = rejection["strongest"]
    if strongest is not None:
        lines += [
            f"Strongest case: {strongest['process']} at mean `{_format(strongest['mean'])}`, "
            f"amplitude `{_format(strongest['amplitude'])}`, correlation time "
            f"`{_format(strongest['correlation_time'])}` gives mean order "
            f"`{_format(strongest['measured_order'])}` where `r_ss(mean)` is exactly zero. Its "
            f"spread across replicas is `{_format(strongest['order_spread'])}`, which is the "
            "size of the effect itself: a crossing drive is not self-averaging over one run.",
            "",
        ]
    gaussian = [row for row in summary["drives"] if row["process"] == "ornstein_uhlenbeck"]
    if gaussian:
        worst = max(row["negative_fraction"] for row in gaussian)
        lines += [
            "The Gaussian coupling is not clipped, because clipping would move the mean under "
            f"test; at most `{_format(worst)}` of its sampled time is spent at negative coupling.",
            "",
        ]
    extended = controls["extended_horizon"]
    if extended is not None:
        lines += [
            f"At four times that horizon (`{_format(extended['horizon'])}`) the same drive gives "
            f"`{_format(extended['measured_order'])}`.",
            "",
        ]
    lines += [
        f"Control: step halving moves the mean order by `{_format(controls['step_halving'], 3)}`.",
        "",
    ]
    return lines


# ── assembly ───────────────────────────────────────────────────────────────


def build_report(error: Row, noise: Row) -> str:
    """The two sections, with the header that says where they came from."""
    lines = [
        "# N12–N13: the rate and the fluctuation of an evolving coupling",
        "",
        "Generated by simulations/coupling_rate_report.py from the saved summaries;",
        "do not edit manually. Every number here is read from a JSON artifact a run",
        "left behind, and nothing in this file integrates or estimates.",
        "",
        *error_section(error),
        *noise_section(noise),
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=FIGURES)
    args = parser.parse_args()
    error = load(ERROR_DIR, "quasistatic_error_summary.json")
    noise = load(NOISE_DIR, "fluctuating_coupling_summary.json")
    error_figure(error, ERROR_DIR / "quasistatic_error.png")
    noise_figure(noise, NOISE_DIR / "fluctuating_coupling.png")
    report = args.output / "COUPLING_RATE_REPORT.md"
    report.write_text(build_report(error, noise), encoding="utf-8")
    print(f"wrote {report}")


if __name__ == "__main__":
    main()
