"""Figures and conditional physical readout from the saved S5 artifacts.

Run `geometric_frustration.py` first; it writes `summary.json`, the legs and,
on a failed baseline gate, the noise control. This module reads those files and
integrates nothing, so a lost figure costs a second of plotting rather than the
sweep that produced the data.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from numpy.typing import NDArray

from fermi_estimate_check import FERMI_FIELD_MIN, FERMI_FIELD_MAX
from geometric_frustration import FAILED_BASELINE, LEG_KEYS, ROOT


def report(
    summary: dict[str, Any],
    baseline: dict[str, NDArray[np.float64]],
    strongest: dict[str, NDArray[np.float64]],
    output: Path,
) -> None:
    """Plot the two legs the sweep is read from: zero field and its largest coupling."""
    config = summary["config"]
    floor = 1 / np.sqrt(config["n"])
    fig, ax = plt.subplots(figsize=(7, 3))
    ax.plot(baseline["time"], baseline["order"])
    ax.axhline(floor, color="black", ls="--", label=r"$1/\sqrt{N}$")
    ax.set(
        xlabel="Time (simulation units)",
        ylabel="Order r",
        title="Dale-balanced zero-field baseline",
    )
    ax.legend()
    fig.tight_layout()
    fig.savefig(output / "baseline.png", dpi=180)
    plt.close(fig)
    _transition(summary, output)
    fig, axes = plt.subplots(1, 2, subplot_kw={"projection": "polar"}, figsize=(7, 3.5))
    for ax, leg, title in zip(
        axes, (baseline, strongest), ("Zero field", "Largest uniform coupling"), strict=True
    ):
        ax.hist(leg["final_phases"], bins=np.linspace(-np.pi, np.pi, 25), density=True)
        ax.set_title(title)
    fig.tight_layout()
    fig.savefig(output / "phases.png", dpi=180)
    plt.close(fig)
    _readout(summary, output)


def _transition(summary: dict[str, Any], output: Path) -> None:
    config = summary["config"]
    epsilon = np.array(summary["epsilon"])
    fields = summary["conditional_field_mV_mm"]
    factor = fields[1] / summary["critical_epsilon"]
    fig, ax = plt.subplots(figsize=(8, 4.5))
    ax.semilogx(epsilon[1:], summary["steady_order"][1:], "o-", label="Steady order (second half)")
    if "order_min" in summary:
        ax.fill_between(
            epsilon[1:],
            summary["order_min"][1:],
            summary["order_max"][1:],
            alpha=0.2,
            label="Range across three seeds",
        )
    ax.axhline(1 / np.sqrt(config["n"]), color="black", ls="--", label=r"$1/\sqrt{N}$")
    ax.axhline(0.2, color="gray", ls=":", label="Operational crossing r=0.2")
    ax.axvline(2 * config["diffusion"] / config["n"], color="red", ls="--", label=r"$2D/N$")
    ax.axvspan(*summary["threshold_bracket"], color="orange", alpha=0.25)
    ax.axvspan(
        FERMI_FIELD_MIN / factor,
        FERMI_FIELD_MAX / factor,
        color="green",
        alpha=0.15,
        label="1–5 mV/mm comparison band",
    )
    top = ax.secondary_xaxis("top", functions=(lambda x: x * factor, lambda x: x / factor))
    top.set_xlabel("Conditional field (mV/mm), decay length 0.2 mm")
    ax.set(xlabel=r"Uniform per-pair coupling $\epsilon$", ylabel="Order r", ylim=(0, 1))
    ax.legend(fontsize=8, loc="lower right")
    fig.tight_layout()
    fig.savefig(output / "transition.png", dpi=180)
    plt.close(fig)


def _readout(summary: dict[str, Any], output: Path) -> None:
    lines = [
        "# S5: finite-N frustration rescue",
        "",
        f"Configuration: `{summary['config']}`; omega=0.",
        f"Saved integration runtime: {summary['runtime_seconds']:.2f} seconds.",
        f"Row sums (min, mean, max): {summary['row_sum_min_mean_max']}.",
        f"Zero-field steady r={summary['steady_order'][0]:.5f}.",
        "",
        "Threshold: second-half mean r crosses 0.2 and stays above it at all larger "
        "sampled couplings.",
        f"epsilon_c={summary['critical_epsilon']:.7f}; "
        f"sampled bracket={summary['threshold_bracket']}.",
        f"K_eff={summary['effective_coupling']:.5f}; "
        f"K_eff/D={summary['coupling_over_diffusion']:.5f} (reference 2).",
        "",
        "| Decay (mm) | Conditional field (mV/mm) |",
        "|---|---|",
    ]
    for lam, field in zip(summary["decay_mm"], summary["conditional_field_mV_mm"], strict=True):
        lines.append(f"| {lam:.1f} | {field:.5f} |")
    lines += [
        "",
        "Compare these conditional values with the 1–5 mV/mm band.",
        "Conversion: K_eff=N_sim epsilon_c; E=K_eff/(N_cortex shift f), with "
        "constants imported from fermi_estimate_check.py and rate gamma=1. "
        "For other gamma, divide every reported field by gamma.",
        "Dimensional limitation: " + summary["calibration_limit"],
        "Thus this is conditional arithmetic, not an independent physical-unit "
        "validation or a measured cortical threshold.",
        "One fixed ER network (no self-edges), 80/20 Dale columns; signed row sums, "
        "probability and seeds are saved above and in each NPZ.",
        "Row normalization preserves signs, but not equal per-synapse magnitudes. Row "
        "balance alone does not prove frustration; the zero-field trajectory is the "
        "empirical control.",
        "The operational bracket is sweep resolution, not a confidence interval. "
        "Seed, network, finite-N, timestep and threshold-definition dependence remain "
        "unquantified.",
        "No propagation-of-chaos, dynamical-selection or gluing theorem is "
        "established; no Lean obligation is discharged.",
        "",
    ]
    text = "\n".join(lines)
    (output / "FRUSTRATION_REPORT.md").write_text(text)
    print(text)


def failed_baseline_report(
    summary: dict[str, Any],
    leg: dict[str, NDArray[np.float64]],
    control: dict[str, NDArray[np.float64]],
    output: Path,
) -> None:
    """Report a failed baseline without fabricating a rescue threshold."""
    fig, ax = plt.subplots(figsize=(8, 3.5))
    ax.plot(leg["time"], leg["order"], label="Balanced Dale network", alpha=0.8)
    ax.plot(control["time"], control["order"], label="Matched independent-noise control", alpha=0.7)
    ax.axhline(summary["finite_size_floor"], color="black", ls="--", label=r"$1/\sqrt{N}$")
    ax.set(xlabel="Time (simulation units)", ylabel="Order r", title="S5: baseline gate failed")
    ax.legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(output / "baseline.png", dpi=180)
    plt.close(fig)
    lines = [
        "# S5: baseline gate failed",
        "",
        f"Configuration: `{summary['config']}`; omega=0; trajectory seed=config seed+1.",
        f"Second-half mean order: {summary['baseline_order']:.5f}.",
        f"Matched independent-noise control: {summary['noise_control_order']:.5f}.",
        f"Finite-size reference: {summary['finite_size_floor']:.5f}.",
        f"Row sums (min, mean, max): {summary['row_sum_min_mean_max']}.",
        f"Saved integration runtime (baseline + control): {summary['runtime_seconds']:.2f} s.",
        "",
        "The baseline exceeds the declared generous gate of twice 1/sqrt(N).",
        "The modulatory sweep was not run; epsilon_c, K_eff and E_req are unavailable.",
        "Exact row balance and Dale signs do not ensure an incoherent finite-N baseline.",
        "This single network and seed do not establish persistent macroscopic order.",
        "",
        "## Open questions",
        "",
        "What synaptic strength and topology define the intended baseline? The specification",
        "leaves both unspecified; this attempt fixed positive row sum 4 and probability 0.2",
        "(0.5 in the N=100 smoke). Reducing strength to obtain a pass changes that regime.",
        "Also, N_cortex*shift*f is dimensionless, whereas the SDE coupling is inverse time.",
        "An independently justified rate calibration is required before the requested",
        "conversion can establish physical-unit consistency. No measured field is inferred.",
        "",
        "Artifacts retain only decimated order and final phases, with seeded metadata.",
        "No Lean obligation, gluing claim or dynamical-selection theorem is discharged.",
        "",
    ]
    (output / "FRUSTRATION_REPORT.md").write_text("\n".join(lines))


def _saved(path: Path) -> dict[str, NDArray[np.float64]]:
    """Read one saved trajectory back; the arrays are what the sweep decimated."""
    with np.load(path, allow_pickle=False) as saved:
        return {key: saved[key] for key in LEG_KEYS}


def rebuild(source: Path, output: Path) -> None:
    """Rebuild a finished run's figures and readout, dispatching on its own status."""
    summary: dict[str, Any] = json.loads((source / "summary.json").read_text())
    baseline = _saved(source / "leg_00.npz")
    if summary.get("status") == FAILED_BASELINE:
        failed_baseline_report(summary, baseline, _saved(source / "noise_control.npz"), output)
        return
    # The largest coupling the sweep sampled is the last leg of the coarse grid,
    # the refinement having subdivided a step below it. A summary written before
    # the refinement existed carries only `epsilon`, which was that grid.
    coarse = summary.get("coarse_epsilon", summary["epsilon"])
    strongest = _saved(source / f"leg_{len(coarse) - 1:02d}.npz")
    report(summary, baseline, strongest, output)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT)
    args = parser.parse_args()
    rebuild(args.output, args.output)


if __name__ == "__main__":
    main()
