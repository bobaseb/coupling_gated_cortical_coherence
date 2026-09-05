"""Regenerate the S5 comparison report and figures from saved compact artifacts only."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from geometric_frustration import ROOT
from geometric_frustration_report import _transition


def read_json(path: Path) -> Any:
    return json.loads(path.read_text())


def aggregate(output: Path) -> dict[str, Any]:
    """Aggregate every declared seed, without selecting a favorable trajectory."""
    summaries = [
        read_json(output / f"weak_seed{seed}" / "summary.json")
        for seed in (20261905, 20262905, 20263905)
    ]
    orders = np.array([item["steady_order"] for item in summaries])
    fields = np.array([item["conditional_field_mV_mm"] for item in summaries])
    coupling = np.array([item["effective_coupling"] for item in summaries])
    result = dict(summaries[0])
    result.update(
        {
            "steady_order": orders.mean(axis=0).tolist(),
            "order_min": orders.min(axis=0).tolist(),
            "order_max": orders.max(axis=0).tolist(),
            "baseline_range": [float(orders[:, 0].min()), float(orders[:, 0].max())],
            "coupling_range": [float(coupling.min()), float(coupling.max())],
            "epsilon_range": [float(coupling.min() / 500), float(coupling.max() / 500)],
            "conditional_field_min": fields.min(axis=0).tolist(),
            "conditional_field_max": fields.max(axis=0).tolist(),
            "conditional_field_mV_mm": fields.mean(axis=0).tolist(),
            "critical_epsilon": float(coupling.mean() / 500),
            "threshold_bracket": [
                min(item["threshold_bracket"][0] for item in summaries),
                max(item["threshold_bracket"][1] for item in summaries),
            ],
            "runtime_seconds": sum(item["runtime_seconds"] for item in summaries),
            "seeds": [item["config"]["seed"] for item in summaries],
            "scope": (
                "Seed ranges, not confidence intervals; operational crossing, not critical point."
            ),
        }
    )
    result["effective_coupling"] = float(coupling.mean())
    result["coupling_over_diffusion"] = float(coupling.mean() / result["config"]["diffusion"])
    return result


def diagnostic_plot(records: list[dict[str, Any]], output: Path) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(9, 3.7))
    for strength in (0, 1, 2, 4):
        groups = [
            [
                r
                for r in records
                if r["config"]["n"] == n and r["config"]["positive_sum"] == strength
            ]
            for n in (250, 500, 1000)
        ]
        for ax, key in zip(axes, ("mean_order", "scaled_second_moment"), strict=True):
            values = np.array([[r[key] for r in group] for group in groups])
            ax.plot([250, 500, 1000], values.mean(axis=1), "o-", label=f"g={strength}")
            ax.fill_between([250, 500, 1000], values.min(axis=1), values.max(axis=1), alpha=0.15)
            ax.set_xlabel("N")
    axes[0].plot([250, 500, 1000], 1 / np.sqrt([250, 500, 1000]), "k--", label=r"$1/\sqrt{N}$")
    axes[0].set_ylabel("Second-half mean r")
    axes[1].axhline(1, color="black", ls="--")
    axes[1].set_ylabel(r"$N\langle r^2\rangle$")
    axes[0].legend(fontsize=8)
    fig.suptitle("Zero-field controls: lines are seed means; shading is seed range")
    fig.tight_layout()
    fig.savefig(output / "diagnostics.png", dpi=180)
    plt.close(fig)


def _tables(records: list[dict[str, Any]]) -> list[str]:
    lines = ["| N | g | mean r (seed range) | N mean(r²) (seed range) |", "|---|---|---|---|"]
    for n in (250, 500, 1000):
        for strength in (0, 1, 2, 4):
            group = [
                r
                for r in records
                if r["config"]["n"] == n and r["config"]["positive_sum"] == strength
            ]
            orders = [r["mean_order"] for r in group]
            scaled = [r["scaled_second_moment"] for r in group]
            lines.append(
                f"| {n} | {strength} | {min(orders):.4f}–{max(orders):.4f} | "
                f"{min(scaled):.3f}–{max(scaled):.3f} |"
            )
    return lines


def write_report(
    result: dict[str, Any],
    records: list[dict[str, Any]],
    timestep: list[dict[str, Any]],
    output: Path,
) -> None:
    lines = [
        "# S5: strength, finite-size and rescue controls",
        "",
        "Design fixed in tasks/s5_followup.md before these sweeps. All three seeds retained.",
        "N=500 rescue: g=1, p=0.2, D=1, omega=0, dt=0.01, T=100; 20 epsilon values.",
        "Each row has positive sum g and negative sum -g, with 80/20 Dale columns.",
        "The original g=4 failed baseline is retained; g=1 is a different regime.",
        "At g=1 the positive-only mean-field reference is also subcritical. Thus this",
        "regime does not establish that inhibition causes disorder; "
        "it tests added uniform coupling.",
        "",
        *_tables(records),
        "",
        "Mean order decreases with size in both g=1 and g=4 controls, while N mean(r²)",
        "stays above the independent-noise value. This is consistent with amplified",
        "finite-size fluctuations; these sizes cannot establish an asymptotic scaling law.",
        "",
        f"Rescue baseline seed range: {result['baseline_range']} (floor 1/sqrt(500)).",
        f"epsilon crossing seed range: {result['epsilon_range']}.",
        f"K_eff/D crossing seed range: {result['coupling_range']} (reference 2).",
        f"Union of sampled epsilon brackets: {result['threshold_bracket']}.",
        "Crossing means second-half r=0.2 with all larger samples above it.",
        "Ranges across three seeds and sampled brackets are not confidence intervals.",
        "",
        "| Decay (mm) | Conditional E range (mV/mm), gamma=1 |",
        "|---|---|",
    ]
    for index, lam in enumerate(result["decay_mm"]):
        lines.append(
            f"| {lam} | {result['conditional_field_min'][index]:.5f}–"
            f"{result['conditional_field_max'][index]:.5f} |"
        )
    lines += [
        "",
        "E_req=K_eff/(gamma N_cortex shift f); all field values scale as 1/gamma.",
        "The gamma=1 numerical convention reproduces the requested Fermi arithmetic.",
        "Gamma must carry the missing inverse-time calibration; this model does not measure it.",
        "The values are below 1–5 mV/mm conditionally, not an independent physical validation.",
        "",
        "| K | dt=0.01 mean r (seed range) | dt=0.005 mean r (seed range) |",
        "|---|---|---|",
    ]
    for coupling in (1.6, 2.0, 2.4):
        cells = []
        for dt in (0.01, 0.005):
            values = [
                r["mean_order"]
                for r in timestep
                if r["coupling"] == coupling and r["config"]["dt"] == dt
            ]
            cells.append(f"{min(values):.4f}–{max(values):.4f}")
        lines.append(f"| {coupling} | " + " | ".join(cells) + " |")
    runtime = result["runtime_seconds"] + sum(r["runtime_seconds"] for r in records + timestep)
    lines += [
        "",
        f"Saved integration runtime for diagnostics, rescue and dt controls: {runtime:.2f} s.",
        "Timestep controls use equal duration and sampling cadence; their noise paths differ.",
        "Three sizes, three seeds and two timesteps do not establish a limiting law.",
        "No Lean, gluing, propagation-of-chaos or dynamical-selection theorem is discharged.",
        "",
    ]
    (output / "FOLLOWUP_REPORT.md").write_text("\n".join(lines))


def main() -> None:
    result = aggregate(ROOT)
    records = read_json(ROOT / "diagnostics" / "summary.json")
    timestep = read_json(ROOT / "timestep" / "summary.json")
    (ROOT / "followup_summary.json").write_text(json.dumps(result, indent=2) + "\n")
    diagnostic_plot(records, ROOT)
    _transition(result, ROOT)
    write_report(result, records, timestep, ROOT)


if __name__ == "__main__":
    main()
