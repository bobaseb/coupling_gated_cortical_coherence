"""The physical-unity paper's yardstick figure, drawn from saved summaries (U78).

Reads ``figures/unity_occupancy/yardstick.json`` (the membrane at every
yardstick) and ``switching.json`` (a clocked chip by the same protocol) and
writes ``unity/unity_yardstick.png``, beside the paper, where its arXiv build
looks for figures. Nothing is propagated or integrated here:
``unity_occupancy.py --yardstick`` and ``unity_switching.py`` produce the
summaries as separate commands.

Left: the share of occupied states that pass, per yardstick. Right: the chance
of entering a passing state within the longest content window. The membrane is
a band over every declared regime (and, on the right, every noise share); the
switching node is a band over the declared activity factors; the latch passes
nowhere; the synchronizer's share is the upper bound ``T_W f_D``.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"
OUTPUT = ROOT.parent / "unity" / "unity_yardstick.png"

# The first three categorical slots, which validate all pairs; the latch is ink.
MEMBRANE, NODE, SYNC, INK = "#2a78d6", "#eb6834", "#1baf7a", "#52514e"


@dataclass(frozen=True)
class Series:
    """Every curve of the figure, per yardstick."""

    yardsticks: list[float]
    fluctuation: float
    membrane_pass: tuple[list[float], list[float]]
    membrane_hit: tuple[list[float], list[float]]
    node_pass: tuple[list[float], list[float]]
    node_hit: list[float]
    sync_pass: float
    sync_hit: float
    latched_pass: list[float]


def _read(path: Path) -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(path.read_text()))


def _band(rows: list[list[float]]) -> tuple[list[float], list[float]]:
    return [min(col) for col in zip(*rows, strict=True)], [
        max(col) for col in zip(*rows, strict=True)
    ]


def series(figures: Path) -> Series:
    """The curves, from the saved yardstick sweep and the switching summary."""
    swept = _read(figures / "unity_occupancy" / "yardstick.json")
    chip = _read(figures / "unity_occupancy" / "switching.json")
    neurons = swept["neurons"]
    window = f"{max(chip['declared']['windows_ms']):g}"
    passing = [[row["pass_fraction"] for row in n["by_yardstick"]] for n in neurons]
    hits = [
        [row["window_hit_probability"][share][window] for row in n["by_yardstick"]]
        for n in neurons
        for share in n["by_yardstick"][0]["window_hit_probability"]
    ]
    nodes = [n["pass_fraction_by_yardstick"] for n in chip["nodes"]]
    events = chip["synchronizer"]["events_per_window"][window]
    return Series(
        yardsticks=list(swept["yardsticks"]),
        fluctuation=chip["fluctuation_tv"],
        membrane_pass=_band(passing),
        membrane_hit=_band(hits),
        node_pass=_band(nodes),
        node_hit=[1.0 if min(col) > 0 else 0.0 for col in zip(*nodes, strict=True)],
        sync_pass=chip["synchronizer"]["pass_fraction_bound"],
        sync_hit=-math.expm1(-events),
        latched_pass=list(chip["latched"]["pass_fraction_by_yardstick"]),
    )


def _style(axis: Any, s: Series, label: str) -> None:
    axis.axvline(s.fluctuation, color=INK, linewidth=0.8, linestyle=":")
    axis.set_xlabel("yardstick")
    axis.set_ylabel(label)
    axis.spines[["top", "right"]].set_visible(False)
    axis.grid(alpha=0.25, linewidth=0.5)


def _membrane(
    axis: Any, y: list[float], band: tuple[list[float], list[float]], label: str | None
) -> None:
    """A band over every regime, edged by its least and its greatest value."""
    axis.fill_between(y, *band, color=MEMBRANE, alpha=0.25, linewidth=0)
    for edge in band:
        axis.plot(y, edge, color=MEMBRANE, linewidth=1.5, marker="o", markersize=4, label=label)
        label = None


def _left(axis: Any, s: Series) -> None:
    y = s.yardsticks
    _membrane(axis, y, s.membrane_pass, "membrane")
    nodes = [(x, lo, hi) for x, lo, hi in zip(y, *s.node_pass, strict=True) if hi > 0]
    xs, lows, highs = (list(col) for col in zip(*nodes, strict=True))
    axis.fill_between(xs, lows, highs, color=NODE, alpha=0.25, linewidth=0)
    axis.plot(xs, highs, color=NODE, linewidth=2, marker="s", label="node's crossing time")
    axis.axhline(s.sync_pass, color=SYNC, linewidth=2, linestyle="--", label="synchronizer bound")
    axis.set_yscale("log")
    axis.set_ylim(1e-5, 1.5)
    axis.text(y[0], 2e-5, "latched value: none", color=INK, fontsize=8)
    _style(axis, s, "share of states that pass")


def _right(axis: Any, s: Series) -> None:
    y = s.yardsticks
    _membrane(axis, y, s.membrane_hit, None)
    # The node passes up to the fluctuation and at no higher yardstick.
    xs = [x for x in y if x <= s.fluctuation] + [s.fluctuation]
    xs += [x for x in y if x > s.fluctuation]
    hit = [1.0] * sum(x <= s.fluctuation for x in y) + [0.0] * (
        len(xs) - sum(x <= s.fluctuation for x in y)
    )
    axis.plot(xs, hit, color=NODE, linewidth=2, drawstyle="steps-post")
    axis.plot(y, s.node_hit, color=NODE, linestyle="none", marker="s")
    axis.axhline(s.sync_hit, color=SYNC, linewidth=2, linestyle="--")
    axis.plot(y, s.latched_pass, color=INK, linewidth=2, linestyle="-.", label="latched value")
    axis.set_ylim(-0.03, 1.05)
    _style(axis, s, "passing state within 400 ms")


def draw(s: Series, path: Path) -> None:
    """Both panels, one legend, saved as a PNG."""
    figure, (left, right) = plt.subplots(1, 2, figsize=(7.2, 3.1))
    _left(left, s)
    _right(right, s)
    handles = left.get_legend_handles_labels()[0] + right.get_legend_handles_labels()[0]
    figure.legend(handles=handles, loc="upper center", ncol=4, frameon=False, fontsize=8)
    figure.tight_layout(rect=(0, 0, 1, 0.9))
    figure.savefig(path, dpi=200)
    plt.close(figure)


if __name__ == "__main__":
    draw(series(FIGURES), OUTPUT)
