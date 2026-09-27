"""Generate the physical-unity paper's numerals from saved summaries only.

Reads ``figures/unity_agreement/summary.json`` (the sheet simulations),
``resistance.json`` (the exact resistance scaling) and
``figures/unity_occupancy/summary.json`` (the occupancy-weighted carrier test)
and writes ``unity/unity_results.tex``. Nothing here integrates a sheet, sums a
Fourier series or propagates a membrane: ``unity_agreement.py`` and
``unity_occupancy.py`` produce the summaries as separate commands.
"""

import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any, cast

ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"
OUTPUT = ROOT.parent / "unity" / "unity_results.tex"

# TeX macro names cannot hold digits, so shapes are spelled out.
SHAPE_NAMES = {
    "nearest": "Nearest",
    "exponential": "Exponential",
    "power_sigma1": "SigmaOne",
    "power_sigma3": "SigmaThree",
}


def _read(path: Path) -> dict[str, Any]:
    return cast(dict[str, Any], json.loads(path.read_text()))


def _finite(value: object) -> float:
    number = float(cast(float, value))
    if not math.isfinite(number):
        raise ValueError(f"Nonfinite saved result: {value}")
    return number


def _select(runs: list[dict[str, Any]], **config: float) -> list[dict[str, Any]]:
    found = [r for r in runs if all(r["config"][k] == v for k, v in config.items())]
    if not found:
        raise ValueError(f"No saved run with {config}")
    return found


def _ordered_values(runs: list[dict[str, Any]], high: float) -> list[tuple[str, str]]:
    ordered = [r for r in runs if float(r["config"]["noise"]) < high]
    logarithmic = [r for r in ordered if r["fit"]["better"] == "logarithmic"]
    return [("uOrderedRuns", str(len(ordered))), ("uLogarithmicRuns", str(len(logarithmic)))]


def _harmonic_values(runs: list[dict[str, Any]], low: float, mid: float) -> list[tuple[str, str]]:
    values = []
    for name, noise in (("Low", low), ("Mid", mid)):
        ratio = max(_finite(r["harmonic_ratio_max"]) for r in _select(runs, noise=noise))
        values.append((f"uHarmonicRatio{name}", f"{ratio:.2f}"))
    return values


def _chord_values(runs: list[dict[str, Any]], high: float, side: int) -> list[tuple[str, str]]:
    disordering = _select(runs, noise=high, side=side)
    values = []
    for shape, name in SHAPE_NAMES.items():
        (run,) = [r for r in disordering if r["shape"] == shape]
        values.append((f"uChord{name}High", f"{_finite(run['discrepancy'][-1]):.2f}"))
    return values


def _simulation_values(summary: dict[str, Any]) -> list[tuple[str, str]]:
    runs = cast(list[dict[str, Any]], summary["runs"])
    if not runs:
        raise ValueError("The saved U3 summary has no runs")
    low, mid, high = sorted({float(r["config"]["noise"]) for r in runs})
    sides = sorted({int(r["config"]["side"]) for r in runs})
    return [
        ("uNoiseLow", f"{low:g}"),
        ("uNoiseMid", f"{mid:g}"),
        ("uNoiseHigh", f"{high:g}"),
        ("uSideSmall", str(sides[0])),
        ("uSideLarge", str(sides[-1])),
        *_ordered_values(runs, high),
        *_harmonic_values(runs, low, mid),
        *_chord_values(runs, high, sides[-1]),
    ]


def _scaling_values(scaling: dict[str, Any]) -> list[tuple[str, str]]:
    sides = [int(side) for side in scaling["sides"]]
    values = [(f"uScalingSide{label}", str(side)) for label, side in zip("ABC", sides, strict=True)]
    for shape in ("exponential", "power_sigma1", "power_sigma3"):
        far = scaling["far_resistance"][shape]
        for label, resistance in zip("ABC", far, strict=True):
            values.append((f"uFar{SHAPE_NAMES[shape]}{label}", f"{_finite(resistance):.3f}"))
    stiffness = scaling["stiffness"]
    ratio = _finite(stiffness["exponential"]) / _finite(stiffness["nearest"])
    values.append(("uStiffnessRatio", f"{ratio:.0f}"))
    return values


def _config_range(neurons: list[dict[str, Any]], key: str) -> tuple[str, str]:
    values = sorted({_finite(n["config"][key]) for n in neurons})
    return f"{values[0]:g}", f"{values[-1]:g}"


def _window_values(neurons: list[dict[str, Any]]) -> list[tuple[str, str]]:
    """Per content window: the least visit probability, and the links it gives."""
    windows = sorted(neurons[0]["window_hit_probability"]["1"], key=float)
    short, long = windows[0], windows[-1]
    hits = {
        w: [_finite(h[w]) for n in neurons for h in n["window_hit_probability"].values()]
        for w in (short, long)
    }
    carriers = sorted(int(k) for k in neurons[0]["link_probability"]["1"])
    few, mid, many = carriers
    instant = min(_finite(v[str(many)]) for n in neurons for v in n["link_probability"].values())
    miss = (1.0 - min(hits[long])) ** mid
    return [
        ("uOccContentShortMs", f"{float(short):g}"),
        ("uOccContentLongMs", f"{float(long):g}"),
        ("uOccCarriersFew", str(few)),
        ("uOccCarriersMid", str(mid)),
        ("uOccCarriersMany", str(many)),
        ("uOccInstantLinkMin", f"{instant:.2g}"),
        ("uOccHitMinLong", f"{min(hits[long]):.2g}"),
        ("uOccHitMaxLong", f"{max(hits[long]):.3g}"),
        ("uOccLinkFewLong", f"{1.0 - (1.0 - min(hits[long])) ** few:.2g}"),
        ("uOccMissOrdersMidLong", f"{math.floor(-math.log10(miss))}"),
        ("uOccLinkMidShort", f"{1.0 - (1.0 - min(hits[short])) ** mid:.2g}"),
    ]


def _regime_values(neurons: list[dict[str, Any]]) -> list[tuple[str, str]]:
    """The declared ranges, and where the membrane sits and passes across them."""
    passing = [100 * _finite(n["pass_fraction"]) for n in neurons]
    distance = [_finite(n["mean_distance"]) for n in neurons]
    tau, rate, window = (_config_range(neurons, k) for k in ("tau_ms", "rate_hz", "window_ms"))
    return [
        ("uOccTauFast", tau[0]),
        ("uOccTauSlow", tau[1]),
        ("uOccRateLow", rate[0]),
        ("uOccRateHigh", rate[1]),
        ("uOccNextShort", window[0]),
        ("uOccNextLong", window[1]),
        ("uOccDistanceMin", f"{min(distance):.1f}"),
        ("uOccDistanceMax", f"{max(distance):.1f}"),
        ("uOccPassMinPercent", f"{min(passing):.2g}"),
        ("uOccPassMaxPercent", f"{max(passing):.2g}"),
    ]


def _control_values(summary: dict[str, Any]) -> list[tuple[str, str]]:
    """The noise share, the clock, the resolution check and the restored bit."""
    neurons = cast(list[dict[str, Any]], summary["neurons"])
    scales = sorted(float(s) for s in neurons[0]["pass_fraction_by_scale"])
    share = Fraction(scales[0] ** 2).limit_denominator(100)
    windows = {_finite(n["config"]["window_ms"]) for n in neurons}
    periods = sorted({float(p) for n in neurons for p in n["latched_pass_fraction"]} - windows)
    check = summary["resolution_check"]
    coarse, fine = (_finite(check[k]["pass_fraction"]) for k in ("coarse", "fine"))
    (bit,) = [b for b in summary["bits"] if _finite(b["margin"]) > 100]
    return [
        ("uOccShiftMax", f"{max(summary['shifts']):g}"),
        ("uOccShareMin", f"{share.numerator}/{share.denominator}"),
        ("uOccLatchShortMs", f"{periods[0]:g}"),
        ("uOccLatchLongMs", f"{periods[-1]:g}"),
        ("uOccResolutionPercent", f"{100 * abs(fine - coarse) / coarse:.0f}"),
        ("uOccBitOrders", f"{-_finite(bit['log10_max_response']):.0f}"),
    ]


def _occupancy_values(summary: dict[str, Any]) -> list[tuple[str, str]]:
    neurons = cast(list[dict[str, Any]], summary["neurons"])
    if not neurons:
        raise ValueError("The saved occupancy summary has no regimes")
    return [*_regime_values(neurons), *_control_values(summary), *_window_values(neurons)]


def render(figures: Path) -> str:
    """Read saved summaries; never integrate a sheet or recompute a resistance."""
    directory = figures / "unity_agreement"
    values = _simulation_values(_read(directory / "summary.json"))
    values += _scaling_values(_read(directory / "resistance.json"))
    values += _occupancy_values(_read(figures / "unity_occupancy" / "summary.json"))
    lines = [
        "% Generated by simulations/unity_macros.py from saved JSON summaries in",
        "% simulations/figures/unity_agreement/ and simulations/figures/unity_occupancy/.",
        "% Do not edit manually.",
        "% Regeneration does not run a simulation.",
        *(f"\\newcommand{{\\{name}}}{{{value}}}" for name, value in values),
    ]
    return "\n".join(lines) + "\n"


def write() -> None:
    """Refresh only the TeX macro file from saved summaries."""
    OUTPUT.write_text(render(FIGURES))


if __name__ == "__main__":
    write()
