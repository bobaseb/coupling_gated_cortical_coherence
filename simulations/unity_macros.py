"""Generate the physical-unity paper's numerals from saved summaries only.

Reads ``figures/unity_agreement/summary.json`` (the sheet simulations),
``resistance.json`` (the exact resistance scaling), and in
``figures/unity_occupancy/`` ``summary.json`` (the occupancy-weighted carrier
test), ``yardstick.json`` (the same test at other yardsticks), ``correlated.json``
(carriers sharing input), ``switching.json`` (a clocked chip by the same
protocol), ``window.json`` (the per-window link at every window length),
``bridge.json`` (the bridge's two loops on a model pair of regions) and
``relay.json`` (a thalamic relay cell in tonic and burst mode), and
``recordings.json`` with ``recordings_slow200.json`` (recorded membranes of awake
cortex, at two splits of their slow part), and writes
``unity/unity_results.tex``. Nothing here integrates a sheet, sums a Fourier
series or propagates a membrane: ``unity_agreement.py``, ``unity_occupancy.py``,
``unity_correlated.py``, ``unity_switching.py``, ``unity_window.py``,
``unity_bridge.py``, ``unity_relay.py`` and ``unity_recordings.py`` produce the summaries as
separate commands.
"""

import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any, cast

import numpy as np

from unity_estimates import reported_orders

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


def _sig(value: float, digits: int, *, up: bool) -> str:
    """A bound to ``digits`` significant figures, rounded only away from the claim."""
    scale = 10 ** (math.floor(math.log10(value)) - digits + 1)
    steps = round(value / scale, 9)
    rounded = (math.ceil(steps) if up else math.floor(steps)) * scale
    return f"{rounded:.{digits}g}"


def _floor(value: float, digits: int) -> str:
    """A lower bound printed without rounding up."""
    return f"{math.floor(value * 10**digits) / 10**digits:.{digits}f}"


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
        values.append((f"uHarmonicRatio{name}", f"{math.ceil(ratio * 100) / 100:.2f}"))
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
    return [
        ("uOccContentShortMs", f"{float(short):g}"),
        ("uOccContentLongMs", f"{float(long):g}"),
        ("uOccCarriersFew", str(few)),
        ("uOccCarriersMid", str(mid)),
        ("uOccCarriersMany", str(many)),
        ("uOccInstantLinkMin", _sig(instant, 2, up=True)),
        ("uOccHitMinLong", _sig(min(hits[long]), 2, up=False)),
        ("uOccHitMaxLong", _sig(max(hits[long]), 3, up=True)),
        ("uOccLinkFewLong", _floor(1.0 - (1.0 - min(hits[long])) ** few, 2)),
        ("uOccLinkMidShort", _floor(1.0 - (1.0 - min(hits[short])) ** mid, 2)),
    ]


def _regime_values(neurons: list[dict[str, Any]]) -> list[tuple[str, str]]:
    """The declared ranges, and where the membrane sits and passes across them."""
    passing = [100 * _finite(n["pass_fraction"]) for n in neurons]
    # A reader that registers only whether the membrane fired within the window.
    counted = [
        100 * _finite(n["latched_pass_fraction"][f"{_finite(n['config']['window_ms']):g}"])
        for n in neurons
    ]
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
        ("uOccPassMinPercent", _sig(min(passing), 2, up=False)),
        ("uOccPassMaxPercent", _sig(max(passing), 2, up=True)),
        ("uOccCountPassMinPercent", _sig(min(counted), 2, up=False)),
        ("uOccCountPassMaxPercent", _sig(max(counted), 2, up=True)),
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
        ("uOccBitOrders", str(reported_orders(-_finite(bit["log10_max_response"])))),
    ]


def _occupancy_values(summary: dict[str, Any]) -> list[tuple[str, str]]:
    neurons = cast(list[dict[str, Any]], summary["neurons"])
    if not neurons:
        raise ValueError("The saved occupancy summary has no regimes")
    return [*_regime_values(neurons), *_control_values(summary), *_window_values(neurons)]


def _yardstick_values(swept: dict[str, Any]) -> list[tuple[str, str]]:
    """The range of yardsticks over which the membrane still reaches a passing state."""
    yardsticks = [_finite(y) for y in swept["yardsticks"]]
    if not yardsticks:
        raise ValueError("The saved yardstick sweep has no yardsticks")
    neurons = cast(list[dict[str, Any]], swept["neurons"])
    best = min(_finite(b) for n in neurons for b in n["best_response"].values())
    top = yardsticks.index(max(yardsticks))
    hits = [
        _finite(per[w])
        for n in neurons
        for per in n["by_yardstick"][top]["window_hit_probability"].values()
        for w in per
        if float(w) == max(float(k) for k in per)
    ]
    return [
        ("uYardLow", f"{min(yardsticks):g}"),
        ("uYardHigh", f"{max(yardsticks):g}"),
        ("uYardBinaryCeiling", f"{_finite(swept['binary_ceiling']):.2f}"),
        ("uYardBestMin", _floor(best, 2)),
        ("uYardHitMinHigh", _sig(min(hits), 2, up=False)),
    ]


# Shares at which the miss probability is printed, besides the tolerated one.
MISS_SHARES = ("0.25", "0.5")


def _ceil_sig(value: float) -> str:
    """An upper bound to two significant figures, never rounded down."""
    scale = 10 ** (math.floor(math.log10(value)) - 1)
    return f"{math.ceil(value / scale) * scale:.2g}"


def _links(
    neurons: list[dict[str, Any]], share: str, window: str, carriers: int, errors: float = 0.0
) -> list[float]:
    """The link probability in every regime and noise share, ``errors`` standard errors low."""
    return [
        1.0 - _finite(row["probability"]) - errors * _finite(row["standard_error"])
        for n in neurons
        for per in n["by_scale"].values()
        for row in [per[share][window]["no_link"][str(carriers)]]
    ]


def _misses(neurons: list[dict[str, Any]], share: str, carriers: int) -> float:
    """The largest miss probability, two standard errors high."""
    return max(
        _finite(row["probability"]) + 2 * _finite(row["standard_error"])
        for n in neurons
        for per in n["by_scale"].values()
        for row in [per[share]["400"]["no_link"][str(carriers)]]
    )


def _correlated_values(swept: dict[str, Any]) -> list[tuple[str, str]]:
    """The largest share every regime tolerates, and the links and misses around it."""
    neurons = cast(list[dict[str, Any]], swept["neurons"])
    if not neurons:
        raise ValueError("The saved correlated sweep has no regimes")
    tolerated = min(_finite(t) for n in neurons for t in n["largest_share"].values())
    tol = f"{tolerated:g}"
    mid, many = str(swept["link_carriers"]), str(max(swept["carriers"]))
    values = [
        ("uCorShareTol", tol),
        ("uCorPaths", str(swept["paths"])),
        # Monte Carlo bounds: two standard errors below the least link.
        ("uCorLinkMidTol", _floor(min(_links(neurons, tol, "400", int(mid), 2.0)), 2)),
        ("uCorLinkManyTol", _floor(min(_links(neurons, tol, "400", int(many), 2.0)), 2)),
        ("uCorLinkShortTol", f"{min(_links(neurons, tol, '40', int(mid))):.2f}"),
    ]
    for label, share in zip("AB", MISS_SHARES, strict=True):
        miss = _misses(neurons, share, int(mid))
        values += [(f"uCorShare{label}", share), (f"uCorMiss{label}", _ceil_sig(miss))]
    values.append(("uCorMissC", _ceil_sig(_misses(neurons, tol, int(mid)))))
    check = swept["resolution_check"]
    rho = [
        [_finite(row["400"]["pair_correlation"]) for row in check[k]["by_scale"]["1"].values()]
        for k in ("coarse", "fine")
    ]
    shift = max(abs(a - b) for a, b in zip(*rho, strict=True))
    values.append(("uCorResolutionRho", _ceil_sig(shift)))
    return values


def _scientific(value: float) -> str:
    """A positive count in TeX math, one significant figure: ``8\\times10^{5}``."""
    exponent = math.floor(math.log10(value))
    return f"{round(value / 10**exponent):d}\\times10^{{{exponent}}}"


def _switching_values(chip: dict[str, Any]) -> list[tuple[str, str]]:
    """The clocked chip by the same protocol: its nodes, its latch, its synchronizer."""
    nodes = cast(list[dict[str, Any]], chip["nodes"])
    if not nodes:
        raise ValueError("The saved switching summary has no nodes")
    declared, sync = chip["declared"], chip["synchronizer"]
    passing = [100 * _finite(n["pass_fraction"]) for n in nodes]
    silent = min(-_finite(v) for n in nodes for v in n["log10_no_transition"].values())
    long = f"{max(_finite(w) for w in declared['windows_ms']):g}"
    return [
        ("uSwClockGHz", f"{_finite(declared['clock_hz']) / 1e9:g}"),
        ("uSwActivityLow", f"{min(_finite(n['activity']) for n in nodes):g}"),
        ("uSwActivityHigh", f"{max(_finite(n['activity']) for n in nodes):g}"),
        ("uSwTransitionPs", f"{_finite(declared['transition_s']) * 1e12:.0f}"),
        ("uSwNodePassMinPercent", f"{min(passing):.2g}"),
        ("uSwNodePassMaxPercent", f"{max(passing):.2g}"),
        ("uSwNoTransitionOrders", str(reported_orders(silent))),
        ("uSwAperturePs", f"{_finite(declared['aperture_s']) * 1e12:.0f}"),
        ("uSwTauPs", f"{_finite(declared['resolution_tau_s']) * 1e12:.0f}"),
        ("uSwDataMHz", f"{_finite(declared['data_hz']) / 1e6:.0f}"),
        ("uSwSyncPassPercent", f"{100 * _finite(sync['pass_fraction_bound']):.2g}"),
        ("uSwSyncEventsLong", _scientific(_finite(sync["events_per_window"][long]))),
        ("uSwMtbfOrders", str(math.floor(math.log10(_finite(sync["mtbf_years"]))))),
    ]


def _window_sweep_values(swept: dict[str, Any]) -> list[tuple[str, str]]:
    """Where the membrane stops linking two regions as the window shortens."""
    ends = swept["lower_end_ms"]
    many, mid = (str(k) for k in sorted(swept["carriers"])[-1:-3:-1])
    if ends[many] is None or ends[mid] is None:
        raise ValueError("The saved window sweep never links two regions")
    return [
        ("uWinPerceptMs", f"{_finite(swept['percept_low_ms']):g}"),
        ("uWinLongestMs", f"{_finite(swept['longest_ms']):g}"),
        # "from this window upward": an upper bound, never rounded down.
        ("uWinLowManyMs", _sig(_finite(ends[many]), 2, up=True)),
        ("uWinLowMidMs", _sig(_finite(ends[mid]), 2, up=True)),
        ("uWinLinkPercept", _floor(_finite(swept["least_link_at_percept_low"][many]), 2)),
    ]


def _spans(row: dict[str, Any], task: dict[str, Any]) -> bool:
    """Whether the task variable spans at least half a quantizer step."""
    return 2 * _finite(task["sd"]) >= _finite(row["step"])


def _declared_rows(bridge: dict[str, Any]) -> list[dict[str, Any]]:
    """The declared step's row in every regime whose task spans half a step."""
    rows = [
        {**row, "spread": r["spread"]}
        for r in bridge["regimes"]
        for row in r["steps"]
        if row["step"] == bridge["declared_step"] and _spans(row, r["task"])
    ]
    if not rows or not all(_complete(row) for row in rows):
        raise ValueError("The saved bridge run has no match at the declared step")
    return rows


def _complete(row: dict[str, Any]) -> bool:
    """Whether a declared row has every match, the common cutoff and its spread."""
    matches = (row["linear"]["gap"], row["neighbour"]["decodability_cutoff_hz"])
    return None not in matches and row["common"] is not None and row["spread"] is not None


def _bridge_task_values(bridge: dict[str, Any]) -> list[tuple[str, str]]:
    """The declared task regimes and effect sizes."""
    tasks = [r["task"] for r in bridge["regimes"]]
    sds = [_finite(t["sd"]) for t in tasks]
    taus = [_finite(t["tau_ms"]) for t in tasks]
    effects = bridge["effects"]
    return [
        ("uBrTaskSdLow", f"{min(sds):g}"),
        ("uBrTaskSdHigh", f"{max(sds):g}"),
        ("uBrTaskTauShort", f"{min(taus):g}"),
        ("uBrTaskTauLong", f"{max(taus):g}"),
        ("uBrAccHigh", f"{_finite(effects['accuracy_high']):g}"),
        ("uBrAccLow", f"{_finite(effects['accuracy_low']):g}"),
        ("uBrNeuralEffect", f"{_finite(effects['neural']):g}"),
    ]


def _bridge_match_values(bridge: dict[str, Any]) -> list[tuple[str, str]]:
    """Where the loops match, and by how much the matched analog loop falls short."""
    rows = _declared_rows(bridge)
    cutoffs = [_finite(r["linear"]["te_cutoff_hz"]) for r in rows]
    gaps = [-_finite(r["linear"]["gap"]) for r in rows]
    others = [
        _finite(row["linear"]["gap"])
        for r in bridge["regimes"]
        for row in r["steps"]
        if row["linear"]["gap"] is not None and not _spans(row, r["task"])
    ]
    return [
        ("uBrCutoffMin", f"{math.floor(min(cutoffs)):d}"),
        ("uBrCutoffMax", f"{math.ceil(max(cutoffs)):d}"),
        ("uBrGapMin", _sig(min(gaps), 2, up=False)),
        ("uBrGapMax", _sig(max(gaps), 2, up=True)),
        ("uBrGapOtherMax", _sig(max(others), 2, up=True)),
    ]


def _bridge_trial_values(bridge: dict[str, Any]) -> list[tuple[str, str]]:
    """Trials per loop, and how closely the pilot blocks pin the match at that count."""
    rows = _declared_rows(bridge)
    trials, block = bridge["trials"], _finite(bridge["block_trials"])
    scale = 1.959963984540054 * math.sqrt(block / _finite(trials["behaviour"]))
    spreads = [r["spread"][name] for r in rows for name in ("linear", "neighbour")]
    te = 100 * scale * max(_finite(s["relative_te_sd"]) for s in spreads)
    gap = scale * max(_finite(s["gap_sd"]) for s in spreads)
    return [
        ("uBrBlockTrials", f"{block:g}"),
        ("uBrTrialsBehaviour", str(trials["behaviour"])),
        ("uBrTrialsNeural", str(trials["neural"])),
        ("uBrTeTolPercent", _sig(te, 2, up=True)),
        ("uBrGapTol", _ceil_sig(gap)),
    ]


def _bridge_neighbour_values(bridge: dict[str, Any]) -> list[tuple[str, str]]:
    """The nearest-neighbour estimator: its binding match, and where a TE match exists."""
    rows = _declared_rows(bridge)
    cutoffs = [_finite(r["neighbour"]["decodability_cutoff_hz"]) for r in rows]
    gaps = [
        _finite(row["neighbour"]["gap"])
        for r in bridge["regimes"]
        for row in r["steps"]
        if row["neighbour"]["gap"] is not None and _spans(row, r["task"])
    ]
    return [
        ("uBrNnCutoffMin", f"{math.floor(min(cutoffs)):d}"),
        ("uBrNnCutoffMax", f"{math.ceil(max(cutoffs)):d}"),
        ("uBrNnGapPositive", str(sum(g > 0 for g in gaps))),
        ("uBrNnGapCases", str(len(gaps))),
        ("uBrNnGapMax", _sig(max(gaps), 2, up=True)),
    ]


def _bridge_common_values(bridge: dict[str, Any]) -> list[tuple[str, str]]:
    """How far below the quantized loop the analog loop falls at the common cutoff."""
    rows = [r["common"]["neighbour"] for r in _declared_rows(bridge)]
    te = [-100 * _finite(r["relative_te_excess"]) for r in rows]
    gap = [-_finite(r["decodability_excess"]) for r in rows]
    return [
        ("uBrCommonTeMinPercent", _sig(min(te), 2, up=False)),
        ("uBrCommonTeMaxPercent", _sig(max(te), 2, up=True)),
        ("uBrCommonGapMin", _sig(min(gap), 2, up=False)),
        ("uBrCommonGapMax", _sig(max(gap), 2, up=True)),
    ]


def _by_kind(bridge: dict[str, Any], kind: str) -> dict[str, Any]:
    """The run restricted to continuous (``ou``) or held task regimes (U106)."""
    regimes = [r for r in bridge["regimes"] if r["task"].get("kind", "ou") == kind]
    return {**bridge, "regimes": regimes}


def _at_declared(bridge: dict[str, Any]) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    """Each regime with its row at the declared step."""
    return [
        (r, row)
        for r in bridge["regimes"]
        for row in r["steps"]
        if row["step"] == bridge["declared_step"]
    ]


def _bridge_visit_values(bridge: dict[str, Any]) -> list[tuple[str, str]]:
    """Criterion G per window at the declared step: continuous against held stimuli (U106)."""
    ou = [row for r, row in _at_declared(_by_kind(bridge, "ou")) if _spans(row, r["task"])]
    held = [row for _, row in _at_declared(_by_kind(bridge, "held"))]
    if not ou or not held:
        raise ValueError("The saved bridge run lacks continuous or held regimes")
    least = min(_finite(r["visit_fraction"]) for r in ou)
    most = max(_finite(r["visit_fraction"]) for r in held)
    return [
        ("uBrOuVisitMinPercent", f"{math.floor(100 * least):d}"),
        ("uBrHeldVisitMaxPercent", f"{math.ceil(100 * most):d}"),
    ]


def _bridge_held_values(bridge: dict[str, Any]) -> list[tuple[str, str]]:
    """The information both loops carry with held stimuli, the analog one at its floor."""
    held = _at_declared(_by_kind(bridge, "held"))
    stimuli = [2 * int(r["task"]["levels"]) + 1 for r, _ in held]
    decodable = [_finite(row["linear"]["decodability"]) for _, row in held]
    decodable += [_finite(r["floor"]["linear"]["decodability"]) for r, _ in held]
    te = [
        100
        * _finite(r["floor"]["linear"]["transfer_entropy"])
        / _finite(row["linear"]["transfer_entropy"])
        for r, row in held
    ]
    return [
        ("uBrHeldStimuliFew", str(min(stimuli))),
        ("uBrHeldStimuliMany", str(max(stimuli))),
        ("uBrHeldSpread", f"{_finite(bridge['held_spread']):g}"),
        ("uBrHeldDecodMin", _floor(min(decodable), 2)),
        ("uBrHeldFloorTeMinPercent", f"{math.floor(min(te)):d}"),
        ("uBrHeldFloorTeMaxPercent", f"{math.ceil(max(te)):d}"),
    ]


def _bridge_values(bridge: dict[str, Any]) -> list[tuple[str, str]]:
    """The bridge's two loops on a model pair of regions."""
    ou = _by_kind(bridge, "ou")
    return [
        *_bridge_task_values(ou),
        *_bridge_match_values(ou),
        *_bridge_neighbour_values(ou),
        *_bridge_common_values(ou),
        *_bridge_trial_values(ou),
        *_bridge_visit_values(bridge),
        *_bridge_held_values(bridge),
    ]


def _relay_pairs(cells: list[dict[str, Any]]) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    """Tonic and burst cells at the same noise, rate and window."""
    burst = [c for c in cells if c["mode"] == "burst"]
    tonic = {json.dumps(c["config"], sort_keys=True): c for c in cells if c["mode"] == "tonic"}
    return [(tonic[json.dumps(b["config"], sort_keys=True)], b) for b in burst]


def _relay_mode_values(cells: list[dict[str, Any]], mode: str, label: str) -> list[tuple[str, str]]:
    """One mode's passing share at an instant and its visit probability over a percept."""
    rows = [c for c in cells if c["mode"] == mode]
    passing = [100 * _finite(c["pass_fraction"]) for c in rows]
    long = max(rows[0]["window_hit_probability"], key=float)
    hits = [_finite(c["window_hit_probability"][long]) for c in rows]
    return [
        (f"uRl{label}PassMinPercent", _sig(min(passing), 2, up=False)),
        (f"uRl{label}PassMaxPercent", _sig(max(passing), 2, up=True)),
        (f"uRl{label}HitMin", _sig(min(hits), 2, up=False)),
        (f"uRl{label}HitMax", _sig(max(hits), 2, up=True)),
    ]


def _relay_values(relay: dict[str, Any]) -> list[tuple[str, str]]:
    """A thalamic relay cell at matched rates in its two modes."""
    cells = relay["cells"]
    ratios = [
        _finite(tonic["window_hit_probability"][w]) / _finite(burst["window_hit_probability"][w])
        for tonic, burst in _relay_pairs(cells)
        for w in tonic["window_hit_probability"]
    ]
    check = relay["resolution_check"]
    moved = [
        abs(_finite(f["window_hit_probability"][w]) / _finite(c["window_hit_probability"][w]) - 1)
        for c, f in zip(check["coarse"], check["fine"], strict=True)
        for w in c["window_hit_probability"]
    ]
    sigmas = sorted({_finite(c["config"]["sigma_mv"]) for c in cells})
    rates = sorted({_finite(c["config"]["rate_hz"]) for c in cells})
    return [
        ("uRlSigmaLow", f"{sigmas[0]:g}"),
        ("uRlSigmaHigh", f"{sigmas[-1]:g}"),
        ("uRlRateLow", f"{rates[0]:g}"),
        ("uRlRateHigh", f"{rates[-1]:g}"),
        *_relay_mode_values(cells, "tonic", "Tonic"),
        *_relay_mode_values(cells, "burst", "Burst"),
        ("uRlHitRatioMin", _floor(min(ratios), 1)),
        ("uRlResolutionPercent", _ceil_sig(100 * max(moved))),
    ]


# The recorded cells the paper states: excitatory, the membranes the model is of.
RECORDED_TYPE = "EXC"
# Spread across cells is stated as the tenth to the ninetieth percentile.
DECILES = (10.0, 90.0)
# The share at which recorded window visits are stated, as in the model's claim.
RECORDED_SCALE = "0.25"


def _states(recordings: dict[str, Any], state: str) -> list[dict[str, Any]]:
    cells = recordings["cells"]
    return [
        c["states"][state]
        for c in cells
        if c["type"] == RECORDED_TYPE and state in c.get("states", {})
    ]


def _hits(states: list[dict[str, Any]], long: str) -> list[float]:
    """Each state's measured chance of a passing state within the long window."""
    return [
        _finite(s["windows"][0]["window_hit_probability"][RECORDED_SCALE][long]) for s in states
    ]


def _passes(states: list[dict[str, Any]]) -> list[float]:
    return [100 * _finite(s["windows"][0]["pass_fraction"]["1"]["measured"]) for s in states]


def _deciles(values: list[float]) -> tuple[float, float]:
    low, high = np.percentile(values, DECILES)
    return float(low), float(high)


def _outward(values: list[float], digits: int) -> tuple[str, str]:
    """The decile range to ``digits`` decimals, each end rounded away from the middle."""
    low, high = _deciles(values)
    scale = 10**digits
    return (
        f"{math.floor(low * scale) / scale:.{digits}f}",
        f"{math.ceil(high * scale) / scale:.{digits}f}",
    )


def _model_bounds(summary: dict[str, Any]) -> tuple[float, float, float]:
    """The model's least and greatest pass fraction, in percent, and its least visit."""
    neurons = summary["neurons"]
    passing = [100 * _finite(n["pass_fraction"]) for n in neurons]
    hits = [_finite(h["400"]) for n in neurons for h in n["window_hit_probability"].values()]
    return min(passing), max(passing), min(hits)


def _recordings_values(
    recordings: dict[str, Any], alternative: dict[str, Any], summary: dict[str, Any]
) -> list[tuple[str, str]]:
    """Recorded excitatory membranes in quiet wakefulness, beside the model's declared ranges."""
    quiet, whisking = _states(recordings, "quiet"), _states(recordings, "whisking")
    windows = quiet[0]["windows"][0]["window_hit_probability"][RECORDED_SCALE]
    long = max(windows, key=float)
    hits, passes = _hits(quiet, long), _passes(quiet)
    pass_low, pass_high, hit_min = _model_bounds(summary)
    ratios = [_finite(s["twin_rate_hz"]) / _finite(s["rate_hz"]) for s in quiet]
    few = min(int(k) for k in summary["neurons"][0]["link_probability"]["1"])
    mean_hit = sum(hits) / len(hits)
    distance = [_finite(s["distance"]) for s in quiet]
    fast = [_finite(s["fast_correlation_ms"]) for s in quiet]
    pairs = recordings["pairs"]
    alt = _states(alternative, "quiet")
    return [
        ("uRecCellsTotal", str(len(recordings["cells"]))),
        ("uRecCellsQuiet", str(len(quiet))),
        ("uRecCellsWhisk", str(len(whisking))),
        ("uRecTimedSweeps", str(pairs["timed_sweeps"])),
        ("uRecSlowMs", f"{_finite(recordings['slow_ms']):g}"),
        ("uRecMinStateS", f"{_finite(recordings['min_state_s']):g}"),
        ("uRecSlowAltMs", f"{_finite(alternative['slow_ms']):g}"),
        ("uRecDistanceMed", f"{np.median(distance):.1f}"),
        *zip(("uRecDistanceLow", "uRecDistanceHigh"), _outward(distance, 1), strict=True),
        *zip(("uRecFastMsLow", "uRecFastMsHigh"), _outward(fast, 0), strict=True),
        ("uRecPassMedPercent", f"{np.median(passes):.2g}"),
        ("uRecPassLowPercent", _sig(_deciles(passes)[0], 2, up=False)),
        ("uRecPassHighPercent", _sig(_deciles(passes)[1], 2, up=True)),
        (
            "uRecPassInsidePercent",
            f"{100 * np.mean([pass_low <= p <= pass_high for p in passes]):.0f}",
        ),
        ("uRecHitMedLong", f"{np.median(hits):.2f}"),
        ("uRecHitLowLong", _floor(_deciles(hits)[0], 2)),
        ("uRecHitHighLong", f"{math.ceil(_deciles(hits)[1] * 100) / 100:.2f}"),
        ("uRecHitBelowPercent", f"{100 * np.mean([h < hit_min for h in hits]):.0f}"),
        ("uRecLinkFewLong", _floor(1.0 - (1.0 - mean_hit) ** few, 2)),
        ("uRecHitMedLongWhisk", f"{np.median(_hits(whisking, long)):.2f}"),
        ("uRecDistanceMedWhisk", f"{np.median([_finite(s['distance']) for s in whisking]):.1f}"),
        ("uRecHitMedLongAlt", f"{np.median(_hits(alt, long)):.2f}"),
        ("uRecPassMedPercentAlt", f"{np.median(_passes(alt)):.2g}"),
        ("uRecRateRatioMed", f"{np.median(ratios):.2f}"),
        ("uRecRateWithinTwoPercent", f"{100 * np.mean([0.5 <= r <= 2.0 for r in ratios]):.0f}"),
    ]


def render(figures: Path) -> str:
    """Read saved summaries; never integrate a sheet or recompute a resistance."""
    directory = figures / "unity_agreement"
    values = _simulation_values(_read(directory / "summary.json"))
    values += _scaling_values(_read(directory / "resistance.json"))
    values += _occupancy_values(_read(figures / "unity_occupancy" / "summary.json"))
    values += _yardstick_values(_read(figures / "unity_occupancy" / "yardstick.json"))
    values += _correlated_values(_read(figures / "unity_occupancy" / "correlated.json"))
    values += _switching_values(_read(figures / "unity_occupancy" / "switching.json"))
    values += _window_sweep_values(_read(figures / "unity_occupancy" / "window.json"))
    values += _bridge_values(_read(figures / "unity_occupancy" / "bridge.json"))
    values += _relay_values(_read(figures / "unity_occupancy" / "relay.json"))
    values += _recordings_values(
        _read(figures / "unity_occupancy" / "recordings.json"),
        _read(figures / "unity_occupancy" / "recordings_slow200.json"),
        _read(figures / "unity_occupancy" / "summary.json"),
    )
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
