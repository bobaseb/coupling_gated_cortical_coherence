"""The per-window noise-floor test of a clocked chip, transients included (U75).

``unity_occupancy.py`` tests a membrane over every state it occupies, and a bit
restored to its rail. A working chip's nodes also pass through their
thresholds, many times in every window a percept takes, so this module counts
them by the same protocol, at the three places a chip's physics meets its
contents.

The node. On the rising half of a transition the node's voltage ramps through
its threshold at a slew ``V̇``. A change ``ΔV`` moves the time of the crossing by
``ΔV / V̇``, and noise ``σ`` jitters it by ``σ / V̇``, so the response is
``2Φ(ΔV / 2σ) − 1`` whatever the slew, the spike-time identity of
``unity_estimates.py``. Every change of at least one noise amplitude reaches the
fluctuation, so the node passes, if its next content is the time of its
crossing, on the rising half of every transition and nowhere else. A node that
switches in a fraction ``α`` of cycles spends ``α f t / 2`` of its time there,
and a window of ``N`` cycles contains no transition with probability
``(1 − α)^N``.

The latch. A clocked path is timing-closed: every transition lies outside the
latch's setup-and-hold window, so the value the latch reads is the node at its
rail, which is the restored bit of ``unity_occupancy.bit_summary`` at the logic
node's margin.

The synchronizer. A flip-flop sampling data from another clock domain catches a
transition inside its aperture ``T_W`` at the rate ``T_W f_C f_D`` (Ginosar
2011), and what its reader takes is the bit it resolves to. Under Gaussian
noise a single bit's response to a change of one noise amplitude, asked in both
directions as the criterion asks, is at most ``Φ(1) − 1/2``, below the
fluctuation, and the stage's own noise only lowers it. So the synchronizer
passes at no yardstick above that ceiling, and below it counting every sample
in the aperture as passing bounds its passing fraction by ``T_W f_D``. A second
stage allowed one cycle ``S`` to resolve fails with mean
time ``e^{S/τ} / (T_W f_C f_D)``.

Other noise laws (U89). A bit read as 1 when a quantity plus noise exceeds a
threshold responds to a change ``a`` by the noise law's mass on one of the two
intervals of width ``a`` that meet at the threshold, so its two-sided response
is the smaller of the two. For a symmetric law with one peak this is largest
with the threshold at the state, where it is ``F(a) − 1/2``, so one bit stays
below the fluctuation exactly when the law puts less than twice the fluctuation
of its mass within one amplitude of its centre. Gaussian, logistic and Laplace
laws at unit standard deviation do; a Student law with three degrees of
freedom does not. Thermal noise is Gaussian.

Several bits reading one quantity (U89). A word of stages reading one graded
quantity, each adding noise of its own, is a function of that quantity plus
noise independent of it, so by the data-processing inequality its response to
a change is at most the quantity's own, ``2Φ(a/2) − 1``. Two thresholds half an
amplitude either side of the state, with no stage noise, attain it: the word
passes where the quantity it reads passes, and nowhere else.

Declared parameters, not measured ones: a 1 GHz clock; activity factors from a
memory-like 0.02 through random logic's typical 0.1 to a node that switches
every other cycle, 0.5 (the dynamic-power convention ``P = α C V² f``); a
transition of 20 ps and the synchronizer of Ginosar's 28 nm example, ``τ`` = 10
ps, ``T_W`` = 20 ps, data changing every ten cycles, both close to a gate delay:

  Ginosar 2011, IEEE Design & Test of Computers 28(5):23-35 (MTBF formula;
    28 nm example: 4×10^29 years; 2×10^6 metastable samples per second)

Nothing is integrated and nothing is sampled; ``switching.json`` is written
beside the occupancy summaries, and ``unity_macros.py`` reads it.
"""

from __future__ import annotations

import itertools
import json
import math
from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

from unity_estimates import FLUCTUATION_TV, noise_floor, normal_cdf, tv_of_shift
from unity_occupancy import CONTENT_WINDOWS_MS, SHIFTS, YARDSTICKS, bit_summary

OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_occupancy"

CLOCK_HZ = 1e9
ACTIVITIES = (0.02, 0.1, 0.5)
TRANSITION_S = 20e-12
APERTURE_S = 20e-12
RESOLUTION_TAU_S = 10e-12
DATA_HZ = CLOCK_HZ / 10
SECONDS_PER_YEAR = 365.25 * 24 * 3600
# The largest two-sided response of one bit to a change of one noise amplitude.
BINARY_CEILING = normal_cdf(1.0) - 0.5
WORD_THRESHOLDS = (-0.5, 0.5)

Cdf = Callable[[float], float]


def _logistic(x: float) -> float:
    return 1.0 / (1.0 + math.exp(-x * math.pi / math.sqrt(3.0)))


def _laplace(x: float) -> float:
    tail = 0.5 * math.exp(-abs(x) * math.sqrt(2.0))
    return tail if x < 0 else 1.0 - tail


def _student3(x: float) -> float:
    t = x * math.sqrt(3.0)
    return 0.5 + (t / (math.sqrt(3.0) * (1 + t * t / 3)) + math.atan(t / math.sqrt(3.0))) / math.pi


# Symmetric single-peaked noise laws, each scaled to unit standard deviation.
NOISE_LAWS: dict[str, Cdf] = {
    "gaussian": normal_cdf,
    "logistic": _logistic,
    "laplace": _laplace,
    "student3": _student3,
}


def variance(cdf: Cdf, reach: float = 2000.0, nodes: int = 400_001) -> float:
    """``E[x²]`` of a symmetric law from its distribution function, on a grid."""
    edges = [reach * math.sinh(6 * k / (nodes - 1)) / math.sinh(6) for k in range(nodes)]
    total = 0.0
    for low, high in itertools.pairwise(edges):
        mid = 0.5 * (low + high)
        total += mid * mid * (cdf(high) - cdf(low))
    return 2 * total


def bit_ceiling(cdf: Cdf, change: float = 1.0) -> float:
    """The largest two-sided response of one bit to ``change``, over thresholds."""
    offsets = [k / 1000 for k in range(-3000, 3001)]
    return max(min(cdf(u) - cdf(u - change), cdf(u + change) - cdf(u)) for u in offsets)


def _stage_one(level: float, threshold: float, stage_noise: float) -> float:
    if stage_noise == 0.0:
        return float(level > threshold)
    return normal_cdf((level - threshold) / stage_noise)


def word_law(thresholds: Sequence[float], state: float, stage_noise: float) -> list[float]:
    """The law of the word read from ``state`` plus unit Gaussian noise, one stage per threshold."""
    outcomes = list(itertools.product((0, 1), repeat=len(thresholds)))
    law = [0.0] * len(outcomes)
    step = 1e-3
    for k in range(-10_000, 10_001):
        noise = k * step
        weight = math.exp(-0.5 * noise * noise) * step / math.sqrt(2 * math.pi)
        ones = [_stage_one(state + noise, t, stage_noise) for t in thresholds]
        for i, word in enumerate(outcomes):
            law[i] += weight * math.prod(p if b else 1 - p for p, b in zip(ones, word, strict=True))
    return law


def _interval_law(thresholds: Sequence[float], state: float) -> list[float]:
    cuts = [-math.inf, *sorted(thresholds), math.inf]
    return [
        normal_cdf(high - state) - normal_cdf(low - state) for low, high in itertools.pairwise(cuts)
    ]


def word_response(thresholds: Sequence[float], change: float, stage_noise: float) -> float:
    """Total variation a ``change`` of the quantity makes to the word's law."""
    if stage_noise == 0.0:
        pair = [_interval_law(thresholds, x) for x in (0.0, change)]
    else:
        pair = [word_law(thresholds, x, stage_noise) for x in (0.0, change)]
    first, second = pair
    return 0.5 * sum(abs(p - q) for p, q in zip(first, second, strict=True))


def crossing_response(change: float, slew: float) -> float:
    """Total variation a ``change`` (noise amplitudes) makes to a crossing time at ``slew``."""
    shift, jitter = change / slew, 1.0 / slew
    return tv_of_shift(shift / jitter)


def node_passes(yardstick: float) -> bool:
    """Whether every admissible change moves the crossing time by ``yardstick``."""
    return min(crossing_response(s, 1.0) for s in SHIFTS) >= yardstick


def node_pass_fraction(activity: float, clock_hz: float, transition_s: float) -> float:
    """Share of time a node spends on the rising half of a transition."""
    return activity * clock_hz * transition_s / 2


def log10_no_transition(activity: float, cycles: float) -> float:
    """``log10`` of the chance that a window of ``cycles`` holds no transition."""
    return cycles * math.log10(1.0 - activity)


def metastable_rate(aperture_s: float, clock_hz: float, data_hz: float) -> float:
    """Samples per second that catch a transition inside the aperture."""
    return aperture_s * clock_hz * data_hz


def synchronizer_pass_bound(aperture_s: float, data_hz: float) -> float:
    """At most this share of a synchronizer's samples falls inside its aperture."""
    return aperture_s * data_hz


def synchronizer_passes(yardstick: float) -> bool:
    """Whether the bit a synchronizer resolves to can move by ``yardstick``."""
    return yardstick <= BINARY_CEILING


def mtbf_years(
    resolution_s: float, tau_s: float, aperture_s: float, clock_hz: float, data_hz: float
) -> float:
    """Mean time between synchronizer failures, ``e^{S/τ} / (T_W f_C f_D)``."""
    rate = metastable_rate(aperture_s, clock_hz, data_hz)
    return math.exp(resolution_s / tau_s) / rate / SECONDS_PER_YEAR


def _node(activity: float) -> dict[str, Any]:
    fraction = node_pass_fraction(activity, CLOCK_HZ, TRANSITION_S)
    return {
        "activity": activity,
        "pass_fraction": fraction,
        "pass_fraction_by_yardstick": [fraction if node_passes(y) else 0.0 for y in YARDSTICKS],
        "log10_no_transition": {
            f"{w:g}": log10_no_transition(activity, CLOCK_HZ * w / 1000) for w in CONTENT_WINDOWS_MS
        },
    }


def latched_summary() -> dict[str, Any]:
    """The latch reads the node at its rail: the restored bit at the logic node's margin."""
    margin = noise_floor()["marginToNoise"]
    bit = bit_summary(margin)
    return {
        "margin": margin,
        "pass_fraction": bit["pass_fraction"],
        "log10_max_response": bit["log10_max_response"],
        "pass_fraction_by_yardstick": [bit_summary(margin, y)["pass_fraction"] for y in YARDSTICKS],
    }


def _synchronizer() -> dict[str, Any]:
    rate = metastable_rate(APERTURE_S, CLOCK_HZ, DATA_HZ)
    bound = synchronizer_pass_bound(APERTURE_S, DATA_HZ)
    return {
        "pass_fraction_bound": bound,
        "binary_ceiling": BINARY_CEILING,
        "pass_fraction_by_yardstick": [
            bound if synchronizer_passes(y) else 0.0 for y in YARDSTICKS
        ],
        "events_per_window": {f"{w:g}": rate * w / 1000 for w in CONTENT_WINDOWS_MS},
        "mtbf_years": mtbf_years(1 / CLOCK_HZ, RESOLUTION_TAU_S, APERTURE_S, CLOCK_HZ, DATA_HZ),
    }


def run() -> dict[str, Any]:
    """Every declared activity, the latch and the synchronizer, at every yardstick."""
    return {
        "fluctuation_tv": FLUCTUATION_TV,
        "yardsticks": list(YARDSTICKS),
        "declared": {
            "clock_hz": CLOCK_HZ,
            "transition_s": TRANSITION_S,
            "aperture_s": APERTURE_S,
            "resolution_tau_s": RESOLUTION_TAU_S,
            "data_hz": DATA_HZ,
            "windows_ms": list(CONTENT_WINDOWS_MS),
        },
        "nodes": [_node(a) for a in ACTIVITIES],
        "latched": latched_summary(),
        "synchronizer": _synchronizer(),
        "noise_laws": {
            name: {
                "centre_mass": cdf(1.0) - cdf(-1.0),
                "ceiling": bit_ceiling(cdf),
                "below_fluctuation": bit_ceiling(cdf) < FLUCTUATION_TV,
            }
            for name, cdf in NOISE_LAWS.items()
        },
        "word": {
            "thresholds": list(WORD_THRESHOLDS),
            "best_response": word_response(WORD_THRESHOLDS, 1.0, 0.0),
            "quantity_response": tv_of_shift(1.0),
        },
    }


def write(directory: Path) -> None:
    """Save the summary; publication macros read it later."""
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "switching.json").write_text(json.dumps(run(), indent=2) + "\n")


if __name__ == "__main__":
    write(OUTPUT)
