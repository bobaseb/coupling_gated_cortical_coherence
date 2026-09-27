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
2011). Counting every such sample as passing bounds its passing fraction by
``T_W f_D``. A second stage allowed one cycle ``S`` to resolve fails with mean
time ``e^{S/τ} / (T_W f_C f_D)``.

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

import json
import math
from pathlib import Path
from typing import Any

from unity_estimates import FLUCTUATION_TV, noise_floor, tv_of_shift
from unity_occupancy import CONTENT_WINDOWS_MS, SHIFTS, YARDSTICKS, bit_summary

OUTPUT = Path(__file__).resolve().parent / "figures" / "unity_occupancy"

CLOCK_HZ = 1e9
ACTIVITIES = (0.02, 0.1, 0.5)
TRANSITION_S = 20e-12
APERTURE_S = 20e-12
RESOLUTION_TAU_S = 10e-12
DATA_HZ = CLOCK_HZ / 10
SECONDS_PER_YEAR = 365.25 * 24 * 3600


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
    return {
        "pass_fraction_bound": synchronizer_pass_bound(APERTURE_S, DATA_HZ),
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
    }


def write(directory: Path) -> None:
    """Save the summary; publication macros read it later."""
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "switching.json").write_text(json.dumps(run(), indent=2) + "\n")


if __name__ == "__main__":
    write(OUTPUT)
