"""Closed-form magnitude estimates for the physical-unity paper (U8, U9, U13).

Every input is a declared, published value; nothing is fitted or integrated.
``--write-tex`` regenerates ``unity/unity_estimates.tex``.

The unity window (U8) opens at the causal deadline, conduction along the
longest cortico-cortical fibres plus one synapse, and must open before the
content changes. With disagreement decaying as ``exp(-t/τ)``, reducing it by
the factor ``REDUCTION`` inside the remaining time needs
``τ ≤ (T_content − T_cone) / ln(REDUCTION)``. The same deadline is the field's
causal-cone signature (U9): a quasi-static field reaches across the tissue
with no propagation delay, so re-agreement well inside it is not synaptic.
The strict deadline uses the fastest callosal axons, not the median ones: a
median arrival is not a causal bound. The field's reach is where an endogenous
peak field, decaying as the gradient of an ``r^-2.1`` potential, falls to the
network detection threshold; placing the peak at the nearest distance at which
the decay was measured is a declared choice, like ``REDUCTION``.
The hardware ratio (U13) compares the supply variation a designer expects
with a textbook inverter's static noise margin.

References:
  Nunez & Srinivasan 2014, Brain Res 1542:138-166 (fibres up to 15-20 cm)
  Caminiti et al. 2009, PNAS 106:19551-19556 (median velocities 4.9-8.8 m/s,
    individual axons up to 20 m/s)
  Froehlich & McCormick 2010, Neuron 67:129-143 (in vivo peak 2.36 mV/mm)
  Francis, Gluckman & Schiff 2003, J Neurosci 23:7255-7261 (network detection
    at 0.14 mV/mm rms)
  Rebollo et al. 2021, Sci Adv 7:eabc7772 (potential ~ r^-2.1, from 1.5 mm)
  Sabatini & Regehr 1996, Nature 384:170-172; Katz & Miledi 1965,
    Proc R Soc B 161:483-495 (synaptic delay 0.15-0.75 ms)
  Herzog, Kammer & Scharnowski 2016, PLoS Biol 14:e1002433 (integration
    up to 400 ms)
  Rabaey, Chandrakasan & Nikolic 2003, Digital Integrated Circuits, 2nd ed.
    (Example 5.2: 1.03 V margin at 2.5 V supply; p. 123: 10% supply variation)
"""

import argparse
import math
from pathlib import Path

OUTPUT = Path(__file__).resolve().parent.parent / "unity" / "unity_estimates.tex"

FIBRE_LENGTH_M = 0.15
VELOCITY_SLOW_M_S = 4.9
VELOCITY_FAST_M_S = 8.8
VELOCITY_MAX_M_S = 20.0
SYNAPTIC_DELAY_S = 0.0005
CONTENT_TIME_S = 0.4
# Declared, not measured: agreement means a tenfold reduction of disagreement.
REDUCTION = 10.0
NOISE_MARGIN_V = 1.03
SUPPLY_V = 2.5
SUPPLY_VARIATION = 0.10
FIELD_PEAK_MV_MM = 2.36
FIELD_DETECTION_MV_MM = 0.14
# The field is the gradient of a potential decaying as r^-2.1.
FIELD_DECAY_EXPONENT = 3.1
# Declared, not measured: the peak sits at the nearest measured distance.
FIELD_NEAR_MM = 1.5


def field_reach(peak: float, detection: float, near: float, exponent: float) -> float:
    """Distance (units of ``near``) at which a power-law field falls to ``detection``."""
    return float(near * (peak / detection) ** (1 / exponent))


def field_deficit_orders(distance: float) -> float:
    """Orders of magnitude by which the field at ``distance`` (mm) misses detection."""
    field = FIELD_PEAK_MV_MM * (FIELD_NEAR_MM / distance) ** FIELD_DECAY_EXPONENT
    return math.log10(FIELD_DETECTION_MV_MM / field)


def cone_delay(length: float, velocity: float, synapse: float) -> float:
    """Seconds from a perturbation to its first synaptic effect at ``length``."""
    return length / velocity + synapse


def required_rate(reduction: float, content_time: float, cone: float) -> float:
    """The least decay rate (1/s) reaching ``reduction`` before the content changes."""
    remaining = content_time - cone
    if remaining <= 0:
        raise ValueError("The causal deadline falls after the content changes: no window")
    return math.log(reduction) / remaining


def estimates() -> dict[str, float]:
    """Every published quantity, in the units the paper states it."""
    cone_slow = cone_delay(FIBRE_LENGTH_M, VELOCITY_SLOW_M_S, SYNAPTIC_DELAY_S)
    cone_fast = cone_delay(FIBRE_LENGTH_M, VELOCITY_FAST_M_S, SYNAPTIC_DELAY_S)
    return {
        "fibreCm": 100 * FIBRE_LENGTH_M,
        "velocitySlow": VELOCITY_SLOW_M_S,
        "velocityFast": VELOCITY_FAST_M_S,
        "synapseMs": 1000 * SYNAPTIC_DELAY_S,
        "contentMs": 1000 * CONTENT_TIME_S,
        "reduction": REDUCTION,
        "coneSlowMs": 1000 * cone_slow,
        "coneFastMs": 1000 * cone_fast,
        "velocityMax": VELOCITY_MAX_M_S,
        "coneMaxMs": 1000 * cone_delay(FIBRE_LENGTH_M, VELOCITY_MAX_M_S, SYNAPTIC_DELAY_S),
        "fieldPeak": FIELD_PEAK_MV_MM,
        "fieldDetection": FIELD_DETECTION_MV_MM,
        "fieldReachMm": field_reach(
            FIELD_PEAK_MV_MM, FIELD_DETECTION_MV_MM, FIELD_NEAR_MM, FIELD_DECAY_EXPONENT
        ),
        "fieldDeficitOrders": field_deficit_orders(1000 * FIBRE_LENGTH_M),
        "tauSlowMs": 1000 / required_rate(REDUCTION, CONTENT_TIME_S, cone_slow),
        "tauFastMs": 1000 / required_rate(REDUCTION, CONTENT_TIME_S, cone_fast),
        "marginPercent": 100 * NOISE_MARGIN_V / SUPPLY_V,
        "supplyPercent": 100 * SUPPLY_VARIATION,
        "noiseToMargin": SUPPLY_VARIATION * SUPPLY_V / NOISE_MARGIN_V,
    }


def _format(value: float) -> str:
    return f"{value:.0f}" if value >= 10 else f"{value:.2g}"


def render() -> str:
    """The macro file, one ``\\ue...`` macro per estimate."""
    lines = [
        "% Generated by simulations/unity_estimates.py --write-tex from declared,",
        "% published parameters. Do not edit manually.",
        *(
            f"\\newcommand{{\\ue{name[0].upper()}{name[1:]}}}{{{_format(value)}}}"
            for name, value in estimates().items()
        ),
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    """Print the estimates, or regenerate the macro file."""
    parser = argparse.ArgumentParser(description="Physical-unity magnitude estimates")
    parser.add_argument("--write-tex", action="store_true")
    if parser.parse_args().write_tex:
        OUTPUT.write_text(render(), encoding="utf-8")
    for name, value in estimates().items():
        print(f"{name:>14}: {value:.4g}")


if __name__ == "__main__":
    main()
