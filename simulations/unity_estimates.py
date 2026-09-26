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

The noise floor (U24) applies a criterion fixed before either substrate was
evaluated: every sub-threshold change of a region larger than its own noise
amplitude must move the next content by at least one fluctuation, the total
variation ``2Φ(1/2) − 1`` that a one-standard-deviation shift produces in a
Gaussian carrier. A digital node's noise is thermal, ``sqrt(kT/C)``; a change
of ``η`` leaves the node within its margin except with probability
``Q((margin − η)/σ)``, which bounds the response in the Lean theorem. A spike
time's shift under a sub-threshold input ``ΔV`` is ``ΔV / V̇`` and its jitter
``σ_V / V̇`` at the same crossing, so their ratio is ``ΔV / σ_V`` whatever the
slope; ``σ_V`` combines the membrane noise with the input's own release
variability.

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
  Johnson 1928, Phys Rev 32:97-109; Nyquist 1928, Phys Rev 32:110-113
    (thermal noise, kT/C on a capacitive node)
  Kish 2002, Phys Lett A 305:144-149 (thermal bit flips as a Gaussian tail
    beyond the noise margin)
  Markram et al. 1997, J Physiol 500:409-440 (unitary EPSP 1.3 mV, c.v. 0.52)
  Jacobson et al. 2005, J Physiol 564:145-160 (membrane noise s.d. 0.54 mV
    at -55 mV)
  Mainen & Sejnowski 1995, Science 268:1503-1506 (spike generation adds
    little noise: timing reproducible to under 1 ms)
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
BOLTZMANN_J_K = 1.380649e-23
TEMPERATURE_K = 300.0
# Declared, not measured: a logic node of one femtofarad.
NODE_CAPACITANCE_F = 1e-15
EPSP_MV = 1.3
EPSP_CV = 0.52
MEMBRANE_NOISE_MV = 0.54
# Above this argument the Gaussian tail is taken from its asymptotic series.
TAIL_SWITCH = 30.0


def normal_cdf(x: float) -> float:
    """The standard normal distribution function."""
    return 0.5 * math.erfc(-x / math.sqrt(2))


def tv_of_shift(d: float) -> float:
    """Total variation between two unit Gaussians whose means differ by ``d``."""
    return 2 * normal_cdf(abs(d) / 2) - 1


# The fluctuation: what a one-standard-deviation shift does to a Gaussian carrier.
FLUCTUATION_TV = tv_of_shift(1.0)


def log10_gaussian_tail(x: float) -> float:
    """``log10 Q(x)`` for ``x > 0``, without underflow at large ``x``."""
    if x < TAIL_SWITCH:
        return math.log10(0.5 * math.erfc(x / math.sqrt(2)))
    series = 1 - 1 / x**2 + 3 / x**4 - 15 / x**6
    log_density = -(x**2) / 2 - 0.5 * math.log(2 * math.pi)
    return (log_density - math.log(x) + math.log(series)) / math.log(10)


def inverse_gaussian_tail(p: float) -> float:
    """The ``z`` with ``Q(z) = p``, for ``0 < p < 1/2``, by bisection."""
    low, high = 0.0, 40.0
    for _ in range(200):
        mid = (low + high) / 2
        if 0.5 * math.erfc(mid / math.sqrt(2)) > p:
            low = mid
        else:
            high = mid
    return (low + high) / 2


def thermal_noise_v(capacitance: float) -> float:
    """RMS thermal voltage ``sqrt(kT/C)`` on a capacitive node."""
    return math.sqrt(BOLTZMANN_J_K * TEMPERATURE_K / capacitance)


def shift_to_jitter(epsp: float, cv: float, noise: float) -> float:
    """Spike-time shift over jitter for a sub-threshold input of mean ``epsp``."""
    return epsp / math.sqrt(noise**2 + (cv * epsp) ** 2)


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


def smallest_passing_input(cv: float, noise: float) -> float:
    """The least input whose spike-time shift reaches its jitter."""
    if cv >= 1:
        raise ValueError("Release variability at or above the mean: no input passes")
    return noise / math.sqrt(1 - cv**2)


def noise_floor() -> dict[str, float]:
    """The U24 criterion evaluated on a logic node and on a cortical spike time."""
    sigma = thermal_noise_v(NODE_CAPACITANCE_F)
    ratio = NOISE_MARGIN_V / sigma
    dprime = shift_to_jitter(EPSP_MV, EPSP_CV, MEMBRANE_NOISE_MV)
    return {
        "fluctuationTV": FLUCTUATION_TV,
        "nodeCapFf": 1e15 * NODE_CAPACITANCE_F,
        "thermalNoiseMv": 1000 * sigma,
        "marginToNoise": ratio,
        # A change of one noise amplitude leaves margin − σ: the response bound.
        "errorOrders": float(f"{-log10_gaussian_tail(ratio - 1):.3g}"),
        # The response reaches the fluctuation only this close to the threshold.
        "gradedWindowPercent": 100 * inverse_gaussian_tail(FLUCTUATION_TV) / ratio,
        "epspMv": EPSP_MV,
        "epspCv": EPSP_CV,
        "membraneNoiseMv": MEMBRANE_NOISE_MV,
        "corticalShiftToJitter": dprime,
        "corticalTV": tv_of_shift(dprime),
        # Every larger sub-threshold input passes: the ratio grows with the input.
        "epspPassMv": smallest_passing_input(EPSP_CV, MEMBRANE_NOISE_MV),
    }


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
        **noise_floor(),
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
