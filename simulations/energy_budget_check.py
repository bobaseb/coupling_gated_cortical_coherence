#!/usr/bin/env python3
"""The installed-energy bound, read against the cortical metabolic budget.

The coherence condition of the article's Eq. (installed-coupling-bound) is
``U_inst > 2 D / kappa``: the energy installed in the arrangement's response
modes, converted at the hardware's own rate ``kappa``, must exceed the noise
threshold. This script asks what a cortical energy budget says about it.

What it can and cannot decide
-----------------------------
``kappa`` is declared hardware data -- coupling per unit installed energy --
and this repository derives it from nothing: cortical field generation has no
canonical decomposition into priced modes, so choosing the basis would choose
the answer. The energy budget therefore cannot evaluate the condition. What it
does is *invert* it. Given the metabolic power of one decay length's worth of
cortex, the condition becomes a bound on ``kappa`` alone, and the number it
returns is what the identification would have to deliver.

That is the useful reading, and it is the whole of it: the budget decides
nothing by itself, because the quantity it is compared against is `2 D / kappa`
and `kappa` is unknown. What the budget does settle is that *energy* is not the
scarce side. The installed energy of one decay sphere is reported in units of
`kT` at body temperature as well as in joules, and it is fourteen orders of
magnitude above that floor, so the condition can fail for cortex only through
the conversion factor. It is a sharp instrument where the installed energy
itself is small, and a statement about `kappa` everywhere else.

Inputs, and where each comes from
---------------------------------
* ``ATP_PER_NEURON_PER_SECOND``: 3.29e9 ATP/s per neuron in rat grey matter at
  a 4 Hz mean action-potential rate (Attwell & Laughlin 2001).
* ``SYNAPTIC_FRACTION``: synaptic mechanisms take 55% of the ATP spent on
  action potentials, synaptic transmission and resting potentials
  (Harris, Jolivet & Attwell 2012). Reported alongside the total because the
  currents that generate the extracellular field are the synaptic ones.
* ``ATP_FREE_ENERGY_KJ_PER_MOL``: 57 kJ/mol released per ATP hydrolysed at
  cytoplasmic concentrations (Nicholls & Ferguson 2013).
* The region is the LFP decay sphere of ``fermi_estimate_check``: radius
  ``lam`` at density ``rho``, so the neuron count is that file's.
* ``DIFFUSION``: 0.5 rad^2/s, the phase diffusion the spatial sweeps declare.
  It enters twice -- in the threshold ``2 D`` and in the residence time ``1/D``
  below -- so the required conversion goes as ``D^2``.

The residence time
------------------
A metabolic budget is a power and the bound wants an energy, and no measurement
here supplies the interval over which energy counts as installed. The declared
choice is one phase-diffusion time ``1/D``: the interval over which the noise
the coupling is competing against randomizes a phase. Any other choice rescales
the answer by its ratio to this one, and the script reports the interval so
that the rescaling is one division.

Usage:
  python simulations/energy_budget_check.py                    # print the budget
  python simulations/energy_budget_check.py --write-tex        # regenerate macros

References:
  Attwell & Laughlin 2001, J Cereb Blood Flow Metab 21:1133-1145
  Harris, Jolivet & Attwell 2012, Neuron 75:762-777
  Nicholls & Ferguson 2013, Bioenergetics 4, Academic Press
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path

from fermi_estimate_check import DEFAULTS, neurons_within

# ── declared inputs ─────────────────────────────────────────────────────

# Attwell & Laughlin 2001, rat grey matter, 4 Hz mean action-potential rate.
ATP_PER_NEURON_PER_SECOND = 3.29e9
FIRING_RATE_HZ = 4.0

# Harris, Jolivet & Attwell 2012: the share of signalling ATP spent at synapses.
SYNAPTIC_FRACTION = 0.55

# Nicholls & Ferguson 2013: free energy per ATP hydrolysed in the cytoplasm.
ATP_FREE_ENERGY_KJ_PER_MOL = 57.0

# CODATA 2019, exact by definition.
AVOGADRO = 6.02214076e23

# Phase diffusion, rad^2/s. The value the spatial sweeps of this repository
# declare; it is a parameter of this comparison and not a cortical measurement.
DIFFUSION = 0.5

# CODATA 2019 (exact) and body temperature, for the one scale against which
# "the energy is not the scarce quantity" is a statement rather than a feeling.
BOLTZMANN = 1.380649e-23
BODY_TEMPERATURE_K = 310.15


@dataclass(frozen=True)
class Budget:
    """One region's metabolic budget and the conversion factor it demands."""

    neurons: float
    neuron_power: float
    region_power: float
    synaptic_power: float
    residence_time: float
    installed_energy: float
    thermal_quanta: float
    kappa_required: float


def joules_per_atp() -> float:
    """Free energy released by hydrolysing one ATP, in joules."""
    return ATP_FREE_ENERGY_KJ_PER_MOL * 1000.0 / AVOGADRO


def budget(lam: float, rho: float, diffusion: float) -> Budget:
    """Evaluate the budget of a decay sphere and the ``kappa`` it demands.

    ``kappa_required`` is ``2 D / U_inst``: the smallest conversion factor at
    which the installed energy of this region clears the threshold. A hardware
    identification supplying anything above it satisfies the resource
    condition; nothing here says one does.
    """
    neurons = neurons_within(lam, rho)
    neuron_power = ATP_PER_NEURON_PER_SECOND * joules_per_atp()
    region_power = neurons * neuron_power
    residence_time = 1.0 / diffusion
    installed_energy = region_power * residence_time
    return Budget(
        neurons=neurons,
        neuron_power=neuron_power,
        region_power=region_power,
        synaptic_power=region_power * SYNAPTIC_FRACTION,
        residence_time=residence_time,
        installed_energy=installed_energy,
        thermal_quanta=installed_energy / (BOLTZMANN * BODY_TEMPERATURE_K),
        kappa_required=2.0 * diffusion / installed_energy,
    )


def cortical_budget() -> Budget:
    """The budget at the declared cortical parameters."""
    return budget(float(DEFAULTS["lam"]), float(DEFAULTS["rho"]), DIFFUSION)


# ── Tex generation ──────────────────────────────────────────────────────


TEX_HEADER = """%% Auto-generated by simulations/energy_budget_check.py --write-tex
%% Do not edit manually. Edit the Python script instead and regenerate.
%% Metabolic rates: Attwell & Laughlin 2001; Harris, Jolivet & Attwell 2012.
%% ATP free energy: Nicholls & Ferguson 2013."""


def _sci(value: float, digits: int = 1) -> str:
    """Render a value in LaTeX scientific notation."""
    mantissa, _, exponent = f"{value:.{digits}e}".partition("e")
    return f"{mantissa}\\times10^{{{int(exponent)}}}"


def _tc(name: str, value: object, comment: str) -> str:
    return f"\\newcommand{{\\{name}}}{{{value}}}  % {comment}"


def write_tex(path: str) -> None:
    """Write energy_budget.tex from this script's constants and one budget."""
    result = cortical_budget()
    lines = [
        TEX_HEADER,
        "",
        "% --- Declared inputs ---",
        _tc("energyAtpRate", _sci(ATP_PER_NEURON_PER_SECOND, 2), "ATP/s per neuron"),
        _tc("energyFiringRate", f"{FIRING_RATE_HZ:.0f}", "mean rate the budget assumes (Hz)"),
        _tc("energySynapticPercent", f"{SYNAPTIC_FRACTION * 100:.0f}", "synaptic share (per cent)"),
        _tc("energyAtpJoules", f"{ATP_FREE_ENERGY_KJ_PER_MOL:.0f}", "kJ per mol of ATP"),
        _tc("energyDiffusion", f"{DIFFUSION:.1f}", "phase diffusion (rad$^2$/s)"),
        "",
        "% --- The decay sphere's budget ---",
        _tc("energyNeurons", f"{result.neurons:.0f}", "neurons within one decay length"),
        _tc("energyNeuronPower", _sci(result.neuron_power), "W per neuron"),
        _tc("energyRegionPower", _sci(result.region_power), "W in the decay sphere"),
        _tc("energySynapticPower", _sci(result.synaptic_power), "W at synapses"),
        _tc("energyResidence", f"{result.residence_time:.0f}", "residence time $1/D$ (s)"),
        _tc("energyInstalled", _sci(result.installed_energy), "installed energy (J)"),
        _tc("energyThermalQuanta", _sci(result.thermal_quanta), "installed energy in $kT$"),
        "",
        "% --- What the bound then demands of the conversion factor ---",
        _tc("energyKappaRequired", _sci(result.kappa_required), "minimum kappa (J$^{-1}$s$^{-1}$)"),
    ]
    Path(path).write_text("\n".join(lines) + "\n")
    print(f"Wrote {path}")


# ── CLI ─────────────────────────────────────────────────────────────────


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Read the installed-energy bound against a cortical energy budget."
    )
    parser.add_argument(
        "--write-tex",
        metavar="PATH",
        nargs="?",
        const="simulations/energy_budget.tex",
        help="regenerate energy_budget.tex from this script's constants",
    )
    return parser


def main() -> None:
    args = _build_parser().parse_args()
    if args.write_tex:
        write_tex(args.write_tex)
        return

    result = cortical_budget()
    print("=" * 64)
    print("  Installed energy against the cortical metabolic budget")
    print("=" * 64)
    print()
    print(f"  neurons within lambda = {DEFAULTS['lam']} mm : {result.neurons:.0f}")
    print(f"  power per neuron                  : {result.neuron_power:.3e} W")
    print(f"  signalling power in the sphere    : {result.region_power:.3e} W")
    share = f"{SYNAPTIC_FRACTION:.0%}"
    print(f"  of which synaptic ({share})           : {result.synaptic_power:.3e} W")
    print(f"  residence time 1/D                : {result.residence_time:.2f} s")
    print(f"  installed energy U_inst           : {result.installed_energy:.3e} J")
    print(f"  ... in units of kT at 37 C        : {result.thermal_quanta:.3e}")
    print()
    print(f"  threshold 2D                      : {2.0 * DIFFUSION:.2f} rad/s")
    print(f"  required kappa = 2D / U_inst      : {result.kappa_required:.3e} J^-1 s^-1")
    print()
    print("  kappa is declared hardware data and is derived nowhere here, so")
    print("  this is what the identification must deliver, not a verdict on it.")


if __name__ == "__main__":
    main()
