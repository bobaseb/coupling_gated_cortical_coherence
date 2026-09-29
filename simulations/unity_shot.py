"""A pilot grid kernel for a membrane with sparse positive synaptic jumps.

The Gaussian and jump variances sum to the OU innovation variance. The input
rate and jump scale must be set from voltage statistics; the firing rate is
reserved as an independent check. ``two_moment`` sets both from the measured
fast skew and three-SD tail excess. The bridge correction remains the diffusion
approximation used by ``unity_occupancy`` and is tested against simulated paths.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.laguerre import laggauss
from numpy.typing import NDArray
from scipy import stats
from scipy.special import ndtr

import unity_occupancy as uo

FloatArray = NDArray[np.float64]


@dataclass(frozen=True)
class ShotInput:
    """Poisson event rate per millisecond and exponential jump mean in noise units."""

    rate_per_ms: float
    scale: float


def step(
    grid: uo.Grid, membrane: uo.Membrane, dt_ms: float, shot: ShotInput
) -> tuple[FloatArray, FloatArray]:
    """Surviving node kernel and spike mass for at most one jump per grid step."""
    probability = shot.rate_per_ms * dt_ms
    if not 0 <= probability < 1 or shot.scale < 0:
        raise ValueError("invalid jump rate or scale")
    decay = math.exp(-dt_ms / membrane.tau_ms)
    variance = 1 - decay**2 - probability * (2 - probability) * shot.scale**2
    if variance <= 0:
        raise ValueError("jump input exceeds the unit innovation variance")
    v = grid.nodes
    centre = membrane.mean + decay * (v - membrane.mean) - probability * shot.scale
    upper = np.append(v[:-1] + grid.step / 2, 0.0)
    spread = math.sqrt(variance)
    baseline = ndtr((upper[:, None] - centre[None, :]) / spread)
    nodes, weights = laggauss(16)
    jump = sum(
        float(weight) * ndtr((upper[:, None] - centre[None, :] - shot.scale * node) / spread)
        for node, weight in zip(nodes, weights, strict=True)
    )
    cumulative = (1 - probability) * baseline + probability * jump
    cell = np.diff(np.vstack([np.zeros_like(centre), cumulative]), axis=0)
    bridge = np.exp(-2 * np.outer(v, v) / variance)
    surviving = cell * (1 - bridge)
    return surviving, 1 - surviving.sum(axis=0)


def chain(grid: uo.Grid, membrane: uo.Membrane, dt_ms: float, shot: ShotInput) -> FloatArray:
    """Transition matrix over subthreshold nodes and refractory stages."""
    surviving, spiking = step(grid, membrane, dt_ms, shot)
    count = grid.nodes.size
    stages = max(1, round(membrane.refractory_ms / dt_ms))
    matrix = np.zeros((count + stages, count + stages))
    matrix[:count, :count] = surviving
    matrix[count, :count] = spiking
    for index in range(stages - 1):
        matrix[count + index + 1, count + index] = 1
    matrix[:count, count + stages - 1] = uo._reset_mass(grid, membrane.reset)
    return matrix


def stationary_rate(grid: uo.Grid, membrane: uo.Membrane, dt_ms: float, shot: ShotInput) -> float:
    """The firing rate predicted without fitting to spike counts."""
    matrix = chain(grid, membrane, dt_ms, shot)
    mass = uo._stationary_mass(matrix)
    return float(mass[grid.nodes.size] * 1000 / dt_ms)


def tail_ratio(fraction: float, skew: float) -> float:
    """Stationary mass above three SD over a Gaussian's, for unit-variance input.

    Filtered exponential jumps are Gamma distributed; ``fraction`` of the
    variance is theirs and the rest Gaussian, with the given stationary skew.
    """
    shape = 4 * fraction**3 / skew**2
    scale = math.sqrt(fraction / shape)
    shift = 3 + shape * scale
    z = np.linspace(-10, 10, 4001)
    tail = stats.gamma.sf(shift - math.sqrt(1 - fraction) * z, shape, scale=scale)
    return float(np.trapezoid(stats.norm.pdf(z) * tail, z) / stats.norm.sf(3))


def two_moment(skew: float, tail: float, tau_ms: float) -> tuple[ShotInput, bool]:
    """Jump input matching skew and tail excess, and whether the tail was reachable.

    Among members with the measured skew, the lightest jumps that reach the
    tail are taken; if none reaches it, the heaviest-tailed member is.
    """
    fractions = np.linspace(0.01, 0.99, 197)
    ratios = np.array([tail_ratio(float(f), skew) for f in fractions])
    peak = int(np.argmax(ratios))
    reachable = bool(ratios[peak] >= tail)
    index = peak + int(np.flatnonzero(ratios[peak:] >= tail)[-1]) if reachable else peak
    fraction = float(fractions[index])
    shape = 4 * fraction**3 / skew**2
    return ShotInput(shape / tau_ms, math.sqrt(fraction / shape)), reachable
