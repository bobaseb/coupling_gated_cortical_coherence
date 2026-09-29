"""A pilot grid kernel for a membrane with sparse positive synaptic jumps.

The Gaussian and jump variances sum to the OU innovation variance. The input
rate and jump scale must be set from voltage statistics; the firing rate is
reserved as an independent check. The bridge correction remains the diffusion
approximation used by ``unity_occupancy`` and is tested against simulated paths.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.laguerre import laggauss
from numpy.typing import NDArray
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
