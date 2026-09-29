"""A jump-input membrane tested against paths generated from its own dynamics."""

import math
import unittest

import numpy as np

import unity_occupancy as uo
from unity_shot import ShotInput, stationary_rate, step
from unity_shot_pilot import threshold_rate


class ShotKernelTest(unittest.TestCase):
    def test_zero_threshold_spread_recovers_the_ou_rate(self) -> None:
        grid = uo.Grid(-8, 0.1)
        membrane = uo.Membrane(10.0, -2.5, -2.5, 2.0)
        expected = uo.stationary(grid, membrane, 0.1)[2]
        self.assertAlmostEqual(threshold_rate(grid, membrane, 0.1, 0), expected)

    def test_kernel_conserves_probability_and_raises_spiking_from_upward_jumps(self) -> None:
        grid = uo.Grid(-8, 0.1)
        membrane = uo.Membrane(10.0, -2.5, -2.5, 2.0)
        shot = ShotInput(0.04, 0.6)
        surviving, spiking = step(grid, membrane, 0.1, shot)
        np.testing.assert_allclose(surviving.sum(axis=0) + spiking, 1.0, atol=1e-12)
        self.assertGreater(stationary_rate(grid, membrane, 0.1, shot), 0.0)

    def test_rate_matches_a_path_of_the_jump_model(self) -> None:
        grid = uo.Grid(-8, 0.1)
        membrane = uo.Membrane(10.0, -2.5, -2.5, 2.0)
        shot = ShotInput(0.04, 0.6)
        rng = np.random.default_rng(3)
        decay = math.exp(-0.1 / membrane.tau_ms)
        probability = shot.rate_per_ms * 0.1
        spread = math.sqrt(1 - decay**2 - probability * (2 - probability) * shot.scale**2)
        voltage, refractory, spikes = membrane.mean, 0, 0
        for _ in range(500_000):
            if refractory:
                refractory -= 1
                continue
            jump = rng.exponential(shot.scale) if rng.random() < probability else 0.0
            voltage = membrane.mean + decay * (voltage - membrane.mean)
            voltage += spread * rng.normal() + jump - probability * shot.scale
            if voltage >= 0:
                spikes += 1
                voltage = membrane.reset
                refractory = round(membrane.refractory_ms / 0.1) - 1
        measured = spikes / 50.0
        self.assertAlmostEqual(
            stationary_rate(grid, membrane, 0.1, shot) / measured, 1.0, delta=0.2
        )


if __name__ == "__main__":
    unittest.main()
