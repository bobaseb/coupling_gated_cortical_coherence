import unittest
from typing import cast

import numpy as np

from dynamic_ramp import (
    RampConfig,
    detect_escape_coupling,
    estimate_log_density_concentration,
    simulate_ramp,
)


class DynamicRampTest(unittest.TestCase):
    def test_simulation_is_reproducible_and_crosses_critical_coupling(self) -> None:
        config = RampConfig(
            n_oscillators=64,
            n_replicas=3,
            diffusion=0.2,
            ramp_speed=0.4,
            coupling_half_window=0.2,
            dt=0.02,
            sample_every=5,
            seed=1729,
        )

        first = simulate_ramp(config)
        second = simulate_ramp(config)

        np.testing.assert_array_equal(first.order_mean, second.order_mean)
        np.testing.assert_array_equal(first.concentration_mean, second.concentration_mean)
        self.assertAlmostEqual(first.coupling[0], config.critical_coupling - 0.2)
        self.assertAlmostEqual(first.coupling[-1], config.critical_coupling + 0.2)
        self.assertTrue(np.any(first.coupling == config.critical_coupling))
        self.assertEqual(first.phase_snapshots, 0)

    def test_summary_is_decimated_and_includes_both_endpoints(self) -> None:
        config = RampConfig(
            n_oscillators=32,
            n_replicas=2,
            diffusion=0.1,
            ramp_speed=0.5,
            coupling_half_window=0.1,
            dt=0.02,
            sample_every=3,
            seed=7,
        )

        result = simulate_ramp(config)

        self.assertEqual(result.steps, 20)
        self.assertEqual(len(result.time), 8)
        self.assertAlmostEqual(result.time[0], 0.0)
        self.assertAlmostEqual(result.time[-1], result.steps * config.dt)

    def test_log_density_slope_recovers_a_von_mises_shape(self) -> None:
        rng = np.random.default_rng(20260903)
        phases = rng.vonmises(mu=0.7, kappa=2.0, size=100_000)

        estimate = estimate_log_density_concentration(phases, bins=48)

        self.assertAlmostEqual(estimate, 2.0, delta=0.12)

    def test_escape_detection_uses_the_finite_size_floor(self) -> None:
        coupling = np.array([1.9, 2.0, 2.1, 2.2])
        order = np.array([0.03, 0.04, 0.08, 0.12])

        escape = detect_escape_coupling(coupling, order, n_oscillators=400)

        self.assertIsNotNone(escape)
        self.assertAlmostEqual(cast(float, escape), 2.2)

    def test_escape_detection_reports_no_crossing(self) -> None:
        coupling = np.array([1.9, 2.0, 2.1])
        order = np.array([0.01, 0.02, 0.03])

        escape = detect_escape_coupling(coupling, order, n_oscillators=400)

        self.assertIsNone(escape)


if __name__ == "__main__":
    unittest.main()
