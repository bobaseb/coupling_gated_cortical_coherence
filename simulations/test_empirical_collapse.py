import unittest

import numpy as np

from empirical_collapse import (
    OBSERVED_CONCENTRATION_RANGE,
    bessel_ratio,
    compute_window_sensitivity,
    tangent_separation,
)


class WindowSensitivityTest(unittest.TestCase):
    def test_reports_each_requested_window_with_enough_pooled_samples(self) -> None:
        phase = np.zeros((62, 500), dtype=float)

        rows = compute_window_sensitivity(phase, fs=5000.0, windows_ms=(5, 20, 100))

        self.assertEqual([row.window_ms for row in rows], [5, 20, 100])
        self.assertTrue(all(row.pooled_samples >= 100 for row in rows))
        self.assertTrue(all(np.isfinite(row.mean_residual) for row in rows))


class TangentSeparationTest(unittest.TestCase):
    def test_deviations_bound_the_curve_over_the_observed_range(self) -> None:
        separation = tangent_separation()

        low, high = OBSERVED_CONCENTRATION_RANGE
        grid = np.linspace(low, high, 401)
        curve = np.array([bessel_ratio(a) for a in grid])
        self.assertAlmostEqual(
            separation.linear_deviation, float(np.max(np.abs(curve - grid / 2))), places=5
        )
        self.assertAlmostEqual(
            separation.tanh_deviation,
            float(np.max(np.abs(curve - np.tanh(grid / 2)))),
            places=5,
        )

    def test_probe_and_target_are_consistent_with_the_curve(self) -> None:
        separation = tangent_separation(probe=1.5, target=0.17)

        self.assertAlmostEqual(separation.probe_separation, 1.5 / 2 - bessel_ratio(1.5), places=6)
        self.assertAlmostEqual(
            separation.target_concentration / 2 - bessel_ratio(separation.target_concentration),
            0.17,
            places=6,
        )
        self.assertGreater(separation.target_concentration, 1.5)


if __name__ == "__main__":
    unittest.main()
