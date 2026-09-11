import unittest

import numpy as np

from empirical_collapse import (
    BANDS,
    OBSERVED_CONCENTRATION_RANGE,
    bessel_ratio,
    compute_window_sensitivity,
    extract_phase,
    extract_phase_bipolar,
    extract_phase_car,
    tangent_separation,
)


class WindowSensitivityTest(unittest.TestCase):
    def test_reports_each_requested_window_with_enough_pooled_samples(self) -> None:
        phase = np.zeros((62, 500), dtype=float)

        rows = compute_window_sensitivity(phase, fs=5000.0, windows_ms=(5, 20, 100))

        self.assertEqual([row.window_ms for row in rows], [5, 20, 100])
        self.assertTrue(all(row.pooled_samples >= 100 for row in rows))
        self.assertTrue(all(np.isfinite(row.mean_residual) for row in rows))


class MontagePaddingTest(unittest.TestCase):
    def test_all_montages_discard_the_same_filter_padding(self) -> None:
        rng = np.random.default_rng(7)
        fs = 200.0
        padding = 0.25
        data = rng.normal(size=(65, 800))

        raw = extract_phase(data, fs, pad_seconds=padding)
        bipolar = extract_phase_bipolar(data, fs, pad_seconds=padding)
        car = extract_phase_car(data, fs, pad_seconds=padding)

        expected_samples = data.shape[1] - 2 * int(fs * padding)
        self.assertEqual(raw.shape[1], expected_samples)
        self.assertEqual(bipolar.shape[1], expected_samples)
        self.assertEqual(car.shape[1], expected_samples)


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


class AnalysisConfigurationTest(unittest.TestCase):
    def test_named_narrowband_set_includes_the_reported_gamma_band(self) -> None:
        self.assertEqual(BANDS["gamma"], [30.0, 40.0])


if __name__ == "__main__":
    unittest.main()
