import unittest
from typing import cast

import numpy as np

from tighter_threshold import compute_exponent, fit_diagnostics


class TighterThresholdTest(unittest.TestCase):
    def test_baseline_reproduces_the_published_six_leg_fit(self) -> None:
        result = compute_exponent(2000, 0.2, n_boot=200)
        self.assertTrue(result["complete"])
        self.assertEqual(result["n_fit_legs"], 6)
        self.assertAlmostEqual(float(str(result["exponent_ols"] or 0.0)), 0.444, places=3)
        self.assertIn("matched_exponent_ols", result)
        self.assertEqual(len(cast(list[float], result["fit_log_residuals"])), 6)
        self.assertEqual(len(cast(list[float], result["leave_one_out_exponents"])), 6)
        self.assertGreaterEqual(cast(float, result["largest_precritical_order"]), 0)
        self.assertGreaterEqual(cast(float, result["largest_coupling_step"]), 0)
        self.assertEqual(len(cast(list[float], result["precritical_max_by_speed"])), 8)
        self.assertEqual(len(cast(list[float], result["censored_count_by_speed"])), 8)

    def test_larger_population_uses_all_completed_artifacts(self) -> None:
        result = compute_exponent(8000, 0.05, n_boot=200)
        self.assertTrue(result["complete"])
        self.assertEqual(result["n_artifacts"], 8)
        self.assertEqual(result["n_fit_legs"], 7)
        self.assertEqual(result["missing_speeds"], [])
        self.assertIn("matched_exponent_ols", result)

    def test_log_residuals_detect_curvature_and_leave_one_out_instability(self) -> None:
        speeds = np.array([0.001, 0.002, 0.005, 0.01])
        exact = 2 * speeds**0.5
        self.assertLess(cast(float, fit_diagnostics(speeds, exact)["rms_log_residual"]), 1e-12)
        curved = exact.copy()
        curved[-1] *= 2
        diagnostics = fit_diagnostics(speeds, curved)
        self.assertGreater(cast(float, diagnostics["rms_log_residual"]), 0.1)
        slopes = cast(list[float], diagnostics["leave_one_out_exponents"])
        self.assertGreater(
            max(slopes) - min(slopes),
            0.1,
        )


if __name__ == "__main__":
    unittest.main()
