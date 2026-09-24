import unittest
from tighter_threshold import compute_exponent


class TighterThresholdTest(unittest.TestCase):
    def test_baseline_reproduces_the_published_six_leg_fit(self) -> None:
        result = compute_exponent(2000, 0.2, n_boot=200)
        self.assertTrue(result["complete"])
        self.assertEqual(result["n_fit_legs"], 6)
        self.assertAlmostEqual(float(str(result["exponent_ols"] or 0.0)), 0.444, places=3)
        self.assertIn("matched_exponent_ols", result)

    def test_larger_population_uses_all_completed_artifacts(self) -> None:
        result = compute_exponent(8000, 0.05, n_boot=200)
        self.assertTrue(result["complete"])
        self.assertEqual(result["n_artifacts"], 8)
        self.assertEqual(result["n_fit_legs"], 7)
        self.assertEqual(result["missing_speeds"], [])
        self.assertIn("matched_exponent_ols", result)


if __name__ == "__main__":
    unittest.main()
