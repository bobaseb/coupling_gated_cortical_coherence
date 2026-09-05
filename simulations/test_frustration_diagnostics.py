import unittest

import numpy as np

from frustration_diagnostics import order_statistics
from frustration_summary import aggregate, read_json
from geometric_frustration import ROOT


class DiagnosticsTest(unittest.TestCase):
    def test_tail_statistics_use_order_squared_and_preserve_size_scaling(self) -> None:
        leg = {"time": np.array([0.0, 1.0, 2.0, 3.0]), "order": np.array([1.0, 1.0, 0.1, 0.2])}
        mean, scaled_square = order_statistics(leg, 100)
        self.assertAlmostEqual(mean, 0.15)
        self.assertAlmostEqual(scaled_square, 2.5)

    def test_aggregate_summary_has_no_drift_from_saved_seed_results(self) -> None:
        self.assertEqual(aggregate(ROOT), read_json(ROOT / "followup_summary.json"))


if __name__ == "__main__":
    unittest.main()
