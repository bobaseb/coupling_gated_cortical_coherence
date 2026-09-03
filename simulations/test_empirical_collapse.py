import unittest

import numpy as np

from empirical_collapse import compute_window_sensitivity


class WindowSensitivityTest(unittest.TestCase):
    def test_reports_each_requested_window_with_enough_pooled_samples(self) -> None:
        phase = np.zeros((62, 500), dtype=float)

        rows = compute_window_sensitivity(phase, fs=5000.0, windows_ms=(5, 20, 100))

        self.assertEqual([row.window_ms for row in rows], [5, 20, 100])
        self.assertTrue(all(row.pooled_samples >= 100 for row in rows))
        self.assertTrue(all(np.isfinite(row.mean_residual) for row in rows))


if __name__ == "__main__":
    unittest.main()
