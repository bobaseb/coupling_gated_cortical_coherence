"""Checks for diagnostics used to choose a recorded-membrane twin."""

import unittest

import numpy as np

from unity_recording_diagnostics import fast_shape, slow_histogram, threshold_spread


class DiagnosticTest(unittest.TestCase):
    def test_positive_events_raise_skew_and_upper_tail(self) -> None:
        rng = np.random.default_rng(4)
        gaussian = rng.normal(size=100_000)
        jumps = gaussian + rng.exponential(3, size=gaussian.size) * (
            rng.random(gaussian.size) < 0.03
        )
        base = fast_shape(gaussian)
        shot = fast_shape(jumps)
        self.assertGreater(shot["skew"], base["skew"] + 0.4)
        self.assertGreater(shot["upper_tail_ratio"], base["upper_tail_ratio"] + 1)

    def test_threshold_spread_uses_each_spike(self) -> None:
        self.assertAlmostEqual(threshold_spread(np.array([-0.05, -0.049, -0.051])), 1.0)

    def test_slow_histogram_keeps_the_empirical_level_weights(self) -> None:
        result = slow_histogram(np.array([-0.050, -0.050, -0.049]))
        self.assertEqual(result, [[-50.0, 2], [-49.0, 1]])


if __name__ == "__main__":
    unittest.main()
