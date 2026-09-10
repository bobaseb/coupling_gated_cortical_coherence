import math
import unittest

import numpy as np

from dynamic_ramp_report import SizeMetrics, _size_metrics, adiabatic_onset_exponent


class AdiabaticReferenceTest(unittest.TestCase):
    def test_estimator_on_the_stationary_branch_falls_short_of_one_half(self) -> None:
        coupling = np.linspace(1.5, 2.5, 101)

        reference = adiabatic_onset_exponent(coupling)

        self.assertLess(reference, 0.5)
        self.assertAlmostEqual(reference, 0.443, places=3)


class SizeControlTest(unittest.TestCase):
    def test_scaled_delay_divides_by_the_predicted_size_dependence(self) -> None:
        metrics = SizeMetrics(
            n_oscillators=8000,
            delay_mean=0.2341,
            delay_error=0.0,
            precritical_order_max=0.1,
        )

        self.assertAlmostEqual(metrics.scaled_delay, 0.2341 / math.sqrt(math.log(8000)))

    def test_smallest_population_reaches_the_escape_level_before_threshold(self) -> None:
        sizes = _size_metrics()

        self.assertEqual([item.n_oscillators for item in sizes], [500, 2000, 8000])
        self.assertGreater(sizes[0].precritical_order_max, 0.2)
        self.assertLess(sizes[-1].precritical_order_max, 0.2)


if __name__ == "__main__":
    unittest.main()
