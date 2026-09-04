import unittest

import numpy as np

from dynamic_ramp_analysis import (
    collapse_deviation,
    fit_onset_exponent,
    fit_power_law,
    replica_escape_couplings,
)


class DynamicRampAnalysisTest(unittest.TestCase):
    def test_power_law_fit_recovers_known_exponent(self) -> None:
        x = np.geomspace(1e-4, 1e-1, 20)
        y = 3.0 * x**0.5

        fit = fit_power_law(x, y)

        self.assertAlmostEqual(fit.exponent, 0.5, places=12)
        self.assertAlmostEqual(fit.prefactor, 3.0, places=12)

    def test_escape_requires_sustained_crossing_of_fixed_order_level(self) -> None:
        coupling = np.array([2.0, 2.1, 2.2, 2.3, 2.4])
        order = np.array(
            [
                [0.1, 0.1],
                [0.21, 0.1],
                [0.19, 0.22],
                [0.23, 0.24],
                [0.25, 0.26],
            ]
        )

        escape = replica_escape_couplings(coupling, order, level=0.2, sustain=2)

        np.testing.assert_allclose(escape, np.array([2.3, 2.2]))

    def test_escape_ignores_precritical_finite_size_crossings(self) -> None:
        coupling = np.array([1.8, 1.9, 2.0, 2.1, 2.2])
        order = np.array([[0.3], [0.3], [0.1], [0.21], [0.22]])

        escape = replica_escape_couplings(coupling, order, level=0.2, sustain=2)

        np.testing.assert_allclose(escape, np.array([2.1]))

    def test_collapse_deviation_is_root_mean_square_residual(self) -> None:
        concentration = np.array([0.0, 0.0, 0.0])
        order = np.array([0.0, 0.1, 0.2])

        deviation = collapse_deviation(concentration, order)

        self.assertAlmostEqual(deviation, np.sqrt(0.05 / 3.0))

    def test_onset_fit_recovers_shifted_square_root(self) -> None:
        coupling = np.linspace(2.01, 2.4, 80)
        order = 0.8 * np.sqrt(coupling - 2.0)

        fit = fit_onset_exponent(coupling, order, critical_coupling=2.0)

        self.assertAlmostEqual(fit.exponent, 0.5, places=6)
        self.assertAlmostEqual(fit.onset_coupling, 2.0, places=6)


if __name__ == "__main__":
    unittest.main()
