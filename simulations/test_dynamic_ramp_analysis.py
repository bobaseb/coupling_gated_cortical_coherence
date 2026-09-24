import unittest

import numpy as np

from dynamic_ramp_analysis import (
    collapse_deviation,
    fit_onset_exponent,
    fit_power_law,
    replica_escape_couplings,
    split_span_exponents,
)


class DynamicRampAnalysisTest(unittest.TestCase):
    def test_power_law_fit_recovers_known_exponent(self) -> None:
        x = np.geomspace(1e-4, 1e-1, 20)
        y = 3.0 * x**0.5

        fit = fit_power_law(x, y)

        self.assertAlmostEqual(fit.exponent, 0.5, places=12)
        self.assertAlmostEqual(fit.prefactor, 3.0, places=12)

    def test_an_exact_power_law_has_a_degenerate_slope_interval(self) -> None:
        """No scatter, no interval width: the interval measures the scatter."""
        x = np.geomspace(1e-4, 1e-1, 20)

        fit = fit_power_law(x, 3.0 * x**0.5)

        self.assertAlmostEqual(fit.exponent_low, 0.5, places=8)
        self.assertAlmostEqual(fit.exponent_high, 0.5, places=8)

    def test_the_slope_interval_brackets_the_slope_and_widens_with_scatter(self) -> None:
        x = np.geomspace(1e-4, 1e-1, 8)
        noise = np.array([1.05, 0.95, 1.04, 0.96, 1.03, 0.97, 1.02, 0.98])

        tight = fit_power_law(x, 3.0 * x**0.5 * (1.0 + (noise - 1.0) / 10.0))
        loose = fit_power_law(x, 3.0 * x**0.5 * noise)

        for fit in (tight, loose):
            self.assertLess(fit.exponent_low, fit.exponent)
            self.assertLess(fit.exponent, fit.exponent_high)
        self.assertLess(
            tight.exponent_high - tight.exponent_low,
            loose.exponent_high - loose.exponent_low,
        )

    def test_two_points_leave_no_residual_degree_of_freedom(self) -> None:
        x = np.array([1e-3, 1e-1])

        fit = fit_power_law(x, 3.0 * x**0.5)

        self.assertTrue(np.isnan(fit.exponent_low))
        self.assertTrue(np.isnan(fit.exponent_high))

    def test_split_span_agrees_on_an_exact_law_and_separates_a_drifting_one(self) -> None:
        x = np.geomspace(1e-4, 1e-1, 8)

        fast, slow = split_span_exponents(x, 3.0 * x**0.5)
        self.assertAlmostEqual(fast.exponent, slow.exponent, places=8)

        # A curved trace in log-log: the halves must not agree.
        curved = np.exp(0.5 * np.log(x) + 0.05 * np.log(x) ** 2)
        fast, slow = split_span_exponents(x, curved)
        self.assertGreater(abs(fast.exponent - slow.exponent), 0.1)

    def test_split_span_refuses_a_sweep_it_cannot_halve(self) -> None:
        x = np.array([1e-3, 1e-2, 1e-1])
        with self.assertRaises(ValueError):
            split_span_exponents(x, 3.0 * x**0.5)

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

    def test_onset_fit_records_the_window_it_realised(self) -> None:
        coupling = np.linspace(2.01, 2.4, 80)
        order = 0.8 * np.sqrt(coupling - 2.0)
        selected = (order >= 0.1) & (order <= 0.4)

        fit = fit_onset_exponent(coupling, order, critical_coupling=2.0)

        self.assertEqual(fit.samples, int(selected.sum()))
        self.assertAlmostEqual(fit.order_min, float(order[selected].min()))
        self.assertAlmostEqual(fit.order_max, float(order[selected].max()))
        self.assertAlmostEqual(fit.excess_min, float(coupling[selected].min()) - 2.0)
        self.assertAlmostEqual(fit.excess_max, float(coupling[selected].max()) - 2.0)

    def test_onset_fit_flags_a_shift_returned_at_its_lower_bound(self) -> None:
        coupling = np.linspace(2.01, 2.6, 120)

        at_threshold = fit_onset_exponent(coupling, 0.8 * np.sqrt(coupling - 2.0))
        past_threshold = fit_onset_exponent(
            coupling, 0.8 * np.sqrt(np.maximum(coupling - 2.2, 0.0))
        )

        self.assertTrue(at_threshold.onset_pinned)
        self.assertFalse(past_threshold.onset_pinned)


class BootstrapTest(unittest.TestCase):
    def test_bootstrap_records_zero_delay_resamples(self) -> None:
        from dynamic_ramp_analysis import bootstrap_delay_exponent

        speeds = np.array([0.1, 0.01, 0.001])
        replica_delays = [np.array([0.0, 0.0, 0.0, v]) for v in speeds]
        result = bootstrap_delay_exponent(speeds, replica_delays, n_boot=100, seed=7)
        self.assertGreater(result.n_invalid, 0)
        self.assertTrue(np.isfinite(result.ci_low))

    def test_bootstrap_recovers_known_exponent_from_exact_data(self) -> None:
        from dynamic_ramp_analysis import bootstrap_delay_exponent

        speeds = np.geomspace(1e-4, 1e-1, 6)
        replica_delays = [np.full(32, 3.0 * v**0.5) for v in speeds]
        result = bootstrap_delay_exponent(speeds, replica_delays, n_boot=100)
        self.assertAlmostEqual(result.exponent, 0.5, places=8)
        self.assertAlmostEqual(result.ci_low, 0.5, places=8)
        self.assertAlmostEqual(result.ci_high, 0.5, places=8)

    def test_bootstrap_ci_widens_with_replica_variability(self) -> None:
        from dynamic_ramp_analysis import bootstrap_delay_exponent

        speeds = np.geomspace(1e-4, 1e-1, 6)
        rng = np.random.default_rng(123)

        tight_delays = []
        loose_delays = []
        for v in speeds:
            base = 3.0 * v**0.5
            tight_delays.append(base * rng.uniform(0.99, 1.01, size=32))
            loose_delays.append(base * rng.uniform(0.8, 1.2, size=32))

        tight = bootstrap_delay_exponent(speeds, tight_delays, n_boot=1000)
        loose = bootstrap_delay_exponent(speeds, loose_delays, n_boot=1000)

        tight_width = tight.ci_high - tight.ci_low
        loose_width = loose.ci_high - loose.ci_low
        self.assertLess(tight_width, loose_width)

    def test_bootstrap_p_above_is_one_for_exponent_well_below_threshold(self) -> None:
        from dynamic_ramp_analysis import bootstrap_delay_exponent

        speeds = np.geomspace(1e-4, 1e-1, 6)
        rng = np.random.default_rng(456)
        # Exponent is 0.3
        replica_delays = [3.0 * v**0.3 * rng.uniform(0.9, 1.1, size=32) for v in speeds]
        result = bootstrap_delay_exponent(speeds, replica_delays, n_boot=500, threshold=0.5)
        self.assertEqual(result.p_above, 0.0)

    def test_bootstrap_rejects_mismatched_inputs(self) -> None:
        from dynamic_ramp_analysis import bootstrap_delay_exponent

        speeds = np.geomspace(1e-4, 1e-1, 6)
        replica_delays = [np.full(32, 3.0 * v**0.5) for v in speeds[:5]]
        with self.assertRaises(ValueError):
            bootstrap_delay_exponent(speeds, replica_delays)


if __name__ == "__main__":
    unittest.main()
