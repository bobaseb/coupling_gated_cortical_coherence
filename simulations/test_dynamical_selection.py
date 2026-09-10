import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

import numpy as np

from dynamical_selection import (
    SelectionConfig,
    dt_control_configs,
    estimate_growth_rate,
    mean_field_drift,
    run_experiment,
    simulate_selection,
    theoretical_growth_rate,
)


class DynamicalSelectionTest(unittest.TestCase):
    def test_mean_field_reduction_matches_explicit_pair_sum(self) -> None:
        phases = np.array([[0.1, 0.7, -1.2, 2.4], [-2.0, -0.3, 0.8, 1.7]])
        coupling = 2.3

        reduced = mean_field_drift(phases, coupling)
        explicit = np.empty_like(phases)
        for replica in range(phases.shape[0]):
            for oscillator in range(phases.shape[1]):
                explicit[replica, oscillator] = coupling * np.mean(
                    np.sin(phases[replica] - phases[replica, oscillator])
                )

        np.testing.assert_allclose(reduced, explicit, atol=1e-14)

    def test_seeded_smoke_run_is_reproducible_and_decimated(self) -> None:
        config = SelectionConfig(
            n_oscillators=32,
            n_replicas=4,
            diffusion=0.2,
            coupling=0.6,
            dt=0.02,
            steps=20,
            sample_every=4,
            seed=20260904,
        )

        first = simulate_selection(config)
        second = simulate_selection(config)

        np.testing.assert_array_equal(first.order_mean, second.order_mean)
        np.testing.assert_array_equal(first.order_std, second.order_std)
        self.assertEqual(first.time.shape, (6,))
        self.assertAlmostEqual(first.time[-1], 0.4)
        self.assertFalse(hasattr(first, "phase_history"))
        self.assertFalse(hasattr(first, "order_replicas"))
        self.assertAlmostEqual(first.finite_size_floor, 1.0 / np.sqrt(32))

    def test_theoretical_growth_rate_has_exact_slope_and_threshold(self) -> None:
        coupling = np.array([1.8, 2.0, 2.2, 2.8])

        rates = theoretical_growth_rate(coupling, diffusion=1.0)

        np.testing.assert_allclose(rates, [-0.1, 0.0, 0.1, 0.4])

    def test_log_linear_fit_recovers_known_early_growth_rate(self) -> None:
        time = np.linspace(0.0, 8.0, 161)
        order = 0.025 * np.exp(0.18 * time)

        fit = estimate_growth_rate(time, order, lower_bound=0.0, upper_bound=0.3)

        self.assertAlmostEqual(fit.rate, 0.18, places=12)
        self.assertAlmostEqual(fit.intercept, np.log(0.025), places=12)
        self.assertGreater(fit.sample_count, 20)
        self.assertAlmostEqual(fit.r_squared, 1.0, places=12)

    def test_growth_fit_rejects_a_window_with_too_few_points(self) -> None:
        time = np.array([0.0, 1.0, 2.0])
        order = np.array([0.02, 0.03, 0.4])

        with self.assertRaisesRegex(ValueError, "at least three"):
            estimate_growth_rate(time, order, lower_bound=0.01, upper_bound=0.3)

    def test_invalid_configuration_is_rejected(self) -> None:
        config = SelectionConfig(dt=0.0)

        with self.assertRaisesRegex(ValueError, "positive"):
            simulate_selection(config)

    def test_growth_window_excludes_a_later_re_entry(self) -> None:
        time = np.linspace(0.0, 10.0, 11)
        order = np.array([0.02, 0.05, 0.10, 0.20, 0.40, 0.60, 0.40, 0.20, 0.10, 0.20, 0.40])

        fit = estimate_growth_rate(time, order, lower_bound=0.03, upper_bound=0.5)

        self.assertEqual(fit.sample_count, 4)

    def test_dt_control_refines_the_base_step_at_fixed_duration(self) -> None:
        base = SelectionConfig(dt=0.02, steps=300, sample_every=5)

        configs = dt_control_configs(base, coupling=2.8)

        self.assertEqual([config.dt for config in configs], [0.01, 0.005])
        for config in configs:
            self.assertEqual(config.coupling, 2.8)
            self.assertAlmostEqual(config.steps * config.dt, base.steps * base.dt)
            self.assertAlmostEqual(config.sample_every * config.dt, base.sample_every * base.dt)

    def test_dt_control_series_opens_at_the_production_step(self) -> None:
        base = SelectionConfig(
            n_oscillators=1024, n_replicas=8, dt=0.02, steps=400, sample_every=5, seed=42
        )
        regimes = np.array([1.6, 2.0, 2.8])
        growth = np.array([2.8, 3.0])

        with TemporaryDirectory() as directory:
            summary = run_experiment(base, regimes, growth, Path(directory))
            saved = sorted(path.name for path in Path(directory).glob("selection_dt_control*.npz"))

        self.assertEqual(summary.dt_control_coupling, 2.8)
        self.assertEqual(summary.dt_control_dt, [0.02, 0.01, 0.005])
        self.assertEqual(summary.dt_control_order[0], summary.regime_final_order[2])
        self.assertEqual(
            saved, ["selection_dt_control_dt0.005.npz", "selection_dt_control_dt0.01.npz"]
        )


if __name__ == "__main__":
    unittest.main()
