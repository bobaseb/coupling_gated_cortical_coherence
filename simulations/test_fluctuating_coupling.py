import unittest
from typing import cast

import numpy as np

import fluctuating_coupling as fc
from quasistatic_error import stationary_order


CONFIG = fc.NoiseConfig(n_harmonics=10, replicas=4, min_horizon=120.0, horizon_factor=20.0)


class ProcessTest(unittest.TestCase):
    def test_the_telegraph_stays_on_its_two_declared_levels(self) -> None:
        drive = fc.Drive("telegraph", 2.0, 0.6, 1.0)
        rng = np.random.default_rng(0)
        coupling = fc.initial_coupling(drive, CONFIG, rng)
        for _ in range(200):
            coupling = fc.step_coupling(coupling, drive, 0.05, rng)
            self.assertTrue(np.all(np.isin(np.round(coupling, 12), (1.4, 2.6))))

    def test_both_processes_hold_their_declared_mean_and_spread(self) -> None:
        # The statistic under test is the mean, so a process whose realised mean
        # drifts would make every comparison below meaningless.
        rng = np.random.default_rng(7)
        for process, tolerance in (("telegraph", 0.05), ("ornstein_uhlenbeck", 0.05)):
            drive = fc.Drive(process, 2.2, 0.5, 0.5)
            coupling = fc.initial_coupling(drive, fc.NoiseConfig(replicas=4000), rng)
            samples = [coupling]
            for _ in range(400):
                coupling = fc.step_coupling(coupling, drive, 0.05, rng)
                samples.append(coupling)
            stacked = np.concatenate(samples)
            self.assertAlmostEqual(float(np.mean(stacked)), 2.2, delta=tolerance)
            self.assertAlmostEqual(float(np.std(stacked)), 0.5, delta=tolerance)

    def test_the_transition_is_exact_in_the_step_size(self) -> None:
        # Both updates use the exact stationary transition over `dt`, so the
        # correlation time is a declared parameter and not a by-product of `dt`.
        rng = np.random.default_rng(3)
        drive = fc.Drive("ornstein_uhlenbeck", 0.0, 1.0, 2.0)
        coupling = np.zeros(20000)
        for _ in range(1):
            coupling = fc.step_coupling(coupling, drive, 2.0, rng)
        self.assertAlmostEqual(float(np.std(coupling)), np.sqrt(1 - np.exp(-2.0)), delta=0.02)

    def test_an_unknown_process_is_refused(self) -> None:
        rng = np.random.default_rng(0)
        with self.assertRaises(ValueError):
            fc.initial_coupling(fc.Drive("brownian", 2.0, 0.5, 1.0), CONFIG, rng)


class SubstitutionTest(unittest.TestCase):
    def test_the_quasi_static_average_of_a_telegraph_is_its_two_branch_values(self) -> None:
        drive = fc.Drive("telegraph", 2.4, 1.0, 1.0)
        expected = 0.5 * (stationary_order(1.4, 1.0) + stationary_order(3.4, 1.0))
        self.assertAlmostEqual(fc.quasi_static_average(drive, 1.0), expected)

    def test_a_subcritical_mean_can_have_a_positive_quasi_static_average(self) -> None:
        # `r_ss` is zero below threshold and leaves the axis with infinite
        # slope, so it is convex there and the two substitutions disagree about
        # whether there is any order at all. That disagreement is the point.
        drive = fc.Drive("telegraph", 1.8, 1.0, 1.0)
        self.assertEqual(stationary_order(drive.mean, 1.0), 0.0)
        self.assertGreater(fc.quasi_static_average(drive, 1.0), 0.2)

    def test_a_gaussian_coupling_far_below_threshold_averages_to_nearly_zero(self) -> None:
        drive = fc.Drive("ornstein_uhlenbeck", 0.5, 0.2, 1.0)
        self.assertLess(fc.quasi_static_average(drive, 1.0), 1e-6)

    def test_the_crossing_flag_matches_the_declared_band(self) -> None:
        self.assertTrue(fc.crosses_threshold(fc.Drive("telegraph", 1.8, 1.0, 1.0), CONFIG))
        self.assertFalse(fc.crosses_threshold(fc.Drive("telegraph", 2.4, 0.25, 1.0), CONFIG))
        self.assertTrue(
            fc.crosses_threshold(fc.Drive("ornstein_uhlenbeck", 2.4, 0.25, 1.0), CONFIG)
        )


class DriveTest(unittest.TestCase):
    def test_a_fast_coupling_is_the_mean_coupling(self) -> None:
        drive = fc.Drive("telegraph", 2.4, 0.25, 0.01)
        run = fc.run_drive(drive, CONFIG)
        self.assertAlmostEqual(run.measured_order, run.mean_substitution, delta=0.02)
        self.assertGreater(
            abs(run.measured_order - run.quasi_static_average),
            abs(run.measured_order - run.mean_substitution),
        )

    def test_a_slow_non_crossing_coupling_is_the_quasi_static_average(self) -> None:
        drive = fc.Drive("telegraph", 2.4, 0.25, 20.0)
        run = fc.run_drive(drive, fc.NoiseConfig(n_harmonics=10, replicas=4, horizon_factor=40.0))
        self.assertLess(
            abs(run.measured_order - run.quasi_static_average),
            abs(run.measured_order - run.mean_substitution),
        )

    def test_a_subcritical_mean_with_supercritical_excursions_orders(self) -> None:
        # The rejection the module exists for: the mean coupling says exactly
        # zero and the run is not at zero.
        # The replica spread on a crossing drive is as large as its mean, so
        # this reads the production ensemble rather than the small one the other
        # cases use.
        drive = fc.Drive("telegraph", 2.0, 1.0, 3.0)
        run = fc.run_drive(drive, fc.NoiseConfig(n_harmonics=10))
        self.assertEqual(run.mean_substitution, 0.0)
        self.assertGreater(run.measured_order, fc.NoiseConfig().seed_order)

    def test_a_constant_coupling_reproduces_its_own_branch(self) -> None:
        # The positive control: zero amplitude is a constant coupling, and the
        # driven integrator must then land on the stationary branch it is being
        # compared against.
        drive = fc.Drive("telegraph", 3.0, 0.0, 1.0)
        run = fc.run_drive(drive, CONFIG)
        self.assertAlmostEqual(run.measured_order, run.mean_substitution, delta=1e-3)

    def test_the_horizon_is_many_correlation_times(self) -> None:
        self.assertEqual(fc.horizon(fc.Drive("telegraph", 2.0, 0.5, 0.01), CONFIG), 120.0)
        self.assertEqual(fc.horizon(fc.Drive("telegraph", 2.0, 0.5, 10.0), CONFIG), 200.0)


class SweepTest(unittest.TestCase):
    def test_the_drive_grid_is_the_declared_product(self) -> None:
        drives = fc.build_drives()
        self.assertEqual(
            len(drives),
            len(fc.PROCESSES)
            * len(fc.AMPLITUDES)
            * len(fc.CORRELATION_TIMES)
            * len(fc.MEAN_COUPLINGS),
        )
        self.assertEqual(
            len({(d.process, d.mean, d.amplitude, d.correlation_time) for d in drives}), len(drives)
        )

    def test_the_summary_records_both_limits_and_the_rejection(self) -> None:
        import tempfile
        from pathlib import Path

        drives = [
            fc.Drive(process, mean, 0.25, tau)
            for process in fc.PROCESSES
            for tau in (min(fc.CORRELATION_TIMES), max(fc.CORRELATION_TIMES))
            for mean in (2.0, 2.4)
        ]
        with tempfile.TemporaryDirectory() as directory:
            summary = fc.run_sweep(CONFIG, drives, Path(directory))
            self.assertTrue((Path(directory) / "fluctuating_coupling_summary.json").exists())
        for key in ("fast_limit", "slow_limit", "crossover", "mean_substitution_rejection"):
            self.assertIn(key, summary)
        self.assertEqual(len(cast(list[object], summary["drives"])), len(drives))


if __name__ == "__main__":
    unittest.main()
