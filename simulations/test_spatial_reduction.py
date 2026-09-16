import unittest

import numpy as np

import spatial_reduction as reduction
from spatial_kernel import build_kernel


CONFIG = reduction.ReductionConfig(side=16, total_time=4.0, samples=5)


class AggregationRuleTest(unittest.TestCase):
    def test_the_reduced_coupling_is_the_row_sum_of_the_implied_matrix(self) -> None:
        # The kernel is stored as a displacement array and used through a
        # circular convolution, so this pins the reading: entry (dx, dy) is the
        # coupling between any pair of sites that far apart on the torus, and
        # the row sum of the matrix that array stands for is its total.
        side = 6
        kernel = build_kernel(side, 1.5, 3.0)
        matrix = np.array(
            [
                [kernel[(k - i) % side, (b - a) % side] for k in range(side) for b in range(side)]
                for i in range(side)
                for a in range(side)
            ]
        )
        self.assertAlmostEqual(reduction.reduced_coupling(kernel), 3.0)
        self.assertTrue(np.allclose(matrix.sum(axis=1), 3.0))
        self.assertTrue(np.allclose(np.diag(matrix), 0.0))

    def test_row_normalized_excludes_double_counting(self) -> None:
        # The population within a decay length is already inside the row sum, so
        # the reduced coupling does not move when the decay length or the sheet
        # size does. Every decay dependence measured downstream is therefore
        # error of the reduction, not a change in the quantity reduced.
        for decay in (0.05, 0.1, 0.2, 0.4):
            kernel = reduction.build_decay_kernel(CONFIG, decay, 2.5)
            self.assertAlmostEqual(reduction.reduced_coupling(kernel), 2.5)
        finer = reduction.ReductionConfig(side=32)
        self.assertAlmostEqual(
            reduction.reduced_coupling(reduction.build_decay_kernel(finer, 0.2, 2.5)), 2.5
        )

    def test_the_neighbour_count_times_the_peak_is_the_row_sum(self) -> None:
        kernel = reduction.build_decay_kernel(CONFIG, 0.2, 2.0)
        peak = float(np.max(kernel))
        self.assertAlmostEqual(reduction.effective_neighbours(kernel) * peak, 2.0)

    def test_a_shorter_decay_reaches_fewer_neighbours(self) -> None:
        near = reduction.effective_neighbours(reduction.build_decay_kernel(CONFIG, 0.05, 1.0))
        far = reduction.effective_neighbours(reduction.build_decay_kernel(CONFIG, 0.4, 1.0))
        self.assertLess(near, far)

    def test_the_uniform_kernel_is_the_scalar_model_at_the_same_row_sum(self) -> None:
        kernel = reduction.build_uniform_kernel(16, 1.5)
        self.assertAlmostEqual(reduction.reduced_coupling(kernel), 1.5)
        self.assertEqual(kernel[0, 0], 0.0)
        self.assertAlmostEqual(reduction.effective_neighbours(kernel), 16 * 16 - 1)

    def test_a_kernel_with_no_positive_entry_has_no_neighbour_count(self) -> None:
        with self.assertRaises(ValueError):
            reduction.effective_neighbours(np.zeros((4, 4)))


class ScheduleTest(unittest.TestCase):
    def test_the_step_is_capped_by_the_per_step_phase_advance(self) -> None:
        dt, steps = reduction._schedule(CONFIG, 20.0)
        self.assertLessEqual(dt * 20.0, CONFIG.max_phase_step + 1e-12)
        self.assertAlmostEqual(dt * steps, CONFIG.total_time, places=6)

    def test_a_weak_coupling_keeps_the_declared_step(self) -> None:
        dt, _ = reduction._schedule(CONFIG, 0.5)
        self.assertAlmostEqual(dt, CONFIG.max_dt)

    def test_a_negative_diffusion_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            reduction.steady_order(
                reduction.ReductionConfig(diffusion=-1.0),
                reduction.build_uniform_kernel(8, 1.0),
                1,
            )


class ThresholdTest(unittest.TestCase):
    def test_the_incoherent_floor_is_removed_from_the_squared_order(self) -> None:
        order = np.array([0.1, 0.5])
        excess = reduction.excess_order_squared(order, 100)
        self.assertAlmostEqual(excess[0], 0.0)
        self.assertAlmostEqual(excess[1], 0.25 - 0.01)

    def test_the_intercept_recovers_a_constructed_threshold(self) -> None:
        # r^2 - 1/N built exactly linear in K above 1.4 and flat below it.
        coupling = np.linspace(1.0, 3.0, 21)
        excess = np.clip(0.3 * (coupling - 1.4), 0.0, None)
        order = np.sqrt(excess + 1.0 / 256)
        located = reduction.threshold_location(coupling, order, 256)
        if located is None:
            self.fail("the constructed sweep has an ordered branch to extrapolate")
        self.assertAlmostEqual(located.estimate, 1.4, places=2)
        self.assertGreater(located.points_used, 2)
        self.assertLessEqual(located.low, located.estimate + 1e-9)
        self.assertGreaterEqual(located.high, located.estimate - 1e-9)

    def test_the_size_crossing_locates_a_constructed_threshold(self) -> None:
        # Scaled orders built to agree at 1.2 and to part in opposite directions
        # on either side of it, which is the finite-size signature the crossing
        # reads and the extrapolated intercept cannot.
        coupling = np.linspace(0.5, 2.0, 16)
        small, large = 256, 4096
        offset = coupling - 1.2
        order_large = (1.0 + offset / 2.0) / large**0.25
        order_small = (1.0 - offset / 2.0) / small**0.25
        crossing = reduction.crossing_threshold(coupling, order_small, small, order_large, large)
        if crossing is None:
            self.fail("the constructed scaled orders cross")
        self.assertAlmostEqual(crossing.estimate, 1.2, places=6)
        self.assertAlmostEqual(crossing.scaled_order, 1.0, places=6)
        self.assertEqual((crossing.small_sites, crossing.large_sites), (small, large))

    def test_scaled_orders_that_never_cross_report_no_threshold(self) -> None:
        coupling = np.linspace(0.5, 2.0, 8)
        order = np.full(coupling.size, 0.1)
        self.assertIsNone(reduction.crossing_threshold(coupling, order, 256, order / 2.0, 4096))

    def test_a_sweep_that_never_orders_reports_no_threshold(self) -> None:
        coupling = np.linspace(0.5, 2.0, 8)
        order = np.full(coupling.size, 1.0 / 16.0)
        self.assertIsNone(reduction.threshold_location(coupling, order, 256))


class ReferenceTest(unittest.TestCase):
    def test_the_self_consistency_branch_leaves_the_axis_at_twice_the_diffusion(self) -> None:
        reference = reduction.mean_field_reference(np.array([0.5, 1.0, 1.5, 3.0]), 0.5)
        self.assertEqual(reference[0], 0.0)
        self.assertEqual(reference[1], 0.0)
        self.assertGreater(reference[2], 0.0)
        self.assertGreater(reference[3], reference[2])

    def test_the_declared_threshold_is_the_one_the_module_tests(self) -> None:
        self.assertAlmostEqual(CONFIG.scalar_threshold, 2.0 * CONFIG.diffusion)


class IntegrationTest(unittest.TestCase):
    def test_strong_coupling_orders_the_sheet_and_weak_coupling_does_not(self) -> None:
        config = reduction.ReductionConfig(side=16, total_time=20.0, samples=10)
        weak = reduction.steady_order(config, reduction.build_uniform_kernel(16, 0.2), 1)
        strong = reduction.steady_order(config, reduction.build_uniform_kernel(16, 8.0), 1)
        self.assertLess(weak, 0.2)
        self.assertGreater(strong, 0.8)

    def test_the_production_grid_brackets_the_scalar_threshold(self) -> None:
        grid = reduction.production_couplings()
        self.assertLess(float(grid.min()), reduction.ReductionConfig().scalar_threshold)
        self.assertGreater(float(grid.max()), reduction.ReductionConfig().scalar_threshold)
        self.assertTrue(np.all(np.diff(grid) > 0.0))


if __name__ == "__main__":
    unittest.main()
