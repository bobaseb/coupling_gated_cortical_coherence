"""Gates on the occupancy-weighted noise-floor test of a carrier (U36)."""

import math
import time
import unittest

import numpy as np

import unity_occupancy as uo
from unity_estimates import FLUCTUATION_TV, normal_cdf

GRID = uo.Grid(low=-6.0, step=0.1)
MEMBRANE = uo.Membrane(tau_ms=10.0, mean=-1.5, reset=-1.5, refractory_ms=2.0)
DT_MS = 0.2


class FirstPassageTest(unittest.TestCase):
    def test_the_law_of_the_next_content_is_a_probability(self) -> None:
        law = uo.first_passage_law(GRID, MEMBRANE, start=-1.0, window_ms=10.0, dt_ms=DT_MS)
        self.assertAlmostEqual(float(law.sum()), 1.0, places=9)
        self.assertTrue(np.all(law >= 0.0))

    def test_no_change_moves_nothing(self) -> None:
        self.assertEqual(uo.response(GRID, MEMBRANE, -1.0, 0.0, 10.0, DT_MS), 0.0)

    def test_a_larger_change_toward_threshold_moves_more(self) -> None:
        small = uo.response(GRID, MEMBRANE, -3.0, 1.0, 10.0, DT_MS)
        large = uo.response(GRID, MEMBRANE, -3.0, 2.0, 10.0, DT_MS)
        self.assertGreater(large, small)
        self.assertGreater(small, 0.0)

    def test_far_below_threshold_a_short_window_barely_responds(self) -> None:
        self.assertLess(uo.response(GRID, MEMBRANE, -5.5, 1.0, 2.0, DT_MS), 1e-3)

    def test_coarsening_the_content_never_raises_the_response(self) -> None:
        fine = uo.response(GRID, MEMBRANE, -1.5, 1.0, 10.0, DT_MS)
        for period in (1.0, 5.0, 10.0):
            latched = uo.response(GRID, MEMBRANE, -1.5, 1.0, 10.0, DT_MS, period_ms=period)
            self.assertLessEqual(latched, fine + 1e-12)

    def test_a_latch_as_long_as_the_window_reads_one_bit(self) -> None:
        law = uo.first_passage_law(GRID, MEMBRANE, -1.0, 10.0, DT_MS)
        self.assertEqual(uo.latch(law, DT_MS, 10.0).size, 2)


class OccupancyTest(unittest.TestCase):
    def test_the_stationary_law_is_a_probability(self) -> None:
        density, refractory, _ = uo.stationary(GRID, MEMBRANE, DT_MS)
        self.assertAlmostEqual(float(density.sum()) + refractory, 1.0, places=9)

    def test_the_mean_is_calibrated_to_the_declared_rate(self) -> None:
        membrane = uo.calibrate(GRID, 10.0, 2.0, rate_hz=3.0, dt_ms=DT_MS)
        _, _, rate = uo.stationary(GRID, membrane, DT_MS)
        self.assertAlmostEqual(rate, 3.0, delta=0.03)

    def test_a_higher_rate_sits_closer_to_threshold(self) -> None:
        low = uo.calibrate(GRID, 10.0, 2.0, rate_hz=1.0, dt_ms=DT_MS)
        high = uo.calibrate(GRID, 10.0, 2.0, rate_hz=8.0, dt_ms=DT_MS)
        self.assertGreater(high.mean, low.mean)


class BitTest(unittest.TestCase):
    def test_a_bit_moves_by_the_mass_its_noise_carries_across_the_edge(self) -> None:
        self.assertAlmostEqual(uo.bit_response(2.0, 1.0), normal_cdf(2.0) - normal_cdf(1.0))
        self.assertAlmostEqual(uo.bit_response(2.0, -1.0), normal_cdf(3.0) - normal_cdf(2.0))

    def test_no_bit_state_exceeds_the_fluctuation(self) -> None:
        best = max(uo.bit_response(x / 100, 1.0) for x in range(-300, 300))
        self.assertLessEqual(best, FLUCTUATION_TV + 1e-12)

    def test_a_wide_margin_leaves_no_state_passing(self) -> None:
        self.assertEqual(uo.bit_summary(margin=506.0)["pass_fraction"], 0.0)
        self.assertLess(uo.bit_summary(margin=506.0)["log10_max_response"], -1000.0)


class SummaryTest(unittest.TestCase):
    def test_every_pass_fraction_is_a_fraction(self) -> None:
        row = uo.neuron_summary(GRID, uo.NeuronConfig(10.0, 3.0, 10.0), DT_MS, (1.0, 10.0))
        hits = [h for per in row["window_hit_probability"].values() for h in per.values()]
        for value in (row["pass_fraction"], *row["latched_pass_fraction"].values(), *hits):
            self.assertGreaterEqual(value, 0.0)
            self.assertLessEqual(value, 1.0)

    def test_a_carrier_supplying_less_of_the_noise_passes_less_often(self) -> None:
        row = uo.neuron_summary(GRID, uo.NeuronConfig(20.0, 8.0, 10.0), DT_MS, ())
        by_scale = row["pass_fraction_by_scale"]
        self.assertEqual(by_scale["1"], row["pass_fraction"])
        self.assertLessEqual(by_scale["0.25"], by_scale["0.5"])
        self.assertLessEqual(by_scale["0.5"], by_scale["1"])
        self.assertGreater(by_scale["1"], 0.0)

    def test_more_independent_carriers_link_more_often(self) -> None:
        self.assertEqual(uo.link_probability(0.0, 1000), 0.0)
        self.assertAlmostEqual(uo.link_probability(0.5, 2), 0.75)
        self.assertLess(uo.link_probability(0.01, 10), uo.link_probability(0.01, 100))

    def test_a_carrier_visits_passing_states_more_often_in_a_longer_window(self) -> None:
        density, _, _ = uo.stationary(GRID, MEMBRANE, DT_MS)
        table = uo.laws(GRID, MEMBRANE, 10.0, DT_MS)
        passing = uo.passing_states(table, GRID, 1.0)
        at_once = float(density @ passing)
        short = uo.hit_probability(GRID, MEMBRANE, passing, 20.0, DT_MS)
        long = uo.hit_probability(GRID, MEMBRANE, passing, 200.0, DT_MS)
        self.assertGreater(at_once, 0.0)
        self.assertGreaterEqual(short, at_once)
        self.assertGreater(long, short)
        self.assertLessEqual(long, 1.0)

    def test_no_passing_state_is_never_visited(self) -> None:
        nowhere = np.zeros(GRID.nodes.size, dtype=bool)
        self.assertEqual(uo.hit_probability(GRID, MEMBRANE, nowhere, 200.0, DT_MS), 0.0)

    def test_the_summary_is_deterministic_and_fast(self) -> None:
        start = time.perf_counter()
        config = uo.NeuronConfig(10.0, 3.0, 10.0)
        first = uo.neuron_summary(GRID, config, DT_MS, (5.0,))
        second = uo.neuron_summary(GRID, config, DT_MS, (5.0,))
        self.assertEqual(first, second)
        self.assertLess(time.perf_counter() - start, 30.0)
        self.assertTrue(math.isfinite(first["mean_distance"]))


if __name__ == "__main__":
    unittest.main()
