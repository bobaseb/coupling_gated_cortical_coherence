"""Gates on carriers that share part of their input (U47)."""

import time
import unittest

import numpy as np

import unity_correlated as uc
import unity_occupancy as uo

GRID = uo.Grid(low=-6.0, step=0.1)
MEMBRANE = uo.Membrane(tau_ms=10.0, mean=-1.5, reset=-1.5, refractory_ms=2.0)
DT_MS = 0.2


def _passing() -> np.ndarray:
    table = uo.laws(GRID, MEMBRANE, 10.0, DT_MS)
    return uo.passing_states(table, GRID, 1.0)


class SharedPathTest(unittest.TestCase):
    def test_a_shared_path_has_the_declared_variance(self) -> None:
        rng = np.random.default_rng(0)
        paths = uc.shared_paths(rng, 0.5, 10.0, DT_MS, 4000, 64)
        self.assertEqual(paths.shape, (4001, 64))
        self.assertAlmostEqual(float(paths.var()), 0.5, delta=0.05)

    def test_no_share_gives_no_path(self) -> None:
        paths = uc.shared_paths(np.random.default_rng(0), 0.0, 10.0, DT_MS, 10, 4)
        self.assertEqual(float(np.abs(paths).max()), 0.0)


class CorrelatedHitTest(unittest.TestCase):
    def test_no_share_reproduces_the_independent_carrier(self) -> None:
        passing = _passing()
        hits = uc.correlated_hits(GRID, MEMBRANE, passing, 0.0, (20.0,), DT_MS, 4, seed=1)
        alone = uo.hit_probability(GRID, MEMBRANE, passing, 20.0, DT_MS)
        self.assertTrue(np.allclose(hits["20"], alone, atol=1e-9))
        self.assertAlmostEqual(uc.pair_correlation(hits["20"]), 0.0)
        no_link = uc.no_link(hits["20"], 100)
        self.assertAlmostEqual(no_link["probability"], (1.0 - alone) ** 100)

    def test_the_marginal_carrier_is_unchanged(self) -> None:
        passing = _passing()
        alone = uo.hit_probability(GRID, MEMBRANE, passing, 20.0, DT_MS)
        hits = uc.correlated_hits(GRID, MEMBRANE, passing, 0.75, (20.0,), DT_MS, 400, seed=2)
        # About three standard errors over 400 paths.
        self.assertAlmostEqual(float(hits["20"].mean()), alone, delta=0.03)

    def test_sharing_input_makes_a_missing_link_more_likely(self) -> None:
        passing = _passing()
        misses = []
        for share in (0.0, 0.5, 0.9):
            hits = uc.correlated_hits(GRID, MEMBRANE, passing, share, (20.0,), DT_MS, 200, seed=3)
            misses.append(uc.no_link(hits["20"], 100)["probability"])
        self.assertLessEqual(misses[0], misses[1])
        self.assertLess(misses[1], misses[2])

    def test_shared_input_correlates_passing(self) -> None:
        passing = _passing()
        hits = uc.correlated_hits(GRID, MEMBRANE, passing, 0.9, (20.0,), DT_MS, 200, seed=4)
        self.assertGreater(uc.pair_correlation(hits["20"]), 0.05)

    def test_a_run_is_deterministic_under_its_seed_and_fast(self) -> None:
        passing = _passing()
        start = time.perf_counter()
        first = uc.correlated_hits(GRID, MEMBRANE, passing, 0.5, (20.0, 40.0), DT_MS, 64, seed=5)
        second = uc.correlated_hits(GRID, MEMBRANE, passing, 0.5, (20.0, 40.0), DT_MS, 64, seed=5)
        self.assertLess(time.perf_counter() - start, 30.0)
        for window in ("20", "40"):
            self.assertTrue(np.array_equal(first[window], second[window]))
        self.assertTrue(np.all(first["40"] >= first["20"]))


class SummaryTest(unittest.TestCase):
    def test_the_standard_error_shrinks_with_more_paths(self) -> None:
        rng = np.random.default_rng(6)
        few = uc.no_link(rng.uniform(size=16), 10)["standard_error"]
        many = uc.no_link(rng.uniform(size=1600), 10)["standard_error"]
        self.assertLess(many, few)

    def test_the_largest_tolerated_share_is_read_off_the_sweep(self) -> None:
        links = {"0": 0.99, "0.25": 0.95, "0.5": 0.85, "0.75": 0.5}
        self.assertEqual(uc.largest_share(links, 0.9), 0.25)
        self.assertIsNone(uc.largest_share({"0": 0.5}, 0.9))


if __name__ == "__main__":
    unittest.main()
