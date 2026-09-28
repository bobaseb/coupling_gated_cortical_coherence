"""Gates on the bridge's feasibility: matching the loops and counting trials (U95)."""

import json
import math
import tempfile
import unittest
from pathlib import Path

import numpy as np

import unity_bridge as ub

SMALL = ub.Task(sd=5.0, tau_ms=100.0)


class LoopTest(unittest.TestCase):
    def test_a_first_order_filter_passes_a_constant_unchanged(self) -> None:
        out = ub.lowpass(np.ones((1, 2000)), 10.0)
        self.assertAlmostEqual(float(out[0, -1]), 1.0, places=6)

    def test_the_quantizer_reads_the_nearest_step(self) -> None:
        values = ub.quantize(np.array([0.4, 0.6, -1.6, 7.4]), 1.0)
        self.assertEqual(values.tolist(), [0.0, 1.0, -2.0, 7.0])

    def test_the_same_seed_gives_the_same_trials(self) -> None:
        first = ub.simulate(SMALL, ub.Loop("analog", 10.0), trials=4, seed=3)
        second = ub.simulate(SMALL, ub.Loop("analog", 10.0), trials=4, seed=3)
        self.assertTrue(np.array_equal(first.recorded_b, second.recorded_b))


class InformationTest(unittest.TestCase):
    def test_a_lower_cutoff_carries_less_transfer_entropy(self) -> None:
        low = ub.evaluate(SMALL, ub.Loop("analog", 2.0), trials=60, seed=0)
        high = ub.evaluate(SMALL, ub.Loop("analog", 200.0), trials=60, seed=0)
        self.assertLess(low.transfer_entropy, high.transfer_entropy)

    def test_a_coarser_step_carries_less_of_both(self) -> None:
        fine = ub.evaluate(SMALL, ub.Loop("quantized", 5.0), trials=60, seed=0)
        coarse = ub.evaluate(SMALL, ub.Loop("quantized", 30.0), trials=60, seed=0)
        self.assertLess(coarse.transfer_entropy, fine.transfer_entropy)
        self.assertLess(coarse.decodability, fine.decodability)

    def test_transfer_entropy_of_independent_series_is_near_zero(self) -> None:
        rng = np.random.default_rng(0)
        te = ub.transfer_entropy(rng.standard_normal((50, 400)), rng.standard_normal((50, 400)))
        self.assertLess(abs(te), 0.5)

    def test_decodability_is_a_share_of_variance(self) -> None:
        score = ub.evaluate(SMALL, ub.Loop("analog", 50.0), trials=60, seed=0).decodability
        self.assertGreater(score, 0.0)
        self.assertLess(score, 1.0)


class MatchTest(unittest.TestCase):
    def test_the_matched_cutoff_reproduces_the_quantized_transfer_entropy(self) -> None:
        cutoffs = np.geomspace(1.0, 1000.0, 12)
        analog = [ub.evaluate(SMALL, ub.Loop("analog", f), 60, 0) for f in cutoffs]
        target = ub.evaluate(SMALL, ub.Loop("quantized", 10.0), 60, 0)
        cutoff = ub.matched_cutoff(cutoffs, analog, target.transfer_entropy)
        if cutoff is None:
            self.fail("the quantized loop's transfer entropy lies within the analog range")
        matched = ub.evaluate(SMALL, ub.Loop("analog", cutoff), 60, 0)
        relative = abs(matched.transfer_entropy / target.transfer_entropy - 1)
        self.assertLess(relative, 0.1)

    def test_a_target_below_the_floor_has_no_matched_cutoff(self) -> None:
        cutoffs = np.array([1.0, 10.0])
        analog = [ub.Measures(5.0, 0.5), ub.Measures(20.0, 0.6)]
        self.assertIsNone(ub.matched_cutoff(cutoffs, analog, 1.0))


class PowerTest(unittest.TestCase):
    def test_two_proportions_at_the_textbook_values(self) -> None:
        self.assertEqual(ub.trials_two_proportions(0.75, 0.70, 0.05, 0.8), 1248)

    def test_two_means_at_the_textbook_values(self) -> None:
        self.assertEqual(ub.trials_two_means(0.2, 0.05, 0.8), 393)

    def test_a_confidence_interval_shrinks_with_the_square_root_of_trials(self) -> None:
        wide = ub.half_width(0.1, 100, 100)
        narrow = ub.half_width(0.1, 100, 400)
        self.assertAlmostEqual(wide / narrow, 2.0)
        self.assertAlmostEqual(wide, 1.959963984540054 * 0.1)


class SavedTest(unittest.TestCase):
    def test_a_coarse_run_is_saved_with_its_declared_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ub.write(
                Path(tmp),
                tasks=(SMALL,),
                steps=(10.0,),
                trials=40,
                cutoffs=8,
                seeds=2,
            )
            saved = json.loads((Path(tmp) / "bridge.json").read_text())
        self.assertEqual(saved["declared_step"], ub.DECLARED_STEP)
        self.assertEqual(len(saved["regimes"]), 1)
        row = saved["regimes"][0]["steps"][0]
        self.assertIn("gap", row)
        self.assertTrue(math.isfinite(saved["trials"]["behaviour"]))


if __name__ == "__main__":
    unittest.main()
