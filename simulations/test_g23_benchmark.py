"""Held-out episode tests for the finite phase/register feedback witness."""

import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from g23_benchmark import fit_readout, run_benchmark, sample_final_episodes
from g23_closed_loop import FeedbackConfig, control_result


class FeedbackBenchmarkTests(unittest.TestCase):
    def test_training_readout_requires_both_register_values(self) -> None:
        register = np.array([0, 0, 1, 1])
        next_phase = np.array([0, 0, 1, 1])
        np.testing.assert_array_equal(fit_readout(register, next_phase), [0, 1])
        with self.assertRaises(ValueError):
            fit_readout(np.zeros(4, dtype=int), next_phase)

    def test_episode_sample_matches_analytical_prediction(self) -> None:
        config = FeedbackConfig(horizon=4)
        result = control_result(config, "informed")
        sample = sample_final_episodes(config, result, 50_000, seed=231)
        observed = np.mean(sample["register"] == sample["next_phase"])
        self.assertAlmostEqual(observed, result.prediction_accuracy[-1], delta=0.01)
        self.assertEqual(set(sample), {"phase", "register", "next_phase"})

    def test_saved_heldout_families_and_matched_controls(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            run_benchmark(output, train_episodes=2000, test_episodes=2000, seed=230)
            summary = json.loads((output / "summary.json").read_text())
            np.testing.assert_array_equal(summary["trained_readout"], [0, 1])
            self.assertEqual(summary["train_family"], "field_0p4")
            self.assertEqual(
                {row["family"] for row in summary["rows"]}, {"field_0p25", "field_0p55"}
            )
            for family in ("field_0p25", "field_0p55"):
                rows = {row["control"]: row for row in summary["rows"] if row["family"] == family}
                self.assertEqual(set(rows), {"informed", "blind", "replayed", "frozen"})
                self.assertAlmostEqual(
                    rows["informed"]["phase_order"], rows["blind"]["phase_order"]
                )
                self.assertAlmostEqual(
                    rows["informed"]["phase_order"], rows["replayed"]["phase_order"]
                )
                self.assertGreater(
                    rows["informed"]["heldout_accuracy"], rows["blind"]["heldout_accuracy"]
                )
                self.assertIsNone(rows["informed"]["continuous_current_cost"])
                self.assertTrue((output / f"{family}_informed.npz").exists())


if __name__ == "__main__":
    unittest.main()
