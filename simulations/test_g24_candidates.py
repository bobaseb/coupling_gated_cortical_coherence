"""CPU controls for nonlinear attention and a coupled phase code."""

import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from g24_candidates import fit_phase_network, fit_transformer, save_candidate_comparison
from g24_shared_task import build_task


class CandidateTests(unittest.TestCase):
    def test_saved_scene_pair_split(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_candidate_comparison(output, repeats=2, seed=24, iterations=3, split="scene_pair")
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["train_family"], "scene_equal")
            self.assertEqual(summary["test_family"], "scene_opposite")

    def test_causal_transformer_code_and_cpu_fit(self) -> None:
        task = build_task(repeats=2, seed=24)
        model = fit_transformer(task.train_input, task.train_target, seed=24, iterations=3)
        code = model.code(task.test_input)
        self.assertEqual(code.shape, (16, 4))
        self.assertEqual(model.query_key_dim, 1)
        self.assertEqual(model.causal_past_tokens, 2)
        self.assertTrue(np.isfinite(code).all())
        self.assertLess(
            np.mean(np.sum((model.predict(task.train_input) - task.train_target) ** 2, axis=1)),
            6,
        )

    def test_phase_graph_and_same_order_different_content(self) -> None:
        task = build_task(repeats=2, seed=24)
        model = fit_phase_network(task.train_input, task.train_target, seed=24, iterations=5)
        code = model.code(task.test_input)
        self.assertEqual(code.shape[0], 16)
        self.assertEqual(model.communication_rounds, 3)
        self.assertTrue(np.isfinite(code).all())
        phases = model.phases(task.test_input[:1])[0]
        shifted = phases + 0.7
        self.assertAlmostEqual(abs(np.exp(1j * phases).mean()), abs(np.exp(1j * shifted).mean()))
        self.assertGreater(np.linalg.norm(np.exp(1j * phases) - np.exp(1j * shifted)), 0)
        uncoupled = fit_phase_network(
            task.train_input, task.train_target, seed=24, iterations=3, rounds=0
        )
        self.assertEqual(uncoupled.communication_rounds, 0)
        changed_first_view = task.test_input.copy()
        changed_first_view[:, :3] *= -1
        np.testing.assert_allclose(
            uncoupled.code(task.test_input), uncoupled.code(changed_first_view)
        )

    def test_saved_shared_comparison_and_shuffled_control(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_candidate_comparison(output, repeats=2, seed=24, iterations=3)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(
                {row["candidate"] for row in summary["candidates"]},
                {"linear_full", "transformer", "phase_round0", "phase_round1", "phase_network"},
            )
            self.assertTrue((output / "transformer.npz").exists())
            self.assertTrue((output / "phase_network.npz").exists())
            with np.load(output / "transformer.npz", allow_pickle=False) as saved:
                self.assertEqual(saved["train_code"].shape, (16, 4))
                self.assertEqual(saved["test_code"].shape, (16, 4))
            for row in summary["candidates"]:
                self.assertGreaterEqual(row["shuffled_code_error"], row["train_squared_error"])
                self.assertGreaterEqual(row["inference_ms_per_sample"], 0)
                self.assertTrue(np.isfinite(row["incompatible_decoder_error"]))
                self.assertGreaterEqual(row["test_self_relation_error"], 0)
                self.assertGreaterEqual(row["shared_content_error"], 0)
                self.assertGreaterEqual(row["intervention_error_d0p5"], 0)
                self.assertGreaterEqual(row["intervention_error_d1p0"], 0)
                self.assertGreaterEqual(row["overlap_disagreement_error_d0p5"], 0)
                self.assertGreaterEqual(row["overlap_disagreement_error_d1p0"], 0)
            self.assertAlmostEqual(summary["candidates"][0]["intervention_error_d1p0"], 0)
            self.assertGreater(summary["candidates"][0]["overlap_disagreement_error_d1p0"], 0)
            self.assertTrue((output / "dataset.npz").exists())
            self.assertAlmostEqual(summary["phase_same_order_control"]["order_difference"], 0)
            self.assertGreater(summary["phase_same_order_control"]["code_distance"], 0)


if __name__ == "__main__":
    unittest.main()
