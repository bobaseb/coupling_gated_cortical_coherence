"""Tests for the fixed G24 local-observation reconstruction task."""

import unittest
import json
import tempfile
from pathlib import Path

import numpy as np

from followup_foundations import covariance_rank_tail
from g24_shared_task import (
    build_task,
    fit_reduced_rank,
    intervention_set,
    overlap_disagreement_set,
    reconstruction_scores,
    save_linear_baseline,
)


class SharedTaskTests(unittest.TestCase):
    def test_scene_pair_split_holds_out_unseen_scene_combinations(self) -> None:
        task = build_task(repeats=2, noise=0.0, seed=24, split="scene_pair")
        self.assertEqual(task.train_input.shape, (16, 6))
        np.testing.assert_array_equal(task.train_state[:, 0], task.train_state[:, 1])
        np.testing.assert_array_equal(task.test_state[:, 0], -task.test_state[:, 1])
        self.assertGreater(
            reconstruction_scores(
                task.test_input,
                task.test_target,
                fit_reduced_rank(task.train_input, task.train_target, 4),
            )["squared_error"],
            0,
        )
        with self.assertRaises(ValueError):
            build_task(split="unknown")  # type: ignore[arg-type]

    def test_self_intervention_distance_preserves_scene(self) -> None:
        task = build_task(repeats=2, noise=0.0, seed=24)
        inputs, targets = intervention_set(task, distance=0.5, noise=0.0, seed=25)
        np.testing.assert_allclose(inputs[:, 0], task.test_input[:, 0])
        np.testing.assert_allclose(inputs[:, 1], task.test_input[:, 1])
        np.testing.assert_allclose(targets[:, 2], task.test_target[:, 2] + 0.5)
        np.testing.assert_allclose(targets[:, -1], task.test_target[:, -1] + 0.5)
        with self.assertRaises(ValueError):
            intervention_set(task, distance=-0.5, noise=0.0, seed=25)

    def test_saved_linear_baseline_matches_predicted_floor(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_linear_baseline(output, repeats=2, noise=0.0, seed=24)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["seed"], 24)
            self.assertEqual(summary["train_family"], "even_parity")
            self.assertEqual(summary["test_family"], "odd_parity")
            self.assertEqual(len(summary["ranks"]), 5)
            for row in summary["ranks"]:
                self.assertAlmostEqual(row["test_squared_error"], row["predicted_train_floor"])
                self.assertLessEqual(row["effective_rank"], row["rank"])
                self.assertEqual(row["stored_parameter_count"], 30)
                self.assertEqual(row["decoder_bytes"], 240)
            with np.load(output / "dataset.npz", allow_pickle=False) as saved:
                self.assertEqual(saved["train_input"].shape, (16, 6))
            with np.load(output / "decoders.npz", allow_pickle=False) as saved:
                self.assertEqual(saved["rank_2"].shape, (5, 6))

    def test_split_overlap_and_self_intervention(self) -> None:
        task = build_task(repeats=3, noise=0.0, seed=24)
        self.assertEqual(task.train_input.shape, (24, 6))
        self.assertEqual(task.test_input.shape, (24, 6))
        np.testing.assert_array_equal(np.prod(task.train_state, axis=1), 1)
        np.testing.assert_array_equal(np.prod(task.test_state, axis=1), -1)
        np.testing.assert_array_equal(task.train_input[:, 1], task.train_input[:, 3])
        np.testing.assert_array_equal(task.train_input[:, 2], task.train_input[:, 4])
        np.testing.assert_allclose(task.test_input @ task.target_operator.T, task.test_target)
        for state in task.train_state:
            intervention = state.copy()
            intervention[2] *= -1
            self.assertTrue(np.any(np.all(task.test_state == intervention, axis=1)))

    def test_linear_rank_floor_on_unseen_combinations(self) -> None:
        task = build_task(repeats=2, noise=0.0, seed=24)
        covariance = task.train_input.T @ task.train_input / len(task.train_input)
        test_covariance = task.test_input.T @ task.test_input / len(task.test_input)
        np.testing.assert_allclose(covariance, test_covariance)
        for rank in range(5):
            with self.subTest(rank=rank):
                decoder = fit_reduced_rank(task.train_input, task.train_target, rank)
                score = reconstruction_scores(task.test_input, task.test_target, decoder)
                predicted = covariance_rank_tail(task.target_operator, covariance, rank)
                self.assertLessEqual(np.linalg.matrix_rank(decoder), rank)
                self.assertAlmostEqual(score["squared_error"], predicted)
        self.assertAlmostEqual(
            reconstruction_scores(task.test_input, task.test_target, task.target_operator)[
                "squared_error"
            ],
            0,
        )

    def test_independent_overlap_noise_and_seed(self) -> None:
        first = build_task(repeats=2, noise=0.1, seed=24)
        second = build_task(repeats=2, noise=0.1, seed=24)
        np.testing.assert_array_equal(first.train_input, second.train_input)
        self.assertGreater(np.mean((first.train_input[:, 1] - first.train_input[:, 3]) ** 2), 0)
        with self.assertRaises(ValueError):
            build_task(repeats=0)
        with self.assertRaises(ValueError):
            build_task(noise=-0.1)

    def test_overlap_disagreement_changes_only_second_local_view(self) -> None:
        task = build_task(repeats=2, seed=24)
        inputs, targets = overlap_disagreement_set(task, distance=0.5)
        np.testing.assert_array_equal(inputs[:, :3], task.test_input[:, :3])
        np.testing.assert_array_equal(inputs[:, 5], task.test_input[:, 5])
        np.testing.assert_allclose(inputs[:, 3:5], task.test_input[:, 3:5] + 0.5)
        np.testing.assert_array_equal(targets, task.test_target)
        with self.assertRaises(ValueError):
            overlap_disagreement_set(task, distance=-0.5)


if __name__ == "__main__":
    unittest.main()
