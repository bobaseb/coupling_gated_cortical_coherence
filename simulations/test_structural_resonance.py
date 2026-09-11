"""Deterministic contracts for joint phase/plasticity dynamics."""

import unittest
from typing import Any

import numpy as np

from structural_resonance import (
    Config,
    alignment_ratio,
    complete_interval_means,
    descent_fractions,
    drift,
    environment,
    interleaved_labels,
    partition_percentile,
    metrics,
    permutation_percentile,
    project,
    simulate,
    step_direction,
    sweep_records,
    symmetric_gradient,
    template_correlation,
)


class StructuralResonanceTest(unittest.TestCase):
    def test_complete_intervals_exclude_partial_interval_and_terminal_endpoint(self) -> None:
        values = np.array([1.0, 3.0, 5.0, 7.0, 100.0])
        np.testing.assert_array_equal(complete_interval_means(values, 2), [2.0, 6.0])
        with self.assertRaises(ValueError):
            complete_interval_means(values, 0)

    def test_interval_objective_includes_rebound_between_updates(self) -> None:
        config = Config(n=12, steps=100, update_every=10, sample_every=1)
        dense = simulate(config, "gradient")
        # Existing endpoint diagnostics at every step supply a separate readout
        # of the states used by the next step. The final state has no duration.
        expected = dense["dissipation"][:-1].reshape(10, 10).mean(axis=1)
        np.testing.assert_allclose(dense["interval_objective"], expected)
        np.testing.assert_allclose(
            dense["interval_order"], dense["order"][:-1].reshape(10, 10).mean(axis=1)
        )
        np.testing.assert_allclose(dense["interval_alignment"], dense["alignment_ratio"][:-1:10])
        self.assertGreater(abs(float(expected.mean() - dense["dissipation"][10::10].mean())), 0.1)
        np.testing.assert_allclose(dense["interval_time"], np.arange(10) * 0.1)

    def test_gradient_matches_symmetric_finite_difference(self) -> None:
        theta = np.array([0.2, 1.1, -0.7])
        omega = np.array([0.5, 1.0, 1.5])
        coupling = np.ones((3, 3)) - np.eye(3)
        gradient = symmetric_gradient(theta, drift(theta, coupling, omega))
        delta = np.zeros((3, 3))
        delta[0, 1] = delta[1, 0] = 1e-6
        plus = drift(theta, coupling + delta, omega)
        minus = drift(theta, coupling - delta, omega)
        self.assertAlmostEqual(float((plus @ plus - minus @ minus) / 4e-6), gradient[0, 1])
        np.testing.assert_allclose(gradient, gradient.T)

    def test_projection_preserves_resources(self) -> None:
        result = project(np.array([[2.0, -1.0, 2.0], [-1.0, 3.0, 1.0], [2.0, 1.0, 0.0]]), 7.0)
        self.assertAlmostEqual(float(result.sum()), 7.0)
        self.assertTrue(np.all(result >= 0))
        np.testing.assert_array_equal(result.diagonal(), 0.0)
        np.testing.assert_array_equal(result, result.T)
        with self.assertRaises(ValueError):
            project(np.zeros((3, 3)), 7.0)

    def test_environment_and_collective_drive(self) -> None:
        world = environment(12, 48.0, 42)
        self.assertGreater(float(world.omega.mean()), 0.0)
        np.testing.assert_array_equal(
            world.shuffled, world.target[np.ix_(world.permutation, world.permutation)]
        )
        self.assertFalse(np.array_equal(world.target, world.shuffled))
        self.assertAlmostEqual(float(world.target.sum()), 48.0)
        theta = np.linspace(-3.0, 3.0, 12)
        self.assertAlmostEqual(float(drift(theta, world.target, world.omega).mean()), 1.0)
        np.testing.assert_array_equal(world.labels, np.arange(12) * 3 // 12)

    def test_random_step_matches_gradient_norm_and_symmetry(self) -> None:
        """The random arm isolates gradient specificity, so its step size must match."""
        config = Config(n=8)
        world = environment(8, 32.0, 7)
        rng = np.random.default_rng(0)
        theta = rng.normal(size=8)
        coupling = project(rng.uniform(0.0, 1.0, (8, 8)), 32.0)
        gradient = step_direction("gradient", theta, coupling, world.omega, rng)
        noise = step_direction("random", theta, coupling, world.omega, rng)
        self.assertAlmostEqual(float(np.linalg.norm(noise)), float(np.linalg.norm(gradient)))
        np.testing.assert_allclose(noise, noise.T)
        np.testing.assert_array_equal(noise.diagonal(), 0.0)
        self.assertFalse(np.allclose(noise, gradient))
        self.assertEqual(config.permutations, 2000)

    def test_permuted_step_relabels_the_gradient_without_rescaling_it(self) -> None:
        """The deformation control keeps the gradient's entries and moves which edges get them."""
        world = environment(8, 32.0, 7)
        rng = np.random.default_rng(0)
        theta = rng.normal(size=8)
        coupling = project(rng.uniform(0.0, 1.0, (8, 8)), 32.0)
        gradient = step_direction("gradient", theta, coupling, world.omega, rng)
        permuted = step_direction("permuted", theta, coupling, world.omega, rng)
        self.assertAlmostEqual(float(np.linalg.norm(permuted)), float(np.linalg.norm(gradient)))
        np.testing.assert_allclose(np.sort(permuted, axis=None), np.sort(gradient, axis=None))
        np.testing.assert_allclose(permuted, permuted.T)
        np.testing.assert_array_equal(permuted.diagonal(), 0.0)
        self.assertFalse(np.allclose(permuted, gradient))

    def test_permuted_arm_tracks_the_deformation_the_random_arm_cancels(self) -> None:
        """B6: a matched per-step norm alone leaves the random arm far less deformed."""
        config = Config(n=24, steps=2000, permutations=50)
        growth = {
            mode: metrics(simulate(config, mode), config)["kernel_norm_growth"]
            for mode in ("gradient", "random", "permuted")
        }
        self.assertGreater(growth["permuted"], 1.5 * growth["random"])
        self.assertGreater(growth["permuted"], 0.75 * growth["gradient"])

    def test_arms_share_one_phase_noise_stream(self) -> None:
        """At zero learning rate every arm must reproduce the frozen trajectory exactly."""
        config = Config(n=12, steps=400, learning_rate=0.0)
        frozen = simulate(config, "frozen")
        for mode in ("gradient", "random", "permuted"):
            result = simulate(config, mode)
            np.testing.assert_allclose(result["order"], frozen["order"])
            np.testing.assert_allclose(result["theta_final"], frozen["theta_final"])

    def test_alignment_statistics_are_scale_free(self) -> None:
        labels = np.arange(12) * 3 // 12
        block = 1.0 + (labels[:, None] == labels[None, :]).astype(float)
        np.fill_diagonal(block, 0.0)
        self.assertAlmostEqual(template_correlation(block, block), 1.0)
        self.assertAlmostEqual(template_correlation(2.0 * block, block), 1.0)
        self.assertAlmostEqual(alignment_ratio(block, labels), alignment_ratio(3.0 * block, labels))
        self.assertAlmostEqual(alignment_ratio(block, labels), 2.0)
        self.assertAlmostEqual(alignment_ratio(np.ones((12, 12)), labels), 1.0)

    def test_interleaved_labels_carry_no_frequency_information(self) -> None:
        """The second template's partition must be balanced against the frequency clusters."""
        world = environment(99, 99.0, 11)
        crossed = interleaved_labels(99)
        counts = np.zeros((3, 3), dtype=int)
        for cluster, group in zip(world.labels, crossed, strict=True):
            counts[cluster, group] += 1
        self.assertLessEqual(int(counts.max() - counts.min()), 1)
        np.testing.assert_array_equal(np.bincount(crossed), np.bincount(world.labels))
        uniform = np.ones((99, 99))
        np.fill_diagonal(uniform, 0.0)
        self.assertAlmostEqual(alignment_ratio(uniform, crossed), 1.0)
        self.assertLess(abs(alignment_ratio(world.target, crossed) - 1.0), 3 / 99 * 3)

    def test_metrics_score_both_templates_on_the_same_kernel(self) -> None:
        """D2: the crossed partition is a second readout, never an input to the update."""
        config = Config(n=12, steps=200, permutations=50)
        result = simulate(config, "gradient")
        scored = metrics(result, config)
        crossed = interleaved_labels(config.n)
        self.assertAlmostEqual(
            float(result["crossed_alignment_ratio"][0]),
            alignment_ratio(result["coupling_initial"], crossed),
        )
        self.assertNotAlmostEqual(
            scored["tail_crossed_alignment_ratio"], scored["tail_alignment_ratio"]
        )
        self.assertIn("blind_partition_percentile", scored)

    def test_partition_percentile_brackets_the_frequency_partition(self) -> None:
        """D2: a blind relabelling keeps the group sizes and loses the frequency."""
        labels = np.arange(12) * 3 // 12
        aligned = project((labels[:, None] == labels[None, :]).astype(float) + 0.5, 48.0)
        self.assertGreater(partition_percentile(aligned, labels, 200, 3), 0.99)
        opposed = project(1.5 - (labels[:, None] == labels[None, :]).astype(float), 48.0)
        self.assertLess(partition_percentile(opposed, labels, 200, 3), 0.01)
        uniform = project(np.ones((12, 12)), 48.0)
        self.assertEqual(partition_percentile(uniform, labels, 200, 3), 0.0)

    def test_permutation_percentile_brackets_alignment(self) -> None:
        labels = np.arange(12) * 3 // 12
        target = project((labels[:, None] == labels[None, :]).astype(float), 48.0)
        self.assertAlmostEqual(permutation_percentile(target, target, 200, 3), 0.0)
        antipodal = project(1.0 - (labels[:, None] == labels[None, :]).astype(float), 48.0)
        self.assertGreater(permutation_percentile(antipodal, target, 200, 3), 0.99)

    def test_descent_fraction_is_measured_against_the_frozen_arm(self) -> None:
        records: list[dict[str, Any]] = [
            {"seed": 1, "mode": "frozen", "tail_dissipation": 1400.0, "sigma_floor": 1000.0},
            {"seed": 1, "mode": "gradient", "tail_dissipation": 1120.0, "sigma_floor": 1000.0},
            {"seed": 1, "mode": "random", "tail_dissipation": 1400.0, "sigma_floor": 1000.0},
        ]
        descent_fractions(records)
        self.assertAlmostEqual(records[0]["descent_fraction"], 0.0)
        self.assertAlmostEqual(records[1]["descent_fraction"], 0.7)
        self.assertAlmostEqual(records[2]["descent_fraction"], 0.0)

    def test_seed_storage_and_update_cadence(self) -> None:
        config = Config(n=12, steps=101, update_every=50, sample_every=50)
        first = simulate(config, "gradient")
        second = simulate(config, "gradient")
        for key in first:
            np.testing.assert_array_equal(first[key], second[key])
        np.testing.assert_allclose(first["time"], [0.0, 0.5, 1.0, 1.01])
        self.assertEqual(int(first["updates"]), 2)
        self.assertEqual(first["theta_final"].shape, (12,))
        self.assertNotIn("theta_history", first)
        self.assertAlmostEqual(float(first["coupling_final"].sum()), config.n * config.row_sum)
        frozen = simulate(config, "frozen")
        np.testing.assert_array_equal(frozen["coupling_initial"], frozen["coupling_final"])
        self.assertFalse(np.array_equal(first["coupling_initial"], first["coupling_final"]))

    def test_sweep_reports_every_rate(self) -> None:
        rates = (0.0, 0.05)
        records = sweep_records(Config(n=12, steps=200), rates)
        self.assertEqual([row["learning_rate"] for row in records], list(rates))
        for row in records:
            self.assertIn("tail_dissipation", row)
            self.assertIn("minimum_order_after_ten", row)
            self.assertIn("plateau_relative_change", row)

    def test_invalid_config(self) -> None:
        with self.assertRaises(ValueError):
            simulate(Config(dt=-1.0), "gradient")
        with self.assertRaises(ValueError):
            simulate(Config(n=12, steps=50), "orthogonal")


if __name__ == "__main__":
    unittest.main()
