"""Deterministic contracts for joint phase/plasticity dynamics."""

import unittest

import numpy as np

from structural_resonance import Config, drift, environment, project, simulate, symmetric_gradient


class StructuralResonanceTest(unittest.TestCase):
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
        omega, target, shuffled, permutation = environment(12, 48.0, 42)
        self.assertGreater(float(omega.mean()), 0.0)
        np.testing.assert_array_equal(shuffled, target[np.ix_(permutation, permutation)])
        self.assertFalse(np.array_equal(target, shuffled))
        self.assertAlmostEqual(float(target.sum()), 48.0)
        theta = np.linspace(-3.0, 3.0, 12)
        self.assertAlmostEqual(float(drift(theta, target, omega).mean()), float(omega.mean()))

    def test_seed_storage_and_update_cadence(self) -> None:
        config = Config(n=12, steps=101, update_every=50, sample_every=50)
        first = simulate(config)
        second = simulate(config)
        for key in first:
            np.testing.assert_array_equal(first[key], second[key])
        np.testing.assert_allclose(first["time"], [0.0, 0.5, 1.0, 1.01])
        self.assertEqual(int(first["updates"]), 2)
        self.assertEqual(first["theta_final"].shape, (12,))
        self.assertNotIn("theta_history", first)
        self.assertAlmostEqual(float(first["coupling_final"].sum()), config.n * config.row_sum)
        frozen = simulate(config, adaptive=False)
        np.testing.assert_array_equal(frozen["coupling_initial"], frozen["coupling_final"])
        self.assertFalse(np.array_equal(first["coupling_initial"], first["coupling_final"]))

    def test_invalid_config(self) -> None:
        with self.assertRaises(ValueError):
            simulate(Config(dt=-1.0))


if __name__ == "__main__":
    unittest.main()
