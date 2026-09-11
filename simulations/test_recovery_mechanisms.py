"""F6 checks analytic equivalence before adding observation complications."""

import unittest

import numpy as np

from bifurcation import bessel_ratio, coherent_r
from recovery_mechanisms import (
    FAMILIES,
    branch_concentration,
    fit_models,
    ideal_observation,
    observe_density,
    parameters,
    tie_weights,
)


class RecoveryMechanismsTest(unittest.TestCase):
    def test_fast_stationary_solver_agrees_with_existing_quadrature(self) -> None:
        self.assertEqual(branch_concentration(1.9), 0.0)
        self.assertEqual(branch_concentration(2.0), 0.0)
        self.assertAlmostEqual(branch_concentration(3.2), 3.2 * coherent_r(3.2), places=10)

    def test_equivalent_distributions_have_different_physical_generators(self) -> None:
        windows = np.linspace(0, 1, 9)
        observations = [ideal_observation(name, 3.2, 0.7, windows) for name in FAMILIES]
        for observation in observations[1:]:
            np.testing.assert_allclose(observation, observations[0], atol=1e-13)
        coupling, diffusion, _ = parameters("coupling", 3.2, windows)
        noise_coupling, noise_diffusion, _ = parameters("diffusion", 3.2, windows)
        drive_coupling, _, drive = parameters("shared_drive", 3.2, windows)
        self.assertTrue(np.all(np.diff(coupling) > 0))
        np.testing.assert_array_equal(diffusion, 1.0)
        np.testing.assert_array_equal(noise_coupling, 3.2)
        self.assertTrue(np.all(np.diff(noise_diffusion) < 0))
        np.testing.assert_array_equal(drive_coupling, 0.0)
        self.assertGreater(float(drive[-1]), 0.0)

    def test_concentration_and_order_are_separate_density_measurements(self) -> None:
        theta = np.linspace(-np.pi, np.pi, 4096, endpoint=False)
        # A second harmonic violates the von Mises ansatz. A concentration
        # estimator that inverts r would hide that violation by construction.
        density = np.exp(1.1 * np.cos(theta - 0.7) + 0.4 * np.cos(2 * (theta - 0.7)))
        density /= float(density.mean() * 2 * np.pi)
        measured = observe_density(density[None, :])
        self.assertAlmostEqual(float(measured["concentration"][0]), 1.1)
        self.assertGreater(abs(float(measured["order"][0]) - bessel_ratio(1.1)), 0.01)

    def test_inference_needs_only_observations_and_preserves_all_tied_models(self) -> None:
        windows = np.linspace(0, 1, 9)
        density = ideal_observation("diffusion", 3.2, 0.7, windows)
        fitted = fit_models(density, windows)
        self.assertEqual(set(fitted), set(FAMILIES))
        for row in fitted.values():
            self.assertAlmostEqual(row["endpoint_ratio"], 3.2, places=5)
        np.testing.assert_allclose(tie_weights(fitted), np.full(3, 1 / 3))
        fitted["coupling"]["squared_error"] = 1.0
        np.testing.assert_array_equal(tie_weights(fitted), [0.0, 0.5, 0.5])


if __name__ == "__main__":
    unittest.main()
