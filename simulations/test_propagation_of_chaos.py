import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

import hypothesis.strategies as st
import numpy as np
from hypothesis import given, settings
from hypothesis.extra.numpy import arrays

from propagation_of_chaos import (
    ChaosConfig,
    Summary,
    circular_correlation,
    simulate_snapshot,
    sliced_joint_product_distance,
    von_mises_density,
    write_tex_macros,
)


class PropagationOfChaosTest(unittest.TestCase):
    def test_circular_correlation_is_branch_cut_invariant(self) -> None:
        first = np.array([3.12, -3.10, 3.08, -3.04, 2.98])
        second = np.array([3.02, -3.00, 2.93, -2.89, 2.82])

        original = circular_correlation(first, second)
        shifted = circular_correlation(first + 2.0 * np.pi, second - 4.0 * np.pi)

        self.assertAlmostEqual(original, shifted, places=14)
        self.assertGreater(original, 0.9)

    def test_circular_correlation_rejects_degenerate_sample(self) -> None:
        with self.assertRaisesRegex(ValueError, "non-degenerate"):
            circular_correlation(np.zeros(8), np.linspace(-1.0, 1.0, 8))

    def test_sliced_distance_detects_dependence_and_is_seeded(self) -> None:
        rng = np.random.default_rng(17)
        first = rng.uniform(-np.pi, np.pi, 600)
        dependent = (first + 0.05 * rng.standard_normal(first.size) + np.pi) % (2.0 * np.pi) - np.pi
        independent = rng.permutation(dependent)

        dependent_distance = sliced_joint_product_distance(first, dependent, 64, 101)
        repeated = sliced_joint_product_distance(first, dependent, 64, 101)
        independent_distance = sliced_joint_product_distance(first, independent, 64, 101)

        self.assertEqual(dependent_distance, repeated)
        self.assertGreater(dependent_distance, 2.0 * independent_distance)

    def test_von_mises_density_is_normalized_and_even(self) -> None:
        theta = np.linspace(-np.pi, np.pi, 4001)
        density = von_mises_density(theta, concentration=2.4)

        self.assertAlmostEqual(float(np.trapezoid(density, theta)), 1.0, places=6)
        np.testing.assert_allclose(density, density[::-1], atol=1e-14)

    def test_seeded_smoke_snapshot_is_reproducible_and_compact(self) -> None:
        config = ChaosConfig(
            n_oscillators=24,
            n_ensembles=12,
            diffusion=0.4,
            coupling=1.4,
            dt=0.02,
            steps=15,
            seed=20260904,
        )

        first = simulate_snapshot(config)
        second = simulate_snapshot(config)

        np.testing.assert_array_equal(first.theta_one, second.theta_one)
        np.testing.assert_array_equal(first.theta_two, second.theta_two)
        np.testing.assert_array_equal(first.aligned_theta_one, second.aligned_theta_one)
        self.assertEqual(first.theta_one.shape, (12,))
        self.assertFalse(hasattr(first, "phases"))
        self.assertAlmostEqual(first.finite_size_floor, 1.0 / np.sqrt(24))
        self.assertGreaterEqual(first.measured_concentration, 0.0)

    def test_invalid_configuration_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "at least two"):
            simulate_snapshot(ChaosConfig(n_oscillators=1))

    def test_tex_macros_are_generated_from_summary(self) -> None:
        summary: Summary = {
            "records": [
                {
                    "config": {"coupling": 1.0, "n_oscillators": 10},
                    "snapshot": {"mean_order": 0.37, "runtime_seconds": 2.0},
                    "metrics": {
                        "correlation": -0.04,
                        "distance_mean": 0.05,
                        "density_l1_error": 0.26,
                        "self_consistency_error": 0.19,
                    },
                },
                {
                    "config": {"coupling": 1.0, "n_oscillators": 1000},
                    "snapshot": {"mean_order": 0.04, "runtime_seconds": 3.0},
                    "metrics": {
                        "correlation": 0.001,
                        "distance_mean": 0.042,
                        "density_l1_error": 0.13,
                        "self_consistency_error": 0.02,
                    },
                },
                {
                    "config": {"coupling": 3.0, "n_oscillators": 10},
                    "snapshot": {"mean_order": 0.74, "runtime_seconds": 4.0},
                    "metrics": {
                        "correlation": 0.52,
                        "distance_mean": 0.10,
                        "density_l1_error": 0.16,
                        "self_consistency_error": 0.008,
                    },
                },
                {
                    "config": {"coupling": 3.0, "n_oscillators": 1000},
                    "snapshot": {
                        "mean_order": 0.7208,
                        "measured_concentration": 2.1624,
                        "runtime_seconds": 5.0,
                    },
                    "metrics": {
                        "correlation": 0.46,
                        "distance_mean": 0.081,
                        "density_l1_error": 0.129,
                        "self_consistency_error": 0.00191,
                    },
                },
            ]
        }
        with TemporaryDirectory() as directory:
            output = Path(directory) / "macros.tex"
            write_tex_macros(summary, output)
            content = output.read_text(encoding="utf-8")

        self.assertIn(r"\newcommand{\chaosSuperCorrelationMin}{0.460}", content)
        self.assertIn(r"\newcommand{\chaosSuperCorrelationMax}{0.520}", content)
        self.assertIn(r"\newcommand{\chaosBesselResidual}{0.00191}", content)
        self.assertIn(r"\newcommand{\chaosRuntimeSeconds}{14.00}", content)


class ChaosPropertyTest(unittest.TestCase):
    @given(
        arrays(
            dtype=float,
            shape=st.shared(st.integers(min_value=2, max_value=50), key="n"),
            elements=st.floats(min_value=-np.pi, max_value=np.pi),
        ),
        arrays(
            dtype=float,
            shape=st.shared(st.integers(min_value=2, max_value=50), key="n"),
            elements=st.floats(min_value=-np.pi, max_value=np.pi),
        ),
    )
    @settings(deadline=None)
    def test_property_circular_correlation_symmetry(
        self, first: np.ndarray, second: np.ndarray
    ) -> None:
        # The guard counts distinct floats, but degeneracy is circular: [-pi, pi]
        # is two values and one angle, so samples that pass it can still centre
        # to all-zero sines and be refused. Refusal is symmetric too -- it is a
        # property of the centred samples, not of the argument order -- so the
        # degenerate branch asserts that rather than returning from the test.
        if len(set(np.round(first, 4))) > 1 and len(set(np.round(second, 4))) > 1:
            try:
                forward = circular_correlation(first, second)
            except ValueError:
                with self.assertRaises(ValueError):
                    circular_correlation(second, first)
                return
            self.assertAlmostEqual(forward, circular_correlation(second, first), places=10)

    @given(st.floats(min_value=-np.pi, max_value=np.pi), st.floats(min_value=0.1, max_value=10.0))
    @settings(deadline=None)
    def test_property_von_mises_density_is_positive(
        self, theta: float, concentration: float
    ) -> None:
        self.assertGreater(von_mises_density(np.array([theta]), concentration)[0], 0.0)


if __name__ == "__main__":
    unittest.main()
