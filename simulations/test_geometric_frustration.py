import unittest
import json
from pathlib import Path
from tempfile import TemporaryDirectory

import hypothesis.strategies as st
import numpy as np
from hypothesis import given, settings

from geometric_frustration import (
    Config,
    FAILED_BASELINE,
    balanced_network,
    drift,
    field_required,
    simulate,
    threshold,
    run,
    epsilon_grid,
    refinement_grid,
    REFINEMENT_POINTS,
)


class FrustrationTest(unittest.TestCase):
    def test_network_obeys_dale_balance_and_no_self_edges(self) -> None:
        matrix = balanced_network(100, 0.2, 4.0, 42)
        np.testing.assert_allclose(matrix.sum(axis=1), 0, atol=1e-14)
        self.assertTrue(np.all(matrix[:, :80] >= 0))
        self.assertTrue(np.all(matrix[:, 80:] <= 0))
        np.testing.assert_array_equal(np.diag(matrix), 0)
        np.testing.assert_allclose(np.maximum(matrix, 0).sum(axis=1), 4)
        np.testing.assert_array_equal(matrix, balanced_network(100, 0.2, 4.0, 42))

    def test_drift_matches_explicit_pair_sum(self) -> None:
        matrix = balanced_network(50, 0.5, 4.0, 7)
        phases = np.random.default_rng(8).uniform(-np.pi, np.pi, 50)
        expected = np.sum((matrix + 0.03) * np.sin(phases[None, :] - phases[:, None]), axis=1)
        np.testing.assert_allclose(drift(phases, matrix, 0.03), expected, atol=1e-14)

    def test_field_conversion_reuses_millisecond_constants(self) -> None:
        self.assertAlmostEqual(field_required(2, 0.2), 2 / (1675.5160819145565 * 0.0004 * 40))
        self.assertAlmostEqual(field_required(2, 0.1) / field_required(2, 0.2), 8)

    def test_simulation_is_seeded_decimated_and_endpoint_inclusive(self) -> None:
        config = Config(n=50, steps=21, sample_every=5)
        matrix = balanced_network(50, 0.5, 4, 2)
        first = simulate(config, matrix, 0.02, 3)
        second = simulate(config, matrix, 0.02, 3)
        np.testing.assert_array_equal(first["order"], second["order"])
        self.assertEqual(first["time"].size, 6)
        self.assertAlmostEqual(first["time"][-1], 0.21)
        self.assertEqual(first["final_phases"].shape, (50,))

    def test_threshold_uses_persistent_crossing_and_rejects_unbracketed(self) -> None:
        self.assertEqual(
            threshold(np.arange(5.0), np.array([0.04, 0.3, 0.1, 0.3, 0.4])), (2.5, 2, 3)
        )
        with self.assertRaises(ValueError):
            threshold(np.arange(3.0), np.array([0.04, 0.1, 0.15]))

    def test_failed_baseline_stops_sweep_and_saves_negative_result(self) -> None:
        with TemporaryDirectory() as directory:
            output = Path(directory)
            with self.assertRaisesRegex(ValueError, "Baseline exceeds"):
                run(Config(n=100, steps=2000, probability=0.5), output)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["status"], FAILED_BASELINE)
            self.assertIsNone(summary["critical_epsilon"])
            self.assertEqual(len(list(output.glob("leg_*.npz"))), 1)
            self.assertLess(summary["noise_control_order"], 2 * summary["finite_size_floor"])
            self.assertTrue((output / "noise_control.npz").exists())
            self.assertEqual(list(output.glob("*.png")), [])

    def test_invalid_configuration_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "positive"):
            simulate(Config(dt=0), np.zeros((500, 500)), 0, 2)

    def test_weak_synapse_sweep_still_brackets_mean_field_threshold(self) -> None:
        config = Config(positive_sum=1)
        values = epsilon_grid(config)
        self.assertEqual(values.size, 20)
        self.assertEqual(values[0], 0)
        self.assertTrue(np.all(np.diff(values) > 0))
        self.assertGreater(values[-1], 2 * config.diffusion / config.n)

    def test_refinement_subdivides_the_bracket_without_repeating_its_ends(self) -> None:
        grid = refinement_grid((0.002, 0.004), points=3)

        np.testing.assert_allclose(grid, [0.0025, 0.003, 0.0035])
        with self.assertRaisesRegex(ValueError, "increasing"):
            refinement_grid((0.004, 0.004))

    def test_refinement_step_follows_the_bracket_rather_than_a_fixed_scale(self) -> None:
        wide = np.diff(refinement_grid((0.002, 0.004))).mean()
        narrow = np.diff(refinement_grid((0.002, 0.0021))).mean()

        self.assertAlmostEqual(wide / narrow, 20.0)

    def test_sweep_refines_the_crossing_step_without_re_running_the_coarse_legs(self) -> None:
        config = Config(n=64, steps=600, sample_every=10, probability=0.5, positive_sum=1)

        with TemporaryDirectory() as directory:
            output = Path(directory)
            returned = run(config, output)
            summary = json.loads((output / "summary.json").read_text())
            coarse = np.asarray(summary["coarse_epsilon"])
            merged = np.asarray(summary["epsilon"])
            names = sorted(path.name for path in output.glob("leg_*.npz"))
            figures = list(output.glob("*.png"))

        self.assertEqual(json.loads(json.dumps(returned)), summary)
        self.assertEqual(figures, [])

        self.assertEqual(names[: coarse.size], [f"leg_{index:02d}.npz" for index in range(20)])
        self.assertEqual(len(names), coarse.size + REFINEMENT_POINTS)
        np.testing.assert_array_equal(np.sort(merged), merged)
        added = np.setdiff1d(merged, coarse)
        self.assertEqual(added.size, REFINEMENT_POINTS)
        lower, upper = summary["coarse_bracket"]
        self.assertTrue(np.all((added > lower) & (added < upper)))
        self.assertGreaterEqual(summary["threshold_bracket"][0], lower)
        self.assertLessEqual(summary["threshold_bracket"][1], upper)

    def test_rate_calibration_is_explicit_and_inverse(self) -> None:
        self.assertAlmostEqual(field_required(2, 0.2, rate=10), field_required(2, 0.2) / 10)
        with self.assertRaisesRegex(ValueError, "positive"):
            field_required(2, 0.2, rate=0)

    def test_negative_synaptic_strength_cannot_reverse_dale_signs(self) -> None:
        with self.assertRaisesRegex(ValueError, "nonnegative"):
            balanced_network(100, 0.2, -1, 42)


class GeometricFrustrationPropertyTest(unittest.TestCase):
    @given(
        st.integers(min_value=20, max_value=200),
        st.floats(min_value=0.05, max_value=0.95),
        st.floats(min_value=0.1, max_value=10.0),
        st.integers(min_value=0, max_value=1000),
    )
    @settings(deadline=None, max_examples=20)
    def test_property_balanced_network_invariants(
        self, n: int, probability: float, positive_sum: float, seed: int
    ) -> None:
        try:
            matrix = balanced_network(n, probability, positive_sum, seed)
        except ValueError as e:
            if "denser configuration" in str(e):
                import hypothesis

                hypothesis.assume(False)
                return
            raise
        np.testing.assert_allclose(matrix.sum(axis=1), 0.0, atol=1e-10)
        np.testing.assert_allclose(np.maximum(matrix, 0).sum(axis=1), positive_sum, atol=1e-10)
        np.testing.assert_array_equal(np.diag(matrix), 0.0)
        n_excitatory = int(0.8 * n)
        self.assertTrue(np.all(matrix[:, :n_excitatory] >= 0.0))
        self.assertTrue(np.all(matrix[:, n_excitatory:] <= 0.0))


if __name__ == "__main__":
    unittest.main()
