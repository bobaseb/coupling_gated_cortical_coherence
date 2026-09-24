import unittest

import numpy as np

from eeg_pipeline_check import (
    FS,
    PAD_SECONDS,
    centred_phase,
    evaluate,
    instantaneous_order,
    locked_rotation,
    noisy_field,
    quadratic_variation_rate,
)


class LockedRotationTest(unittest.TestCase):
    """A perfectly phase-locked rotating signal through the reported pipeline."""

    def setUp(self) -> None:
        self.data = locked_rotation(seconds=1.0, freq=10.0)

    def test_instantaneous_bipolar_order_is_one(self) -> None:
        row = evaluate("locked", self.data)
        self.assertGreater(row.instantaneous_r, 0.99)

    def test_pooled_order_misses_the_locking(self) -> None:
        row = evaluate("locked", self.data)
        self.assertLess(row.pooled_r, 0.2)
        self.assertLess(row.pooled_a, 0.5)

    def test_pooled_locking_sits_on_the_bessel_curve(self) -> None:
        row = evaluate("locked", self.data)
        self.assertLess(abs(row.pooled_residual), 1e-3)

    def test_centring_each_sample_recovers_the_locking(self) -> None:
        row = evaluate("locked", self.data)
        self.assertGreater(row.centred_r, 0.99)


class NoisyFieldTest(unittest.TestCase):
    def setUp(self) -> None:
        rng = np.random.default_rng(0)
        data = noisy_field(seconds=1.0, freq=10.0, kappa=4.0, noise_sd=0.2, rng=rng)
        self.row = evaluate("field", data)

    def test_raw_channels_are_coherent(self) -> None:
        self.assertGreater(self.row.raw_instantaneous_r, 0.7)

    def test_bipolar_pairs_lose_the_field_coherence(self) -> None:
        self.assertLess(self.row.instantaneous_r, 0.5 * self.row.raw_instantaneous_r)

    def test_pooled_order_reports_neither(self) -> None:
        self.assertLess(self.row.pooled_r, 0.2)


class HelperTest(unittest.TestCase):
    def test_instantaneous_order_of_identical_phases_is_one(self) -> None:
        phase = np.tile(np.linspace(0.0, 6.0, 1000), (5, 1))
        np.testing.assert_allclose(instantaneous_order(phase, 500), [1.0, 1.0])

    def test_centred_phase_removes_common_rotation(self) -> None:
        phase = np.tile(np.linspace(0.0, 6.0, 100), (3, 1))
        np.testing.assert_allclose(centred_phase(phase), 0.0, atol=1e-12)

    def test_quadratic_variation_rate_of_filtered_phase_depends_on_step(self) -> None:
        rng = np.random.default_rng(1)
        data = noisy_field(seconds=1.0, freq=10.0, kappa=4.0, noise_sd=0.5, rng=rng)
        fine = quadratic_variation_rate(data, step=1)
        coarse = quadratic_variation_rate(data, step=100)
        self.assertLess(fine, 0.5 * coarse)

    def test_padding_and_rate_are_the_reported_pipeline_values(self) -> None:
        self.assertEqual(FS, 5000.0)
        self.assertEqual(PAD_SECONDS, 3.0)


if __name__ == "__main__":
    unittest.main()
