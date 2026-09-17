import unittest

import numpy as np

from empirical_collapse import (
    BANDS,
    OBSERVED_CONCENTRATION_RANGE,
    bessel_ratio,
    compute_window_sensitivity,
    extract_phase,
    extract_phase_bipolar,
    extract_phase_car,
    tangent_separation,
)


class WindowSensitivityTest(unittest.TestCase):
    def test_reports_each_requested_window_with_enough_pooled_samples(self) -> None:
        phase = np.zeros((62, 500), dtype=float)

        rows = compute_window_sensitivity(phase, fs=5000.0, windows_ms=(5, 20, 100))

        self.assertEqual([row.window_ms for row in rows], [5, 20, 100])
        self.assertTrue(all(row.pooled_samples >= 100 for row in rows))
        self.assertTrue(all(np.isfinite(row.mean_residual) for row in rows))


class MontageBehaviourTest(unittest.TestCase):
    """What each montage computes, not just how many samples it returns.

    The padding test above asserts three output shapes and nothing else, so it
    holds for any phases whatever -- including a montage that quietly returns
    another montage's answer. Mutation testing found the gap: roughly a third of
    the mutants in these three functions survived the suite, and they feed the
    empirical collapse claim from real EEG.
    """

    SCALP = 62

    def _phases(self) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
        rng = np.random.default_rng(7)
        data = rng.normal(size=(65, 800))
        fs, pad = 200.0, 0.25
        return (
            extract_phase(data, fs, pad_seconds=pad),
            extract_phase_bipolar(data, fs, pad_seconds=pad),
            extract_phase_car(data, fs, pad_seconds=pad),
        )

    def test_the_common_average_reference_removes_the_circular_mean(self) -> None:
        """CAR's defining property: the instantaneous circular mean goes to zero.

        This is what separates CAR from plain extraction rather than a detail of
        it, and the raw montage leaves the same quantity at ~pi, so the two
        cannot be confused for one another by any tolerance.
        """
        raw, _, car = self._phases()

        residual = np.angle(np.sum(np.exp(1j * car[: self.SCALP]), axis=0))
        self.assertLess(float(np.max(np.abs(residual))), 1e-10)

        untouched = np.angle(np.sum(np.exp(1j * raw[: self.SCALP]), axis=0))
        self.assertGreater(float(np.max(np.abs(untouched))), 1.0)

    def test_only_the_scalp_channels_are_filled(self) -> None:
        """Indices 0-61 are scalp; EOG/EMG rows stay NaN and pairs come to 61."""
        raw, bipolar, car = self._phases()

        for name, phases in (("raw", raw), ("car", car)):
            with self.subTest(montage=name):
                self.assertTrue(np.all(np.isfinite(phases[: self.SCALP])))
                self.assertTrue(np.all(np.isnan(phases[self.SCALP :])))
                self.assertGreaterEqual(float(np.min(phases[: self.SCALP])), -np.pi)
                self.assertLessEqual(float(np.max(phases[: self.SCALP])), np.pi)

        self.assertEqual(bipolar.shape[0], self.SCALP - 1)
        self.assertTrue(np.all(np.isfinite(bipolar)))

    def test_the_defaults_and_an_explicit_band_are_both_exercised(self) -> None:
        """Call each montage as its signature allows, not only as the suite does.

        Every other case here passes `pad_seconds` explicitly and takes the
        default band, so `pad_seconds = 0.0` and the `high` argument are never
        read: mutants that change the default to 1.0, or that drop `high` from
        the call CAR makes into `extract_phase`, leave those cases untouched.
        Defaults are part of the contract these functions offer their callers.
        """
        rng = np.random.default_rng(7)
        data = rng.normal(size=(65, 800))
        fs = 200.0

        # pad_seconds defaults to 0.0, so nothing is trimmed.
        for name, montage, rows, first in (
            ("raw", extract_phase, 65, [1.510825, 1.440106, 1.866114]),
            ("bipolar", extract_phase_bipolar, 61, [-0.382434, 0.401989, 0.903535]),
            ("car", extract_phase_car, 65, [-0.723957, -1.285065, -0.730760]),
        ):
            with self.subTest(montage=name, call="defaults"):
                phases = montage(data, fs)
                self.assertEqual(phases.shape, (rows, data.shape[1]))
                np.testing.assert_allclose(phases[0, :3], first, rtol=0, atol=5e-7)

        # A band that is not the module default, so `high` has to be carried.
        for name, montage, first in (
            ("raw", extract_phase, [1.420329, 1.236754, 0.876516]),
            ("bipolar", extract_phase_bipolar, [0.634094, 0.593257, 0.380256]),
            ("car", extract_phase_car, [-1.479628, -1.812702, -2.599116]),
        ):
            with self.subTest(montage=name, call="band"):
                phases = montage(data, fs, 4.0, 12.0)
                np.testing.assert_allclose(phases[0, :3], first, rtol=0, atol=5e-7)

    def test_each_montage_reports_its_own_phases(self) -> None:
        """Pinned first samples, so no montage can return another's answer."""
        raw, bipolar, car = self._phases()

        np.testing.assert_allclose(
            raw[0, :5],
            [0.919964, 1.719288, 2.642195, -2.403657, -1.150149],
            rtol=0,
            atol=5e-7,
        )
        np.testing.assert_allclose(
            car[0, :5], [0.867549, 0.937997, 1.087933, 1.412231, 2.430319], rtol=0, atol=5e-7
        )
        np.testing.assert_allclose(
            bipolar[0, :5], [0.177369, 0.661884, 1.010745, 1.428974, 1.995657], rtol=0, atol=5e-7
        )


class MontagePaddingTest(unittest.TestCase):
    def test_all_montages_discard_the_same_filter_padding(self) -> None:
        rng = np.random.default_rng(7)
        fs = 200.0
        padding = 0.25
        data = rng.normal(size=(65, 800))

        raw = extract_phase(data, fs, pad_seconds=padding)
        bipolar = extract_phase_bipolar(data, fs, pad_seconds=padding)
        car = extract_phase_car(data, fs, pad_seconds=padding)

        expected_samples = data.shape[1] - 2 * int(fs * padding)
        self.assertEqual(raw.shape[1], expected_samples)
        self.assertEqual(bipolar.shape[1], expected_samples)
        self.assertEqual(car.shape[1], expected_samples)


class TangentSeparationTest(unittest.TestCase):
    def test_deviations_bound_the_curve_over_the_observed_range(self) -> None:
        separation = tangent_separation()

        low, high = OBSERVED_CONCENTRATION_RANGE
        grid = np.linspace(low, high, 401)
        curve = np.array([bessel_ratio(a) for a in grid])
        self.assertAlmostEqual(
            separation.linear_deviation, float(np.max(np.abs(curve - grid / 2))), places=5
        )
        self.assertAlmostEqual(
            separation.tanh_deviation,
            float(np.max(np.abs(curve - np.tanh(grid / 2)))),
            places=5,
        )

    def test_probe_and_target_are_consistent_with_the_curve(self) -> None:
        separation = tangent_separation(probe=1.5, target=0.17)

        self.assertAlmostEqual(separation.probe_separation, 1.5 / 2 - bessel_ratio(1.5), places=6)
        self.assertAlmostEqual(
            separation.target_concentration / 2 - bessel_ratio(separation.target_concentration),
            0.17,
            places=6,
        )
        self.assertGreater(separation.target_concentration, 1.5)


class AnalysisConfigurationTest(unittest.TestCase):
    def test_named_narrowband_set_includes_the_reported_gamma_band(self) -> None:
        self.assertEqual(BANDS["gamma"], [30.0, 40.0])


if __name__ == "__main__":
    unittest.main()
