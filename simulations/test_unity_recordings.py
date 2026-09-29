"""Gates on the occupancy measured in recorded membranes (U100).

Every test runs on synthetic traces whose answer is known, so none needs the
deposit: the pipeline that reads a recording must return, on a path of the
model itself, what the model computes by propagating probability exactly.
"""

import math
import unittest
from typing import Any

import numpy as np

import unity_occupancy as uo
import unity_recordings as ur

DT_MS = 0.1


def ornstein_uhlenbeck(tau_ms: float, samples: int, seed: int) -> np.ndarray:
    """A stationary path of unit standard deviation, sampled every ``DT_MS``."""
    rng = np.random.default_rng(seed)
    decay = math.exp(-DT_MS / tau_ms)
    kicks = rng.standard_normal(samples) * math.sqrt(1.0 - decay**2)
    path = np.empty(samples)
    path[0] = rng.standard_normal()
    for k in range(1, samples):
        path[k] = decay * path[k - 1] + kicks[k]
    return path


def integrate_and_fire(
    membrane: uo.Membrane, samples: int, seed: int, means: np.ndarray | None = None
) -> tuple[np.ndarray, np.ndarray]:
    """A path of the model membrane, threshold zero, and the samples spent spiking.

    The step and the Brownian-bridge crossing between samples are those
    ``unity_occupancy`` propagates, so the path's statistics are the model's.
    With ``means``, the mean moves sample by sample and a spike resets to it.
    """
    means = np.full(samples, membrane.mean) if means is None else means
    rng = np.random.default_rng(seed)
    decay = math.exp(-DT_MS / membrane.tau_ms)
    spread = math.sqrt(1.0 - decay**2)
    stages = round(membrane.refractory_ms / DT_MS)
    path, spiking = np.empty(samples), np.zeros(samples, dtype=bool)
    v, hold = membrane.mean, 0
    for k in range(samples):
        if hold:
            hold -= 1
            spiking[k], path[k] = True, 0.0
            v = means[k] if hold == 0 else v
            continue
        new = means[k] + (v - means[k]) * decay + spread * rng.standard_normal()
        crossed = new >= 0.0 or rng.random() < math.exp(-2.0 * v * new / spread**2)
        if crossed:
            hold, spiking[k], new = stages - 1, True, 0.0
        v = path[k] = new
    return path, spiking


class SpikeDetectionTest(unittest.TestCase):
    """The authors' detector: a slope threshold, a peak within 1.5 ms, 5 mV tall."""

    def trace(self) -> tuple[np.ndarray, float, list[int]]:
        rate_hz = 20_000.0
        v = -0.060 + 0.001 * ornstein_uhlenbeck(10.0, 40_000, seed=1)
        onsets = [5_000, 17_000, 31_000]
        for k in onsets:
            rise = np.linspace(0.0, 0.070, 11)
            fall = np.linspace(0.070, -0.005, 41)
            v[k : k + 11] += rise
            v[k + 11 : k + 52] += fall
        return v, rate_hz, onsets

    def test_every_spike_is_found_once_at_its_onset(self) -> None:
        v, rate_hz, onsets = self.trace()
        spikes = ur.detect_spikes(v, rate_hz, slope_v_per_s=10.0)
        self.assertEqual(len(spikes.onsets), len(onsets))
        for found, true in zip(spikes.onsets, onsets, strict=True):
            self.assertLessEqual(abs(int(found) - true), 2)

    def test_the_threshold_is_the_potential_at_the_onset(self) -> None:
        v, rate_hz, _ = self.trace()
        spikes = ur.detect_spikes(v, rate_hz, slope_v_per_s=10.0)
        np.testing.assert_allclose(spikes.thresholds, v[spikes.onsets])

    def test_a_small_fast_event_is_not_a_spike(self) -> None:
        v = np.full(4_000, -0.060)
        v[2_000:2_005] += np.linspace(0.0, 0.003, 5)
        self.assertEqual(len(ur.detect_spikes(v, 20_000.0, 10.0).onsets), 0)

    def test_the_mask_covers_each_spike_and_its_repolarisation(self) -> None:
        v, rate_hz, onsets = self.trace()
        spikes = ur.detect_spikes(v, rate_hz, slope_v_per_s=10.0)
        mask = ur.spike_mask(v, spikes, rate_hz)
        for k in onsets:
            self.assertTrue(mask[k + 1 : k + 40].all())
        self.assertLess(mask.mean(), 0.01)


class MembraneStatisticsTest(unittest.TestCase):
    def test_the_correlation_time_of_an_ornstein_uhlenbeck_path_is_its_time_constant(self) -> None:
        for tau in (5.0, 20.0):
            with self.subTest(tau=tau):
                path = ornstein_uhlenbeck(tau, 400_000, seed=2)
                segments = [path[k : k + 100_000] for k in range(0, 400_000, 100_000)]
                self.assertAlmostEqual(
                    ur.correlation_time_ms(segments, DT_MS) / tau, 1.0, delta=0.1
                )


class WindowTest(unittest.TestCase):
    def test_a_window_counts_when_any_sample_in_it_passes(self) -> None:
        passing = np.zeros(100, dtype=bool)
        passing[[5, 35]] = True
        self.assertAlmostEqual(ur.window_hits(passing, [(0, 100)], window=10), 2 / 10)

    def test_windows_never_straddle_two_epochs(self) -> None:
        passing = np.zeros(100, dtype=bool)
        passing[12] = True
        # Epochs of 15 and 30 samples hold one and three whole windows of ten.
        self.assertAlmostEqual(ur.window_hits(passing, [(5, 20), (50, 80)], window=10), 1 / 4)

    def test_an_epoch_shorter_than_a_window_contributes_nothing(self) -> None:
        passing = np.ones(100, dtype=bool)
        self.assertTrue(math.isnan(ur.window_hits(passing, [(0, 5)], window=10)))


class TwinTest(unittest.TestCase):
    """Measured on a path of the model, the pipeline returns what the model computes."""

    membrane: uo.Membrane
    twin: ur.Twin
    path: np.ndarray
    spiking: np.ndarray

    @classmethod
    def setUpClass(cls) -> None:
        cls.membrane = uo.Membrane(tau_ms=10.0, mean=-2.0, reset=-2.0, refractory_ms=2.0)
        grid = uo.Grid(-8.0, ur.GRID_STEP)
        cls.twin = ur.Twin(grid, cls.membrane, window_ms=10.0, dt_ms=DT_MS)
        cls.path, cls.spiking = integrate_and_fire(cls.membrane, 600_000, seed=5)

    def test_the_twin_predicts_the_correlation_time_of_the_recorded_path(self) -> None:
        smooth = ur._interpolated(self.path, self.spiking)
        measured = ur.correlation_time_ms([smooth], DT_MS)
        twin = ur.twin_correlation_time_ms(self.twin.grid, self.membrane, DT_MS)
        self.assertAlmostEqual(measured / twin, 1.0, delta=0.08)

    def test_the_measured_pass_fraction_is_the_model_pass_fraction(self) -> None:
        for scale in (0.25, 1.0):
            with self.subTest(scale=scale):
                passing = self.twin.occupied(self.path, self.spiking, scale)
                self.assertAlmostEqual(
                    float(passing.mean()), self.twin.pass_fraction(scale), delta=0.01
                )

    def test_the_measured_window_visits_are_the_model_visits(self) -> None:
        passing = self.twin.occupied(self.path, self.spiking, 0.25)
        window = round(40.0 / DT_MS)
        measured = ur.window_hits(passing, [(0, self.path.size)], window)
        self.assertAlmostEqual(measured, self.twin.hit_probability(0.25, 40.0), delta=0.04)

    def test_the_twin_predicts_the_rate_of_the_path(self) -> None:
        onsets = np.flatnonzero(np.diff(self.spiking.astype(int)) == 1)
        measured = onsets.size / (self.path.size * DT_MS / 1000.0)
        self.assertAlmostEqual(self.twin.rate_hz / measured, 1.0, delta=0.1)

    def test_a_shorter_window_is_read_exactly_off_a_longer_one(self) -> None:
        longer = uo.laws(self.twin.grid, self.membrane, 30.0, DT_MS)
        np.testing.assert_allclose(ur.shorten(longer, 100), self.twin.table, atol=1e-12)

    def test_a_state_above_threshold_without_a_spike_fails(self) -> None:
        path = np.array([0.2, -1.0])
        passing = self.twin.occupied(path, np.zeros(2, dtype=bool), 1.0)
        self.assertFalse(passing[0])


class EpochTest(unittest.TestCase):
    """States as the authors score them: quiet clear of contact, whisking guarded from it."""

    def test_a_quiet_epoch_touching_a_contact_is_dropped_whole(self) -> None:
        quiet = np.array([[0.0, 2.0], [3.0, 5.0]])
        contacts = np.array([[4.0, 4.1]])
        epochs = ur.state_epochs(quiet, np.full((1, 2), np.nan), contacts)
        self.assertEqual(epochs["quiet"], [(0.0, 2.0)])

    def test_whisking_loses_each_contact_and_a_guard_either_side(self) -> None:
        whisking = np.array([[1.0, 4.0]])
        contacts = np.array([[2.0, 2.5]])
        epochs = ur.state_epochs(np.full((1, 2), np.nan), whisking, contacts)
        guard = ur.CONTACT_GUARD_S
        self.assertEqual(epochs["whisking"], [(1.0, 2.0 - guard), (2.5 + guard, 4.0)])

    def test_missing_epochs_are_nan_rows(self) -> None:
        nothing = np.full((1, 2), np.nan)
        self.assertEqual(ur.state_epochs(nothing, nothing, nothing), {"quiet": [], "whisking": []})

    def test_the_deposit_marks_no_epochs_with_a_lone_nan(self) -> None:
        lone = np.full((1, 1), np.nan)
        quiet = np.array([[0.0, 2.0]])
        self.assertEqual(ur.state_epochs(quiet, lone, lone)["quiet"], [(0.0, 2.0)])


class MeasureTest(unittest.TestCase):
    """One cell in one state, end to end, on a path of the model in volts."""

    result: dict[str, Any]

    @classmethod
    def setUpClass(cls) -> None:
        membrane = uo.Membrane(tau_ms=10.0, mean=-2.0, reset=-2.0, refractory_ms=2.0)
        path, spiking = integrate_and_fire(membrane, 600_000, seed=6)
        volts = -0.050 + 0.004 * path
        epochs = [(0, 300_000), (300_000, 600_000)]
        onsets = int(np.sum(np.diff(spiking.astype(int)) == 1))
        cls.result = ur.measure_state(volts, spiking, epochs, -0.050, onsets, DT_MS)

    def test_the_distance_and_amplitude_are_recovered(self) -> None:
        self.assertAlmostEqual(self.result["sigma_mv"] / 4.0, 1.0, delta=0.1)
        self.assertAlmostEqual(self.result["mean_level"], -2.0, delta=0.15)
        self.assertAlmostEqual(self.result["tau_ms"], 10.0, delta=1.5)

    def test_measured_and_twin_agree_on_a_path_of_the_model(self) -> None:
        for window in self.result["windows"]:
            with self.subTest(window=window["window_ms"]):
                for scale, pair in window["pass_fraction"].items():
                    self.assertAlmostEqual(pair["measured"], pair["twin"], delta=0.02, msg=scale)
        self.assertAlmostEqual(
            self.result["twin_rate_hz"] / self.result["rate_hz"], 1.0, delta=0.25
        )


class SlowMeanTest(unittest.TestCase):
    """A membrane whose mean wanders slowly, as the potential of awake cortex does."""

    result: dict[str, Any]

    @classmethod
    def setUpClass(cls) -> None:
        membrane = uo.Membrane(tau_ms=10.0, mean=-2.5, reset=-2.5, refractory_ms=2.0)
        samples = 1_200_000
        means = -2.5 + 0.7 * ornstein_uhlenbeck(500.0, samples, seed=8)
        path, spiking = integrate_and_fire(membrane, samples, seed=9, means=means)
        volts = -0.050 + 0.004 * path
        epochs = [(k, k + 200_000) for k in range(0, samples, 200_000)]
        onsets = int(np.sum(np.diff(spiking.astype(int)) == 1))
        cls.result = ur.measure_state(volts, spiking, epochs, -0.050, onsets, DT_MS)

    def test_the_fast_noise_is_the_unit(self) -> None:
        self.assertAlmostEqual(self.result["sigma_mv"] / 4.0, 1.0, delta=0.1)
        self.assertAlmostEqual(self.result["tau_ms"], 10.0, delta=1.5)
        self.assertAlmostEqual(self.result["slow_sd"], 0.7, delta=0.15)

    def test_the_twin_predicts_rate_and_occupancy(self) -> None:
        self.assertAlmostEqual(
            self.result["twin_rate_hz"] / self.result["rate_hz"], 1.0, delta=0.25
        )
        for window in self.result["windows"]:
            with self.subTest(window=window["window_ms"]):
                for scale, pair in window["pass_fraction"].items():
                    self.assertAlmostEqual(
                        pair["measured"] / pair["twin"], 1.0, delta=0.2, msg=scale
                    )


if __name__ == "__main__":
    unittest.main()
