"""Gates on the relay cell's occupancy in tonic and burst mode (U99)."""

import json
import math
import tempfile
import unittest
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import erfcx

import unity_relay as ur

COARSE = ur.Resolution(dv_per_sigma=0.1, dh=0.05, dt_ms=0.2)
# The mean inactivation each mode keeps: de-inactivated in burst mode, not in tonic.
MEAN_H: dict[ur.Mode, tuple[float, float]] = {"burst": (0.5, 1.0), "tonic": (0.0, 0.05)}


def siegert_rate(rest: float, sigma: float) -> float:
    """The leaky integrate-and-fire rate in Hz, for a membrane of stationary SD ``sigma``."""
    scale = sigma * math.sqrt(2.0)
    lower, upper = (ur.VRESET - rest) / scale, (ur.VTH - rest) / scale
    mean_isi, _ = quad(lambda u: erfcx(-u), lower, upper)
    return float(1000.0 / (ur.TAU_MS * math.sqrt(math.pi) * mean_isi))


class DynamicsTest(unittest.TestCase):
    def test_no_mass_is_created_by_a_step(self) -> None:
        cell = ur.RelayCell(sigma_mv=2.0, bias=0.0, resolution=COARSE)
        kept = np.asarray(cell.surviving.sum(axis=0)).ravel()
        self.assertTrue(np.all(kept <= 1.0 + 1e-9))
        self.assertTrue(np.allclose(kept + cell.spiking, 1.0))

    def test_the_t_current_deinactivates_below_its_threshold_and_inactivates_above(self) -> None:
        below, above = ur.next_h(np.array([-70.0, -50.0]), np.array([0.5, 0.5]), 1.0)
        self.assertGreater(below, 0.5)
        self.assertLess(above, 0.5)

    def test_a_deinactivated_cell_pushed_past_the_t_threshold_bursts(self) -> None:
        cell = ur.RelayCell(sigma_mv=2.0, bias=-0.1, resolution=COARSE)
        table = cell.laws(10.0)
        below = table[:, cell.index(ur.VH - 3.0, 1.0)]
        above = table[:, cell.index(ur.VH + 1.0, 1.0)]
        self.assertGreater(1.0 - above[-1], 0.9)
        self.assertLess(1.0 - below[-1], 0.5)

    def test_in_tonic_mode_the_grid_reproduces_the_integrate_and_fire_rate(self) -> None:
        for sigma in (2.0, 4.0):
            with self.subTest(sigma=sigma):
                rest = -40.0
                cell = ur.RelayCell(sigma, ur.bias_for_rest(rest), ur.DEFAULT)
                _, rate = cell.stationary()
                self.assertLess(abs(rate / siegert_rate(rest, sigma) - 1.0), 0.05)

    def test_the_stationary_law_is_a_probability(self) -> None:
        cell = ur.RelayCell(sigma_mv=2.0, bias=0.0, resolution=COARSE)
        mass, rate = cell.stationary()
        self.assertAlmostEqual(float(mass.sum()), 1.0, places=9)
        self.assertGreater(rate, 0.0)


class ModeTest(unittest.TestCase):
    def test_each_mode_is_calibrated_to_the_rate_and_keeps_its_t_current_state(self) -> None:
        for mode, (low, high) in MEAN_H.items():
            with self.subTest(mode=mode):
                cell = ur.calibrate(mode, sigma_mv=4.0, rate_hz=2.0, resolution=COARSE)
                mass, rate = cell.stationary()
                self.assertAlmostEqual(rate, 2.0, delta=0.02)
                mean_h = float(mass @ cell.h_of_state)
                self.assertGreaterEqual(mean_h, low)
                self.assertLessEqual(mean_h, high)

    def test_burst_mode_passes_with_its_current_deinactivated_and_tonic_without(self) -> None:
        for mode, (low, high) in MEAN_H.items():
            with self.subTest(mode=mode):
                cell = ur.calibrate(mode, sigma_mv=4.0, rate_hz=2.0, resolution=COARSE)
                mass, _ = cell.stationary()
                passing = cell.passing(10.0)
                self.assertGreater(float(mass @ passing), 0.0)
                where = cell.h_of_state[passing]
                weights = mass[passing]
                centre = float(where @ weights / weights.sum())
                self.assertGreaterEqual(centre, low)
                self.assertLessEqual(centre, high)


class SavedTest(unittest.TestCase):
    def test_a_coarse_run_is_saved_with_both_modes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ur.write(
                Path(tmp),
                sigmas_mv=(4.0,),
                rates_hz=(2.0,),
                windows_ms=(10.0,),
                resolution=COARSE,
                check=False,
            )
            saved = json.loads((Path(tmp) / "relay.json").read_text())
        modes = {row["mode"] for row in saved["cells"]}
        self.assertEqual(modes, {"burst", "tonic"})
        for row in saved["cells"]:
            self.assertIn("pass_fraction", row)
            for hit in row["window_hit_probability"].values():
                self.assertGreaterEqual(hit, 0.0)
                self.assertLessEqual(hit, 1.0)


if __name__ == "__main__":
    unittest.main()
