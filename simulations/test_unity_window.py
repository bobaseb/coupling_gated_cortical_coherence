"""Gates on the per-window link at every window length (U94)."""

import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

import unity_occupancy as uo
import unity_window as uw

GRID = uo.Grid(low=-6.0, step=0.1)
MEMBRANE = uo.Membrane(tau_ms=10.0, mean=-1.5, reset=-1.5, refractory_ms=2.0)
DT_MS = 0.2


def _passing() -> np.ndarray:
    table = uo.laws(GRID, MEMBRANE, 10.0, DT_MS)
    return uo.passing_states(table, GRID, 1.0)


class HitCurveTest(unittest.TestCase):
    def test_the_curve_agrees_with_the_single_window_computation(self) -> None:
        passing = _passing()
        curve = uw.hit_curve(GRID, MEMBRANE, passing, 100, DT_MS)
        single = uo.hit_probability(GRID, MEMBRANE, passing, 20.0, DT_MS)
        self.assertAlmostEqual(float(curve[100]), single, places=12)

    def test_a_longer_window_never_lowers_the_chance_of_a_passing_state(self) -> None:
        curve = uw.hit_curve(GRID, MEMBRANE, _passing(), 200, DT_MS)
        self.assertTrue(np.all(np.diff(curve) >= -1e-15))

    def test_the_curve_starts_at_the_stationary_passing_mass(self) -> None:
        passing = _passing()
        curve = uw.hit_curve(GRID, MEMBRANE, passing, 5, DT_MS)
        density = uo.stationary(GRID, MEMBRANE, DT_MS)[0]
        self.assertAlmostEqual(float(curve[0]), float(density @ passing), places=12)

    def test_no_passing_state_is_never_hit(self) -> None:
        none = np.zeros(GRID.nodes.size, dtype=bool)
        self.assertEqual(float(uw.hit_curve(GRID, MEMBRANE, none, 50, DT_MS).max()), 0.0)


class LowerEndTest(unittest.TestCase):
    CURVES = np.array([[0.0, 0.001, 0.002, 0.004, 0.008], [0.0, 0.002, 0.004, 0.008, 0.016]])

    def test_the_lower_end_is_the_first_window_every_curve_links(self) -> None:
        end = uw.lower_end_ms(self.CURVES, carriers=100, level=0.5, dt_ms=1.0)
        self.assertEqual(end, 4.0)
        for curve in self.CURVES:
            self.assertGreaterEqual(uo.link_probability(curve[4], 100), 0.5)
        self.assertLess(uo.link_probability(self.CURVES[0][3], 100), 0.5)

    def test_more_carriers_never_move_the_lower_end_later(self) -> None:
        few = uw.lower_end_ms(self.CURVES, carriers=100, level=0.5, dt_ms=1.0)
        many = uw.lower_end_ms(self.CURVES, carriers=1000, level=0.5, dt_ms=1.0)
        if few is None or many is None:
            self.fail("both carrier counts link within the curves")
        self.assertLessEqual(many, few)

    def test_a_link_never_reached_has_no_lower_end(self) -> None:
        self.assertIsNone(uw.lower_end_ms(self.CURVES, carriers=1, level=0.5, dt_ms=1.0))


class SavedSweepTest(unittest.TestCase):
    def test_a_coarse_sweep_is_saved_with_its_declared_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            uw.write(Path(tmp), uo.Grid(-6.0, 0.2), 0.5, max_ms=50.0)
            saved = json.loads((Path(tmp) / "window.json").read_text())
        self.assertEqual(saved["percept_low_ms"], uw.PERCEPT_LOW_MS)
        self.assertEqual(saved["level"], uw.LEVEL)
        self.assertEqual(len(saved["curves"]), 36)
        self.assertIn("1000", saved["lower_end_ms"])
        self.assertIn("resolution_check", saved)

    def test_the_saved_lower_ends_are_no_earlier_than_at_finer_resolution(self) -> None:
        saved = json.loads((uw.OUTPUT / "window.json").read_text())
        fine = saved["resolution_check"]["lower_end_ms"]
        for carriers, end in saved["lower_end_ms"].items():
            if fine[carriers] is not None:
                self.assertLessEqual(fine[carriers], end)


if __name__ == "__main__":
    unittest.main()
