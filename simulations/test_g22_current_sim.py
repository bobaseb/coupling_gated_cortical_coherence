"""Regression tests for the conservative G22 phase-density pilot."""

import tempfile
import unittest
from pathlib import Path
from typing import cast

import numpy as np

from g22_current_report import first_upcrossing
from g22_current_sim import (
    Config,
    run_onset_resolution,
    run_parameter_grid,
    run_protocol,
    save_protocol,
)


class CurrentSimulationTests(unittest.TestCase):
    def test_onset_resolution_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paths = run_onset_resolution(Path(directory), cells=(32, 64))
            self.assertEqual(len(paths), 2)
            with np.load(paths[0], allow_pickle=False) as first:
                self.assertEqual(int(first["cells"]), 32)
                self.assertAlmostEqual(float(first["diffusion"]), 0.25)

    def test_exploratory_onset_time_refines_with_grid(self) -> None:
        times = []
        for cells in (32, 48, 64, 96):
            result = run_protocol(
                Config(cells=cells, duration=1.0, diffusion=0.25, schedule="early")
            )
            onset = first_upcrossing(result.time, result.order, 0.3)
            self.assertIsNotNone(onset)
            times.append(cast(float, onset))
        self.assertLess(abs(times[-1] - times[-2]), abs(times[-2] - times[0]))

    def test_parameter_grid_saves_distinct_reproducible_protocols(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paths = run_parameter_grid(
                Path(directory), cells=32, diffusions=(0.25, 0.5), durations=(0.4,)
            )
            self.assertEqual(len(paths), 10)  # Three ramps and two controls per D.
            self.assertEqual(len(set(paths)), len(paths))
            for path in paths:
                with np.load(path, allow_pickle=False) as data:
                    self.assertEqual(int(data["cells"]), 32)
                    self.assertAlmostEqual(float(data["duration"]), 0.4)
                    self.assertIn(float(data["diffusion"]), (0.25, 0.5))
                    self.assertGreater(data["density"].min(), 0)
                    self.assertGreaterEqual(
                        float(data["accumulated_cost"][-1]) + 2e-3,
                        float(data["endpoint_bound"]),
                    )

    def test_uniform_path_has_zero_current_and_order(self) -> None:
        result = run_protocol(
            Config(
                cells=48,
                duration=0.4,
                diffusion=0.5,
                initial_order=0.0,
                start_coupling=0.0,
                end_coupling=2.0,
                schedule="linear",
            )
        )
        self.assertLess(np.max(np.abs(result.order)), 1e-12)
        self.assertLess(np.max(np.abs(result.current)), 1e-12)
        self.assertLess(abs(result.accumulated_cost[-1]), 1e-12)
        np.testing.assert_allclose(result.density.sum(axis=1) * result.spacing, 1, atol=1e-12)

    def test_ordered_relaxation_and_cost_bound(self) -> None:
        result = run_protocol(
            Config(
                cells=64,
                duration=0.6,
                diffusion=0.5,
                initial_order=0.2,
                start_coupling=0.0,
                end_coupling=0.0,
                schedule="linear",
            )
        )
        self.assertLess(result.order[-1], result.order[0])
        self.assertGreater(result.accumulated_cost[-1], 0)
        self.assertGreaterEqual(result.accumulated_cost[-1] + 2e-3, result.endpoint_bound)
        self.assertTrue(np.all(result.density > 0))
        np.testing.assert_allclose(result.density.sum(axis=1) * result.spacing, 1, atol=1e-10)

    def test_relaxation_converges_under_grid_refinement(self) -> None:
        exact = 0.2 * np.exp(-0.5)
        errors = [
            abs(
                run_protocol(
                    Config(
                        cells=cells,
                        duration=1.0,
                        diffusion=0.5,
                        initial_order=0.2,
                        start_coupling=0.0,
                        end_coupling=0.0,
                    )
                ).order[-1]
                - exact
            )
            for cells in (32, 64, 128)
        ]
        self.assertGreater(errors[0], errors[1])
        self.assertGreater(errors[1], errors[2])

    def test_equal_endpoints_distinct_schedules_and_artifact(self) -> None:
        early = run_protocol(
            Config(
                cells=48,
                duration=1.0,
                diffusion=0.5,
                initial_order=0.2,
                start_coupling=0.4,
                end_coupling=2.0,
                schedule="early",
            )
        )
        late = run_protocol(
            Config(
                cells=48,
                duration=1.0,
                diffusion=0.5,
                initial_order=0.2,
                start_coupling=0.4,
                end_coupling=2.0,
                schedule="late",
            )
        )
        self.assertAlmostEqual(early.coupling[0], late.coupling[0])
        self.assertAlmostEqual(early.coupling[-1], late.coupling[-1])
        self.assertNotAlmostEqual(early.order[-1], late.order[-1])
        self.assertGreaterEqual(early.accumulated_cost[-1] + 2e-3, early.endpoint_bound)
        self.assertGreaterEqual(late.accumulated_cost[-1] + 2e-3, late.endpoint_bound)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "pilot.npz"
            save_protocol(path, early)
            with np.load(path) as data:
                for key in (
                    "time",
                    "density",
                    "current",
                    "order",
                    "coupling",
                    "accumulated_cost",
                    "endpoint_bound",
                    "duration",
                    "diffusion",
                    "cells",
                    "initial_order",
                ):
                    self.assertIn(key, data.files)
                np.testing.assert_allclose(data["density"], early.density)

    def test_bound_and_conservation_across_diffusion_and_ramp_duration(self) -> None:
        for diffusion in (0.25, 0.5, 1.0):
            for duration in (0.4, 1.0):
                for schedule in ("early", "linear", "late"):
                    with self.subTest(diffusion=diffusion, duration=duration, schedule=schedule):
                        result = run_protocol(
                            Config(
                                cells=48,
                                diffusion=diffusion,
                                duration=duration,
                                schedule=schedule,
                            )
                        )
                        self.assertGreater(result.density.min(), 0)
                        np.testing.assert_allclose(
                            result.density.sum(axis=1) * result.spacing, 1, atol=1e-10
                        )
                        self.assertGreaterEqual(
                            result.accumulated_cost[-1] + 2e-3, result.endpoint_bound
                        )
                        self.assertTrue(np.all(np.diff(result.accumulated_cost) >= -1e-14))

    def test_reject_unstable_or_nonpositive_input(self) -> None:
        with self.assertRaises(ValueError):
            run_protocol(Config(cells=32, initial_order=0.5))
        with self.assertRaises(ValueError):
            run_protocol(Config(cells=32, diffusion=0.0))


if __name__ == "__main__":
    unittest.main()
