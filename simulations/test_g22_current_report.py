"""Checks that G22 reporting reads saved trajectories and preserves provenance."""

import tempfile
import unittest
from typing import cast
from pathlib import Path

import numpy as np

from g22_current_report import (
    first_upcrossing,
    onset_cost_summary,
    summarize_artifact,
    write_summary,
)
from g22_current_sim import Config, run_protocol, save_protocol


class ReportTests(unittest.TestCase):
    def test_onset_cost_uses_crossing_time_and_partial_ledger(self) -> None:
        result = onset_cost_summary(
            np.array([0.0, 1.0]),
            np.array([0.2, 0.4]),
            np.array([0.0, 0.4]),
            diffusion=0.5,
            threshold=0.3,
        )
        self.assertIsNotNone(result)
        result = cast(dict[str, float], result)
        self.assertAlmostEqual(result["time"], 0.5)
        self.assertAlmostEqual(result["cost"], 0.2)
        expected = (np.arcsin(0.3) - np.arcsin(0.2)) ** 2 / 0.25
        self.assertAlmostEqual(result["bound"], expected)
        self.assertGreater(result["cost"], result["bound"])

    def test_exploratory_onset_crossing_and_control(self) -> None:
        crossing = first_upcrossing(np.array([0.0, 1.0]), np.array([0.2, 0.4]), 0.3)
        self.assertIsNotNone(crossing)
        self.assertAlmostEqual(cast(float, crossing), 0.5)
        self.assertIsNone(first_upcrossing(np.array([0.0, 1.0]), np.array([0.2, 0.25]), 0.3))
        with tempfile.TemporaryDirectory() as directory:
            early = Path(directory) / "early.npz"
            late = Path(directory) / "late.npz"
            save_protocol(
                early,
                run_protocol(Config(cells=48, duration=1.0, diffusion=0.25, schedule="early")),
            )
            save_protocol(
                late,
                run_protocol(Config(cells=48, duration=1.0, diffusion=0.25, schedule="late")),
            )
            self.assertIsNotNone(summarize_artifact(early)["exploratory_onset_time_r0p3"])
            self.assertIsNone(summarize_artifact(late)["exploratory_onset_time_r0p3"])

    def test_saved_artifact_summary_and_slack(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "linear.npz"
            save_protocol(path, run_protocol(Config(cells=32, duration=0.3)))
            summary = summarize_artifact(path)
            self.assertEqual(summary["schedule"], "linear")
            self.assertEqual(summary["cells"], 32)
            self.assertGreater(cast(float, summary["cost"]), cast(float, summary["endpoint_bound"]))
            self.assertLess(cast(float, summary["mass_error_max"]), 1e-10)
            self.assertGreater(cast(float, summary["density_min"]), 0)
            output = Path(directory) / "summary.json"
            write_summary(output, [path])
            self.assertIn('"linear"', output.read_text())

    def test_reject_truncated_or_corrupt_cost(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.npz"
            np.savez(path, time=np.array([0.0, 1.0]))
            with self.assertRaises(ValueError):
                summarize_artifact(path)

    def test_reject_inconsistent_saved_endpoint_bound(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad_bound.npz"
            save_protocol(path, run_protocol(Config(cells=32, duration=0.3)))
            with np.load(path, allow_pickle=False) as saved:
                artifact = {name: saved[name] for name in saved.files}
            artifact["endpoint_bound"] = np.array(-1.0)
            np.savez(path, **artifact)
            with self.assertRaises(ValueError):
                summarize_artifact(path)

    def test_reject_corrupted_positive_cost_or_density_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "corrupt.npz"
            save_protocol(path, run_protocol(Config(cells=32, duration=0.3)))
            with np.load(path, allow_pickle=False) as saved:
                artifact = {name: saved[name] for name in saved.files}
            artifact["accumulated_cost"][1:] *= 1.5
            np.savez(path, **artifact)
            with self.assertRaisesRegex(ValueError, "current cost"):
                summarize_artifact(path)
            save_protocol(path, run_protocol(Config(cells=32, duration=0.3)))
            with np.load(path, allow_pickle=False) as saved:
                artifact = {name: saved[name] for name in saved.files}
            artifact["density"][1] = np.roll(artifact["density"][1], 1)
            np.savez(path, **artifact)
            with self.assertRaisesRegex(ValueError, "continuity"):
                summarize_artifact(path)


if __name__ == "__main__":
    unittest.main()
