"""Checks for the two-frequency periodic-density G22 extension."""

import tempfile
import unittest
from pathlib import Path
from typing import cast

import numpy as np

from g22_current_sim import Config, run_protocol
from g22_heterogeneous import (
    HeteroConfig,
    run_heterogeneous,
    run_heterogeneous_grid,
    save_heterogeneous,
)
from g22_heterogeneous_report import summarize_heterogeneous, write_heterogeneous_summary


class HeterogeneousCurrentTests(unittest.TestCase):
    def test_report_rejects_cost_drift_from_saved_cohort_flux(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "hetero.npz"
            save_heterogeneous(
                path, run_heterogeneous(HeteroConfig(cells=32, duration=0.2, spread=0.1))
            )
            with np.load(path, allow_pickle=False) as saved:
                artifact = {name: saved[name] for name in saved.files}
            artifact["accumulated_cohort_cost"][1:] *= 1.5
            np.savez(path, **artifact)
            with self.assertRaisesRegex(ValueError, "current cost"):
                summarize_heterogeneous(path)

    def test_grid_and_artifact_only_summary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            paths = run_heterogeneous_grid(
                output, diffusions=(0.25,), spreads=(0.0, 0.1), schedules=("early",)
            )
            self.assertEqual(len(paths), 2)
            rows = [summarize_heterogeneous(path) for path in paths]
            self.assertEqual([row["spread"] for row in rows], [0.0, 0.1])
            for row in rows:
                self.assertGreaterEqual(
                    cast(float, row["cohort_cost"]), cast(float, row["marginal_cost"])
                )
            write_heterogeneous_summary(output / "summary.json", paths)
            self.assertTrue((output / "summary.json").exists())

    def test_zero_spread_recovers_homogeneous_path(self) -> None:
        config = HeteroConfig(cells=48, duration=0.4, diffusion=0.5, spread=0.0)
        result = run_heterogeneous(config)
        homogeneous = run_protocol(Config(cells=48, duration=0.4, diffusion=0.5))
        np.testing.assert_allclose(result.order, homogeneous.order, atol=1e-12)
        np.testing.assert_allclose(result.accumulated_marginal_cost, homogeneous.accumulated_cost)
        np.testing.assert_allclose(result.accumulated_cohort_cost, homogeneous.accumulated_cost)

    def test_moderate_spread_conserves_mass_and_bounds_order_change(self) -> None:
        for spread in (0.1, 0.3):
            with self.subTest(spread=spread):
                result = run_heterogeneous(
                    HeteroConfig(cells=64, duration=1.0, diffusion=0.25, spread=spread)
                )
                self.assertGreater(result.density.min(), 0)
                np.testing.assert_allclose(
                    result.density.sum(axis=2) * result.spacing, 1, atol=1e-10
                )
                self.assertGreaterEqual(
                    result.accumulated_marginal_cost[-1] + 2e-3, result.endpoint_bound
                )
                self.assertGreaterEqual(
                    result.accumulated_cohort_cost[-1] + 1e-10,
                    result.accumulated_marginal_cost[-1],
                )

    def test_uniform_rotating_cohorts_have_zero_marginal_cost(self) -> None:
        result = run_heterogeneous(
            HeteroConfig(cells=48, duration=0.4, initial_order=0.0, spread=0.3)
        )
        self.assertLess(np.max(np.abs(result.order)), 1e-12)
        self.assertLess(abs(result.accumulated_marginal_cost[-1]), 1e-12)
        self.assertGreater(result.accumulated_cohort_cost[-1], 0)

    def test_artifact_records_both_costs(self) -> None:
        result = run_heterogeneous(HeteroConfig(cells=32, duration=0.2, spread=0.1))
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "heterogeneous.npz"
            save_heterogeneous(path, result)
            with np.load(path, allow_pickle=False) as data:
                self.assertIn("accumulated_marginal_cost", data.files)
                self.assertIn("accumulated_cohort_cost", data.files)
                self.assertAlmostEqual(float(data["spread"]), 0.1)


if __name__ == "__main__":
    unittest.main()
