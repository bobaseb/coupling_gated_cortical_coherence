import math
import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

import numpy as np
from matplotlib.collections import PathCollection

from dynamic_ramp_report import (
    FIGURE_DIR,
    SizeMetrics,
    Leg,
    _followup_report,
    _plot_bifurcation,
    _size_metrics,
    adiabatic_onset_exponent,
)


class FollowupReportTest(unittest.TestCase):
    def test_saved_followup_report_matches_completed_summaries(self) -> None:
        generated = _followup_report(
            FIGURE_DIR / "tighter_threshold_summary.json",
            FIGURE_DIR / "hetero" / "hetero_summary.json",
        )
        self.assertIn(generated, (FIGURE_DIR / "DYNAMIC_RAMP_REPORT.md").read_text())

    def test_completed_controls_state_nonconvergence_and_censoring(self) -> None:
        def row(
            exponent: float | None, fit_legs: int, matched_exponent: float | None = 0.5
        ) -> dict[str, object]:
            return {
                "complete": True,
                "n_artifacts": 8,
                "n_fit_legs": fit_legs,
                "missing_speeds": [],
                "exponent_ols": exponent,
                "matched_exponent_ols": matched_exponent,
                "rms_log_residual": 0.24 if exponent == 0.720 else 0.06,
                "leave_one_out_exponents": [0.68, 0.76] if exponent == 0.720 else [0.43, 0.47],
                "largest_precritical_order": 0.30,
                "largest_initial_order": 0.04,
                "largest_coupling_step": 0.01,
                "censored_replicas": 9,
            }

        with TemporaryDirectory() as directory:
            threshold = Path(directory) / "threshold.json"
            hetero = Path(directory) / "hetero.json"
            threshold.write_text(
                json.dumps(
                    {
                        "N2000_r0.20": row(0.444, 6),
                        "N2000_r0.05": row(0.637, 8),
                        "N8000_r0.05": row(0.720, 7),
                    }
                )
            )
            hetero.write_text(
                json.dumps(
                    {
                        "1.5": {
                            "complete": True,
                            "n_artifacts": 4,
                            "n_fit_legs": 2,
                            "missing_speeds": [],
                            "exponent": None,
                        }
                    }
                )
            )
            report = _followup_report(threshold, hetero)
        self.assertIn("does not show convergence toward 0.5", report)
        self.assertIn("log-residual RMS", report)
        self.assertIn("precritical order", report)
        self.assertNotIn("residuals must be inspected", report)
        self.assertIn("fit censored", report)

    def test_missing_sweeps_are_reported_as_pending(self) -> None:
        with TemporaryDirectory() as directory:
            threshold = Path(directory) / "threshold.json"
            hetero = Path(directory) / "hetero.json"
            threshold.write_text(
                json.dumps(
                    {
                        "N8000_r0.05": {
                            "complete": False,
                            "n_artifacts": 1,
                            "n_fit_legs": 1,
                            "missing_speeds": [0.1],
                            "exponent_ols": None,
                        }
                    }
                )
            )
            hetero.write_text(
                json.dumps(
                    {
                        "0.5": {
                            "complete": False,
                            "n_artifacts": 0,
                            "n_fit_legs": 0,
                            "missing_speeds": [0.1],
                            "exponent": None,
                        }
                    }
                )
            )
            paragraph = _followup_report(threshold, hetero)
        self.assertIn("pending", paragraph)
        self.assertIn("N8000_r0.05", paragraph)
        self.assertNotIn("None", paragraph)


class AdiabaticReferenceTest(unittest.TestCase):
    def test_estimator_on_the_stationary_branch_falls_short_of_one_half(self) -> None:
        coupling = np.linspace(1.5, 2.5, 101)

        reference = adiabatic_onset_exponent(coupling)

        self.assertLess(reference, 0.5)
        self.assertAlmostEqual(reference, 0.443, places=3)


class SizeControlTest(unittest.TestCase):
    def test_scaled_delay_divides_by_the_predicted_size_dependence(self) -> None:
        metrics = SizeMetrics(
            n_oscillators=8000,
            delay_mean=0.2341,
            delay_error=0.0,
            precritical_order_max=0.1,
        )

        self.assertAlmostEqual(metrics.scaled_delay, 0.2341 / math.sqrt(math.log(8000)))

    def test_smallest_population_reaches_the_escape_level_before_threshold(self) -> None:
        sizes = _size_metrics()

        self.assertEqual([item.n_oscillators for item in sizes], [500, 2000, 8000])
        self.assertGreater(sizes[0].precritical_order_max, 0.2)
        self.assertLess(sizes[-1].precritical_order_max, 0.2)


class BifurcationFigureTest(unittest.TestCase):
    def test_shows_replica_escape_points_at_recorded_order(self) -> None:
        coupling = np.array([1.9, 2.0, 2.1, 2.2, 2.3, 2.4, 2.5])
        replicas = np.array(
            [
                [0.01, 0.01],
                [0.02, 0.02],
                [0.22, 0.10],
                [0.23, 0.23],
                [0.24, 0.25],
                [0.25, 0.26],
                [0.26, 0.27],
            ]
        )
        leg = Leg(
            speed=0.01,
            n_oscillators=2000,
            coupling=coupling,
            order_mean=replicas.mean(axis=1),
            order_std=replicas.std(axis=1),
            order_replicas=replicas,
            concentration_mean=np.zeros(coupling.size),
            concentration_replicas=np.zeros_like(replicas),
        )

        with patch("dynamic_ramp_report._save_figure") as save:
            _plot_bifurcation([leg])

        figure = save.call_args.args[0]
        points = [
            collection.get_offsets()
            for collection in figure.axes[0].collections
            if isinstance(collection, PathCollection)
        ]
        self.assertEqual(len(points), 1)
        self.assertEqual(np.asarray(points[0]).tolist(), [[2.1, 0.22], [2.2, 0.23]])


if __name__ == "__main__":
    unittest.main()
