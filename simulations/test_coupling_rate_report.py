import json
import tempfile
import unittest
from pathlib import Path
from typing import Any

import coupling_rate_report as report


ERROR: dict[str, Any] = {
    "config": {"diffusion": 1.0, "tolerance": 0.005, "start_offset": 0.02},
    "legs": {
        "crossing": {
            "start": 1.8,
            "end": 2.2,
            "delta": 0.0,
            "admissible_speed": None,
            "required_ratio": None,
            "worst_residual": 0.39,
            "worst_residual_coupling": 2.2,
            "worst_residual_speed": 1.0,
            "runs": [
                {"speed": 0.01, "terminal_error": 0.39, "max_error": 0.39},
                {"speed": 1.0, "terminal_error": 0.39, "max_error": 0.39},
            ],
        },
        "subcritical_0.4": {
            "start": 1.4,
            "end": 1.6,
            "delta": 0.4,
            "admissible_speed": 0.03,
            "required_ratio": 66.7,
            "worst_residual": 0.02,
            "worst_residual_coupling": 1.4,
            "worst_residual_speed": 1.0,
            "runs": [
                {"speed": 0.01, "terminal_error": 0.0001, "max_error": 0.02},
                {"speed": 1.0, "terminal_error": 0.019, "max_error": 0.02},
            ],
        },
    },
    "criterion": [
        {"leg": "crossing", "delta": 0.0, "admissible_speed": None, "required_ratio": None},
        {"leg": "subcritical_0.4", "delta": 0.4, "admissible_speed": 0.03, "required_ratio": 66.7},
    ],
    "bifurcation_delay": {
        "speeds": [0.1, 0.01, 0.001, 0.0001],
        "coupling_excess": [0.94, 0.30, 0.10, 0.044],
        "exponent": 0.447,
        "uncensored_speeds": [0.01, 0.001, 0.0001],
        "uncensored_exponent": 0.418,
        "criterion_scan": [
            {"escape": 0.2, "coupling_excess": [0.94, 0.30, 0.10, 0.044]},
            {"escape": 0.1, "coupling_excess": [0.78, 0.25, 0.08, 0.027]},
            {"escape": 0.05, "coupling_excess": [0.57, 0.18, 0.058, 0.019]},
        ],
        "seed_order": 0.0224,
        "escape_level": 0.2,
    },
    "controls": {
        "stationary_drift": 1.1e-16,
        "step_halving": 4.4e-6,
        "frozen_rejected": True,
        "frozen_leg": "supercritical_0.4",
        "frozen_comparison": {"0.01": 0.07},
    },
    "manuscript": {
        "cited_ratio_range": [600.0, 60000.0],
        "trackable_delta_at_slow_end": 0.8,
        "trackable_delta_at_fast_end": 0.05,
    },
}


def _drive(process: str, tau: float, mean: float, amplitude: float, order: float) -> dict[str, Any]:
    return {
        "process": process,
        "mean": mean,
        "amplitude": amplitude,
        "correlation_time": tau,
        "measured_order": order,
        "order_spread": 0.01,
        "mean_substitution": 0.0 if mean <= 2.0 else 0.5,
        "quasi_static_average": 0.3,
        "negative_fraction": 0.0,
        "horizon": 100.0,
        "crosses_threshold": amplitude > 0.3,
        "closer": "mean" if tau < 1.0 else "quasi_static",
        "orders_below_mean_threshold": mean <= 2.0 and order > 0.02,
        "self_averaging": False,
        "visits_negative_coupling": process == "ornstein_uhlenbeck",
    }


NOISE: dict[str, Any] = {
    "config": {"seed_order": 0.02},
    "processes": ["telegraph", "ornstein_uhlenbeck"],
    "amplitudes": [0.25, 1.0],
    "correlation_times": [0.03, 30.0],
    "mean_couplings": [1.8, 2.4],
    "drives": [
        _drive(process, tau, mean, amplitude, 0.09 if mean <= 2.0 else 0.5)
        for process in ("telegraph", "ornstein_uhlenbeck")
        for tau in (0.03, 30.0)
        for mean in (1.8, 2.4)
        for amplitude in (0.25, 1.0)
    ],
    "fast_limit": {
        "correlation_time": 0.03,
        "worst_mean_substitution_gap": 0.035,
        "worst_quasi_static_gap": 0.34,
    },
    "slow_limit": {
        "correlation_time": 30.0,
        "drives": 8,
        "worst_mean_substitution_gap": 0.084,
        "worst_quasi_static_gap": 0.0197,
    },
    "crossover": [],
    "mean_substitution_rejection": {
        "criterion": "the mean coupling is at or below K_c",
        "count": 8,
        "rejected": True,
        "strongest": _drive("telegraph", 3.0, 1.8, 1.0, 0.09),
    },
    "controls": {
        "step_halving": 0.0034,
        "step_halving_drive": {},
        "extended_horizon": {"horizon": 720.0, "measured_order": 0.039},
    },
}


class LoadTest(unittest.TestCase):
    def test_a_missing_summary_says_which_run_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):
                report.load(Path(directory), "quasistatic_error_summary.json")

    def test_a_saved_summary_round_trips(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "summary.json"
            path.write_text(json.dumps(ERROR), encoding="utf-8")
            self.assertEqual(
                report.load(Path(directory), "summary.json")["criterion"], ERROR["criterion"]
            )


class FormatTest(unittest.TestCase):
    def test_a_quantity_that_does_not_exist_is_printed_as_such(self) -> None:
        # `None` in these summaries means the admissible speed does not exist at
        # that distance, which is the finding and not a gap in the table.
        self.assertEqual(report._format(None), "none")
        self.assertEqual(report._format(0.001234567), "0.001235")
        self.assertEqual(report._format(True), "True")


class ReportTest(unittest.TestCase):
    def test_the_report_carries_every_leg_and_both_limits(self) -> None:
        text = report.build_report(ERROR, NOISE)
        for leg in ERROR["legs"]:
            self.assertIn(leg, text)
        self.assertIn("0.447", text)
        self.assertIn("fast", text)
        self.assertIn("slow", text)

    def test_the_report_fits_every_escape_criterion_over_the_uncensored_legs(self) -> None:
        """The scan's point, in the report that carries it.

        Each level is fitted over the legs the published fit uses, so the three
        numbers are comparable to each other and to the ensemble's. A fit over
        all four speeds of this fixture would mix in the censored leg and the
        approach to 1/2 would be reading something else.
        """
        text = report.build_report(ERROR, NOISE)
        line = next(item for item in text.splitlines() if item.startswith("Against the escape"))

        for entry in ERROR["bifurcation_delay"]["criterion_scan"]:
            self.assertIn(f"r >= {entry['escape']:g}", line)
        self.assertIn("**0.417**", line)
        self.assertIn("**0.488**", line)

    def test_the_report_says_the_crossing_leg_has_no_admissible_speed(self) -> None:
        text = report.build_report(ERROR, NOISE)
        crossing = next(line for line in text.splitlines() if line.startswith("| crossing"))
        self.assertIn("none", crossing)

    def test_the_report_states_the_rejection_and_its_horizon_control(self) -> None:
        text = report.build_report(ERROR, NOISE)
        self.assertIn("refused in **8** drives", text)
        self.assertIn("720", text)

    def test_the_report_says_the_gaussian_coupling_is_not_clipped(self) -> None:
        # Clipping would move the mean, which is the statistic under test, so
        # the report has to say what was done instead.
        self.assertIn("not clipped", report.build_report(ERROR, NOISE))

    def test_the_figures_are_written_without_recomputing_anything(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            error_path = Path(directory) / "error.png"
            noise_path = Path(directory) / "noise.png"
            report.error_figure(ERROR, error_path)
            report.noise_figure(NOISE, noise_path)
            self.assertGreater(error_path.stat().st_size, 0)
            self.assertGreater(noise_path.stat().st_size, 0)


if __name__ == "__main__":
    unittest.main()
