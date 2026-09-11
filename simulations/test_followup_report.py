"""Saved F5/F6 readouts and reports must reproduce without running either study."""

import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import numpy as np

from followup_report import f5_report, f6_report
from plasticity_study import DESIGN, ROOT as F5_ROOT, physical_config, score_pair
from recovery_mechanisms import ROOT as F6_ROOT, confusion_summary


class FollowupReportTest(unittest.TestCase):
    def test_saved_f5_scores_are_recomputed_from_complete_interval_checkpoints(self) -> None:
        summary = json.loads((F5_ROOT / "summary.json").read_text())
        self.assertEqual(summary["design_sha256"], hashlib.sha256(DESIGN.read_bytes()).hexdigest())
        frozen_path = F5_ROOT / "20260910_frozen_rate0_dt0.01_interval0.5.npz"
        with np.load(frozen_path, allow_pickle=False) as checkpoint:
            frozen = dict(checkpoint)
        for row in summary["tuning"]:
            name = f"{row['seed']}_gradient_rate{row['learning_rate']:g}_dt{row['dt']:g}"
            name += f"_interval{row['update_interval']:g}.npz"
            with np.load(F5_ROOT / name, allow_pickle=False) as checkpoint:
                result = dict(checkpoint)
            config = physical_config(
                row["seed"], row["learning_rate"], row["update_interval"], row["dt"]
            )
            for key, value in score_pair(result, frozen, config).items():
                self.assertEqual(row[key], value)

    def test_f6_confusion_is_derived_from_recorded_fits_and_keeps_ties(self) -> None:
        summary = json.loads((F6_ROOT / "summary.json").read_text())
        self.assertEqual(summary["design_sha256"], hashlib.sha256(DESIGN.read_bytes()).hexdigest())
        for key, value in confusion_summary(summary["cases"]).items():
            self.assertEqual(summary[key], value)
        self.assertEqual(summary["uniquely_correct"], [0, 0, 0])

    def test_reports_have_no_simulation_dependency_and_do_not_drift(self) -> None:
        with patch("plasticity_study.simulate", side_effect=AssertionError("integration")):
            for root, render in ((F5_ROOT, f5_report), (F6_ROOT, f6_report)):
                summary = json.loads((root / "summary.json").read_text())
                self.assertEqual((root / "REPORT.md").read_text(), render(summary))
        self.assertEqual(Path(F5_ROOT).parent, Path(F6_ROOT).parent)


if __name__ == "__main__":
    unittest.main()
