"""Every finished S5 run is regenerable from the files it left behind."""

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from geometric_frustration import ROOT
from geometric_frustration_report import rebuild

# Every tracked run directory, and the figures its own status calls for: a
# failed baseline gate has no sweep to plot a transition or a phase pair from.
RUNS = {
    ROOT: ("baseline.png",),
    ROOT / "smoke": ("baseline.png",),
    ROOT / "weak_smoke": ("baseline.png", "transition.png", "phases.png"),
    ROOT / "weak_seed20261905": ("baseline.png", "transition.png", "phases.png"),
    ROOT / "weak_seed20262905": ("baseline.png", "transition.png", "phases.png"),
    ROOT / "weak_seed20263905": ("baseline.png", "transition.png", "phases.png"),
}


class ReportTest(unittest.TestCase):
    def test_every_tracked_run_regenerates_its_own_report(self) -> None:
        for source, figures in RUNS.items():
            with self.subTest(run=source.name or source.parent.name), TemporaryDirectory() as tmp:
                output = Path(tmp)
                rebuild(source, output)

                self.assertEqual(
                    (output / "FRUSTRATION_REPORT.md").read_text(),
                    (source / "FRUSTRATION_REPORT.md").read_text(),
                )
                self.assertEqual(sorted(p.name for p in output.glob("*.png")), sorted(figures))


if __name__ == "__main__":
    unittest.main()
