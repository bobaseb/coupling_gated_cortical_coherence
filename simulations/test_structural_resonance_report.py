"""Saved-artifact reporting must not integrate trajectories."""

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from structural_resonance_report import render_report


class ReportTest(unittest.TestCase):
    def test_report_regeneration(self) -> None:
        root = Path(__file__).parent / "figures" / "structural_resonance"
        with TemporaryDirectory() as directory:
            output = Path(directory) / "report.md"
            render_report(root, output)
            self.assertEqual(output.read_text(), (root / "REPORT.md").read_text())


if __name__ == "__main__":
    unittest.main()
