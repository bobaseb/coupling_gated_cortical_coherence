"""Drift gate for G22–G24 publication numerals from saved summaries."""

import json
import tempfile
import unittest
from pathlib import Path

from g_followup_macros import FIGURES, OUTPUT, render


class FollowupMacroTests(unittest.TestCase):
    def test_generated_file_matches_saved_summaries(self) -> None:
        self.assertEqual(OUTPUT.read_text(), render(FIGURES))
        self.assertIn("Do not edit manually", OUTPUT.read_text())

    def test_missing_onset_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = FIGURES / "g22_onset_resolution" / "summary.json"
            output = root / "g22_onset_resolution"
            output.mkdir()
            summary = json.loads(source.read_text())
            summary["protocols"] = []
            (output / "summary.json").write_text(json.dumps(summary))
            with self.assertRaises(ValueError):
                render(root)


if __name__ == "__main__":
    unittest.main()
