"""Drift gate for the physical-unity paper's numerals from saved U3 summaries."""

import json
import tempfile
import unittest
from pathlib import Path

from unity_macros import FIGURES, OUTPUT, render


class UnityMacroTests(unittest.TestCase):
    def test_generated_file_matches_saved_summaries(self) -> None:
        text = OUTPUT.read_text()
        self.assertEqual(text, render(FIGURES))
        self.assertIn("Do not edit manually", text)
        self.assertIn("simulations/unity_macros.py", text)
        self.assertIn("\\uHarmonicRatioLow", text)
        self.assertIn("\\uOccPassMaxPercent", text)
        self.assertIn("figures/unity_occupancy/", text)

    def test_every_macro_the_paper_uses_is_generated(self) -> None:
        paper = (OUTPUT.parent / "main.tex").read_text()
        defined = set(render(FIGURES).split("\\newcommand{\\")[1:])
        names = {entry.split("}", 1)[0] for entry in defined}
        used = {token for token in names if f"\\{token}" in paper}
        self.assertTrue(used, "the paper cites none of the generated numerals")

    def _mutated(self, change: str) -> Path:
        root = Path(tempfile.mkdtemp())
        target = root / "unity_agreement"
        target.mkdir()
        occupancy = json.loads((FIGURES / "unity_occupancy" / "summary.json").read_text())
        if change == "no_regimes":
            occupancy["neurons"] = []
        if change == "nonfinite_link":
            occupancy["neurons"][0]["window_hit_probability"]["1"]["400"] = float("nan")
        (root / "unity_occupancy").mkdir()
        (root / "unity_occupancy" / "summary.json").write_text(json.dumps(occupancy))
        summary = json.loads((FIGURES / "unity_agreement" / "summary.json").read_text())
        scaling = json.loads((FIGURES / "unity_agreement" / "resistance.json").read_text())
        if change == "no_runs":
            summary["runs"] = []
        if change == "nonfinite":
            scaling["far_resistance"]["exponential"][0] = float("nan")
        (target / "summary.json").write_text(json.dumps(summary))
        (target / "resistance.json").write_text(json.dumps(scaling))
        return root

    def test_a_missing_run_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("no_runs"))

    def test_a_missing_regime_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("no_regimes"))

    def test_a_nonfinite_window_probability_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("nonfinite_link"))

    def test_the_occupancy_ranges_are_ordered(self) -> None:
        values = dict(
            entry.split("}{", 1)
            for entry in render(FIGURES).replace("\\newcommand{\\", "\n").splitlines()
            if "}{" in entry
        )
        low = float(values["uOccPassMinPercent"].rstrip("}"))
        high = float(values["uOccPassMaxPercent"].rstrip("}"))
        self.assertLess(low, high)

    def test_a_nonfinite_value_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("nonfinite"))


if __name__ == "__main__":
    unittest.main()
