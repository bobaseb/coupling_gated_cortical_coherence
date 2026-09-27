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
        self.assertIn("\\uYardBestMin", text)
        self.assertIn("\\uCorShareTol", text)
        self.assertIn("figures/unity_occupancy/", text)

    def test_the_switching_chip_is_generated_from_its_summary(self) -> None:
        text = render(FIGURES)
        self.assertIn("\\newcommand{\\uSwNodePassMinPercent}{0.02}", text)
        self.assertIn("\\newcommand{\\uSwNodePassMaxPercent}{0.5}", text)
        self.assertIn("\\newcommand{\\uSwNoTransitionOrders}{100}", text)
        self.assertIn("\\newcommand{\\uSwSyncPassPercent}{0.2}", text)
        self.assertIn("\\newcommand{\\uSwSyncEventsLong}{8\\times10^{5}}", text)
        self.assertIn("\\newcommand{\\uSwMtbfOrders}{29}", text)

    def test_the_restored_bit_is_reported_as_a_round_bound(self) -> None:
        self.assertIn("\\newcommand{\\uOccBitOrders}{100}", render(FIGURES))

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
        yardstick = json.loads((FIGURES / "unity_occupancy" / "yardstick.json").read_text())
        if change == "nonfinite_best":
            yardstick["neurons"][0]["best_response"]["1"] = float("nan")
        if change == "no_yardsticks":
            yardstick["yardsticks"] = []
        (root / "unity_occupancy").mkdir()
        (root / "unity_occupancy" / "summary.json").write_text(json.dumps(occupancy))
        (root / "unity_occupancy" / "yardstick.json").write_text(json.dumps(yardstick))
        correlated = json.loads((FIGURES / "unity_occupancy" / "correlated.json").read_text())
        if change == "nonfinite_correlated":
            first = correlated["neurons"][0]["by_scale"]["1"]["0.5"]["400"]
            first["no_link"]["100"]["probability"] = float("nan")
        if change == "no_correlated":
            correlated["neurons"] = []
        (root / "unity_occupancy" / "correlated.json").write_text(json.dumps(correlated))
        switching = json.loads((FIGURES / "unity_occupancy" / "switching.json").read_text())
        if change == "no_nodes":
            switching["nodes"] = []
        (root / "unity_occupancy" / "switching.json").write_text(json.dumps(switching))
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

    def test_a_nonfinite_best_response_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("nonfinite_best"))

    def test_a_missing_yardstick_sweep_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("no_yardsticks"))

    def test_a_nonfinite_correlated_link_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("nonfinite_correlated"))

    def test_a_missing_correlated_sweep_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("no_correlated"))

    def test_a_switching_summary_without_nodes_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("no_nodes"))

    def test_printed_bounds_never_overstate_the_sweep(self) -> None:
        values = dict(
            entry.split("}{", 1)
            for entry in render(FIGURES).replace("\\newcommand{\\", "\n").splitlines()
            if "}{" in entry
        )
        swept = json.loads((FIGURES / "unity_occupancy" / "correlated.json").read_text())
        share = values["uCorShareTol"].rstrip("}")
        links = [
            1.0 - per[share]["400"]["no_link"]["100"]["probability"]
            for n in swept["neurons"]
            for per in n["by_scale"].values()
        ]
        self.assertLessEqual(float(values["uCorLinkMidTol"].rstrip("}")), min(links))
        misses = [1.0 - v for v in links]
        self.assertGreaterEqual(float(values["uCorMissC"].rstrip("}")), max(misses))

    def test_the_occupancy_ranges_are_ordered(self) -> None:
        values = dict(
            entry.split("}{", 1)
            for entry in render(FIGURES).replace("\\newcommand{\\", "\n").splitlines()
            if "}{" in entry
        )
        low = float(values["uOccPassMinPercent"].rstrip("}"))
        high = float(values["uOccPassMaxPercent"].rstrip("}"))
        self.assertLess(low, high)

    def test_a_reader_that_discards_every_spike_time_still_finds_passing_states(self) -> None:
        values = dict(
            entry.split("}{", 1)
            for entry in render(FIGURES).replace("\\newcommand{\\", "\n").splitlines()
            if "}{" in entry
        )
        low = float(values["uOccCountPassMinPercent"].rstrip("}"))
        high = float(values["uOccCountPassMaxPercent"].rstrip("}"))
        self.assertGreater(low, 0.0)
        self.assertLessEqual(high, float(values["uOccPassMaxPercent"].rstrip("}")))
        summary = json.loads((FIGURES / "unity_occupancy" / "summary.json").read_text())
        shortest = min(n["config"]["window_ms"] for n in summary["neurons"])
        for n in summary["neurons"]:
            if n["config"]["window_ms"] == shortest:
                counted = n["latched_pass_fraction"][f"{shortest:g}"]
                self.assertAlmostEqual(counted, n["pass_fraction"], places=12)

    def test_a_nonfinite_value_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            render(self._mutated("nonfinite"))


if __name__ == "__main__":
    unittest.main()
