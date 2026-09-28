"""Pins the claim each generated numeral supports in the unity paper (U87).

``test_unity_macros.py`` and ``test_unity_estimates.py`` check that the macro
files match the saved summaries. This checks the other half: that the rounded
value a sentence prints states what the sentence claims. ``CHECKLIST`` classes
every macro by the kind of claim its sentences make, so a new macro fails here
until someone decides which way it may round:

* ``declared``: an input copied through, stated as such.
* ``point``: an estimate stated as a value; rounding either way is fine.
* ``lower``: a sentence says "at least" or "or more"; the print never rounds up.
* ``upper``: a sentence says "at most", "below" or "within"; it never rounds down.
* ``range``: an interval stated from both ends; each end rounds outward.
* ``orders``: "below 10^-k"; the printed exponent never exceeds the true one.
"""

import json
import math
import re
import unittest
from typing import Any

import unity_estimates as ue
from unity_estimates import FLUCTUATION_TV, normal_cdf
from unity_macros import FIGURES, render

OCCUPANCY = FIGURES / "unity_occupancy"

CHECKLIST: dict[str, str] = {
    **dict.fromkeys(
        (
            "ueFibreCm ueVelocitySlow ueVelocityFast ueSynapseMs ueContentMs ueReduction "
            "ueVelocityMax ueFieldPeak ueFieldDetection ueLocalCm ueSupplyPercent ueNodeCapFf "
            "ueEpspMv ueEpspCv ueMembraneNoiseMv ueBridgeStepToNoise "
            "uNoiseLow uNoiseMid uNoiseHigh uSideSmall uSideLarge uScalingSideA uScalingSideB "
            "uScalingSideC uOccTauFast uOccTauSlow uOccRateLow uOccRateHigh uOccNextShort "
            "uOccNextLong uOccShiftMax uOccShareMin uOccLatchShortMs uOccLatchLongMs "
            "uOccContentShortMs uOccContentLongMs uOccCarriersFew uOccCarriersMid "
            "uOccCarriersMany uYardLow uYardHigh uCorShareTol uCorPaths uCorShareA uCorShareB "
            "uSwClockGHz uSwActivityLow uSwActivityHigh uSwTransitionPs uSwAperturePs uSwTauPs "
            "uSwDataMHz uWinPerceptMs uWinLongestMs uBrTaskSdLow uBrTaskSdHigh uBrTaskTauShort "
            "uBrTaskTauLong uBrAccHigh uBrAccLow uBrNeuralEffect uBrBlockTrials uRlSigmaLow "
            "uRlSigmaHigh uRlRateLow uRlRateHigh"
        ).split(),
        "declared",
    ),
    **dict.fromkeys(
        (
            "ueConeSlowMs ueConeFastMs ueConeMaxMs ueFieldDeficitOrders ueConeLocalMaxMs "
            "ueConeLocalFastMs ueFieldDeficitLocalOrders ueMarginPercent ueNoiseToMargin "
            "ueFluctuationTV ueThermalNoiseMv ueMarginToNoise ueGradedWindowPercent "
            "ueCorticalShiftToJitter ueCorticalTV ueMatchedNoiseToStep ueNoiseMatchMaxStep "
            "uOrderedRuns uLogarithmicRuns uChordNearestHigh uChordExponentialHigh "
            "uChordSigmaOneHigh uChordSigmaThreeHigh uFarExponentialA uFarExponentialB "
            "uFarExponentialC uFarSigmaOneA uFarSigmaOneB uFarSigmaOneC uFarSigmaThreeA "
            "uFarSigmaThreeB uFarSigmaThreeC uStiffnessRatio uOccDistanceMin uOccDistanceMax "
            "uOccResolutionPercent uYardBinaryCeiling uCorLinkShortTol uSwNodePassMinPercent "
            "uSwNodePassMaxPercent uSwSyncEventsLong uBrTrialsBehaviour uBrTrialsNeural "
            "uBrNnGapPositive uBrNnGapCases"
        ).split(),
        "point",
    ),
    **dict.fromkeys(
        (
            "ueTauSlowMs ueTauLocalMs ueTauFastMs ueBandMatchFailPercent uOccLinkFewLong "
            "uOccLinkMidShort uYardBestMin uYardHitMinHigh uCorLinkMidTol uCorLinkManyTol "
            "uSwMtbfOrders uWinLinkPercept uRlHitRatioMin"
        ).split(),
        "lower",
    ),
    **dict.fromkeys(
        (
            "ueFieldReachMm ueEpspPassMv ueEdgeQuantile ueNoiseMatchFailPercent "
            "ueBridgeMinCutoffHz uHarmonicRatioLow uHarmonicRatioMid uOccInstantLinkMin "
            "uCorMissA uCorMissB uCorMissC uCorResolutionRho uSwSyncPassPercent "
            "uWinLowManyMs uWinLowMidMs uBrGapOtherMax uBrTeTolPercent uBrGapTol uBrNnGapMax "
            "uRlResolutionPercent"
        ).split(),
        "upper",
    ),
    **dict.fromkeys(
        (
            "uOccPassMinPercent uOccPassMaxPercent uOccCountPassMinPercent "
            "uOccCountPassMaxPercent uOccHitMinLong uOccHitMaxLong uBrCutoffMin uBrCutoffMax "
            "uBrGapMin uBrGapMax uBrNnCutoffMin uBrNnCutoffMax uBrCommonTeMinPercent "
            "uBrCommonTeMaxPercent uBrCommonGapMin uBrCommonGapMax uRlTonicPassMinPercent "
            "uRlTonicPassMaxPercent uRlTonicHitMin uRlTonicHitMax uRlBurstPassMinPercent "
            "uRlBurstPassMaxPercent uRlBurstHitMin uRlBurstHitMax"
        ).split(),
        "range",
    ),
    **dict.fromkeys("ueErrorOrders uOccBitOrders uSwNoTransitionOrders".split(), "orders"),
}


def _printed() -> dict[str, float]:
    text = ue.render() + render(FIGURES)
    values = {}
    for name, value in re.findall(r"\\newcommand\{\\(\w+)\}\{(.*)\}", text):
        if "/" in value or "times" in value:
            continue
        values[name] = float(value)
    return values


def _read(name: str) -> dict[str, Any]:
    result: dict[str, Any] = json.loads((OCCUPANCY / name).read_text())
    return result


class ChecklistTest(unittest.TestCase):
    def test_every_generated_macro_is_classed_once(self) -> None:
        text = ue.render() + render(FIGURES)
        names = set(re.findall(r"\\newcommand\{\\(\w+)\}", text))
        self.assertEqual(set(CHECKLIST), names)

    def test_every_generated_result_is_stated_in_the_paper(self) -> None:
        paper = (ue.OUTPUT.parent / "main.tex").read_text(encoding="utf-8")
        names = re.findall(r"\\newcommand\{\\(\w+)\}", render(FIGURES))
        unused = [n for n in names if not re.search(rf"\\{n}(?![A-Za-z])", paper)]
        self.assertEqual(unused, [])


class EstimateBoundsTest(unittest.TestCase):
    def test_each_estimate_rounds_the_way_its_sentence_allows(self) -> None:
        printed, exact = _printed(), ue.estimates()
        for name, kind in CHECKLIST.items():
            key = name[2].lower() + name[3:]
            if not name.startswith("ue") or key not in exact:
                continue
            with self.subTest(macro=name):
                if kind == "lower":
                    self.assertLessEqual(printed[name], exact[key])
                if kind == "upper":
                    self.assertGreaterEqual(printed[name], exact[key])

    def test_the_graded_window_is_where_one_amplitude_reaches_the_fluctuation(self) -> None:
        est = ue.estimates()
        distance = est["gradedWindowPercent"] / 100 * est["marginToNoise"]
        response = normal_cdf(distance) - normal_cdf(distance - 1)
        self.assertAlmostEqual(response, FLUCTUATION_TV, places=12)

    def test_the_printed_cutoff_keeps_the_loop_within_the_tightest_deadline(self) -> None:
        est = ue.estimates()
        tightest = min(est["tauSlowMs"], est["tauFastMs"], est["tauLocalMs"])
        cutoff = _printed()["ueBridgeMinCutoffHz"]
        self.assertLessEqual(1000 / (2 * math.pi * cutoff), tightest)


class OccupancyBoundsTest(unittest.TestCase):
    def test_the_pass_ranges_enclose_every_regime(self) -> None:
        printed = _printed()
        neurons = _read("summary.json")["neurons"]
        timing = [100 * n["pass_fraction"] for n in neurons]
        counted = [
            100 * n["latched_pass_fraction"][f"{n['config']['window_ms']:g}"] for n in neurons
        ]
        for prefix, values in (("uOccPass", timing), ("uOccCountPass", counted)):
            self.assertLessEqual(printed[f"{prefix}MinPercent"], min(values))
            self.assertGreaterEqual(printed[f"{prefix}MaxPercent"], max(values))

    def test_the_visit_range_encloses_every_regime_and_share(self) -> None:
        printed = _printed()
        hits = [
            h["400"]
            for n in _read("summary.json")["neurons"]
            for h in n["window_hit_probability"].values()
        ]
        self.assertLessEqual(printed["uOccHitMinLong"], min(hits))
        self.assertGreaterEqual(printed["uOccHitMaxLong"], max(hits))

    def test_latching_at_either_clock_changes_no_passing_fraction(self) -> None:
        for n in _read("summary.json")["neurons"]:
            for period in ("1", "5"):
                self.assertAlmostEqual(n["latched_pass_fraction"][period], n["pass_fraction"])

    def test_the_membrane_beats_the_highest_yardstick_at_its_best_state(self) -> None:
        swept = _read("yardstick.json")
        best = min(b for n in swept["neurons"] for b in n["best_response"].values())
        self.assertLessEqual(_printed()["uYardBestMin"], best)
        self.assertGreater(best, max(swept["yardsticks"]))

    def test_the_hit_bound_at_the_highest_yardstick_never_rounds_up(self) -> None:
        swept = _read("yardstick.json")
        top = swept["yardsticks"].index(max(swept["yardsticks"]))
        hits = [
            per["400"]
            for n in swept["neurons"]
            for per in n["by_yardstick"][top]["window_hit_probability"].values()
        ]
        self.assertLessEqual(_printed()["uYardHitMinHigh"], min(hits))

    def test_a_lower_yardstick_never_lowers_the_chance_of_a_passing_state(self) -> None:
        swept = _read("yardstick.json")
        order = sorted(range(len(swept["yardsticks"])), key=lambda i: swept["yardsticks"][i])
        for n in swept["neurons"]:
            for share in n["by_yardstick"][0]["window_hit_probability"]:
                hits = [n["by_yardstick"][i]["window_hit_probability"][share]["400"] for i in order]
                for lower, higher in zip(hits, hits[1:], strict=False):
                    self.assertGreaterEqual(lower + 1e-12, higher)


class CorrelatedBoundsTest(unittest.TestCase):
    def _links(self, share: str, window: str, carriers: str) -> list[tuple[float, float]]:
        return [
            (1 - row["probability"], row["standard_error"])
            for n in _read("correlated.json")["neurons"]
            for per in n["by_scale"].values()
            for row in [per[share][window]["no_link"][carriers]]
        ]

    def test_printed_links_are_two_standard_errors_below_every_estimate(self) -> None:
        printed = _printed()
        tol = f"{printed['uCorShareTol']:g}"
        for macro, carriers in (("uCorLinkMidTol", "100"), ("uCorLinkManyTol", "1000")):
            low = min(p - 2 * e for p, e in self._links(tol, "400", carriers))
            self.assertLessEqual(printed[macro], low)

    def test_printed_misses_are_two_standard_errors_above_every_estimate(self) -> None:
        printed = _printed()
        for macro, share in (("uCorMissA", "0.25"), ("uCorMissB", "0.5"), ("uCorMissC", None)):
            key = share or f"{printed['uCorShareTol']:g}"
            high = max(1 - p + 2 * e for p, e in self._links(key, "400", "100"))
            self.assertGreaterEqual(printed[macro], high)

    def test_the_link_holds_at_every_share_below_the_tolerated_one(self) -> None:
        printed = _printed()
        shares = [s for s in _read("correlated.json")["shares"] if s <= printed["uCorShareTol"]]
        for share in shares:
            low = min(p - 2 * e for p, e in self._links(f"{share:g}", "400", "100"))
            self.assertGreaterEqual(low, printed["uCorLinkMidTol"])


class SwitchingClaimsTest(unittest.TestCase):
    def test_the_saved_synchronizer_passes_no_yardstick_above_its_ceiling(self) -> None:
        chip = _read("switching.json")
        sync = chip["synchronizer"]
        self.assertLess(sync["binary_ceiling"], chip["fluctuation_tv"])
        for y, share in zip(chip["yardsticks"], sync["pass_fraction_by_yardstick"], strict=True):
            if y > sync["binary_ceiling"]:
                self.assertEqual(share, 0.0)

    def test_the_saved_latch_passes_at_no_yardstick(self) -> None:
        latched = _read("switching.json")["latched"]["pass_fraction_by_yardstick"]
        self.assertEqual(latched, [0.0] * len(latched))

    def test_the_node_range_lies_inside_the_membrane_range(self) -> None:
        nodes = [100 * n["pass_fraction"] for n in _read("switching.json")["nodes"]]
        membrane = [100 * n["pass_fraction"] for n in _read("summary.json")["neurons"]]
        self.assertGreaterEqual(min(nodes), min(membrane))
        self.assertLessEqual(max(nodes), max(membrane))

    def test_every_window_holds_a_transition_but_for_the_printed_orders(self) -> None:
        printed = _printed()
        for node in _read("switching.json")["nodes"]:
            for value in node["log10_no_transition"].values():
                self.assertGreaterEqual(-value, printed["uSwNoTransitionOrders"])


class WindowClaimsTest(unittest.TestCase):
    def test_the_printed_lower_ends_are_never_earlier_than_the_saved_ones(self) -> None:
        printed, ends = _printed(), _read("window.json")["lower_end_ms"]
        self.assertGreaterEqual(printed["uWinLowManyMs"], ends["1000"])
        self.assertGreaterEqual(printed["uWinLowMidMs"], ends["100"])

    def test_the_lower_end_falls_below_the_shortest_percept(self) -> None:
        swept = _read("window.json")
        self.assertLess(swept["lower_end_ms"]["1000"], swept["percept_low_ms"])

    def test_the_link_at_the_shortest_percept_never_rounds_up(self) -> None:
        link = _read("window.json")["least_link_at_percept_low"]["1000"]
        self.assertLessEqual(_printed()["uWinLinkPercept"], link)
        self.assertGreaterEqual(link, _read("window.json")["level"])


def _enclose(case: unittest.TestCase, low: str, high: str, values: list[float]) -> None:
    printed = _printed()
    case.assertLessEqual(printed[low], min(values))
    case.assertGreaterEqual(printed[high], max(values))


class BridgeClaimsTest(unittest.TestCase):
    def setUp(self) -> None:
        self.bridge = _read("bridge.json")
        self.printed = _printed()
        self.spanning = [
            {**row, "spread": r["spread"]}
            for r in self.bridge["regimes"]
            for row in r["steps"]
            if 2 * r["task"]["sd"] >= row["step"]
        ]
        self.declared = [r for r in self.spanning if r["step"] == self.bridge["declared_step"]]

    def test_the_printed_ranges_enclose_every_spanning_regime(self) -> None:
        linear = [r["linear"] for r in self.declared]
        _enclose(self, "uBrCutoffMin", "uBrCutoffMax", [r["te_cutoff_hz"] for r in linear])
        _enclose(self, "uBrGapMin", "uBrGapMax", [-r["gap"] for r in linear])
        cutoffs = [r["neighbour"]["decodability_cutoff_hz"] for r in self.declared]
        _enclose(self, "uBrNnCutoffMin", "uBrNnCutoffMax", cutoffs)
        common = [r["common"]["neighbour"] for r in self.declared]
        te = [-100 * c["relative_te_excess"] for c in common]
        _enclose(self, "uBrCommonTeMinPercent", "uBrCommonTeMaxPercent", te)
        gap = [-c["decodability_excess"] for c in common]
        _enclose(self, "uBrCommonGapMin", "uBrCommonGapMax", gap)

    def test_every_matched_cutoff_clears_the_floor(self) -> None:
        for row in self.declared:
            self.assertGreater(row["common"]["cutoff_hz"], self.bridge["cutoff_floor_hz"])

    def test_by_the_neighbour_estimator_the_declared_step_has_no_te_match(self) -> None:
        for row in self.declared:
            self.assertTrue(row["neighbour"]["te_above_grid"])

    def test_at_the_common_cutoff_the_analog_loop_is_never_richer(self) -> None:
        tolerance = self.printed["uBrTeTolPercent"] / 100
        for row in self.spanning:
            linear, neighbour = row["common"]["linear"], row["common"]["neighbour"]
            self.assertLessEqual(linear["relative_te_excess"], tolerance)
            self.assertLessEqual(linear["decodability_excess"], 0.0)
            self.assertLess(neighbour["relative_te_excess"], 0.0)
            self.assertLess(neighbour["decodability_excess"], 0.0)

    def test_the_linear_te_match_is_the_common_cutoff(self) -> None:
        for row in self.declared:
            self.assertEqual(row["common"]["cutoff_hz"], row["linear"]["te_cutoff_hz"])

    def test_the_neighbour_gap_counts_and_bound_are_right(self) -> None:
        gaps = [r["neighbour"]["gap"] for r in self.spanning if r["neighbour"]["gap"] is not None]
        self.assertEqual(self.printed["uBrNnGapCases"], len(gaps))
        self.assertEqual(self.printed["uBrNnGapPositive"], sum(g > 0 for g in gaps))
        self.assertGreaterEqual(self.printed["uBrNnGapMax"], max(gaps))

    def test_the_printed_tolerances_are_upper_bounds_and_resolve_the_margins(self) -> None:
        scale = 1.959963984540054 * math.sqrt(
            self.bridge["block_trials"] / self.bridge["trials"]["behaviour"]
        )
        spreads = [r["spread"][e] for r in self.declared for e in ("linear", "neighbour")]
        te = max(s["relative_te_sd"] for s in spreads) * scale
        gap = max(s["gap_sd"] for s in spreads) * scale
        self.assertGreaterEqual(self.printed["uBrTeTolPercent"], 100 * te)
        self.assertGreaterEqual(self.printed["uBrGapTol"], gap)
        self.assertLess(self.printed["uBrGapTol"], self.printed["uBrGapMin"])
        self.assertLess(self.printed["uBrGapTol"], self.printed["uBrCommonGapMin"])
        self.assertLess(self.printed["uBrTeTolPercent"], self.printed["uBrCommonTeMinPercent"])

    def test_the_behavioural_comparison_is_the_weaker(self) -> None:
        trials = self.bridge["trials"]
        self.assertGreater(trials["behaviour"], trials["neural"])


class RelayClaimsTest(unittest.TestCase):
    def setUp(self) -> None:
        self.relay = _read("relay.json")
        self.printed = _printed()

    def test_the_mode_ranges_enclose_every_regime(self) -> None:
        for mode, label in (("tonic", "Tonic"), ("burst", "Burst")):
            cells = [c for c in self.relay["cells"] if c["mode"] == mode]
            passing = [100 * c["pass_fraction"] for c in cells]
            _enclose(self, f"uRl{label}PassMinPercent", f"uRl{label}PassMaxPercent", passing)
            hits = [c["window_hit_probability"]["400"] for c in cells]
            _enclose(self, f"uRl{label}HitMin", f"uRl{label}HitMax", hits)

    def test_tonic_mode_visits_more_often_in_every_regime_and_window(self) -> None:
        burst = {
            json.dumps(c["config"], sort_keys=True): c
            for c in self.relay["cells"]
            if c["mode"] == "burst"
        }
        for tonic in (c for c in self.relay["cells"] if c["mode"] == "tonic"):
            pair = burst[json.dumps(tonic["config"], sort_keys=True)]
            for window, hit in tonic["window_hit_probability"].items():
                ratio = hit / pair["window_hit_probability"][window]
                self.assertGreaterEqual(ratio, self.printed["uRlHitRatioMin"])
                self.assertGreater(ratio, 1.0)

    def test_the_modes_are_matched_in_rate_and_keep_their_calcium_state(self) -> None:
        for cell in self.relay["cells"]:
            self.assertAlmostEqual(cell["rate_hz"], cell["config"]["rate_hz"], delta=0.01)
            if cell["mode"] == "burst":
                self.assertGreater(cell["mean_h"], 0.5)
            else:
                self.assertLess(cell["mean_h"], 0.05)

    def test_the_resolution_check_moves_less_than_the_difference(self) -> None:
        self.assertLess(
            1 + self.printed["uRlResolutionPercent"] / 100, self.printed["uRlHitRatioMin"]
        )


if __name__ == "__main__":
    unittest.main()
