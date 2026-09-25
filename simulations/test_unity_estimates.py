"""Gates on the physical-unity paper's closed-form magnitude estimates."""

import math
import re
import unittest

import unity_estimates as ue


class WindowTest(unittest.TestCase):
    def test_the_cone_delay_is_conduction_plus_one_synapse(self) -> None:
        self.assertAlmostEqual(ue.cone_delay(0.15, 5.0, 0.0005), 0.0305)

    def test_the_required_rate_reaches_the_reduction_within_the_remaining_time(self) -> None:
        rate = ue.required_rate(reduction=10.0, content_time=0.4, cone=0.03)
        self.assertAlmostEqual(rate * (0.4 - 0.03), math.log(10.0))

    def test_a_cone_longer_than_the_content_leaves_no_window(self) -> None:
        with self.assertRaises(ValueError):
            ue.required_rate(reduction=10.0, content_time=0.02, cone=0.03)

    def test_slow_fibres_give_the_later_edge(self) -> None:
        estimates = ue.estimates()
        self.assertGreater(estimates["coneSlowMs"], estimates["coneFastMs"])
        self.assertLess(estimates["tauSlowMs"], estimates["tauFastMs"])

    def test_the_fastest_axons_set_the_strict_deadline(self) -> None:
        estimates = ue.estimates()
        self.assertLess(estimates["coneMaxMs"], estimates["coneFastMs"])


class FieldTest(unittest.TestCase):
    def test_the_field_reaches_detection_at_its_reach(self) -> None:
        reach = ue.field_reach(peak=2.0, detection=0.25, near=1.0, exponent=3.0)
        self.assertAlmostEqual(reach, 2.0)
        self.assertAlmostEqual(
            ue.field_deficit_orders(ue.estimates()["fieldReachMm"]), 0.0, places=9
        )

    def test_the_field_misses_detection_across_the_cortex(self) -> None:
        self.assertGreater(ue.estimates()["fieldDeficitOrders"], 1.0)


class HardwareTest(unittest.TestCase):
    def test_expected_supply_variation_sits_inside_the_margin(self) -> None:
        self.assertLess(ue.estimates()["noiseToMargin"], 1.0)


class GeneratedFileTest(unittest.TestCase):
    def test_the_committed_file_matches_the_script(self) -> None:
        self.assertEqual(ue.OUTPUT.read_text(encoding="utf-8"), ue.render())
        self.assertIn("simulations/unity_estimates.py", ue.render())
        self.assertIn("Do not edit manually", ue.render())

    def test_every_generated_macro_is_stated_in_the_paper(self) -> None:
        paper = (ue.OUTPUT.parent / "main.tex").read_text(encoding="utf-8")
        names = re.findall(r"\\newcommand\{\\(\w+)\}", ue.render())
        unused = [n for n in names if not re.search(rf"\\{n}(?![A-Za-z])", paper)]
        self.assertEqual(unused, [])


if __name__ == "__main__":
    unittest.main()
