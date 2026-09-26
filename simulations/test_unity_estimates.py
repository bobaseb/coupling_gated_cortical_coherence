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


class NoiseFloorTest(unittest.TestCase):
    def test_the_fluctuation_is_the_gaussian_one_sigma_shift(self) -> None:
        self.assertEqual(ue.tv_of_shift(0.0), 0.0)
        self.assertAlmostEqual(ue.FLUCTUATION_TV, 2 * ue.normal_cdf(0.5) - 1)
        self.assertAlmostEqual(ue.FLUCTUATION_TV, 0.3829, places=4)
        self.assertLess(ue.tv_of_shift(0.5), ue.tv_of_shift(1.0))

    def test_the_tail_is_continuous_across_its_asymptotic_switch(self) -> None:
        for x in (1.0, 5.0, 20.0):
            exact = math.log10(0.5 * math.erfc(x / math.sqrt(2)))
            self.assertAlmostEqual(ue.log10_gaussian_tail(x), exact, places=6)
        below = ue.log10_gaussian_tail(ue.TAIL_SWITCH - 1e-9)
        above = ue.log10_gaussian_tail(ue.TAIL_SWITCH + 1e-9)
        self.assertAlmostEqual(below, above, places=3)

    def test_the_inverse_tail_returns_the_argument(self) -> None:
        z = ue.inverse_gaussian_tail(ue.FLUCTUATION_TV)
        self.assertAlmostEqual(0.5 * math.erfc(z / math.sqrt(2)), ue.FLUCTUATION_TV)

    def test_the_digital_response_at_the_noise_scale_is_far_below_the_fluctuation(self) -> None:
        estimates = ue.estimates()
        self.assertGreater(estimates["marginToNoise"], 10.0)
        self.assertGreater(estimates["errorOrders"], 10.0)
        self.assertLess(estimates["gradedWindowPercent"], 1.0)

    def test_the_cortical_carrier_passes_at_a_unitary_epsp(self) -> None:
        estimates = ue.estimates()
        self.assertGreater(estimates["corticalShiftToJitter"], 1.0)
        self.assertGreater(estimates["corticalTV"], ue.FLUCTUATION_TV)

    def test_every_input_above_the_smallest_passing_one_passes(self) -> None:
        least = ue.smallest_passing_input(cv=0.52, noise=0.54)
        self.assertAlmostEqual(ue.shift_to_jitter(least, 0.52, 0.54), 1.0)
        for scale in (1.01, 2.0, 10.0):
            self.assertGreater(ue.shift_to_jitter(scale * least, 0.52, 0.54), 1.0)
        with self.assertRaises(ValueError):
            ue.smallest_passing_input(cv=1.0, noise=0.54)

    def test_the_slope_cancels_from_shift_over_jitter(self) -> None:
        self.assertAlmostEqual(ue.shift_to_jitter(epsp=1.0, cv=0.0, noise=0.5), 2.0)
        self.assertAlmostEqual(ue.shift_to_jitter(epsp=1.0, cv=0.3, noise=0.4), 2.0)


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
