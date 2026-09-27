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


class ExtentTest(unittest.TestCase):
    def test_a_localized_extent_shortens_the_deadline(self) -> None:
        estimates = ue.estimates()
        self.assertLess(estimates["localCm"], estimates["fibreCm"])
        self.assertLess(estimates["coneLocalMaxMs"], estimates["coneMaxMs"])
        self.assertLess(estimates["coneLocalFastMs"], estimates["coneFastMs"])

    def test_a_localized_extent_leaves_more_time_to_settle(self) -> None:
        estimates = ue.estimates()
        self.assertGreater(estimates["tauLocalMs"], estimates["tauFastMs"])

    def test_the_field_falls_short_of_a_localized_extent_by_less(self) -> None:
        estimates = ue.estimates()
        self.assertLess(estimates["fieldDeficitLocalOrders"], estimates["fieldDeficitOrders"])
        self.assertGreater(estimates["fieldDeficitLocalOrders"], 0.0)


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


class BridgeTest(unittest.TestCase):
    def test_the_analog_arm_passes_exactly_when_its_noise_is_at_most_the_regions(self) -> None:
        self.assertTrue(ue.analog_passes(region_noise=1.0, loop_noise=1.0))
        self.assertTrue(ue.analog_passes(region_noise=1.0, loop_noise=0.5))
        self.assertFalse(ue.analog_passes(region_noise=1.0, loop_noise=1.01))

    def test_the_quantized_arm_fails_beyond_its_fail_distance(self) -> None:
        for recording in (0.01, 0.3, 1.0):
            far = ue.fail_distance(region_noise=1.0, recording_noise=recording)
            for distance in (far, 1.5 * far, 5 * far):
                response = ue.edge_response(distance, 1.0, recording)
                self.assertLess(response, ue.FLUCTUATION_TV)

    def test_the_quantized_arm_passes_close_to_an_edge(self) -> None:
        self.assertGreater(ue.edge_response(0.5, 1.0, 0.1), ue.FLUCTUATION_TV)

    def test_the_noise_matched_analog_loop_has_the_entropy_matched_noise(self) -> None:
        self.assertAlmostEqual(ue.matched_noise(1.0), 1 / math.sqrt(2 * math.pi * math.e))

    def test_noise_matching_separates_the_arms_at_about_half_the_states(self) -> None:
        ceiling = ue.bridge()["noiseMatchFailPercent"]
        self.assertAlmostEqual(ceiling, 100 * (1 - 2 / math.sqrt(2 * math.pi * math.e)))
        self.assertLess(ceiling, 55.0)

    def test_bandwidth_matching_separates_them_at_most_states(self) -> None:
        self.assertGreater(ue.bridge()["bandMatchFailPercent"], 70.0)
        coarse = ue.quantized_fail_fraction(step=20.0, region_noise=1.0, recording_noise=1.0)
        fine = ue.quantized_fail_fraction(step=10.0, region_noise=1.0, recording_noise=1.0)
        self.assertGreater(coarse, fine)
        self.assertEqual(ue.quantized_fail_fraction(1.0, 1.0, 1.0), 0.0)

    def test_the_slowest_admissible_loop_settles_within_the_tightest_deadline(self) -> None:
        self.assertAlmostEqual(ue.loop_min_cutoff_hz(1 / (2 * math.pi)), 1.0)
        est = ue.estimates()
        tightest = min(est["tauSlowMs"], est["tauFastMs"], est["tauLocalMs"])
        cutoff = est["bridgeMinCutoffHz"]
        self.assertAlmostEqual(1000 / (2 * math.pi * cutoff), tightest)


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
