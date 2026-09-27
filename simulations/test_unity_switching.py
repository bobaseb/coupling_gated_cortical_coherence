"""Gates on the per-window noise-floor test of a clocked chip, transients included (U75)."""

import json
import math
import tempfile
import unittest
from pathlib import Path

import unity_switching as us
from unity_estimates import FLUCTUATION_TV, normal_cdf, tv_of_shift


class NodeTimingTest(unittest.TestCase):
    def test_a_change_moves_the_crossing_by_its_size_in_jitters_whatever_the_slew(self) -> None:
        for slew in (0.1, 1.0, 50.0):
            self.assertAlmostEqual(us.crossing_response(2.0, slew), tv_of_shift(2.0))

    def test_one_noise_amplitude_moves_the_crossing_by_the_fluctuation(self) -> None:
        self.assertAlmostEqual(us.crossing_response(1.0, 3.0), FLUCTUATION_TV)

    def test_a_node_passes_on_the_rising_half_of_each_transition(self) -> None:
        fraction = us.node_pass_fraction(activity=0.1, clock_hz=1e9, transition_s=20e-12)
        self.assertAlmostEqual(fraction, 0.1 * 1e9 * 10e-12)

    def test_a_busier_node_passes_more_often(self) -> None:
        low = us.node_pass_fraction(0.02, 1e9, 20e-12)
        high = us.node_pass_fraction(0.5, 1e9, 20e-12)
        self.assertLess(low, high)

    def test_a_window_sees_a_transition_unless_every_cycle_is_idle(self) -> None:
        self.assertAlmostEqual(us.log10_no_transition(0.5, cycles=3), 3 * math.log10(0.5))
        self.assertLess(us.log10_no_transition(0.02, cycles=4e7), -100)

    def test_the_node_passes_at_the_fluctuation_and_no_higher_yardstick(self) -> None:
        self.assertTrue(us.node_passes(FLUCTUATION_TV))
        self.assertFalse(us.node_passes(0.45))


class LatchTest(unittest.TestCase):
    def test_a_latched_node_read_at_its_rail_passes_nowhere(self) -> None:
        latched = us.latched_summary()
        self.assertEqual(latched["pass_fraction"], 0.0)
        self.assertLess(latched["log10_max_response"], -100)


class SynchronizerTest(unittest.TestCase):
    def test_the_mtbf_reproduces_ginosars_28nm_example(self) -> None:
        years = us.mtbf_years(
            resolution_s=1e-9, tau_s=10e-12, aperture_s=20e-12, clock_hz=1e9, data_hz=1e8
        )
        self.assertAlmostEqual(math.log10(years), math.log10(4e29), delta=0.1)

    def test_the_metastable_rate_is_ginosars_first_example(self) -> None:
        rate = us.metastable_rate(aperture_s=20e-12, clock_hz=1e9, data_hz=1e8)
        self.assertAlmostEqual(rate, 2e6)

    def test_a_sample_falls_in_the_aperture_at_most_at_the_data_rate_times_its_width(self) -> None:
        self.assertAlmostEqual(us.synchronizer_pass_bound(20e-12, 1e8), 2e-3)

    def test_its_bit_reaches_at_most_the_binary_ceiling_below_the_fluctuation(self) -> None:
        self.assertAlmostEqual(us.BINARY_CEILING, normal_cdf(1.0) - 0.5)
        self.assertLess(us.BINARY_CEILING, FLUCTUATION_TV)

    def test_the_synchronizer_passes_no_yardstick_above_the_binary_ceiling(self) -> None:
        self.assertTrue(us.synchronizer_passes(0.3))
        self.assertFalse(us.synchronizer_passes(FLUCTUATION_TV))

    def test_the_summary_counts_the_synchronizer_only_up_to_the_ceiling(self) -> None:
        sync = us.run()["synchronizer"]
        bound = sync["pass_fraction_bound"]
        for y, share in zip(
            us.run()["yardsticks"], sync["pass_fraction_by_yardstick"], strict=True
        ):
            self.assertEqual(share, bound if y <= us.BINARY_CEILING else 0.0)


class NoiseLawTest(unittest.TestCase):
    def test_a_symmetric_single_peaked_bit_peaks_with_its_threshold_at_the_state(self) -> None:
        for name, cdf in us.NOISE_LAWS.items():
            with self.subTest(law=name):
                self.assertAlmostEqual(us.bit_ceiling(cdf), cdf(1.0) - 0.5, delta=1e-3)

    def test_the_gaussian_ceiling_is_the_binary_ceiling(self) -> None:
        self.assertAlmostEqual(us.bit_ceiling(us.NOISE_LAWS["gaussian"]), us.BINARY_CEILING, 3)

    def test_each_law_has_unit_standard_deviation(self) -> None:
        for name, cdf in us.NOISE_LAWS.items():
            with self.subTest(law=name):
                self.assertAlmostEqual(us.variance(cdf), 1.0, delta=2e-2)

    def test_one_bit_stays_below_exactly_when_the_centre_holds_less_than_twice_it(self) -> None:
        for name, cdf in us.NOISE_LAWS.items():
            with self.subTest(law=name):
                centre = cdf(1.0) - cdf(-1.0)
                self.assertEqual(us.bit_ceiling(cdf) < FLUCTUATION_TV, centre < 2 * FLUCTUATION_TV)

    def test_gaussian_logistic_and_laplace_stay_below_and_student_three_does_not(self) -> None:
        below = {name: us.bit_ceiling(cdf) < FLUCTUATION_TV for name, cdf in us.NOISE_LAWS.items()}
        self.assertEqual(
            below, {"gaussian": True, "logistic": True, "laplace": True, "student3": False}
        )


class WordTest(unittest.TestCase):
    def test_a_word_responds_no_more_than_the_quantity_it_reads(self) -> None:
        for thresholds in ((0.0,), (-0.5, 0.5), (-1.0, 0.0, 1.0), (-0.3, -0.1, 0.1, 0.3)):
            for stage_noise in (0.0, 0.2, 1.0):
                for change in (1.0, -1.0, 2.0):
                    with self.subTest(t=thresholds, s=stage_noise, c=change):
                        response = us.word_response(thresholds, change, stage_noise)
                        self.assertLessEqual(response, tv_of_shift(change) + 1e-6)

    def test_one_threshold_is_one_bit_under_the_binary_ceiling(self) -> None:
        self.assertAlmostEqual(us.word_response((0.0,), 1.0, 0.0), us.BINARY_CEILING, 4)

    def test_thresholds_half_an_amplitude_either_side_reach_the_fluctuation(self) -> None:
        for change in (1.0, -1.0):
            self.assertAlmostEqual(us.word_response((-0.5, 0.5), change, 0.0), FLUCTUATION_TV, 4)

    def test_stage_noise_only_lowers_the_word_response(self) -> None:
        clean = us.word_response((-0.5, 0.5), 1.0, 0.0)
        self.assertLess(us.word_response((-0.5, 0.5), 1.0, 0.5), clean)

    def test_the_summary_records_both_hardware_cases(self) -> None:
        summary = us.run()
        self.assertEqual(set(summary["noise_laws"]), set(us.NOISE_LAWS))
        self.assertLessEqual(summary["word"]["best_response"], FLUCTUATION_TV + 1e-6)


class SummaryTest(unittest.TestCase):
    def test_the_summary_is_json_and_covers_every_declared_activity(self) -> None:
        summary = us.run()
        text = json.dumps(summary)
        self.assertEqual(json.loads(text), summary)
        self.assertEqual([n["activity"] for n in summary["nodes"]], list(us.ACTIVITIES))

    def test_every_yardstick_is_evaluated_at_every_level(self) -> None:
        summary = us.run()
        for node in summary["nodes"]:
            self.assertEqual(len(node["pass_fraction_by_yardstick"]), len(summary["yardsticks"]))
        self.assertEqual(
            len(summary["latched"]["pass_fraction_by_yardstick"]), len(summary["yardsticks"])
        )

    def test_the_saved_summary_is_what_the_script_writes(self) -> None:
        saved = json.loads((us.OUTPUT / "switching.json").read_text())
        self.assertEqual(saved, json.loads(json.dumps(us.run())))

    def test_main_writes_the_summary(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            us.write(Path(root))
            self.assertTrue((Path(root) / "switching.json").exists())


if __name__ == "__main__":
    unittest.main()
