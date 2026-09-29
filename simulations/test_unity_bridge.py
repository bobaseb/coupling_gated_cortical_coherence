"""Gates on the bridge's feasibility: matching the loops and counting trials (U95, U98)."""

import json
import math
import tempfile
import unittest
from pathlib import Path

import numpy as np

import unity_bridge as ub
import unity_estimates as ue

SMALL = ub.Task(sd=5.0, tau_ms=100.0)


class LoopTest(unittest.TestCase):
    def test_a_first_order_filter_passes_a_constant_unchanged(self) -> None:
        out = ub.lowpass(np.ones((1, 2000)), 10.0)
        self.assertAlmostEqual(float(out[0, -1]), 1.0, places=6)

    def test_the_quantizer_reads_the_nearest_step(self) -> None:
        values = ub.quantize(np.array([0.4, 0.6, -1.6, 7.4]), 1.0)
        self.assertEqual(values.tolist(), [0.0, 1.0, -2.0, 7.0])

    def test_the_same_seed_gives_the_same_trials(self) -> None:
        first = ub.simulate(SMALL, ub.Loop("analog", 10.0), trials=4, seed=3)
        second = ub.simulate(SMALL, ub.Loop("analog", 10.0), trials=4, seed=3)
        self.assertTrue(np.array_equal(first.recorded_b, second.recorded_b))


class InformationTest(unittest.TestCase):
    def test_a_lower_cutoff_carries_less_transfer_entropy(self) -> None:
        low = ub.evaluate(SMALL, ub.Loop("analog", 2.0), trials=60, seed=0)["linear"]
        high = ub.evaluate(SMALL, ub.Loop("analog", 200.0), trials=60, seed=0)["linear"]
        self.assertLess(low.transfer_entropy, high.transfer_entropy)

    def test_a_coarser_step_carries_less_of_both(self) -> None:
        fine = ub.evaluate(SMALL, ub.Loop("quantized", 5.0), trials=60, seed=0)["linear"]
        coarse = ub.evaluate(SMALL, ub.Loop("quantized", 30.0), trials=60, seed=0)["linear"]
        self.assertLess(coarse.transfer_entropy, fine.transfer_entropy)
        self.assertLess(coarse.decodability, fine.decodability)

    def test_transfer_entropy_of_independent_series_is_near_zero(self) -> None:
        rng = np.random.default_rng(0)
        te = ub.transfer_entropy(rng.standard_normal((50, 400)), rng.standard_normal((50, 400)))
        self.assertLess(abs(te), 0.5)

    def test_decodability_is_a_share_of_variance(self) -> None:
        score = ub.evaluate(SMALL, ub.Loop("analog", 50.0), trials=60, seed=0)[
            "linear"
        ].decodability
        self.assertGreater(score, 0.0)
        self.assertLess(score, 1.0)


class NeighbourTest(unittest.TestCase):
    def test_independent_series_carry_no_neighbour_transfer_entropy(self) -> None:
        rng = np.random.default_rng(0)
        te = ub.transfer_entropy_neighbours(
            rng.standard_normal((200, 400)), rng.standard_normal((200, 400))
        )
        self.assertLess(abs(te), 10.0)

    def test_on_the_linear_loop_both_estimators_agree(self) -> None:
        block = ub.simulate(SMALL, ub.Loop("analog", 50.0), trials=100, seed=0)
        linear = ub.transfer_entropy(block.recorded_a, block.recorded_b)
        neighbour = ub.transfer_entropy_neighbours(block.recorded_a, block.recorded_b)
        self.assertLess(abs(neighbour / linear - 1), 0.15)
        self.assertLess(
            abs(
                ub.decodability_neighbours(block.task, block.recorded_b)
                - ub.decodability(block.task, block.recorded_b)
            ),
            0.05,
        )

    def test_the_neighbour_estimator_sees_the_quantizer_s_timing(self) -> None:
        block = ub.simulate(SMALL, ub.Loop("quantized", 10.0), trials=100, seed=0)
        linear = ub.transfer_entropy(block.recorded_a, block.recorded_b)
        neighbour = ub.transfer_entropy_neighbours(block.recorded_a, block.recorded_b)
        self.assertGreater(neighbour, 1.15 * linear)

    def test_every_loop_is_measured_by_both_estimators(self) -> None:
        measured = ub.evaluate(SMALL, ub.Loop("analog", 50.0), trials=40, seed=0)
        self.assertEqual(set(measured), set(ub.ESTIMATORS))


class HeldTest(unittest.TestCase):
    def test_a_held_level_sits_near_a_step_centre_for_the_whole_trial(self) -> None:
        block = ub.simulate(ub.held(2), ub.Loop("quantized", ub.DECLARED_STEP), trials=50, seed=0)
        self.assertTrue(np.all(block.task == block.task[:, :1]))
        offset = block.task[:, 0] - ub.DECLARED_STEP * np.round(block.task[:, 0] / ub.DECLARED_STEP)
        self.assertLessEqual(float(np.abs(offset).max()), ub.HELD_SPREAD)
        self.assertEqual(float(np.abs(block.task).max() // ub.DECLARED_STEP), 2.0)

    def test_a_held_task_records_the_spread_of_its_levels(self) -> None:
        self.assertAlmostEqual(ub.held(1).sd, ub.DECLARED_STEP * math.sqrt(2 / 3), places=0)

    def test_one_trial_is_one_content_window(self) -> None:
        self.assertAlmostEqual(ub.TRIAL_STEPS * ub.DT_S, ue.CONTENT_TIME_S)


class VisitTest(unittest.TestCase):
    def test_a_continuous_task_visits_the_passing_band_in_almost_every_window(self) -> None:
        self.assertGreater(ub.visit_fraction(SMALL, ub.DECLARED_STEP, trials=100, seed=0), 0.9)

    def test_a_held_task_rarely_visits_it(self) -> None:
        self.assertLess(ub.visit_fraction(ub.held(2), ub.DECLARED_STEP, trials=200, seed=0), 0.3)

    def test_a_coarser_step_is_visited_less_often(self) -> None:
        task = ub.held(1)
        fine = ub.visit_fraction(task, 8.0, trials=200, seed=0)
        coarse = ub.visit_fraction(task, 20.0, trials=200, seed=0)
        self.assertLess(coarse, fine)


class RelabelTest(unittest.TestCase):
    """U107: a session's relabelling moves the stimuli and the quantizer's levels together."""

    def test_an_offset_quantizer_reads_the_nearest_shifted_level(self) -> None:
        values = ub.quantize(np.array([0.4, 0.6, -1.6]), 1.0, offset=0.5)
        self.assertEqual(values.tolist(), [0.5, 0.5, -1.5])

    def test_a_relabelled_session_delivers_levels_it_never_delivered_before(self) -> None:
        loop = ub.Loop("quantized", ub.DECLARED_STEP)
        plain = ub.simulate(ub.held(1), loop, trials=40, seed=0)
        shifted = ub.simulate(ub.held(1, offset=0.5), loop, trials=40, seed=0)
        quantized = ub.quantize(shifted.quantizer_input, ub.DECLARED_STEP, offset=0.5)
        before = ub.quantize(plain.quantizer_input, ub.DECLARED_STEP)
        levels = {float(v) for v in np.unique(before)}
        self.assertFalse(levels & {float(v) for v in np.unique(quantized)})

    def test_relabelling_keeps_the_held_spread(self) -> None:
        self.assertEqual(ub.held(2, offset=0.5).sd, ub.held(2).sd)

    def test_relabelling_keeps_what_the_quantized_loop_carries(self) -> None:
        loop = ub.Loop("quantized", ub.DECLARED_STEP)
        plain = ub.evaluate(ub.held(2), loop, trials=100, seed=0)
        shifted = ub.evaluate(ub.held(2, offset=0.5), loop, trials=100, seed=0)
        for estimator in ub.ESTIMATORS:
            for field in ("transfer_entropy", "decodability"):
                with self.subTest(estimator=estimator, field=field):
                    before = getattr(plain[estimator], field)
                    after = getattr(shifted[estimator], field)
                    self.assertAlmostEqual(after, before, delta=1e-6 * abs(before) + 1e-9)

    def test_relabelling_keeps_the_quantized_loop_clear_of_the_passing_band(self) -> None:
        plain = ub.visit_fraction(ub.held(2), ub.DECLARED_STEP, trials=200, seed=0)
        shifted = ub.visit_fraction(ub.held(2, offset=0.5), ub.DECLARED_STEP, trials=200, seed=0)
        self.assertEqual(shifted, plain)


class SettleTest(unittest.TestCase):
    def test_a_held_trial_opens_its_window_after_the_slowest_loop_has_settled(self) -> None:
        tau_ms = 1000 / (2 * math.pi * ue.estimates()["bridgeMinCutoffHz"])
        self.assertGreaterEqual(ub.burn_steps(ub.held(1)) * ub.DT_S * 1000, ub.SETTLE_TAUS * tau_ms)
        self.assertEqual(ub.burn_steps(SMALL), ub.BURN_STEPS)

    def test_the_slowest_analog_loop_delivers_the_held_level_in_the_window(self) -> None:
        floor = ue.estimates()["bridgeMinCutoffHz"]
        block = ub.simulate(ub.held(1), ub.Loop("analog", floor), trials=40, seed=0)
        level = block.task[:, 0]
        early = block.recorded_b[:, :50].mean(axis=1)
        slope = float(np.polyfit(level, early, 1)[0])
        self.assertGreater(slope, 0.95)


class LoopNoiseTest(unittest.TestCase):
    def test_a_silent_loop_noise_leaves_the_trials_unchanged(self) -> None:
        plain = ub.simulate(SMALL, ub.Loop("analog", 10.0), trials=4, seed=3)
        silent = ub.simulate(SMALL, ub.Loop("analog", 10.0, 0.0), trials=4, seed=3)
        self.assertTrue(np.array_equal(plain.recorded_b, silent.recorded_b))

    def test_loop_noise_touches_only_the_analog_drive(self) -> None:
        plain = ub.simulate(SMALL, ub.Loop("analog", 10.0), trials=4, seed=3)
        noisy = ub.simulate(SMALL, ub.Loop("analog", 10.0, 5.0), trials=4, seed=3)
        self.assertTrue(np.array_equal(plain.recorded_a, noisy.recorded_a))
        self.assertFalse(np.array_equal(plain.recorded_b, noisy.recorded_b))

    def test_loop_noise_lowers_the_transfer_entropy(self) -> None:
        floor = ue.estimates()["bridgeMinCutoffHz"]
        quiet = ub.linear(ub.simulate(ub.held(1), ub.Loop("analog", floor), 100, 0))
        noisy = ub.linear(ub.simulate(ub.held(1), ub.Loop("analog", floor, 15.0), 100, 0))
        self.assertLess(noisy.transfer_entropy, quiet.transfer_entropy)

    def test_channel_noise_is_the_filtered_noise_at_the_delivered_current(self) -> None:
        floor = ue.estimates()["bridgeMinCutoffHz"]
        silent = ub.channel_noise(ub.Loop("analog", floor))
        self.assertLess(silent, 0.1)
        self.assertLess(silent, ub.channel_noise(ub.Loop("analog", floor, 5.0)))
        white = ub.channel_noise(ub.Loop("analog", 1000.0))
        self.assertGreater(white, silent)

    def test_the_matched_noise_reproduces_a_target(self) -> None:
        grid = (0.0, 5.0, 10.0)
        self.assertAlmostEqual(ub.matched_noise(grid, [30.0, 20.0, 10.0], 25.0) or 0, 2.5)
        self.assertEqual(ub.matched_noise(grid, [30.0, 20.0, 10.0], 40.0), 0.0)
        self.assertIsNone(ub.matched_noise(grid, [30.0, 20.0, 10.0], 5.0))


class MatchTest(unittest.TestCase):
    def test_the_matched_cutoff_reproduces_the_quantized_transfer_entropy(self) -> None:
        cutoffs = np.geomspace(1.0, 1000.0, 12)
        analog = [ub.evaluate(SMALL, ub.Loop("analog", f), 60, 0)["linear"] for f in cutoffs]
        target = ub.evaluate(SMALL, ub.Loop("quantized", 10.0), 60, 0)["linear"]
        te = [m.transfer_entropy for m in analog]
        cutoff = ub.matched_cutoff(cutoffs, te, target.transfer_entropy)
        if cutoff is None:
            self.fail("the quantized loop's transfer entropy lies within the analog range")
        matched = ub.evaluate(SMALL, ub.Loop("analog", cutoff), 60, 0)["linear"]
        relative = abs(matched.transfer_entropy / target.transfer_entropy - 1)
        self.assertLess(relative, 0.1)

    def test_a_target_below_the_floor_has_no_matched_cutoff(self) -> None:
        self.assertIsNone(ub.matched_cutoff(np.array([1.0, 10.0]), [5.0, 20.0], 1.0))

    def test_the_lower_match_binds(self) -> None:
        row = ub.binding({"te_cutoff_hz": 40.0, "decodability_cutoff_hz": 90.0})
        self.assertEqual(row, ("transfer_entropy", 40.0))
        row = ub.binding({"te_cutoff_hz": None, "decodability_cutoff_hz": 90.0})
        self.assertEqual(row, ("decodability", 90.0))
        self.assertEqual(
            ub.binding({"te_cutoff_hz": None, "decodability_cutoff_hz": None}), (None, None)
        )


class PowerTest(unittest.TestCase):
    def test_two_proportions_at_the_textbook_values(self) -> None:
        self.assertEqual(ub.trials_two_proportions(0.75, 0.70, 0.05, 0.8), 1248)

    def test_two_means_at_the_textbook_values(self) -> None:
        self.assertEqual(ub.trials_two_means(0.2, 0.05, 0.8), 393)

    def test_a_confidence_interval_shrinks_with_the_square_root_of_trials(self) -> None:
        wide = ub.half_width(0.1, 100, 100)
        narrow = ub.half_width(0.1, 100, 400)
        self.assertAlmostEqual(wide / narrow, 2.0)
        self.assertAlmostEqual(wide, 1.959963984540054 * 0.1)


class SavedTest(unittest.TestCase):
    def test_a_coarse_run_is_saved_with_its_declared_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ub.write(
                Path(tmp),
                tasks=(SMALL,),
                steps=(10.0,),
                trials=40,
                cutoffs=8,
                seeds=2,
            )
            saved = json.loads((Path(tmp) / "bridge.json").read_text())
        self.assertEqual(saved["declared_step"], ub.DECLARED_STEP)
        self.assertEqual(saved["held_spread"], ub.HELD_SPREAD)
        self.assertEqual(len(saved["regimes"]), 1)
        row = saved["regimes"][0]["steps"][0]
        spread = saved["regimes"][0]["spread"]
        for estimator in ub.ESTIMATORS:
            self.assertIn("relative_te_sd", spread[estimator])
        common = row["common"]
        bound = [row[e]["cutoff_hz"] for e in ub.ESTIMATORS if row[e]["cutoff_hz"] is not None]
        self.assertEqual(common["cutoff_hz"], min(bound))
        for estimator in ub.ESTIMATORS:
            self.assertIn("relative_te_excess", common[estimator])
            self.assertIn("decodability_excess", common[estimator])
            self.assertIn("gap", row[estimator])
            self.assertIn("te_shortfall", row[estimator])
            self.assertIn("cutoff_hz", row[estimator])
        self.assertIn("visit_fraction", row)
        floor = saved["regimes"][0]["floor"]
        self.assertEqual(floor["cutoff_hz"], saved["cutoff_floor_hz"])
        for estimator in ub.ESTIMATORS:
            self.assertIn("transfer_entropy", floor[estimator])
            self.assertIn("decodability", floor[estimator])
        self.assertEqual(saved["regimes"][0]["task"]["kind"], "ou")
        self.assertTrue(math.isfinite(saved["trials"]["behaviour"]))

    def test_a_held_run_saves_its_noise_match(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            ub.write(
                Path(tmp),
                tasks=(ub.held(1),),
                steps=(10.0,),
                trials=40,
                cutoffs=4,
                seeds=2,
            )
            saved = json.loads((Path(tmp) / "bridge.json").read_text())
        self.assertEqual(saved["settle_taus"], ub.SETTLE_TAUS)
        self.assertEqual(saved["noise_margin"], ub.NOISE_MARGIN)
        match = saved["regimes"][0]["noise_match"]
        for key in ("te_noise", "decodability_noise", "noise"):
            self.assertIn(key, match)
        common = saved["held_noise"]
        self.assertGreaterEqual(common["noise"], match["noise"])
        self.assertLessEqual(common["channel_noise"], 1.0)
        self.assertEqual(common["block_count"], 2)
        block = common["blocks"][0]
        self.assertEqual(block["levels"], 1)
        for key in ("relative_te_excess_mean", "relative_te_excess_sd", "decodability_gap_mean"):
            self.assertIn(key, block)


if __name__ == "__main__":
    unittest.main()
