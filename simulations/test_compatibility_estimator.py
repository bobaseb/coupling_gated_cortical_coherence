import unittest
from dataclasses import replace
from typing import cast

import numpy as np

import compatibility_estimator as estimator


TERRITORY = estimator.Territory()
MATCHED = (estimator.Decoder(), estimator.Decoder())


class TerritoryTest(unittest.TestCase):
    def test_the_overlap_is_the_sub_territory_the_statistic_reads(self) -> None:
        self.assertEqual(TERRITORY.overlap, 8)
        self.assertEqual(TERRITORY.shared, slice(8, 16))

    def test_patches_that_do_not_meet_are_rejected(self) -> None:
        with self.assertRaises(ValueError):
            estimator.Territory(sites=24, patch_size=12)

    def test_private_sites_belong_to_exactly_one_patch(self) -> None:
        first = set(range(*TERRITORY.private_first.indices(TERRITORY.sites)))
        second = set(range(*TERRITORY.private_second.indices(TERRITORY.sites)))
        shared = set(range(*TERRITORY.shared.indices(TERRITORY.sites)))
        self.assertEqual(first | second | shared, set(range(TERRITORY.sites)))
        self.assertFalse(first & second)


class RestrictionTest(unittest.TestCase):
    def test_the_restriction_map_keeps_the_shared_sites_only(self) -> None:
        posteriors = np.zeros((3, TERRITORY.sites, TERRITORY.alphabet))
        self.assertEqual(
            estimator.restrict(posteriors, TERRITORY).shape,
            (3, TERRITORY.overlap, TERRITORY.alphabet),
        )

    def test_equal_restrictions_give_a_zero_statistic(self) -> None:
        rng = np.random.default_rng(1)
        posteriors = rng.dirichlet(np.ones(TERRITORY.alphabet), size=(4, TERRITORY.overlap))
        self.assertAlmostEqual(
            float(estimator.per_trial_statistic(posteriors, posteriors).max()), 0.0
        )

    def test_disjoint_restrictions_give_the_largest_statistic(self) -> None:
        first = np.zeros((1, 1, 3))
        first[..., 0] = 1.0
        second = np.zeros((1, 1, 3))
        second[..., 1] = 1.0
        self.assertAlmostEqual(float(estimator.per_trial_statistic(first, second)[0]), 1.0)


class ConstructedAnswerTest(unittest.TestCase):
    def _measure(
        self, configuration: estimator.Configuration, seed: int = 5
    ) -> estimator.Assessment:
        rng = np.random.default_rng(seed)
        return estimator.measure(rng, TERRITORY, configuration, MATCHED, 200).assessment

    def test_the_built_in_disagreement_is_the_one_recovered(self) -> None:
        null = self._measure(estimator.SINGLE_VALUED)
        disagreeing = self._measure(estimator.DISAGREEING)
        self.assertGreater(disagreeing.statistic, null.statistic + 10 * null.trial_sd)

    def test_a_single_valued_field_sits_at_its_own_null(self) -> None:
        rng = np.random.default_rng(7)
        null = estimator.measure(rng, TERRITORY, estimator.SINGLE_VALUED, MATCHED, 200)
        replica = estimator.measure(rng, TERRITORY, estimator.SINGLE_VALUED, MATCHED, 200)
        scored = estimator.against(replica, null)
        self.assertIsNotNone(scored.z_against_null)
        self.assertLess(abs(scored.z_against_null or 0.0), estimator.SEPARATION_TARGET)

    def test_the_disagreement_is_confined_to_the_shared_sites(self) -> None:
        rng = np.random.default_rng(2)
        data = estimator.generate(rng, TERRITORY, estimator.DISAGREEING, MATCHED, 50)
        private = TERRITORY.private_first
        self.assertTrue(
            np.array_equal(data.content_first[:, private], data.content_second[:, private])
        )
        self.assertFalse(
            np.array_equal(
                data.content_first[:, TERRITORY.shared], data.content_second[:, TERRITORY.shared]
            )
        )


class DependenceAwarenessTest(unittest.TestCase):
    def test_a_site_level_resample_understates_the_spread(self) -> None:
        # Sites of one trial are decoded at that trial's own quality, so they are
        # not independent draws and a site-level interval is too narrow.
        rng = np.random.default_rng(4)
        assessment = estimator.measure(
            rng, TERRITORY, estimator.SINGLE_VALUED, MATCHED, 400
        ).assessment
        self.assertGreater(assessment.dependence_inflation, 1.1)

    def test_removing_the_trial_level_fluctuation_removes_the_inflation(self) -> None:
        rng = np.random.default_rng(4)
        flat = (estimator.Decoder(trial_spread=0.0), estimator.Decoder(trial_spread=0.0))
        assessment = estimator.measure(
            rng, TERRITORY, estimator.SINGLE_VALUED, flat, 400
        ).assessment
        self.assertLess(assessment.dependence_inflation, 1.1)


class SilentFailureTest(unittest.TestCase):
    def test_shrinkage_manufactures_compatibility_and_fails_the_information_floor(self) -> None:
        rng = np.random.default_rng(9)
        shrunk = (estimator.Decoder(shrinkage=0.98), estimator.Decoder(shrinkage=0.98))
        honest = estimator.measure(rng, TERRITORY, estimator.DISAGREEING, MATCHED, 200)
        case = estimator.measure(rng, TERRITORY, estimator.DISAGREEING, shrunk, 200)
        self.assertLess(case.assessment.statistic, 0.1 * honest.assessment.statistic)
        self.assertLess(case.assessment.information_first, estimator.INFORMATION_FLOOR)
        self.assertFalse(case.assessment.admitted)

    def test_mild_bias_manufactures_incompatibility_and_only_calibration_sees_it(self) -> None:
        rng = np.random.default_rng(9)
        biased = (
            estimator.Decoder(bias=1, bias_weight=0.45),
            estimator.Decoder(bias=-1, bias_weight=0.45),
        )
        honest = estimator.measure(rng, TERRITORY, estimator.SINGLE_VALUED, MATCHED, 200)
        case = estimator.measure(rng, TERRITORY, estimator.SINGLE_VALUED, biased, 200)
        self.assertGreater(case.assessment.statistic, honest.assessment.statistic)
        self.assertGreater(case.assessment.information_first, estimator.INFORMATION_FLOOR)
        self.assertGreater(case.assessment.accuracy_first, estimator.ACCURACY_FLOOR)
        self.assertGreater(case.assessment.calibration_first, estimator.CALIBRATION_CEILING)
        self.assertFalse(case.assessment.admitted)


class PhaseObservableTest(unittest.TestCase):
    def test_a_phase_statistic_fails_the_constructed_counterexample(self) -> None:
        # One common phase, two descriptions differing where the patches meet:
        # `overlap_agreement_fails`. The phase bound is required to miss it.
        rng = np.random.default_rng(6)
        null = estimator.measure(rng, TERRITORY, estimator.LOCKED_SINGLE_VALUED, MATCHED, 300)
        locked = estimator.against(
            estimator.measure(rng, TERRITORY, estimator.LOCKED_DISAGREEING, MATCHED, 300), null
        )
        self.assertLess(locked.phase_bound, 1e-6)
        self.assertGreater(locked.z_against_null or 0.0, estimator.SEPARATION_TARGET)
        self.assertGreater(locked.auc_against_null or 0.0, 0.9)

    def test_the_phase_carries_content_built_from_it_and_not_content_built_free_of_it(
        self,
    ) -> None:
        rng = np.random.default_rng(8)
        derived = estimator.measure(rng, TERRITORY, estimator.PHASE_CONTENT, MATCHED, 300)
        free = estimator.measure(rng, TERRITORY, estimator.SINGLE_VALUED, MATCHED, 300)
        self.assertGreater(derived.assessment.phase_share, 0.95)
        self.assertLess(free.assessment.phase_share, 0.05)

    def test_the_phase_bound_cannot_tell_the_two_content_models_apart(self) -> None:
        rng = np.random.default_rng(8)
        rows = estimator.baseline(rng, TERRITORY, 0.2, 300)
        report = estimator.phase_carried_content(rows)
        self.assertTrue(report["share_separates_the_models"])
        self.assertFalse(report["bound_separates_the_models"])


class SweepTest(unittest.TestCase):
    def test_separation_falls_as_the_decoders_get_worse(self) -> None:
        rng = np.random.default_rng(10)
        rows = estimator.error_degradation(rng, replace(TERRITORY), 120)
        scores = [float(row["assessment"]["auc_against_null"]) for row in rows]  # type: ignore[index]
        self.assertGreater(scores[0], scores[-1])

    def test_narrowing_the_shared_territory_costs_separation(self) -> None:
        rng = np.random.default_rng(12)
        rows = estimator.coverage_degradation(rng, TERRITORY, 0.2, 120)
        overlaps = [int(cast(int, row["overlap"])) for row in rows]
        scores = [float(row["assessment"]["auc_against_null"]) for row in rows]  # type: ignore[index]
        self.assertEqual(overlaps, sorted(overlaps))
        self.assertLess(scores[0], scores[-1])


class AucTest(unittest.TestCase):
    def test_a_separated_pair_scores_one_and_an_identical_pair_a_half(self) -> None:
        low = np.arange(10.0)
        high = np.arange(10.0) + 100.0
        self.assertAlmostEqual(estimator.auc(high, low), 1.0)
        self.assertAlmostEqual(estimator.auc(low, low.copy()), 0.5)


if __name__ == "__main__":
    unittest.main()
