import unittest

import hypothesis.strategies as st
import numpy as np
from hypothesis import given, settings

import collapse_design as design
import empirical_collapse as collapse


class BesselGeometryTest(unittest.TestCase):
    def test_the_tangent_gap_is_zero_at_zero_and_grows(self) -> None:
        self.assertAlmostEqual(design.tangent_gap(0.0), 0.0, places=6)
        gaps = [design.tangent_gap(a) for a in (0.5, 1.0, 2.0, 4.0)]
        self.assertTrue(all(np.diff(gaps) > 0.0))

    def test_inverse_bessel_ratio_inverts_the_curve(self) -> None:
        for a in (0.3, 1.0, 3.5):
            self.assertAlmostEqual(design.inverse_bessel_ratio(design.bessel_ratio(a)), a, places=4)

    def test_a_unit_resultant_needs_an_infinite_concentration(self) -> None:
        self.assertEqual(design.inverse_bessel_ratio(1.0), float("inf"))


class DependenceModelTest(unittest.TestCase):
    def test_every_dependence_level_keeps_the_marginal_concentration(self) -> None:
        # The comparison is about dependence, so the marginal it is measured at
        # has to be the same at every level of it.
        target = design.bessel_ratio(2.0)
        for share in (0.0, 0.5, 1.0):
            rng = np.random.default_rng(11)
            draws = [
                design.draw_phases(rng, 2.0, 2000, design.Dependence(share)) for _ in range(40)
            ]
            resultant = float(np.abs(np.mean(np.exp(1j * np.concatenate(draws)))))
            self.assertAlmostEqual(resultant, target, delta=0.03)

    def test_full_dependence_leaves_one_phase_per_cluster(self) -> None:
        rng = np.random.default_rng(3)
        phases = design.draw_phases(rng, 2.0, 100, design.Dependence(1.0))
        self.assertEqual(np.unique(np.round(phases, 12)).size, 10)

    def test_independent_draws_reproduce_the_published_calibration(self) -> None:
        # `\eegCalibrationAMean`, `\eegCalibrationResidualMean` and
        # `\eegCalibrationResidualSd` are 1.346, +0.146 and 0.028; the zero
        # dependence path has to land on the calibration it generalises.
        row = design.null_residual(2.0, 100, design.Dependence(0.0), replicas=400)
        self.assertAlmostEqual(row.a_mean, 1.346, delta=0.03)
        self.assertAlmostEqual(row.residual_mean, 0.146, delta=0.01)
        self.assertAlmostEqual(row.residual_sd, 0.028, delta=0.006)

    def test_effective_sites_run_from_the_count_to_the_cluster_count(self) -> None:
        self.assertAlmostEqual(design.Dependence(0.0).effective_sites(1000), 1000.0)
        self.assertAlmostEqual(design.Dependence(1.0).effective_sites(1000), 100.0)

    def test_a_share_outside_the_unit_interval_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            design.Dependence(1.5)


class FloorTest(unittest.TestCase):
    def _row(self, **kwargs: float) -> design.NullResidual:
        fields: dict[str, float] = {
            "concentration": 2.0,
            "n_sites": 100,
            "dependence": 0.0,
            "replicas": 10,
            "bins": 40,
            "a_mean": 2.0,
            "residual_mean": 0.0,
            "residual_sd": 0.0,
        }
        fields.update(kwargs)
        return design.NullResidual(**fields)  # type: ignore[arg-type]

    def test_a_systematic_offset_counts_toward_the_floor(self) -> None:
        # A bias masquerades as a departure from the curve exactly as scatter
        # does, so a floor built from the scatter alone would pass a biased
        # estimator off as a discriminating one.
        self.assertAlmostEqual(self._row(residual_mean=-0.1).floor, 0.1)

    def test_the_usable_separation_is_the_smaller_of_the_two_gaps(self) -> None:
        # At small counts the pseudocount pulls the estimate down the curve into
        # a region where the two relations are closer together.
        row = self._row(concentration=2.0, a_mean=1.0)
        self.assertAlmostEqual(row.separation, design.tangent_gap(1.0))

    def test_separation_is_measured_against_the_floor(self) -> None:
        self.assertTrue(design.separates(self._row(residual_sd=0.01)))
        self.assertFalse(design.separates(self._row(residual_sd=1.0)))

    def test_replica_budget_thins_the_large_counts_and_caps_the_small_ones(self) -> None:
        self.assertEqual(design.replicas_for(100), design.REPLICAS)
        self.assertLess(design.replicas_for(100_000), design.REPLICAS)
        self.assertGreaterEqual(design.replicas_for(10_000_000), design.REPLICA_MINIMUM)


class SpecificationTest(unittest.TestCase):
    def _rows(self) -> list[design.NullResidual]:
        return [
            design.NullResidual(
                concentration=a,
                n_sites=n,
                dependence=d,
                replicas=10,
                bins=40,
                a_mean=a,
                residual_mean=0.0,
                residual_sd=sd,
            )
            for n, sd in ((100, 0.5), (1000, 0.01))
            for d in (0.0, 1.0)
            for a in (1.0, 2.0, 3.0)
        ]

    def test_the_minimum_concentration_is_the_first_one_that_clears_the_floor(self) -> None:
        self.assertEqual(design.minimum_separating_concentration(self._rows(), 1000, 0.0), 1.0)

    def test_a_count_that_never_clears_the_floor_reports_nothing(self) -> None:
        rows = [row for row in self._rows() if row.n_sites == 100]
        self.assertIsNone(design.minimum_separating_concentration(rows, 100, 0.0))
        self.assertIsNone(design.maximum_tolerable_dependence(rows, 100))

    def test_the_observed_range_is_read_rather_than_recomputed(self) -> None:
        low, high = collapse.OBSERVED_CONCENTRATION_RANGE
        self.assertLess(design.tangent_gap(high), 0.01)
        self.assertLess(low, high)


class BesselGeometryPropertyTest(unittest.TestCase):
    @given(st.floats(min_value=0.01, max_value=20.0))
    @settings(deadline=None)
    def test_property_inverse_bessel_ratio(self, a: float) -> None:
        self.assertAlmostEqual(design.inverse_bessel_ratio(design.bessel_ratio(a)), a, places=4)


if __name__ == "__main__":
    unittest.main()
