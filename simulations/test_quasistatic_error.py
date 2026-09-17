import unittest

import hypothesis.strategies as st
import numpy as np
from hypothesis import given

import quasistatic_error as qe


CONFIG = qe.ErrorConfig(n_harmonics=12, samples=40)


class StationaryBranchTest(unittest.TestCase):
    def test_the_branch_is_zero_at_and_below_the_threshold(self) -> None:
        # K3's boundary case: `fixed_point_eq_zero_of_le_critical` covers the
        # threshold itself, so the reduction target must too.
        for coupling in (0.0, 0.5, 1.0, 1.9, 2.0):
            self.assertEqual(qe.stationary_order(coupling, 1.0), 0.0)

    def test_the_branch_rises_strictly_above_the_threshold(self) -> None:
        orders = [qe.stationary_order(k, 1.0) for k in (2.05, 2.2, 2.6, 3.0, 4.0)]
        self.assertTrue(all(b > a for a, b in zip(orders, orders[1:], strict=False)))
        self.assertTrue(all(0.0 < value < 1.0 for value in orders))

    def test_the_branch_and_the_von_mises_order_are_the_same_number(self) -> None:
        # `r = a D / K` on the branch and `r = I_1(a)/I_0(a)` for the density
        # are two readings of one order parameter; a mismatch would mean the
        # residual is measured against a curve the density cannot sit on.
        for coupling in (2.1, 2.5, 3.5, 6.0):
            order = qe.stationary_order(coupling, 1.0)
            self.assertAlmostEqual(qe.bessel_ratio(qe.concentration_for_order(order)), order)

    def test_inverting_an_impossible_order_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            qe.concentration_for_order(1.0)


class IntegratorTest(unittest.TestCase):
    def test_the_stationary_density_does_not_move(self) -> None:
        # The positive control: a von Mises density at the branch concentration
        # solves the time-dependent equation exactly, so an integrator that
        # moves it would manufacture a residual the rate did not cause.
        for coupling in (2.5, 3.0, 5.0):
            self.assertLess(qe.stationary_control(CONFIG, coupling), 1e-12)

    def test_the_uniform_density_is_stationary_at_every_coupling(self) -> None:
        harmonics = np.zeros(CONFIG.n_harmonics)
        factors = qe.propagator(CONFIG.n_harmonics, CONFIG.diffusion, CONFIG.dt)
        self.assertTrue(np.allclose(qe.advance(harmonics, 9.0, factors), 0.0))

    def test_replicas_and_a_single_trajectory_are_the_same_code(self) -> None:
        # `fluctuating_coupling` drives this integrator along a replica axis.
        # Two replicas at one coupling must reproduce the scalar step exactly,
        # or the two modules are measuring different dynamics.
        factors = qe.propagator(CONFIG.n_harmonics, CONFIG.diffusion, CONFIG.dt)
        single = qe.von_mises_harmonics(1.3, CONFIG.n_harmonics)
        stacked = np.stack([single, single])
        expected = qe.advance(single, 2.7, factors)
        actual = qe.advance(stacked, np.array([2.7, 2.7]), factors)
        self.assertTrue(np.allclose(actual, expected, atol=0.0, rtol=0.0))

    def test_the_first_harmonic_grows_above_and_decays_below_the_threshold(self) -> None:
        factors = qe.propagator(CONFIG.n_harmonics, CONFIG.diffusion, CONFIG.dt)
        for coupling, grows in ((1.5, False), (2.5, True)):
            harmonics = qe.von_mises_harmonics(qe.concentration_for_order(0.01), 12)
            after = qe.advance(harmonics, coupling, factors)
            self.assertEqual(after[0] > harmonics[0], grows)


class ResidualTest(unittest.TestCase):
    def test_a_slower_ramp_tracks_better(self) -> None:
        leg = qe.Leg("supercritical", 2.4, 2.6, 0.4)
        errors = [qe.run_leg(leg, speed, CONFIG).terminal_error for speed in (1e-2, 1e-1, 1.0)]
        self.assertTrue(all(a < b for a, b in zip(errors, errors[1:], strict=False)))

    def test_a_subcritical_leg_started_on_the_branch_has_no_residual(self) -> None:
        # Below threshold the uniform density solves the time-dependent equation
        # at every `K(t)`. This is why the legs are started off the branch: a
        # subcritical leg started on it measures nothing at any rate.
        config = qe.ErrorConfig(n_harmonics=12, samples=40, start_offset=0.0)
        leg = qe.Leg("subcritical", 1.4, 1.6, 0.4)
        self.assertEqual(qe.run_leg(leg, 1.0, config).terminal_error, 0.0)

    def test_a_crossing_leg_does_not_improve_with_rate(self) -> None:
        # The exponential suppression below threshold and the amplification
        # above cancel on a leg symmetric about it, so the residual is
        # rate-independent and no admissible speed exists at zero distance.
        leg = qe.Leg("crossing", 1.8, 2.2, 0.0)
        errors = [qe.run_leg(leg, speed, CONFIG).terminal_error for speed in (1e-2, 1e-1, 1.0)]
        self.assertAlmostEqual(min(errors), max(errors), places=3)
        self.assertIsNone(
            qe.admissible_speed(
                [qe.run_leg(leg, speed, CONFIG) for speed in (1e-2, 1.0)], CONFIG.tolerance
            )
        )

    def test_the_admissible_speed_is_the_largest_passing_one(self) -> None:
        runs = [
            qe.LegRun(0.1, 0.02, 0.02, 2.0),
            qe.LegRun(0.01, 0.001, 0.02, 2.0),
            qe.LegRun(0.001, 0.0005, 0.02, 2.0),
        ]
        self.assertEqual(qe.admissible_speed(runs, 5e-3), 0.01)
        self.assertIsNone(qe.admissible_speed(runs, 1e-6))

    def test_the_frozen_branch_comparison_is_rejected(self) -> None:
        # The silent-failure control: a residual measured against `r_ss` at the
        # leg's initial coupling does not fall as the rate falls, which is how a
        # reduction that had quietly stopped updating the branch would look.
        leg = qe.Leg("supercritical", 2.4, 2.6, 0.4)
        slow = qe.frozen_comparison(leg, 1e-2, CONFIG)
        fast = qe.frozen_comparison(leg, 1.0, CONFIG)
        self.assertGreater(slow, CONFIG.tolerance)
        self.assertGreater(slow, fast)

    def test_halving_the_step_moves_the_residual_negligibly(self) -> None:
        leg = qe.Leg("supercritical", 2.4, 2.6, 0.4)
        self.assertLess(qe.step_halving_control(leg, 1e-1, CONFIG), CONFIG.tolerance / 10.0)


class CriterionTest(unittest.TestCase):
    def test_the_legs_bracket_the_threshold_as_named(self) -> None:
        legs = {leg.name: leg for leg in qe.build_legs(CONFIG)}
        critical = CONFIG.critical_coupling
        self.assertLess(legs["subcritical_0.4"].end, critical)
        self.assertGreater(legs["supercritical_0.4"].start, critical)
        self.assertLess(legs["crossing"].start, critical)
        self.assertGreater(legs["crossing"].end, critical)

    def test_every_leg_reports_its_distance_from_threshold(self) -> None:
        critical = CONFIG.critical_coupling
        for leg in qe.build_legs(CONFIG):
            nearest = min(abs(leg.start - critical), abs(leg.end - critical))
            expected = 0.0 if (leg.start - critical) * (leg.end - critical) < 0 else nearest
            self.assertAlmostEqual(leg.delta, expected)

    def test_the_required_ratio_falls_as_the_speed_rises(self) -> None:
        self.assertAlmostEqual(qe.required_ratio(0.01, CONFIG), 200.0)
        self.assertGreater(qe.required_ratio(0.001, CONFIG), qe.required_ratio(0.01, CONFIG))
        with self.assertRaises(ValueError):
            qe.required_ratio(0.0, CONFIG)


class DelayTest(unittest.TestCase):
    def test_the_threshold_seeded_delay_grows_with_speed(self) -> None:
        measured = [qe.threshold_delay(speed, CONFIG) for speed in (1e-3, 1e-2, 1e-1)]
        self.assertTrue(all(value is not None for value in measured))
        delays = [value for value in measured if value is not None]
        self.assertTrue(all(a < b for a, b in zip(delays, delays[1:], strict=False)))

    def test_the_delay_exponent_reproduces_the_published_fit(self) -> None:
        # The published `\rampDelayExponent` is a finite-`N` measurement; this
        # is its deterministic threshold limit, and the item requires the two to
        # be the same measurement rather than two results.
        speeds = np.asarray(qe.RAMP_SPEEDS)
        delays = np.asarray([qe.threshold_delay(float(speed), CONFIG) for speed in speeds])
        self.assertAlmostEqual(qe.fit_exponent(speeds, delays), qe.RAMP_DELAY_EXPONENT, places=1)

    def test_the_fit_recovers_an_exact_power_law(self) -> None:
        """A slope the fit has to return exactly, rather than to one decimal.

        The published-fit test above compares against `RAMP_DELAY_EXPONENT` to
        `places=1`, a tolerance of 0.05 that most arithmetic errors fit inside:
        14 of 29 mutants in this function survived the suite. On a constructed
        power law `delay = 3 * speed ** -0.75` the answer is known in closed
        form, so the fit can be held to floating-point agreement instead.
        """
        speeds = np.array([0.01, 0.02, 0.05, 0.1])
        delays = 3.0 * speeds**-0.75

        self.assertAlmostEqual(qe.fit_exponent(speeds, delays), -0.75, places=12)

    def test_two_points_are_enough_to_fit(self) -> None:
        """The stated minimum has to be accepted, not just the comfortable case.

        `speeds.size < 2` is a boundary, and a fit given four points never tests
        it: mutants raising it to `<= 2` or `< 3` reject the documented minimum
        and no other test here notices.
        """
        speeds = np.array([0.01, 0.1])
        delays = 3.0 * speeds**-0.75

        self.assertAlmostEqual(qe.fit_exponent(speeds, delays), -0.75, places=12)

    def test_an_exponent_fit_refuses_degenerate_input(self) -> None:
        """Each guard, matched on its own message.

        Matching the message is what makes these cases distinguishing rather
        than decorative. `assertRaises(ValueError)` alone cannot tell this
        function's refusal from numpy blowing up on `log(0)` further down, so a
        mutant that widens `<= 0.0` to `< 0.0` still "raises ValueError" and
        survives -- and so does one that replaces the message with nothing.
        """
        matching = "at least two matching points"
        positive = "strictly positive points"

        with self.assertRaisesRegex(ValueError, matching):
            qe.fit_exponent(np.array([1.0]), np.array([1.0]))
        with self.assertRaisesRegex(ValueError, matching):
            qe.fit_exponent(np.array([1.0, 2.0, 3.0]), np.array([1.0, 2.0]))
        with self.assertRaisesRegex(ValueError, positive):
            qe.fit_exponent(np.array([1.0, 0.0]), np.array([1.0, 1.0]))
        with self.assertRaisesRegex(ValueError, positive):
            qe.fit_exponent(np.array([1.0, -2.0]), np.array([1.0, 2.0]))
        with self.assertRaisesRegex(ValueError, positive):
            qe.fit_exponent(np.array([1.0, 2.0]), np.array([1.0, 0.0]))
        with self.assertRaisesRegex(ValueError, positive):
            qe.fit_exponent(np.array([1.0, 2.0]), np.array([1.0, -1.0]))


class StationaryBranchPropertyTest(unittest.TestCase):
    @given(st.floats(min_value=-100.0, max_value=2.0))
    def test_property_branch_is_zero_at_and_below_threshold(self, coupling: float) -> None:
        self.assertEqual(qe.stationary_order(coupling, 1.0), 0.0)

    @given(st.floats(min_value=2.0001, max_value=100.0))
    def test_property_branch_is_positive_above_threshold(self, coupling: float) -> None:
        order = qe.stationary_order(coupling, 1.0)
        self.assertGreater(order, 0.0)
        self.assertLess(order, 1.0)


if __name__ == "__main__":
    unittest.main()
