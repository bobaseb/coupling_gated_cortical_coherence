"""Analytical checks for the first G22–G24 formal increment."""

import unittest

import numpy as np

from followup_foundations import (
    covariance_rank_truncation,
    covariance_rank_tail,
    current_bound,
    feedback_expected_costs,
    feedback_laws,
    feedback_prediction_accuracy,
    feedback_store,
    feedback_transition,
    weighted_tail,
)


class CurrentTests(unittest.TestCase):
    def test_uniform_zero_cost(self) -> None:
        rho = np.full(128, 1 / (2 * np.pi))
        result = current_bound(rho, np.zeros(128), 0.7)
        self.assertEqual(result["cost"], 0)
        self.assertAlmostEqual(result["flux_squared"], 0)

    def test_manufactured_continuity_path(self) -> None:
        # rho(t,theta)=(1+2*r(t)*cos(theta))/(2*pi), J=-r'(t)*sin(theta)/pi.
        theta = np.arange(1024) * 2 * np.pi / 1024
        rho = (1 + 0.6 * np.cos(theta)) / (2 * np.pi)
        current = -0.2 * np.sin(theta) / np.pi
        result = current_bound(rho, current, 0.5)
        self.assertAlmostEqual(result["order"], 0.3)
        self.assertAlmostEqual(result["flux_squared"], 0.04)
        self.assertGreaterEqual(result["bound"], result["flux_squared"])
        self.assertGreater(result["cost"], 0)

    def test_domain_checks(self) -> None:
        for rho, diffusion in [(np.zeros(8), 1), (np.ones(8), 1), (np.full(8, 1 / (2 * np.pi)), 0)]:
            with self.subTest(diffusion=diffusion, rho=rho):
                with self.assertRaises(ValueError):
                    current_bound(rho, np.zeros(8), diffusion)


class FeedbackTests(unittest.TestCase):
    def test_executed_law_work_store_telescope(self) -> None:
        evolve = np.array([np.eye(2), np.fliplr(np.eye(2))])
        update = np.array([[[1.0, 0.0], [1.0, 0.0]], [[0.0, 1.0], [0.0, 1.0]]])
        transition = feedback_transition(evolve, np.eye(2), update, np.array([0, 1]))
        laws = feedback_laws(np.full((2, 2), 0.25), transition, 4)
        prices = np.array([0.0, 2.0])
        stage_price = (
            np.full((2, 2, 2, 2), 0.3) + prices[None, None, None, :] - prices[None, :, None, None]
        )
        costs = feedback_expected_costs(laws, transition, stage_price)
        replenish = np.full(4, 0.1)
        store = feedback_store(3.0, 0.5, costs, replenish)
        installed_energy = np.einsum("tpr,r->t", laws, prices)
        np.testing.assert_allclose(
            store,
            3.0 - 0.5 - 0.2 * np.arange(5) - installed_energy + installed_energy[0],
        )
        with self.assertRaises(ValueError):
            feedback_expected_costs(laws, transition, np.zeros((2, 2)))
        unrelated = laws.copy()
        unrelated[1] = np.full((2, 2), 0.25)
        with self.assertRaises(ValueError):
            feedback_expected_costs(unrelated, transition, stage_price)

    def test_joint_law_retains_feedback_and_matched_blind_control(self) -> None:
        # A copied phase predicts the next phase; a fair blind bit has the same marginal.
        evolve = np.array([[[0.9, 0.1], [0.4, 0.6]], [[0.6, 0.4], [0.1, 0.9]]])
        update = np.array([[[1.0, 0.0], [1.0, 0.0]], [[0.0, 1.0], [0.0, 1.0]]])
        prior = np.full((2, 2), 0.25)
        informed = feedback_transition(evolve, np.eye(2), update, np.array([0, 1]))
        blind = feedback_transition(evolve, np.full((2, 2), 0.5), update, np.array([0, 1]))
        laws = feedback_laws(prior, informed, 3)
        blind_laws = feedback_laws(prior, blind, 3)
        np.testing.assert_allclose(laws.sum(axis=(1, 2)), 1)
        np.testing.assert_allclose(blind_laws.sum(axis=(1, 2)), 1)
        np.testing.assert_allclose(laws.sum(axis=2), blind_laws.sum(axis=2))
        self.assertGreater(np.trace(laws[-1]), np.trace(blind_laws[-1]))
        # Score the register's prediction of the phase after another evolution.
        prediction = evolve[np.array([0, 1]), :, np.array([0, 1])].T
        self.assertGreater(np.sum(laws[-1] * prediction), np.sum(blind_laws[-1] * prediction))
        informed_accuracy = feedback_prediction_accuracy(
            laws, evolve, np.array([0, 1]), np.array([0, 1])
        )
        blind_accuracy = feedback_prediction_accuracy(
            blind_laws, evolve, np.array([0, 1]), np.array([0, 1])
        )
        self.assertAlmostEqual(informed_accuracy[-1], np.sum(laws[-1] * prediction))
        self.assertGreater(informed_accuracy[-1], blind_accuracy[-1])

    def test_law_rejects_bad_prior_and_horizon(self) -> None:
        transition = np.zeros((2, 2, 2, 2))
        transition[:, :, 0, 0] = 1
        with self.assertRaises(ValueError):
            feedback_laws(np.ones((2, 2)), transition, 2)
        with self.assertRaises(ValueError):
            feedback_laws(np.full((2, 2), 0.25), transition, -1)

    def test_exact_lean_witness_and_blind_control(self) -> None:
        # evolve[action, old_phase, new_phase] is XOR; the learner copies sensor.
        evolve = np.array([np.eye(2), np.fliplr(np.eye(2))])
        update = np.array([[[1.0, 0.0], [1.0, 0.0]], [[0.0, 1.0], [0.0, 1.0]]])
        informed = feedback_transition(evolve, np.eye(2), update, np.array([0, 1]))
        blind = feedback_transition(
            evolve, np.array([[1.0, 0.0], [1.0, 0.0]]), update, np.array([0, 1])
        )
        self.assertEqual(informed[0, 1, 1, 1], 1)
        self.assertEqual(blind[0, 1, 1, 0], 1)
        self.assertEqual(informed[1, 1, 0, 0], 1)
        self.assertEqual(blind[1, 0, 1, 0], 1)
        np.testing.assert_allclose(informed.sum(axis=(2, 3)), 1)

    def test_reject_invalid_channel(self) -> None:
        with self.assertRaises(ValueError):
            feedback_transition(np.ones((2, 2, 2)), np.eye(2), np.ones((2, 2, 2)), np.array([0, 1]))


class RankTests(unittest.TestCase):
    def test_covariance_truncation_attains_rank_floor(self) -> None:
        target = np.array([[3.0, 0.4], [0.0, 1.0]])
        for covariance in (
            np.array([[1.0, 0.8], [0.8, 1.0]]),
            np.array([[1.0, 1.0], [1.0, 1.0]]),
        ):
            with self.subTest(covariance=covariance):
                decoder = covariance_rank_truncation(target, covariance, 1)
                error = np.trace((target - decoder) @ covariance @ (target - decoder).T)
                self.assertLessEqual(np.linalg.matrix_rank(decoder), 1)
                self.assertAlmostEqual(error, covariance_rank_tail(target, covariance, 1))
        np.testing.assert_allclose(covariance_rank_truncation(target, np.eye(2), 0), 0)
        np.testing.assert_allclose(
            covariance_rank_truncation(target, np.eye(2), 2), target, atol=1e-12
        )

    def test_correlated_input_tail_matches_empirical_error(self) -> None:
        target = np.diag([3.0, 1.0])
        inputs = np.array([[1.0, 1.0], [1.0, -1.0]])
        covariance = inputs.T @ inputs / 2
        self.assertAlmostEqual(covariance_rank_tail(target, covariance, 1), 1)
        correlated = np.array([[1.0, 0.8], [0.8, 1.0]])
        floor = covariance_rank_tail(target, correlated, 1)
        self.assertLess(floor, 1)
        self.assertGreater(floor, 0)
        rng = np.random.default_rng(24)
        for _ in range(20):
            approximation = np.outer(rng.normal(size=2), rng.normal(size=2))
            error = np.trace((target - approximation) @ correlated @ (target - approximation).T)
            self.assertGreaterEqual(error + 1e-10, floor)

    def test_covariance_tail_rejects_invalid_inputs(self) -> None:
        target = np.eye(2)
        for covariance in (np.array([[1.0, 2.0], [2.0, 1.0]]), np.array([[1.0, 0.2], [0.0, 1.0]])):
            with self.subTest(covariance=covariance):
                with self.assertRaises(ValueError):
                    covariance_rank_tail(target, covariance, 1)

    def test_anisotropic_order_reversal(self) -> None:
        self.assertEqual(weighted_tail(np.array([3.0, 1.0]), np.array([1.0, 16.0]), 1), 9)
        self.assertEqual(weighted_tail(np.array([3.0, 1.0]), np.ones(2), 1), 1)

    def test_zero_and_full_rank(self) -> None:
        lam, variance = np.array([3.0, 1.0]), np.array([1.0, 16.0])
        self.assertEqual(weighted_tail(lam, variance, 0), 25)
        self.assertEqual(weighted_tail(lam, variance, 2), 0)

    def test_rank_one_competitors(self) -> None:
        rng = np.random.default_rng(22)
        lam, variance = np.array([3.0, 1.0]), np.array([1.0, 16.0])
        for _ in range(20):
            approximation = np.outer(rng.normal(size=2), rng.normal(size=2))
            error = np.sum((np.diag(lam) - approximation) ** 2 * variance)
            self.assertGreaterEqual(error, weighted_tail(lam, variance, 1))

    def test_reject_negative_second_moment(self) -> None:
        with self.assertRaises(ValueError):
            weighted_tail(np.ones(2), np.array([1.0, -1.0]), 1)


if __name__ == "__main__":
    unittest.main()
