"""Exact finite-state checks for a funded learning/phase feedback process."""

import tempfile
import unittest
from pathlib import Path

import numpy as np

from g23_closed_loop import (
    FeedbackConfig,
    control_result,
    installed_coupling,
    phase_channel,
    safe_steps,
    save_controls,
)


class ClosedLoopTests(unittest.TestCase):
    def test_register_installs_distinct_signed_phase_couplings(self) -> None:
        config = FeedbackConfig()
        np.testing.assert_array_equal(installed_coupling(config), [-config.field, config.field])
        self.assertNotAlmostEqual(phase_channel(config)[0, 0, 1], phase_channel(config)[1, 0, 1])
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_controls(output, config)
            with np.load(output / "informed.npz", allow_pickle=False) as artifact:
                np.testing.assert_array_equal(artifact["installed_coupling"], [-0.4, 0.4])

    def test_phase_channel_has_local_detailed_balance_and_support(self) -> None:
        config = FeedbackConfig()
        channel = phase_channel(config)
        np.testing.assert_allclose(channel.sum(axis=2), 1)
        self.assertGreater(channel.min(), 0)
        for action in range(2):
            energy = np.array(
                [-config.field if phase == action else config.field for phase in range(2)]
            )
            ratio = channel[action, 0, 1] / channel[action, 1, 0]
            self.assertAlmostEqual(ratio, np.exp(-config.beta * (energy[1] - energy[0])))

    def test_matched_controls_and_separate_ledgers(self) -> None:
        config = FeedbackConfig(horizon=4)
        informed = control_result(config, "informed")
        blind = control_result(config, "blind")
        frozen = control_result(config, "frozen")
        np.testing.assert_allclose(informed.phase_marginal, blind.phase_marginal)
        self.assertGreater(informed.prediction_accuracy[-1], blind.prediction_accuracy[-1])
        self.assertNotAlmostEqual(informed.prediction_accuracy[-1], frozen.prediction_accuracy[-1])
        self.assertEqual(informed.current_cost, None)
        self.assertEqual(informed.work_cost.shape, (4,))
        self.assertEqual(informed.bath_heat.shape, (4,))
        self.assertAlmostEqual(
            informed.installed_energy[-1] - informed.installed_energy[0],
            informed.installation_work.sum() - informed.bath_heat.sum(),
        )
        np.testing.assert_allclose(
            informed.available_store[-1],
            config.initial_store - config.preparation - informed.work_cost.sum(),
        )

    def test_conservative_stop_and_external_charger(self) -> None:
        config = FeedbackConfig(horizon=20, initial_store=1.0, preparation=0.1)
        self.assertLess(safe_steps(config, replenishment=0.0), config.horizon)
        self.assertEqual(safe_steps(config, replenishment=1.3), config.horizon)
        self.assertGreaterEqual(
            control_result(config, "informed", stop_when_unfunded=True).available_store.min(), 0
        )
        ordinary = FeedbackConfig(horizon=20)
        unfunded = control_result(ordinary, "informed")
        charged = control_result(ordinary, "informed", replenishment=1.3)
        self.assertGreater(unfunded.work_cost[1:].min(), 0)
        self.assertLess(unfunded.available_store[-1], 0)
        self.assertGreaterEqual(charged.available_store.min(), 0)

    def test_replayed_register_marginal_breaks_phase_feedback(self) -> None:
        config = FeedbackConfig(horizon=4)
        informed = control_result(config, "informed")
        replayed = control_result(config, "replayed")
        np.testing.assert_allclose(informed.joint_law.sum(axis=1), replayed.joint_law.sum(axis=1))
        np.testing.assert_allclose(informed.phase_marginal, replayed.phase_marginal)
        self.assertGreater(informed.prediction_accuracy[-1], replayed.prediction_accuracy[-1])
        np.testing.assert_allclose(
            replayed.joint_law,
            replayed.phase_marginal[:, :, None] * replayed.joint_law.sum(axis=1)[:, None, :],
        )
        self.assertAlmostEqual(
            replayed.installed_energy[-1] - replayed.installed_energy[0],
            replayed.installation_work.sum() - replayed.bath_heat.sum(),
        )

    def test_saved_controls_keep_provenance(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_controls(output, FeedbackConfig(horizon=4))
            self.assertTrue((output / "summary.json").exists())
            self.assertTrue((output / "informed_replenished.npz").exists())
            with np.load(output / "informed.npz", allow_pickle=False) as artifact:
                self.assertIn("joint_law", artifact.files)
                self.assertIn("bath_heat", artifact.files)
                self.assertIn("installation_work", artifact.files)
                self.assertGreaterEqual(artifact["available_store"].min(), 0)


if __name__ == "__main__":
    unittest.main()
