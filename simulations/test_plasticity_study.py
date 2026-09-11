"""Estimator and selection contracts for the predeclared F5 study."""

import unittest
from typing import Any

import numpy as np

from plasticity_study import physical_config, score_pair, select_candidate


class PlasticityStudyTest(unittest.TestCase):
    def test_refinement_keeps_duration_and_physical_update_cadence(self) -> None:
        coarse = physical_config(11, 0.05, 0.5, 0.01)
        fine = physical_config(11, 0.05, 0.5, 0.005)
        self.assertEqual(coarse.steps * coarse.dt, 400)
        self.assertEqual(fine.steps * fine.dt, 400)
        self.assertEqual(coarse.update_every * coarse.dt, fine.update_every * fine.dt)
        self.assertEqual(fine.update_every, 2 * coarse.update_every)
        with self.assertRaises(ValueError):
            physical_config(11, 0.05, 0.5, 0.03)
        with self.assertRaises(ValueError):
            physical_config(11, 0.05, 0.5, 0.0)

    def test_selection_is_blind_to_alignment_and_cannot_rescue_a_failed_candidate(self) -> None:
        records: list[dict[str, Any]] = [
            dict(
                learning_rate=0.01,
                update_interval=0.5,
                objective_pass=True,
                coherence_pass=True,
                worst_objective_ratio=0.9,
                alignment_pass=False,
            ),
            dict(
                learning_rate=0.2,
                update_interval=0.05,
                objective_pass=True,
                coherence_pass=True,
                worst_objective_ratio=0.94,
                alignment_pass=True,
            ),
        ]
        self.assertEqual(select_candidate(records), (0.01, 0.5))
        records[0]["alignment_pass"] = True
        records[1]["alignment_pass"] = False
        self.assertEqual(select_candidate(records), (0.01, 0.5))
        for record in records:
            record["objective_pass"] = False
        self.assertIsNone(select_candidate(records))

    def test_a_good_tail_mean_cannot_hide_a_failed_quarter(self) -> None:
        config = physical_config(11, 0.05, 0.5, 0.01)
        times = np.arange(0.0, 400.0, 0.5)
        base = {
            "interval_time": times,
            "interval_objective": np.full(len(times), 100.0),
            "interval_order": np.full(len(times), 0.9),
            "interval_alignment": np.ones(len(times)),
        }
        adaptive = {key: value.copy() for key, value in base.items()}
        adaptive["interval_objective"][400:600] = 80.0
        adaptive["interval_objective"][600:] = 99.0
        scored = score_pair(adaptive, base, config)
        self.assertAlmostEqual(scored["worst_objective_ratio"], 0.99)
        self.assertFalse(scored["objective_pass"])
        self.assertTrue(scored["coherence_pass"])
        self.assertEqual(scored["quarter_objective"], [80.0, 99.0])


if __name__ == "__main__":
    unittest.main()
