"""Graph-distance and communication-deadline checks on the G24 task."""

import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from g24_locality import chain_code, save_locality_comparison
from g24_shared_task import build_task


class LocalityTests(unittest.TestCase):
    def test_node_two_cannot_see_distance_two_before_two_rounds(self) -> None:
        task = build_task(repeats=2, seed=24)
        original = task.test_input
        distance_one = original.copy()
        distance_two = original.copy()
        distance_one[:, 3] += 0.5
        distance_two[:, 0] += 0.5
        for rounds in (0, 1):
            np.testing.assert_allclose(
                chain_code(original, rounds), chain_code(distance_two, rounds), atol=1e-12
            )
        np.testing.assert_allclose(chain_code(original, 0), chain_code(distance_one, 0), atol=1e-12)
        self.assertGreater(np.linalg.norm(chain_code(original, 1) - chain_code(distance_one, 1)), 0)
        self.assertGreater(np.linalg.norm(chain_code(original, 2) - chain_code(distance_two, 2)), 0)

    def test_saved_deadline_comparison_uses_same_task(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_locality_comparison(output, repeats=2, seed=24)
            summary = json.loads((output / "summary.json").read_text())
            self.assertEqual(summary["phase_graph_edges"], [[0, 1], [1, 2]])
            self.assertEqual([row["communication_rounds"] for row in summary["rows"]], [0, 1, 2, 3])
            self.assertAlmostEqual(summary["rows"][1]["distance_two_code_change"], 0)
            self.assertGreater(summary["rows"][2]["distance_two_code_change"], 0)
            self.assertTrue((output / "round_2.npz").exists())


if __name__ == "__main__":
    unittest.main()
