"""Artifact-only verification of the finite feedback held-out scores."""

import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from g23_benchmark import run_benchmark
from g23_benchmark_audit import audit_benchmark


class BenchmarkAuditTests(unittest.TestCase):
    def test_recompute_heldout_accuracy_and_reject_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            run_benchmark(output, train_episodes=500, test_episodes=500)
            audit_benchmark(output)
            audit = json.loads((output / "audit.json").read_text())
            self.assertEqual(len(audit["rows"]), 8)
            path = output / "field_0p25_informed.npz"
            with np.load(path, allow_pickle=False) as saved:
                arrays = {name: saved[name] for name in saved.files}
            arrays["next_phase"][:] = 1 - arrays["next_phase"]
            np.savez_compressed(path, **arrays)
            with self.assertRaisesRegex(ValueError, "held-out score drift"):
                audit_benchmark(output)


if __name__ == "__main__":
    unittest.main()
