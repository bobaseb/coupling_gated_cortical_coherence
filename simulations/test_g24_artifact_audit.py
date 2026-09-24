"""Artifact-only checks for the saved G24 candidate comparison."""

import json
import tempfile
import unittest
from pathlib import Path

import numpy as np

from g24_artifact_audit import (
    audit_candidates,
    audit_confirmation_arrays,
    audit_linear_baseline,
)
from g24_candidates import save_candidate_comparison
from g24_shared_task import save_linear_baseline


class ArtifactAuditTests(unittest.TestCase):
    def test_linear_floor_audit_handles_shifted_family(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_linear_baseline(output, repeats=2, split="scene_pair")
            audit_linear_baseline(output)
            audit = json.loads((output / "audit.json").read_text())
            self.assertEqual(len(audit["ranks"]), 5)
            self.assertGreater(audit["ranks"][-1]["test_squared_error"], 0)
            self.assertAlmostEqual(audit["declared_target_map"]["test_squared_error"], 0)
            with np.load(output / "decoders.npz", allow_pickle=False) as saved:
                arrays = {name: saved[name] for name in saved.files}
            arrays["rank_3"][0, 0] += 1
            np.savez_compressed(output / "decoders.npz", **arrays)
            with self.assertRaisesRegex(ValueError, "rank_3.*drift"):
                audit_linear_baseline(output)

    def test_recompute_scores_from_saved_checkpoints(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_candidate_comparison(output, repeats=2, iterations=3)
            audit_candidates(output)
            audit = json.loads((output / "audit.json").read_text())
            self.assertEqual(len(audit["candidates"]), 5)
            self.assertEqual(audit["source"], "g24_artifact_audit.py")

    def test_reject_changed_checkpoint(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_candidate_comparison(output, repeats=2, iterations=3)
            with np.load(output / "transformer.npz", allow_pickle=False) as saved:
                arrays = {name: saved[name] for name in saved.files}
            arrays["head"][0, 0] += 1
            np.savez_compressed(output / "transformer.npz", **arrays)
            with self.assertRaisesRegex(ValueError, "transformer.*score drift"):
                audit_candidates(output)

    def test_reject_changed_overlap_score(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_candidate_comparison(output, repeats=2, iterations=3)
            summary = json.loads((output / "summary.json").read_text())
            summary["candidates"][0]["overlap_disagreement_error_d1p0"] += 1
            (output / "summary.json").write_text(json.dumps(summary))
            with self.assertRaisesRegex(ValueError, "linear_full.*score drift"):
                audit_candidates(output)

    def test_reject_changed_saved_internal_code(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            save_candidate_comparison(output, repeats=2, iterations=3)
            with np.load(output / "phase_network.npz", allow_pickle=False) as saved:
                arrays = {name: saved[name] for name in saved.files}
            arrays["test_code"][0, 0] += 1
            np.savez_compressed(output / "phase_network.npz", **arrays)
            with self.assertRaisesRegex(ValueError, "phase_network.*code drift"):
                audit_candidates(output)

    def test_confirmation_array_audit_distinguishes_repeated_states(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for seed in (27, 28, 29):
                save_linear_baseline(
                    root / f"g24_confirm_seed{seed}_linear",
                    repeats=2,
                    seed=seed,
                    split="scene_pair",
                )
            audit_confirmation_arrays(root)
            report = json.loads((root / "g24_confirmation_arrays.json").read_text())
            self.assertTrue(report["noiseless_arrays_identical"])
            with np.load(
                root / "g24_confirm_seed29_linear" / "dataset.npz", allow_pickle=False
            ) as saved:
                arrays = {name: saved[name] for name in saved.files}
            arrays["test_input"][0, 0] += 1
            np.savez_compressed(root / "g24_confirm_seed29_linear" / "dataset.npz", **arrays)
            audit_confirmation_arrays(root)
            report = json.loads((root / "g24_confirmation_arrays.json").read_text())
            self.assertFalse(report["noiseless_arrays_identical"])


if __name__ == "__main__":
    unittest.main()
