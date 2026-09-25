"""Tests for the built-arXiv-submission freshness gate.

The submission is not tracked, so the gate's whole job is to answer a question
no diff can: does the directory on disk correspond to the manuscript on disk. It
answers it from the manifest ``prepare_arxiv.sh`` writes, and from the source set
re-derived from the .tex files, so that an *added* figure is caught as well as a
changed one. No built submission is not a failure; a stale one is.
"""

import tempfile
import unittest
from pathlib import Path

import check_arxiv_freshness
from check_arxiv_freshness import COMPANION, UNITY, Submission


class Tree(unittest.TestCase):
    """A repository with both papers' sources, and no built submission."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)
        self.write("main.tex", "\\includegraphics{plot.png}\n")
        self.write("supplementary.tex", "text\n")
        self.write("plot.png", "png")
        for submission in check_arxiv_freshness.SUBMISSIONS:
            for name in submission.unreferenced:
                self.write(name, "asset\n")

    def write(self, name: str, body: str) -> Path:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
        return path

    def build(self, submission: Submission = COMPANION) -> None:
        """What a prepare_arxiv.sh leaves behind: the directory and its manifest."""
        lines = [
            f"{check_arxiv_freshness.digest(self.root / name)} {name}"
            for name in sorted(check_arxiv_freshness.expected_sources(self.root, submission))
        ]
        self.write(submission.manifest, "# built\n" + "\n".join(lines) + "\n")

    def drift(self, submission: Submission = COMPANION) -> list[str]:
        return check_arxiv_freshness.drift(
            self.root,
            submission,
            check_arxiv_freshness.recorded_sources(self.root / submission.manifest),
        )


class FreshnessTest(Tree):
    def test_no_built_submission_passes(self) -> None:
        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 0)

    def test_a_fresh_build_passes(self) -> None:
        self.build()

        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 0)

    def test_a_directory_without_a_manifest_fails(self) -> None:
        (self.root / COMPANION.directory).mkdir()

        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 1)

    def test_an_edited_source_fails(self) -> None:
        self.build()
        self.write("main.tex", "\\includegraphics{plot.png}\n% revised\n")

        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 1)

    def test_a_regenerated_figure_fails(self) -> None:
        """The failure that was missed: the .tex is untouched and the .png is not."""
        self.build()
        self.write("plot.png", "a fourth panel")

        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 1)

    def test_an_added_figure_fails(self) -> None:
        self.build()
        self.write("second.png", "png")
        self.write("supplementary.tex", "\\includegraphics{second.png}\n")

        reasons = self.drift()

        self.assertIn("second.png: in the manuscript, not in the built submission", reasons)

    def test_a_dropped_figure_fails(self) -> None:
        self.build()
        self.write("main.tex", "no figures now\n")

        reasons = self.drift()

        self.assertIn("plot.png: in the built submission, no longer a source", reasons)

    def test_manifest_comments_are_not_sources(self) -> None:
        self.write(COMPANION.manifest, "# built today\n#\n")

        self.assertEqual(check_arxiv_freshness.recorded_sources(self.root / COMPANION.manifest), {})


class UnityTest(Tree):
    """The physical-unity paper has its own build, manifest and source set."""

    def setUp(self) -> None:
        super().setUp()
        self.write("unity/main.tex", "\\input{unity_results}\n")
        self.write("unity/unity_results.tex", "macros\n")

    def test_the_unity_sources_are_read_from_its_own_document(self) -> None:
        sources = check_arxiv_freshness.expected_sources(self.root, UNITY)

        self.assertIn("unity/unity_results.tex", sources)
        self.assertIn("unity/prepare_arxiv.sh", sources)
        self.assertNotIn("main.tex", sources)

    def test_a_fresh_unity_build_passes(self) -> None:
        self.build(UNITY)

        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 0)

    def test_an_edited_unity_source_fails(self) -> None:
        self.build(UNITY)
        self.write("unity/unity_results.tex", "regenerated\n")

        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 1)
        self.assertIn(
            "unity/unity_results.tex: changed since the submission was built", self.drift(UNITY)
        )

    def test_a_stale_unity_build_fails_beside_a_fresh_companion(self) -> None:
        self.build(COMPANION)
        self.build(UNITY)
        self.write("unity/main.tex", "\\input{unity_results}\n% revised\n")

        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 1)

    def test_the_shared_helpers_are_a_source_of_both(self) -> None:
        for submission in check_arxiv_freshness.SUBMISSIONS:
            with self.subTest(submission=submission.directory):
                self.assertIn(
                    "arxiv_assets/arxiv_lib.sh",
                    check_arxiv_freshness.expected_sources(self.root, submission),
                )


if __name__ == "__main__":
    unittest.main()
