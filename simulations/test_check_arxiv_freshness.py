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


class FreshnessTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)
        self.write("main.tex", "\\includegraphics{plot.png}\n")
        self.write("supplementary.tex", "text\n")
        self.write("plot.png", "png")
        for name in check_arxiv_freshness.UNREFERENCED:
            self.write(name, "asset\n")

    def write(self, name: str, body: str) -> Path:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
        return path

    def build(self) -> None:
        """What prepare_arxiv.sh leaves behind: the directory and its manifest."""
        lines = [
            f"{check_arxiv_freshness.digest(self.root / name)} {name}"
            for name in sorted(check_arxiv_freshness.expected_sources(self.root))
        ]
        self.write(check_arxiv_freshness.MANIFEST, "# built\n" + "\n".join(lines) + "\n")

    def test_no_built_submission_passes(self) -> None:
        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 0)

    def test_a_fresh_build_passes(self) -> None:
        self.build()

        self.assertEqual(check_arxiv_freshness.main(["prog", str(self.root)]), 0)

    def test_a_directory_without_a_manifest_fails(self) -> None:
        (self.root / check_arxiv_freshness.SUBMISSION).mkdir()

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

        reasons = check_arxiv_freshness.drift(
            self.root,
            check_arxiv_freshness.recorded_sources(self.root / check_arxiv_freshness.MANIFEST),
        )

        self.assertIn("second.png: in the manuscript, not in the built submission", reasons)

    def test_a_dropped_figure_fails(self) -> None:
        self.build()
        self.write("main.tex", "no figures now\n")

        reasons = check_arxiv_freshness.drift(
            self.root,
            check_arxiv_freshness.recorded_sources(self.root / check_arxiv_freshness.MANIFEST),
        )

        self.assertIn("plot.png: in the built submission, no longer a source", reasons)

    def test_manifest_comments_are_not_sources(self) -> None:
        self.write(check_arxiv_freshness.MANIFEST, "# built today\n#\n")

        self.assertEqual(
            check_arxiv_freshness.recorded_sources(self.root / check_arxiv_freshness.MANIFEST), {}
        )


if __name__ == "__main__":
    unittest.main()
