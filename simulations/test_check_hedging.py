"""Tests for the disclaimer-language reporter.

The reporter is advisory by design: it surfaces candidates and a human or agent
decides whether each one earns its place. These tests pin that contract -- what
it flags, what it merely counts, and the fact that reporting alone does not fail
a commit.
"""

import tempfile
import unittest
from pathlib import Path

import check_hedging


class CheckHedgingTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)

    def write(self, body: str) -> Path:
        path = self.root / "sample.tex"
        path.write_text(body, encoding="utf-8")
        return path

    def test_reader_instruction_is_flagged(self) -> None:
        path = self.write("It is worth noting that the branch is unique.\n")

        hits = check_hedging.find_hits(path)

        self.assertEqual([hit.category for hit in hits], ["reader-instruction"])
        self.assertEqual(hits[0].lineno, 1)

    def test_empty_hedge_is_flagged(self) -> None:
        path = self.write("The result is arguably somewhat surprising.\n")

        categories = {hit.category for hit in check_hedging.find_hits(path)}

        self.assertEqual(categories, {"empty-hedge"})

    def test_scope_disclaimer_is_counted_not_flagged(self) -> None:
        """Scope statements are the paper's honesty; their density is the signal."""
        path = self.write("This does not imply that cortex crosses the threshold.\n")

        self.assertEqual(check_hedging.find_hits(path), [])
        self.assertEqual(check_hedging.count_scope(path), 1)

    def test_density_is_per_thousand_words(self) -> None:
        path = self.write(("word " * 500) + "\nthis does not imply anything\n")

        self.assertAlmostEqual(check_hedging.scope_density(path), 2.0, delta=0.5)

    def test_latex_commands_do_not_match(self) -> None:
        """A macro name is not prose, so matching requires a word boundary in text."""
        path = self.write("\\input{simulation_results}\n\\label{sec:important}\n")

        self.assertEqual(check_hedging.find_hits(path), [])

    def test_advisory_run_succeeds_despite_hits(self) -> None:
        path = self.write("It is important to note that this is arguably true.\n")

        self.assertEqual(check_hedging.main(["check_hedging.py", str(path)]), 0)

    def test_strict_run_fails_on_flags(self) -> None:
        path = self.write("It is important to note this.\n")

        self.assertEqual(check_hedging.main(["check_hedging.py", "--strict", str(path)]), 1)

    def test_strict_run_succeeds_on_scope_only(self) -> None:
        path = self.write("The bound does not establish a learning rule.\n")

        self.assertEqual(check_hedging.main(["check_hedging.py", "--strict", str(path)]), 0)

    def test_missing_file_is_an_error(self) -> None:
        absent = self.root / "absent.tex"

        self.assertEqual(check_hedging.main(["check_hedging.py", str(absent)]), 2)

    def test_publication_files_are_the_default_targets(self) -> None:
        self.assertEqual(check_hedging.FILES, ("main.tex", "supplementary.tex"))


if __name__ == "__main__":
    unittest.main()
