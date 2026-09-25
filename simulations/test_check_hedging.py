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

    def test_structural_disclaimers_are_counted(self) -> None:
        """The project's own dialect of scope statement, which the first lexicon missed."""
        lines = [
            "The factor is stipulated, not derived.",
            "The comparison supplies no energy price.",
            "No physical readout is constructed here.",
            "Identifying the kernel requires independent estimates.",
            "The identification remains a modelling obligation.",
            "The witness holds in a specified model.",
            "It proves neither cortical realization nor experience.",
            "The link is not yet measured.",
        ]
        for line in lines:
            with self.subTest(line=line):
                path = self.write(line + "\n")
                self.assertEqual(check_hedging.find_hits(path), [])
                self.assertGreaterEqual(check_hedging.count_scope(path), 1)

    def test_plain_claims_are_not_counted(self) -> None:
        """Positive statements must not register as disclaimers."""
        path = self.write(
            "Compatible sections glue to a unique global state. "
            "The bound grows as the square root of the population read.\n"
        )

        self.assertEqual(check_hedging.count_scope(path), 0)

    def test_contrast_and_tightness_are_not_counted(self) -> None:
        """Calibration on main.tex: bare 'rather than' and 'cannot' were mostly claims."""
        lines = [
            "Error grows linearly in hops rather than with population.",
            "The order cannot be improved in general.",
            "The cover cannot be chosen to make agreement come out.",
        ]
        for line in lines:
            with self.subTest(line=line):
                self.assertEqual(check_hedging.count_scope(self.write(line + "\n")), 0)

    def test_narrowed_forms_still_count(self) -> None:
        lines = [
            "Each edge is supplied rather than derived.",
            "It is the bridge assumption rather than a derived result.",
            "Phase statistics cannot supply these estimates.",
            "The exponent cannot alone discriminate a field mechanism.",
            "Phase agreement cannot replace that measurement.",
            "It cannot be confirmed against functionalism.",
        ]
        for line in lines:
            with self.subTest(line=line):
                self.assertEqual(check_hedging.count_scope(self.write(line + "\n")), 1)

    def test_publication_files_are_the_default_targets(self) -> None:
        self.assertEqual(check_hedging.FILES, ("main.tex", "supplementary.tex"))


if __name__ == "__main__":
    unittest.main()
