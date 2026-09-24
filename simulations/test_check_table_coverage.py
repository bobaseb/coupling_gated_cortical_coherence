"""Every Lean declaration the article names must have a row in Table S1."""

import unittest

import check_table_coverage as cov
from repo_root import REPO

TABLE = r"""
\begin{longtable}{|l|l|l|}
\caption{Mapping of physical claims to Lean 4 formalization status.}\\
\hline
Winding states & \texttt{char\_\allowbreak is\_\allowbreak kuramoto\_\allowbreak
trajectory} carries it & Theorem \\ \hline
Capacity & \texttt{Phase1\_\allowbreak Phase\-Space\-Capacity} holds
\texttt{absorb\_\allowbreak not\_\allowbreak injective} & Theorem \\ \hline
\label{tab:full}
\end{longtable}
"""

OTHER_TABLE = r"""
\begin{longtable}{|l|l|}
\caption{An unrelated table.}\\
\texttt{no\_isolated\_defect} & irrelevant \\ \hline
\label{tab:summary}
\end{longtable}
"""


class NormaliseTest(unittest.TestCase):
    def test_strips_latex_break_and_escape_markup(self) -> None:
        cases = {
            r"char\_is\_kuramoto\_trajectory": "char_is_kuramoto_trajectory",
            r"char\_\allowbreak is\_\allowbreak kuramoto": "char_is_kuramoto",
            r"Phase1\_\allowbreak Phase\-Space\-Capacity": "Phase1_PhaseSpaceCapacity",
            "order\\_parameter\\_\nr\\_sq": "order_parameter_r_sq",
        }
        for raw, want in cases.items():
            with self.subTest(raw=raw):
                self.assertEqual(cov.normalise(raw), want)


class TableRegionTest(unittest.TestCase):
    def test_selects_the_longtable_carrying_the_claim_map(self) -> None:
        region = cov.table_region(OTHER_TABLE + TABLE)

        self.assertIn("char", region)
        self.assertNotIn("no_isolated_defect", region.replace("\\_", "_"))

    def test_missing_table_is_an_error_not_a_silent_pass(self) -> None:
        with self.assertRaises(cov.TableNotFound):
            cov.table_region(OTHER_TABLE)


class CoverageTest(unittest.TestCase):
    def setUp(self) -> None:
        self.declared = {
            "char_is_kuramoto_trajectory",
            "no_isolated_defect",
            "absorb_not_injective",
        }

    def test_declaration_named_by_the_article_and_absent_from_the_table(self) -> None:
        article = "A defect cannot stand alone (\\texttt{no\\_isolated\\_defect}).\n"

        found = cov.uncovered(article, TABLE, self.declared)

        self.assertEqual(found, [(1, "no_isolated_defect")])

    def test_declaration_present_in_the_table_is_covered(self) -> None:
        article = "Stationary (\\texttt{char\\_is\\_kuramoto\\_trajectory}).\n"

        self.assertEqual(cov.uncovered(article, TABLE, self.declared), [])

    def test_a_row_may_carry_a_name_the_article_never_uses(self) -> None:
        """Coverage runs one way: the table is a map, not an index of the article."""
        self.assertEqual(cov.uncovered("Nothing cited here.\n", TABLE, self.declared), [])

    def test_module_and_file_names_are_not_declarations(self) -> None:
        article = (
            "See \\texttt{Phase4\\_\\allowbreak KuramotoDynamics} and "
            "\\texttt{Chain.lean} and \\texttt{Examples}.\n"
        )

        self.assertEqual(cov.uncovered(article, TABLE, self.declared), [])

    def test_a_qualified_spelling_is_matched_by_its_final_segment(self) -> None:
        article = "By \\texttt{Winding.no\\_isolated\\_defect} it holds.\n"
        table = TABLE.replace("Capacity &", "Defects & \\texttt{no\\_isolated\\_defect} &")

        self.assertEqual(cov.uncovered(article, table, self.declared), [])


class RepositoryTest(unittest.TestCase):
    def test_the_publication_as_committed_is_covered(self) -> None:
        self.assertEqual(cov.main(), 0)

    def test_the_article_actually_names_declarations_to_check(self) -> None:
        """A rule that matches nothing would pass while checking nothing."""
        article = (REPO / "main.tex").read_text(encoding="utf-8")
        declared = cov.declared_tails(cov.LEAN_DIR)

        self.assertGreaterEqual(len(cov.article_references(article, declared)), 0)


if __name__ == "__main__":
    unittest.main()
