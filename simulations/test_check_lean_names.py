"""The main text of either paper names no Lean declaration, module or file."""

import unittest

import check_lean_names as gate

DECLARED = {"conductance_mono", "conductance_le_shell", "of_comp", "energy"}
MODULES = {"Phase10_AgreementResistance", "Chain"}


def names(tex: str) -> list[str]:
    return [name for _, name in gate.findings(tex, DECLARED, MODULES)]


class NormaliseTest(unittest.TestCase):
    def test_strips_latex_break_and_escape_markup(self) -> None:
        cases = {
            r"conductance\_mono": "conductance_mono",
            r"conductance\_\allowbreak le\_\allowbreak shell": "conductance_le_shell",
            r"Phase10\_\allowbreak Agreement\-Resistance": "Phase10_AgreementResistance",
            "conductance\\_\nmono": "conductance_mono",
        }
        for raw, want in cases.items():
            with self.subTest(raw=raw):
                self.assertEqual(gate.normalise(raw), want)


class MainTextTest(unittest.TestCase):
    def test_stops_at_the_appendix(self) -> None:
        text = gate.main_text("body\n\\appendix\nformal results\n")

        self.assertIn("body", text)
        self.assertNotIn("formal", text)

    def test_stops_at_end_of_document_without_an_appendix(self) -> None:
        self.assertNotIn("after", gate.main_text("body\n\\end{document}\nafter\n"))

    def test_keeps_line_numbers(self) -> None:
        text = gate.main_text("one\n% comment\nthree\n\\appendix\n")

        self.assertEqual(text.splitlines()[2], "three")

    def test_drops_comments_but_not_escaped_percent(self) -> None:
        text = gate.main_text("50\\% of it % \\texttt{conductance\\_mono}\n")

        self.assertIn("50\\%", text)
        self.assertNotIn("conductance", text)


class FindingsTest(unittest.TestCase):
    def test_a_declaration_in_texttt_fails(self) -> None:
        self.assertEqual(names("see (\\texttt{conductance\\_mono}).\n"), ["conductance_mono"])

    def test_the_same_name_after_the_appendix_passes(self) -> None:
        tex = "body\n\\appendix\n\\texttt{conductance\\_mono}\n"

        self.assertEqual(names(gate.main_text(tex)), [])

    def test_a_dotted_name_fails_by_its_final_segment(self) -> None:
        self.assertEqual(
            names("\\texttt{GradedDependence.of\\_comp}\n"), ["GradedDependence.of_comp"]
        )

    def test_a_broken_span_is_one_name(self) -> None:
        tex = "\\texttt{conductance\\_\\allowbreak le\\_\\allowbreak\nshell}\n"

        self.assertEqual(names(tex), ["conductance_le_shell"])

    def test_module_names_and_lean_files_fail(self) -> None:
        tex = "\\texttt{Phase10\\_AgreementResistance} and \\texttt{Chain.lean}\n"

        self.assertEqual(names(tex), ["Phase10_AgreementResistance", "Chain.lean"])

    def test_a_bare_escaped_identifier_fails(self) -> None:
        self.assertEqual(names("by conductance\\_le\\_shell we get\n"), ["conductance_le_shell"])

    def test_other_code_spans_pass(self) -> None:
        tex = (
            "\\texttt{simulations/empirical\\_collapse.py}, \\texttt{a@b.com},\n"
            "\\texttt{5ce203ecd53f8c3e47ee5530d7c86b94a55f0183}, \\texttt{1010}\n"
        )

        self.assertEqual(names(tex), [])

    def test_a_declaration_name_used_as_a_prose_word_passes(self) -> None:
        self.assertEqual(names("the energy of the configuration\n"), [])

    def test_reports_the_line(self) -> None:
        found = gate.findings("one\ntwo \\texttt{conductance\\_mono}\n", DECLARED, MODULES)

        self.assertEqual(found, [(2, "conductance_mono")])


class RepositoryTest(unittest.TestCase):
    def test_the_lean_sources_supply_declarations_and_modules(self) -> None:
        declared, modules = gate.lean_names(gate.LEAN_DIR)

        self.assertIn("conductance_mono", declared)
        self.assertIn("Phase10_AgreementResistance", modules)

    def test_both_papers_are_checked(self) -> None:
        self.assertEqual({path.name for path in gate.DOCUMENTS}, {"main.tex"})
        self.assertEqual(len(gate.DOCUMENTS), 2)


if __name__ == "__main__":
    unittest.main()
