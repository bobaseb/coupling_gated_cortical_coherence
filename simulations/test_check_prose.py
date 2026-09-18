"""Publication prose must stand alone while retaining formal source references."""

import io
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

import check_prose


class CheckProseTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)

    def write(self, body: str, name: str = "sample.tex") -> Path:
        path = self.root / name
        path.write_text(body, encoding="utf-8")
        return path

    def test_markdown_references_are_rejected_in_latex_forms(self) -> None:
        references = (
            "See tasks/f5_f6_design.md.",
            r"See \texttt{tasks/f5\_f6\_design.md}.",
            r"See \texttt{tasks/f5\_\allowbreak f6\_\allowbreak design.md}.",
            r"See \texttt{REPORT.md}.",
            r"See \path{tasks/design.markdown}.",
            r"See \url{https://github.com/owner/project/blob/main/README.MD#design}.",
            r"See \href{https://github.com/owner/project/blob/main/design.md}{methods}.",
        )
        for reference in references:
            with self.subTest(reference=reference):
                path = self.write("The study has a fixed design.\n" + reference + "\n")
                hits = check_prose.find_hits(path)

                self.assertEqual(len(hits), 1)
                self.assertEqual(hits[0][0], 2)
                self.assertIn("Markdown", hits[0][2])
                self.assertEqual(hits[0][3], reference)

    def test_lean_references_and_repository_link_are_allowed(self) -> None:
        path = self.write(
            r"\texttt{Phase7\_\allowbreak Rigidity.lean} proves "
            r"\texttt{fieldCorrelation\_\allowbreak sited\_\allowbreak eq\_\allowbreak zero}."
            "\n"
            r"Code: \href{https://github.com/bobaseb/coupling_gated_cortical_coherence}"
            r"{\nolinkurl{bobaseb/coupling_gated_cortical_coherence}}."
            "\n"
            r"See \url{https://example.org/article.pdf} and \texttt{summary.json}."
        )

        self.assertEqual(check_prose.find_hits(path), [])

    def test_markdown_extension_requires_a_boundary(self) -> None:
        path = self.write(r"Files \texttt{checksums.md5} and \texttt{model.mdl}.")

        self.assertEqual(check_prose.find_hits(path), [])

    def test_drafting_history_is_still_rejected(self) -> None:
        path = self.write("An earlier draft stated a different premise.\n")

        self.assertTrue(check_prose.find_hits(path))

    def test_default_gate_rejects_markdown_in_either_publication(self) -> None:
        for name in ("main.tex", "supplementary.tex"):
            with self.subTest(name=name):
                self.write("The stated hypotheses imply the result.\n", "main.tex")
                self.write("The proof is in Lean.\n", "supplementary.tex")
                path = self.write(r"See \texttt{tasks/f5\_f6\_design.md}.", name)
                output = io.StringIO()

                with patch.object(check_prose, "REPO", self.root), redirect_stdout(output):
                    status = check_prose.main(["check_prose.py"])

                self.assertEqual(status, 1)
                self.assertIn(f"{path}:1:", output.getvalue())
                self.assertIn("Markdown", output.getvalue())

    def test_gate_accepts_self_contained_prose_with_lean_references(self) -> None:
        path = self.write(r"The theorem \texttt{rigid\_gap} applies to fixed wiring.")

        self.assertEqual(check_prose.main(["check_prose.py", str(path)]), 0)


if __name__ == "__main__":
    unittest.main()
