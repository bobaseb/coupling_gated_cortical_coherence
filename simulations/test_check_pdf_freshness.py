"""Tests for the tracked-PDF freshness gate.

Two contracts are pinned here. The dependency set is *derived from the sources*
rather than listed, so the tests exercise the derivation -- transitive inputs,
figures found through ``\\graphicspath``, commented-out lines that pull in
nothing. And the gate itself is one-sided: a rebuilt PDF with unchanged sources
is fine, a changed source with an unrebuilt PDF is not.
"""

import subprocess  # nosec B404 -- fixed argv below, no shell
import tempfile
import unittest
from pathlib import Path

import check_pdf_freshness
import repo_root


class DependencyTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)

    def write(self, name: str, body: str = "") -> Path:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
        return path

    def test_inputs_are_followed_transitively(self) -> None:
        top = self.write("top.tex", "\\input{middle}\n")
        middle = self.write("middle.tex", "\\input{leaf}\n")
        leaf = self.write("leaf.tex", "text\n")

        self.assertEqual(check_pdf_freshness.dependencies(top), {middle.resolve(), leaf.resolve()})

    def test_input_above_the_document_directory_resolves(self) -> None:
        """The primer sits in docs/ and inputs generated macros from simulations/."""
        macros = self.write("simulations/results.tex", "\\newcommand{\\x}{1}\n")
        primer = self.write("docs/primer.tex", "\\input{../simulations/results}\n")

        self.assertEqual(check_pdf_freshness.dependencies(primer), {macros.resolve()})

    def test_external_documents_are_followed(self) -> None:
        """The supplement reads the article's numbering, so the article is a source of it."""
        main = self.write("main.tex", "\\input{shared}\n")
        shared = self.write("shared.tex", "macros\n")
        supplement = self.write("supplementary.tex", "\\usepackage{xr}\n\\externaldocument{main}\n")

        self.assertEqual(
            check_pdf_freshness.dependencies(supplement), {main.resolve(), shared.resolve()}
        )

    def test_external_document_without_citations_remains_a_dependency(self) -> None:
        """xr's second option suppresses citations while retaining label dependencies."""
        main = self.write("main.tex", "\\input{shared}\n")
        shared = self.write("shared.tex", "macros\n")
        supplement = self.write("supplementary.tex", "\\externaldocument[][nocite]{main}\n")

        self.assertEqual(
            check_pdf_freshness.dependencies(supplement), {main.resolve(), shared.resolve()}
        )

    def test_figures_resolve_through_graphicspath(self) -> None:
        figure = self.write("figures/plot.png", "not really a png")
        tex = self.write(
            "article.tex",
            "\\graphicspath{{figures/}{./}}\n\\includegraphics[width=0.5\\linewidth]{plot.png}\n",
        )

        self.assertEqual(check_pdf_freshness.dependencies(tex), {figure.resolve()})

    def test_commented_lines_pull_in_nothing(self) -> None:
        self.write("dropped.tex", "text\n")
        tex = self.write("article.tex", "% \\input{dropped}\n")

        self.assertEqual(check_pdf_freshness.dependencies(tex), set())

    def test_unresolvable_name_is_skipped(self) -> None:
        """A missing figure is a build error, caught by LaTeX rather than here."""
        tex = self.write("article.tex", "\\includegraphics{absent.png}\n\\input{absent}\n")

        self.assertEqual(check_pdf_freshness.dependencies(tex), set())

    def test_cycle_terminates(self) -> None:
        first = self.write("first.tex", "\\input{second}\n")
        second = self.write("second.tex", "\\input{first}\n")

        self.assertEqual(
            check_pdf_freshness.dependencies(first), {first.resolve(), second.resolve()}
        )


class GateTest(unittest.TestCase):
    def test_changed_source_without_the_pdf_is_stale(self) -> None:
        behind = check_pdf_freshness.behind_sources(
            "main.pdf", {"main.tex", "references.tex"}, {"main.tex"}
        )

        self.assertEqual(behind, ["main.tex"])

    def test_rebuilt_pdf_is_not_stale(self) -> None:
        behind = check_pdf_freshness.behind_sources(
            "main.pdf", {"main.tex"}, {"main.tex", "main.pdf"}
        )

        self.assertEqual(behind, [])

    def test_unrelated_change_is_not_stale(self) -> None:
        behind = check_pdf_freshness.behind_sources("main.pdf", {"main.tex"}, {"Main.lean"})

        self.assertEqual(behind, [])

    def test_publication_change_without_the_primer_is_noted(self) -> None:
        self.assertTrue(check_pdf_freshness.companion_is_untouched({"main.tex", "main.pdf"}))

    def test_publication_change_with_the_primer_is_not_noted(self) -> None:
        self.assertFalse(
            check_pdf_freshness.companion_is_untouched({"main.tex", "docs/primer.tex"})
        )

    def test_primer_only_change_is_not_noted(self) -> None:
        self.assertFalse(check_pdf_freshness.companion_is_untouched({"docs/primer.tex"}))

    def test_the_physical_unity_paper_is_a_deliverable(self) -> None:
        """Gated from its first commit, before anything links it."""
        self.assertIn(("unity/main.pdf", "unity/main.tex"), check_pdf_freshness.DOCUMENTS)

    def test_documents_are_the_tracked_deliverables(self) -> None:
        """A renamed or dropped deliverable must fail here rather than go unchecked."""
        tracked = subprocess.run(  # noqa: S603  # nosec B603 B607 -- fixed argv
            ["git", "ls-files", "*.pdf"],  # noqa: S607
            cwd=repo_root.REPO,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.split()

        self.assertEqual(sorted(pdf for pdf, _ in check_pdf_freshness.DOCUMENTS), sorted(tracked))


class EndToEndTest(unittest.TestCase):
    """The gate reading a real index, since that wiring is what runs on commit."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)
        for pdf, tex in check_pdf_freshness.DOCUMENTS:
            self._write(tex, "text\n")
            self._write(pdf, "%PDF-1.5\n")
        self._git("init", "-q")
        self._git("add", "-A")
        self._git("-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "base")

    def _write(self, name: str, body: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")

    def _git(self, *args: str) -> None:
        subprocess.run(  # noqa: S603  # nosec B603 B607 -- fixed argv, no shell
            ["git", *args],  # noqa: S607
            cwd=self.root,
            check=True,
            capture_output=True,
        )

    def test_source_staged_alone_fails(self) -> None:
        self._write("docs/primer.tex", "revised\n")
        self._git("add", "docs/primer.tex")

        self.assertEqual(check_pdf_freshness.main(["prog", str(self.root)]), 1)

    def test_source_and_pdf_staged_together_pass(self) -> None:
        self._write("docs/primer.tex", "revised\n")
        self._write("docs/primer.pdf", "%PDF-1.5 rebuilt\n")
        self._git("add", "docs/primer.tex", "docs/primer.pdf")

        self.assertEqual(check_pdf_freshness.main(["prog", str(self.root)]), 0)

    def test_nothing_staged_passes(self) -> None:
        self.assertEqual(check_pdf_freshness.main(["prog", str(self.root)]), 0)


if __name__ == "__main__":
    unittest.main()
