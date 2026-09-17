"""Tests for the no-figure-printed-twice gate.

The rule is about resolved files rather than the strings in the sources, because
the article reaches a figure through ``\\graphicspath`` and the supplement spells
the path out: the duplicate this gate exists to catch was two spellings of one
file. It counts printings, so a repeat inside one document fails too.
"""

import tempfile
import unittest
from pathlib import Path

import check_figures
import check_pdf_freshness
import repo_root


class FigureUseTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)

    def write(self, name: str, body: str = "") -> Path:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
        return path

    def test_a_figure_printed_twice_is_counted_twice(self) -> None:
        figure = self.write("plot.png", "png")
        tex = self.write(
            "article.tex", "\\includegraphics{plot.png}\n\\includegraphics{plot.png}\n"
        )

        self.assertEqual(check_pdf_freshness.figure_uses(tex), [figure.resolve(), figure.resolve()])

    def test_an_external_document_contributes_no_printings(self) -> None:
        """The other document prints its own figures; xr only imports its numbering."""
        self.write("other.tex", "\\includegraphics{plot.png}\n")
        self.write("plot.png", "png")
        tex = self.write("article.tex", "\\externaldocument{other}\n")

        self.assertEqual(check_pdf_freshness.figure_uses(tex), [])

    def test_two_spellings_of_one_file_are_one_figure(self) -> None:
        self.write("simulations/figures/plot.png", "png")
        self.write(
            "main.tex", "\\graphicspath{{simulations/}{./}}\n\\includegraphics{figures/plot.png}\n"
        )
        self.write("supplementary.tex", "\\includegraphics{simulations/figures/plot.png}\n")

        counted = check_figures.printings(self.root)

        self.assertEqual(dict(counted), {"simulations/figures/plot.png": 2})
        self.assertEqual(check_figures.repeated(counted), [("simulations/figures/plot.png", 2)])
        self.assertEqual(check_figures.main(["prog", str(self.root)]), 1)

    def test_one_printing_each_passes(self) -> None:
        self.write("a.png", "png")
        self.write("b.png", "png")
        self.write("main.tex", "\\includegraphics{a.png}\n")
        self.write("supplementary.tex", "\\includegraphics{b.png}\n")

        self.assertEqual(check_figures.main(["prog", str(self.root)]), 0)

    def test_the_publication_itself_prints_each_figure_once(self) -> None:
        """The gate on the real sources, which is what runs on commit."""
        self.assertEqual(check_figures.repeated(check_figures.printings(repo_root.REPO)), [])


if __name__ == "__main__":
    unittest.main()
