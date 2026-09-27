"""Gates on the physical-unity paper's yardstick figure (U78)."""

import tempfile
import unittest
from pathlib import Path

import unity_figures as uf


class YardstickFigureTest(unittest.TestCase):
    def test_the_series_come_from_the_saved_summaries(self) -> None:
        series = uf.series(uf.FIGURES)
        self.assertEqual(len(series.yardsticks), len(series.membrane_pass[0]))
        for low, high in zip(*series.membrane_pass, strict=True):
            self.assertLessEqual(low, high)
        self.assertTrue(all(v == 0.0 for v in series.latched_pass))

    def test_the_node_passes_up_to_the_fluctuation_and_not_beyond(self) -> None:
        series = uf.series(uf.FIGURES)
        for y, hit in zip(series.yardsticks, series.node_hit, strict=True):
            self.assertEqual(hit, 1.0 if y <= series.fluctuation else 0.0)

    def test_the_synchronizer_passes_no_yardstick_from_the_fluctuation_up(self) -> None:
        series = uf.series(uf.FIGURES)
        for y, share, hit in zip(series.yardsticks, series.sync_pass, series.sync_hit, strict=True):
            if y >= series.fluctuation:
                self.assertEqual((share, hit), (0.0, 0.0))

    def test_the_figure_is_drawn_without_running_a_simulation(self) -> None:
        with tempfile.TemporaryDirectory() as root:
            path = Path(root) / "figure.png"
            uf.draw(uf.series(uf.FIGURES), path)
            self.assertGreater(path.stat().st_size, 10_000)

    def test_the_paper_prints_the_committed_figure(self) -> None:
        paper = (uf.OUTPUT.parent / "main.tex").read_text()
        self.assertIn(f"\\includegraphics[width=\\linewidth]{{{uf.OUTPUT.name}}}", paper)
        self.assertTrue(uf.OUTPUT.exists())


if __name__ == "__main__":
    unittest.main()
