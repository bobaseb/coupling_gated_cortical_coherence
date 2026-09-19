"""Gates on the two files of TeX macros the publication \\inputs.

Both are generated, committed and read by ``main.tex`` or ``supplementary.tex``,
and both can fail in the same two ways: the committed file can drift from the
script that writes it, and a macro it defines can be one the publication never
states. The second is a slower failure -- nothing breaks, the numeral is simply
maintained and unread -- so it is the one that needs a gate.

``simulation_results.tex`` has its own drift test in ``test_simulation_tex``;
the citation helpers live here because both files use them.
"""

import re
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from energy_budget_check import DIFFUSION, cortical_budget
from energy_budget_check import write_tex as write_energy_tex
from fermi_estimate_check import compute_k
from fermi_estimate_check import write_tex as write_fermi_tex
from repo_root import REPO


def _published_prose() -> str:
    """The two publication files, concatenated, as the citation record.

    ``docs/primer.tex`` is deliberately excluded: it is a companion document,
    so a macro cited only there is still a numeral the publication generates
    and never states.
    """
    return (REPO / "main.tex").read_text(encoding="utf-8") + (REPO / "supplementary.tex").read_text(
        encoding="utf-8"
    )


def _uncited(content: str, prose: str, prefixes: tuple[str, ...] | None = None) -> list[str]:
    """Macros defined in ``content`` that ``prose`` never uses.

    The match is anchored against a following letter, so ``\\fermiK`` is not
    counted as cited by an occurrence of ``\\fermiKGamma``: TeX reads the
    longest run of letters as the control sequence, and a prefix test would
    certify a dead macro as live whenever a longer one shares its name.
    """
    defined = re.findall(r"\\newcommand\{\\([A-Za-z]+)\}", content)
    selected = defined if prefixes is None else [n for n in defined if n.startswith(prefixes)]
    return [name for name in selected if re.search(rf"\\{name}(?![A-Za-z])", prose) is None]


class FermiParamsTest(unittest.TestCase):
    """The same two questions, asked of the other generated macro file.

    ``fermi_params.tex`` comes from a different script and needs both checks
    for the same reasons: a committed macro file can drift from its generator,
    and a macro the publication never reads is a numeral the repository
    maintains and nobody states. The second is the sharper one here, because
    this generator's calculator computes more than the publication quotes and
    only the emitted part is a claim.
    """

    def _regenerated(self, directory: str) -> str:
        path = Path(directory) / "fermi_params.tex"
        write_fermi_tex(str(path))
        return path.read_text(encoding="utf-8")

    def test_every_generated_macro_is_cited_by_the_publication(self) -> None:
        with TemporaryDirectory() as directory:
            content = self._regenerated(directory)

        uncited = _uncited(content, _published_prose())
        self.assertEqual(uncited, [], f"generated but never cited: {uncited}")

    def test_committed_macros_match_the_generator(self) -> None:
        with TemporaryDirectory() as directory:
            expected = self._regenerated(directory)

        committed = Path(__file__).with_name("fermi_params.tex").read_text(encoding="utf-8")
        self.assertEqual(committed, expected)

    def test_the_coupling_estimate_is_computed_and_not_emitted(self) -> None:
        """The calculator keeps working; the publication keeps not quoting it."""
        _, _, coupling = compute_k(E=3.0, shift=0.4, lam=0.2, rho=5e4, f=6.0)
        self.assertGreater(coupling, 2.0 * 1.5)
        with TemporaryDirectory() as directory:
            content = self._regenerated(directory)
        self.assertNotIn("fpeval", content)
        self.assertNotIn(r"\newcommand{\fermiKGamma}", content)


class EnergyBudgetTest(unittest.TestCase):
    """The energy budget's macros, and the one thing its numbers must not say.

    The budget converts the installed-energy condition into a bound on the
    conversion factor; it does not evaluate the condition, because the
    conversion factor is declared hardware data this development derives
    nowhere. The last test fixes that reading in the arithmetic: the required
    factor is exactly ``2 D`` divided by the installed energy, so a reader who
    supplies a factor can check the comparison themselves.
    """

    def _regenerated(self, directory: str) -> str:
        path = Path(directory) / "energy_budget.tex"
        write_energy_tex(str(path))
        return path.read_text(encoding="utf-8")

    def test_every_generated_macro_is_cited_by_the_publication(self) -> None:
        with TemporaryDirectory() as directory:
            content = self._regenerated(directory)

        uncited = _uncited(content, _published_prose())
        self.assertEqual(uncited, [], f"generated but never cited: {uncited}")

    def test_committed_macros_match_the_generator(self) -> None:
        with TemporaryDirectory() as directory:
            expected = self._regenerated(directory)

        committed = Path(__file__).with_name("energy_budget.tex").read_text(encoding="utf-8")
        self.assertEqual(committed, expected)

    def test_required_conversion_is_the_threshold_over_the_installed_energy(self) -> None:
        result = cortical_budget()
        self.assertAlmostEqual(
            result.kappa_required * result.installed_energy, 2.0 * DIFFUSION, places=12
        )

    def test_the_installed_energy_is_the_power_held_for_one_diffusion_time(self) -> None:
        result = cortical_budget()
        self.assertAlmostEqual(result.residence_time, 1.0 / DIFFUSION)
        self.assertAlmostEqual(result.installed_energy, result.region_power * result.residence_time)

    def test_energy_is_far_above_the_thermal_floor(self) -> None:
        """The one comparison the budget settles on its own."""
        self.assertGreater(cortical_budget().thermal_quanta, 1e12)


if __name__ == "__main__":
    unittest.main()
