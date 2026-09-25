"""Tests for the claims-first gate on the physical-unity paper.

The gate constrains where scope disclaimers may appear, not their wording:
freely in the section labelled ``sec:limitations``, at most one in every other
section, the abstract included. It also requires the introduction to state
numbered claims, each pointing at the section that argues it. These tests pin
that contract, the advisory mode used on the frozen companion paper, and the
pass while the paper does not yet exist.
"""

import tempfile
import unittest
from pathlib import Path

import check_claims

GOOD = r"""
\documentclass{article}
\begin{document}
\begin{abstract}
Physical unity is a requirement current AI hardware lacks.
\end{abstract}
\section{Introduction}
\label{sec:intro}
\begin{enumerate}
\claim{sec:margin}{Digital content is locally constant in micro state.}
\end{enumerate}
\section{The margin theorem}
\label{sec:margin}
A locally constant content map ignores sub-threshold perturbations.
The theorem does not address analog hardware.
\section{Limitations}
\label{sec:limitations}
The premise is not derived. It cannot be confirmed against functionalism.
Neither fields nor synapses are singled out. The rate is stipulated.
\end{document}
"""


class CheckClaimsTest(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.root = Path(self._tmp.name)

    def write(self, body: str) -> Path:
        path = self.root / "main.tex"
        path.write_text(body, encoding="utf-8")
        return path

    def test_clean_paper_passes(self) -> None:
        self.assertEqual(check_claims.violations(self.write(GOOD)), [])

    def test_limitations_section_is_required(self) -> None:
        body = GOOD.replace(r"\section{Limitations}", r"\section{Remarks}").replace(
            r"\label{sec:limitations}", r"\label{sec:remarks}"
        )

        problems = check_claims.violations(self.write(body))

        self.assertTrue(any("sec:limitations" in p for p in problems))

    def test_second_disclaimer_outside_limitations_fails(self) -> None:
        body = GOOD.replace(
            "The theorem does not address analog hardware.",
            "The theorem does not address analog hardware. The rate is stipulated.",
        )

        problems = check_claims.violations(self.write(body))

        self.assertEqual(len(problems), 1)
        self.assertIn("The margin theorem", problems[0])

    def test_disclaimers_in_limitations_are_unlimited(self) -> None:
        body = GOOD.replace(
            "The rate is stipulated.",
            "The rate is stipulated. The kernel is not yet measured. "
            "It cannot be derived. It requires independent estimates.",
        )

        self.assertEqual(check_claims.violations(self.write(body)), [])

    def test_abstract_counts_as_a_section(self) -> None:
        body = GOOD.replace(
            "Physical unity is a requirement current AI hardware lacks.",
            "The premise is not derived and cannot be confirmed.",
        )

        problems = check_claims.violations(self.write(body))

        self.assertTrue(any("abstract" in p for p in problems))

    def test_introduction_needs_a_claim(self) -> None:
        body = GOOD.replace(
            r"\claim{sec:margin}{Digital content is locally constant in micro state.}", ""
        )

        problems = check_claims.violations(self.write(body))

        self.assertTrue(any("claim" in p for p in problems))

    def test_claim_must_point_at_an_existing_label(self) -> None:
        body = GOOD.replace(r"\claim{sec:margin}", r"\claim{sec:missing}")

        problems = check_claims.violations(self.write(body))

        self.assertTrue(any("sec:missing" in p for p in problems))

    def test_commented_lines_are_ignored(self) -> None:
        body = GOOD.replace(
            "The theorem does not address analog hardware.",
            "The theorem does not address analog hardware.\n% It cannot be derived.",
        )

        self.assertEqual(check_claims.violations(self.write(body)), [])

    def test_disclaimer_split_across_lines_is_counted(self) -> None:
        body = GOOD.replace(
            "The theorem does not address analog hardware.",
            "The theorem does not address analog hardware. The rate is\nstipulated.",
        )

        self.assertEqual(len(check_claims.violations(self.write(body))), 1)

    def test_companion_register_fails(self) -> None:
        """H success criterion: prose in the companion paper's register does not pass."""
        register = (
            "The factor is stipulated, not derived. Constructing a map with that "
            "factor remains a modelling obligation. No physical readout is given, "
            "and the joint witness holds in a specified model."
        )
        body = GOOD.replace("The theorem does not address analog hardware.", register)

        problems = check_claims.violations(self.write(body))

        self.assertEqual(len(problems), 1)
        self.assertIn("4 scope disclaimers", problems[0])

    def test_section_counts_report_every_section(self) -> None:
        counts = dict(check_claims.section_counts(self.write(GOOD)))

        self.assertEqual(counts["abstract"], 0)
        self.assertEqual(counts["The margin theorem"], 1)
        self.assertEqual(counts["Limitations"], 4)

    def test_main_fails_on_violations(self) -> None:
        path = self.write(GOOD.replace(r"\claim{sec:margin}", r"\claim{sec:missing}"))

        self.assertEqual(check_claims.main(["check_claims.py", str(path)]), 1)

    def test_main_passes_on_clean_paper(self) -> None:
        self.assertEqual(check_claims.main(["check_claims.py", str(self.write(GOOD))]), 0)

    def test_advisory_never_fails(self) -> None:
        path = self.write(GOOD.replace(r"\section{Limitations}", r"\section{Remarks}"))

        self.assertEqual(check_claims.main(["check_claims.py", "--advisory", str(path)]), 0)

    def test_absent_paper_passes(self) -> None:
        """The gate exists before the paper; nothing to check is not a failure."""
        absent = self.root / "unity" / "main.tex"

        self.assertEqual(check_claims.main(["check_claims.py", str(absent)]), 0)

    def test_default_target_is_the_unity_paper(self) -> None:
        self.assertEqual(check_claims.TARGET.parts[-2:], ("unity", "main.tex"))


if __name__ == "__main__":
    unittest.main()
