# Plan: Add Property-Based Testing

**Intent:** Introduce property-based testing to the Python simulation suite using the `hypothesis` library to verify mathematical invariants of core numerical functions.
**Constraints:** 
- Must use the `hypothesis` framework alongside the existing `unittest` structure.
- Must not break existing deterministic tests. 
- Must comply with the existing strict static type checking (`mypy`) and linting (`ruff`).
- Keep additions Small, Reviewable, Reversible (SRR).
**Success Criteria:** Property tests run successfully and all pre-commit checks pass.

## Tasks

- [x] Add `hypothesis` to the `dev` dependency group in `simulations/pyproject.toml`.
- [x] Run `uv lock` in `simulations/` to update the lockfile.
- [x] Add property-based tests to `simulations/test_structural_resonance.py` for mathematical functions:
  - `project`: prove that total resources are conserved and the matrix is symmetrical with zero diagonal.
  - `symmetric_gradient`: prove symmetry for arbitrary inputs.
- [x] Add property-based tests to `simulations/test_quasistatic_error.py` for logical invariants:
  - `stationary_order`: prove it evaluates to 0 below threshold and falls within (0, 1) above threshold for varied ranges of inputs.
- [x] Run `uv run pytest` to ensure tests pass.
- [x] Run `uv run pre-commit run --all-files` to ensure format, types, and style checks pass.

## M — Publication alignment, closed

**Eight sentences in the publication were waiting on measurements this repository
already had.** N7–N9 and N12–N13 each deferred their publication alignment, for
the same stated reason and on the same terms: a macro is required for every
numeral that *reaches* the publication, and none of theirs does yet, so
generating macros nobody cites would put dead entries into a generated file and
into its drift test. That reasoning is sound for each pass on its own and it
does not survive being repeated — two deferrals with nothing tracking them is
how a numeral that contradicts a published sentence stays published. This
section is what tracks them. Unlike the P-items below, nothing here is blocked
on anyone else.

The sentences, with the item that bears on each:

| From | Sentence |
| :--- | :--- |
| N7 | `supplementary.tex` on what a discriminating awakening experiment must span — the estimator as published cannot discriminate at the 100 sites the protocol permits at *any* concentration, and the first fix is a bin count of 24 or fewer |
| N7 | the same section's independent calibration, called optimistic for EEG — the requirement at the observed concentration rises from 3,000 to 31,000 sites between independence and full clustering |
| N8 | `K_c = 2D` is stated for a scalar coupling with no aggregation rule; N8 supplies the row-sum rule, the ±0.08 error bound over the declared decay range, and the measurement that frequency heterogeneity rather than spatial structure is what the identical-frequency restriction holds back |
| N9 | the compatibility clause is recorded as having no observable; N9 supplies one, its two required diagnostics, and the limit that no phase-derived statistic substitutes for it |
| N12 | `main.tex:182` motivates coupling that "evolves more slowly than phase dynamics" and quantifies nothing; N12 supplies the required time-scale ratio and the reading of the cited geometry against it |
| N12 | `supplementary.tex` reports `ΔK ∝ v^0.443` as "near the predicted exponent 1/2 at this resolution"; N12 supplies the deterministic threshold limit of the same measurement, `0.447` over four speeds and `0.418` over three |
| N12 | the recovery section reads a crossing of `K_c` as an onset; N12 shows the quasi-static residual on a leg symmetric about `K_c` is rate-independent, so branch tracking is unattainable exactly where that argument uses it |
| N13 | nothing says which statistic of a varying coupling `K_c` is read against; N13 supplies the mean in the fast limit, the quasi-static average in the slow non-crossing limit, and neither for a slow crossing drive |

**Acceptance rule.** Every numeral that reaches either publication file is a
generated macro read from a saved summary (AGENTS.md §3) — no hand-typed
numerals, and regenerating must not rerun a sweep. Withdrawn claims go to
`CHANGELOG.md`, which is the pass that earns the entry the four preceding passes
deliberately did not write. The three tracked PDFs are rebuilt in the same
commit as their sources (AGENTS.md §6), and `prepare_arxiv.sh` is re-run or
`arxiv_submit/` removed (AGENTS.md §7).

- [x] **M1 — Generate the macros.** Extend `simulations/simulation_tex.py` to
      read `collapse_design`, `spatial_reduction`, `compatibility_estimator`,
      `quasistatic_error` and `fluctuating_coupling` summaries, emit a macro for
      each numeral the rewritten sentences will cite, and extend
      `test_simulation_tex.py`'s drift test to cover them. Emit a macro only for
      a numeral a sentence actually uses: an unused macro is the dead entry this
      section exists to avoid creating.
- [x] **M2 — Rewrite the eight sentences**, in present tense and with no
      drafting-history narration (AGENTS.md §5, and `check_prose.py` enforces
      it). Three of them — the awakening-experiment span, the `v^0.443` reading
      and the onset crossing — are claims that become false or incomplete, so
      each needs its replacement written rather than deleted.
- [x] **M3 — Close the artifacts.** Rebuild `main.pdf`, `supplementary.pdf` and
      `docs/primer.pdf`, check the primer's explanation still matches what the
      manuscript now says, refresh or remove the built arXiv submission, and
      write the `CHANGELOG.md` entry naming the claims withdrawn.

**Closing record.** `simulation_tex.py` gained `_design_macros`,
`_reduction_macros`, `_compatibility_macros`, `_quasistatic_macros` and
`_fluctuating_macros`, reading the five summaries named in M1; the drift test
gained per-group assertions and a check that those five groups emit no macro the
publication does not cite. The eight sentences are rewritten in place, three of
them withdrawing a claim, and `CHANGELOG.md` carries those three. `main.pdf`,
`supplementary.pdf` and `docs/primer.pdf` are rebuilt; the primer's two
compatibility statements and its aggregation sentence are updated to match.

**Still open from the ledger `0505cac` truncated:** the R research programme
(R1-R12) is restored in `tasks/research_programme.md`. The P submission-readiness
items and the pass records remain in `dde1a36:tasks/todo.md`.
