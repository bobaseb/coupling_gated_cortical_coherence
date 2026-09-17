# Proof companion review — 2026-09-17

## Intent and constraints

Correct the companion's kernel and active-witness explanations, and give the
publication's spatial-measure interpretation an explicit Lean bridge. Preserve
the existing sheaf and chain assumptions, use the pinned toolchain, and add no
axioms or physical postulates. Leave the concurrent simulation work untouched.

## Plan and success criteria

- [ ] Write and run failing Lean acceptance statements before implementation.
- [x] Prove finite-cover gluing of actual finite measures, with uniqueness from
      their restrictions, and connect that measure to the existing sheaf gluing.
      Local finite-measure representations remain explicit; do not infer global
      finite mass from sheafification on an arbitrary space.
- [x] Exercise overlapping patches and fence the finite-cover assumption with
      a countably infinite family whose required total mass is infinite.
- [x] Correct the companion, the matching Lean scope comments, publication
      statements and primer; explain the exact remaining representation scope.
- [x] Refresh the companion extraction/coverage and rebuild affected PDFs and
      any existing arXiv submission. Pass the Lean build/axiom audit, companion
      tests/freshness and relevant repository gates.

## Validation record

The red-first step is left unchecked: the work was carried out across two
sessions and no failing-statement run survives in the working tree, so it is
not something this record can attest to.

`lake build` (17,756 jobs) completes; `Audit` reports 5,185 declarations in 91
modules resting only on `propext`, `Classical.choice` and `Quot.sound`. The
three new results carry their own `#print axioms` lines in source.

Lean added: `SpatialMeasure.finite_glue_unique` and
`SpatialMeasure.no_finite_measure_of_unit_atoms` in `Phase1_MeasureGluing.lean`;
`measureOnOpen`, `measureOnOpen_map_subtype`, `measureOnOpen_restrict`,
`globalSectionOfMeasure`, `globalSectionOfMeasure_restrict`,
`measureOnOpen_eq_of_restrict_eq` and
`ThermodynamicCover.existsUnique_measure_representation` in
`Phase5_GlobalSection.lean`; the real-line witness in
`Examples/MeasureGluing.lean`.

Scope comments corrected in Lean, not only in the companion: `Chain.lean` §9
and the `vertexKernel_fieldCorrelation_eq_zero` docstring no longer claim that
no kernel enters the development (`Phase2_KernelMesh` builds one), and
`chain_hypotheses_jointly_satisfiable` no longer claims one substrate for
components that live over different state spaces.

Companion: selection grows to 129 declarations in seven modules (4,973 tactic
records); `Phase1_MeasureGluing` joins `Chain`, `Phase5_GlobalSection` and
`Phase8_CriticalExponent` as completely covered. `run.sh extract`, `pdf`,
`check` and `test` all pass.

Artifacts: `main.pdf`, `supplementary.pdf`, `docs/primer.pdf` and
`proof_companion/companion.pdf` rebuilt; `prepare_arxiv.sh` recompiled the
submission from its own tarball (77 pages). The supplement's new paragraph
needed break hints in the long Lean names — without them it set an overfull
line 35.5pt into the margin.

Gates: `check_prose`, `check_hedging`, `check_tableS1`, `check_figures`,
`check_sorry`, `check_leaves`, `check_pdf_freshness` and
`check_arxiv_freshness` all pass. The withdrawn claims are recorded in
`CHANGELOG.md`.
