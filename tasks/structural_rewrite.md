# Structural manuscript rewrite — 2026-09-15

## Intent and constraints

Rewrite the main article around coherence, compatibility and self-representation,
integrating the installed-energy condition and conditional content-agreement
results where they bear on those requirements. Give the finite agency models a
structured technical treatment in the supplement. The author approved this
scope after reviewing the growth from 36 to 60 main-PDF pages.

Editorial changes only: no new proofs, simulations, numerical results, references,
dependencies or Python code. Preserve all eight hypotheses of each composition,
the distinct systems used by its witnesses, generated simulation macros, and
the distinction between stored energy and heat. Preserve technical results in
the supplement and source library; avoid implying a single integrated cortical
agent. Keep mathematical assumptions and empirical identifications explicit.

## Plan and success criteria

- [x] Rewrite abstract and introduction around the final contribution hierarchy.
- [x] Place the installed-energy bound beside the phase threshold and the
      content-agreement results beside compatibility.
- [x] Condense the recovery, self-representation and discussion sections; target
      approximately 6,000–7,000 main-source whitespace words, including TeX.
- [x] Condense supporting thermodynamics and retain its full details under
      clear supplement headings, with valid cross-references.
- [x] Align the primer's orientation and record the editorial change.
- [x] Verify preservation of citation keys, generated result macros, labels and
      figures; review the mathematical scope against existing statements.
- [x] Run publication gates and macro-drift tests, rebuild affected tracked PDFs
      with two passes, inspect layouts and refresh the existing arXiv archive.

This is an editorial task. Validation uses existing tests and document gates,
plus a before/after inventory; tests prescribing wording would not verify the
argument. The rewrite was prepared for review; the author subsequently requested
a local commit. Pushing or submitting remains outside this pass.

## Baseline

The working tree is clean. Main source: 11,491 whitespace words, including TeX;
thermodynamics/composition: 4,843. Main PDF: 60 pages; supplement: 53 pages.
Sources, PDFs, logs and the existing arXiv package were copied to a temporary
snapshot before editing.

## Outcome — completed 2026-09-16

- Main source falls from 11,491 to 5,841 whitespace words, including TeX.
  Supporting thermodynamics/composition falls from 4,843 to 984. The abstract
  is 156 source words and fits on the title page. The main PDF is 39 pages,
  compared with 60 at the start.
- The installed-energy condition accompanies the phase threshold; scalar
  content acquisition and retention accompany compatibility. The recovery,
  self-representation and discussion sections follow this contribution order.
- The supplement groups feedback, policy learning, repeated operation/resources
  and coupling bridges into separate sections, adds navigation, and carries the
  seven equations moved from the article. All detailed witnesses remain.
  It is 55 pages, compared with 53. The aligned primer is 93 pages.
- Review against `Phase5_ContentDynamics.lean` clarified three scope points:
  the encoder is common and scalar, observations are constant on a patch, and
  the retained disagreement expression is an upper bound. The population-size
  factor is not asserted optimal. These clarifications appear in the article,
  supplement and primer as appropriate; `CHANGELOG.md` records the corrections.
  No Lean declarations or other executable repository code changed.

## Validation

- All citation keys and original equation/section/figure labels remain in the
  combined publication. No new citation key was introduced. All 200 generated
  macros used before the rewrite remain used; none of their source artifacts or
  definitions changed. There are no duplicate or unresolved labels.
- All 8 existing `test_simulation_tex` tests passed, including macro generation
  drift. No production simulation or new proof was required.
- Applicable pre-commit hooks pass: prose, advisory wording (zero flagged
  passages), Table S1, PDF freshness, figure uniqueness (7 figures), and arXiv
  freshness. Python/Lean hooks correctly skip this editorial change.
- Because the PDF gate normally reads staged paths, separately verified the
  unstaged source/PDF diff and that each PDF is newer than all its transitive
  dependencies. The three final LaTeX logs contain no warnings, undefined
  references or overfull boxes. Underfull-box counts are 3/2/31 for
  main/supplement/primer; these are nonfatal spacing diagnostics.
- Rebuilt the affected PDFs with two passes and inspected the abstract,
  installation/content passages, assumptions table and supplement navigation
  and store equation. The arXiv archive compiles from its unpacked contents to
  71 pages, has a current manifest, and its revised opening and key passages
  were visually inspected.
- Snapshot, draft fragments and validation logs are under
  `/tmp/manuscript-rewrite-2e90jsd8/`. The final working tree contains the source,
  PDF and editorial-record changes together. Following review, the author
  requested that these changes be committed together. No push or submission
  was requested.
