# Final bounded narrative pass — 2026-09-11

Intent: make the contribution hierarchy explicit and remove remaining repetition
after the narrative assessment. The section architecture and the scientific
claims remain fixed.

Constraints: editorial changes only; no new results, simulations, proofs or
references. Preserve the cup illustration, substantive qualifications, all
connecting hypotheses, citation keys and generated numerical macros. Check the
primer for consistency and rebuild every affected tracked PDF, including the
supplement through its external reference to the article. Refresh the existing
arXiv package.

Plan and success criteria:

- [x] Distinguish demonstrated separation results, conditional construction and
      proposed biological interpretation in the abstract and introduction.
- [x] Consolidate repeated self-representation qualifications while retaining
      the functional intervention, constant-readout objection and accuracy limits.
- [x] Compress supporting thermodynamics and repeated discussion exposition.
- [x] Verify citation and macro preservation, publication gates and macro drift;
      rebuild affected PDFs and the arXiv archive, and inspect changed layouts.

Validation uses editorial review and existing document checks. No executable
code is introduced, and tests of prescribed wording would not assess the change.

Outcome:

- The abstract and introductory contribution paragraph distinguish separation
  results, the conditional construction and the proposed interpretation.
- Consolidated reconstruction and perspective qualifications, retaining the
  intervention criterion, constant-readout objection, accuracy limits and
  distinct dissociations. Shortened thermodynamic context and the discussion.
- Main source whitespace-word count (including TeX) fell from 6,224 to 5,875.
  Citation groups, labels, section architecture, displayed equations, the
  assumptions table and usage counts for all 213 generated result macros are
  unchanged. The primer remains consistent with these editorial changes.
- Prose, advisory hedging, Table S1, figure uniqueness, PDF freshness, arXiv
  freshness and whitespace checks pass. All 8 macro-generation tests pass.
  Because the PDF gate reads staged changes, additionally checked the unstaged
  diff and source dependency timestamps for both affected PDFs.
- Rebuilt main and supplement with two LaTeX passes each: 36 and 30 pages.
  Neither has overfull boxes or undefined references; the main has no LaTeX
  warnings, and the supplement retains its external-bibliography duplicate
  citation warnings. The arXiv archive compiles from its unpacked contents to
  44 pages and has a current manifest.
- Visually inspected the assembled abstract and the revised self and
  thermodynamic passages. Backups of the prior main source, affected PDFs and
  arXiv package are in `/tmp/final-narrative-8VuVBF/`.
- No commit, push or upload was performed.
