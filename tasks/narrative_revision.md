# Manuscript narrative revision — 2026-09-11

Intent: organize the article around coherence, compatible local content, and
self-representation, addressing the six narrative criticisms accepted by the
author. Preserve the current working tree's technical corrections.

Constraints: no new simulations, numerical results, mathematical claims or
unverified references. Retain generated result macros and the full control
evidence in the supplement. Preserve the scope of the conditional theorem and
distinguish philosophical motivations from empirical findings.

Plan and success criteria:

- [x] Scope the title to this framework and establish one question in the abstract and introduction.
- [x] Keep the three requirements visible in the section order and transitions.
- [x] Promote the stationary-distribution nonidentifiability result into the physical test.
- [x] Lead plasticity with its mechanism and decisive evidence; retain detailed controls in the supplement.
- [x] Explain why thermodynamic constraints belong, without depicting independent premises as a derived chain.
- [x] Develop motivations and limits for compatibility, the chosen cover, and accurate self-representation.
- [x] Consolidate repeated qualifications and align supplement and primer orientation.
- [x] Run publication gates and macro-drift tests; rebuild and check tracked PDFs and any existing arXiv package.

Baseline: prose, Table S1, and figure-uniqueness gates pass. Narrative weaknesses
are assessed by editorial reading rather than tests of prescribed wording; this
revision introduces no executable code.

The pre-revision manuscript, supplement and primer sources and PDFs are saved
in `/tmp/manuscript-narrative-uoyjcM/` for comparison during this session.

Outcome:

- The title is now “Coupling-gated cortical coherence: a conditional framework
  for unity and self-representation.” The article follows coherence and its
  awakening test, compatibility, self-representation, and supporting
  thermodynamic constraints. The explanatory figure shows separate inputs for
  the three requirements; Table 1 retains all eight connecting hypotheses.
- The article is 37 pages rather than 44. Source whitespace-word counts are
  6,140 versus 8,824 (including TeX commands). Every numerical result macro
  removed from the article remains in the supplement. No citation keys were
  added to the publication, and no simulations or mathematical code changed.
- The philosophical argument now addresses selection of cover and map,
  trivial descriptions and constant readouts, the accuracy idealization,
  representation of uncertainty or conflicting judgments, and separate
  dissociations of unity and reflexivity.
- A scope check against the formal statements confirmed that restriction
  resonance is a separate predicate, not a field consumed by `chain`. The
  article, supplement and primer now distinguish the fixed-point conclusion
  from this further condition needed to interpret encoding as restriction.
- Validation: all 8 `test_simulation_tex` tests passed, including generated
  macro drift. Prose, Table S1, figure uniqueness, PDF freshness, arXiv
  freshness and `git diff --check` passed. The advisory wording check reports
  zero flagged phrases in both publication files.
- Rebuilt `main.pdf`, `supplementary.pdf`, and `docs/primer.pdf` with two
  passes each. Inspected the argument figure and assumptions table visually.
  The final main build has no undefined-reference or overfull-box warnings.
  The companion primer retains existing long-identifier typesetting warnings;
  the standalone supplement retains duplicate citation warnings from its
  external-document bibliography import. Neither prevents compilation.
- Rebuilt the existing arXiv package, preserving its prior copy in the session
  backup. Its unpacked archive compiled successfully to 43 pages. No upload,
  commit, or push was performed.
