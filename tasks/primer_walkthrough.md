# Primer accessibility revision

## Intent and scope

Revise all eighteen parts of `docs/primer.tex` for readers with no prior
familiarity with specialist vocabulary. Introduce ideas and examples before
formal notation. Include a continuous Kuramoto walkthrough from phases to
finite-rate recovery. Preserve distinctions between assumptions, formal
results and measurements. Deliver the companion source and rebuilt PDF.

## Plan and acceptance criteria

- [x] Audit orientation, all topical parts, notation and glossary.
- [x] Explain vocabulary where it first matters, including supporting
      mathematical, statistical and neuroscience concepts.
- [x] Work through phases, coupling, noise, order parameter, rotating frame,
      stationary ansatz, self-consistency, branches, simulation and ramp speed.
- [x] Check explanations against manuscript and saved results; retain generated
      numerical macros and verify any new citation online.
- [x] Compile with resolved references and inspect representative PDF pages.
- [x] Run relevant document gates and review source and PDF together.

This documentation change uses mathematical/source review, LaTeX compilation,
PDF inspection and existing gates. It introduces no Python implementation or
tests that merely assert prose wording.

## Review and validation

Added explanations and worked examples throughout, including the notation
foundation, information and heat, operators, discrete/continuum models, sheaves,
phase lifts, contraction, formal methodology, EEG analysis, calibration and
interpretation. Kuramoto now includes the interaction identity, a phase-arrow
diagram, stochastic increments, rotating coordinates, a zero-current density
derivation, self-consistency, branches and finite-rate simulation.

Aligned the ramp discussion with the manuscript's fitting-window and population
floor qualifications. Clarified that contraction at a prescribed rate is
different from existence of any contraction; a domain wall need not enclose an
agent; and spatial restriction retains masses without renormalizing them.
No references were added. The existing Sakaguchi reference and noisy Kuramoto
description were checked against online primary literature.

Validation: two successful final LaTeX passes; no LaTeX warnings or overfull
boxes; visual review of notation, phase-arrow, stationary-density, simulation,
sheaf and EEG pages. Existing `fokker_planck_von_mises.py` checks passed, as did
`check_prose.py`, `check_arxiv_freshness.py`, and `git diff --check`. The PDF
dependency gate was evaluated against the unstaged `git diff HEAD` paths so it
actually checked the source/PDF pair rather than an empty staging area. No
simulation sweep was run and no manuscript, simulation or Lean source changed.

## 2026-09-13 — Agency and the active composition

Intent: extend the existing accessible explanation to the verified agency
extension and active chain, preserving the rest of the walkthrough.

Plan and acceptance criteria:

- [x] Update the route map, node/edge tables and formal-composition explanation
      to distinguish passive and active branches, with eight hypotheses each.
- [x] Explain the perception--action channels, signed information identity,
      finite path entropy balance and reciprocal two-bit example before relying
      on their notation. Keep physical hypotheses and proof scope explicit.
- [x] Update notation, glossary and master status table consistently.
- [x] Record in `tasks/todo.md` the distinction between further theoretical
      modelling and empirical validation, with a bounded optional Lean target.
- [x] Rebuild the primer twice, inspect affected PDF pages and run relevant
      freshness/consistency gates. Keep publication and Lean sources unchanged.

No new reference, numerical simulation or implementation is needed. Verification
uses the existing Lean statements and witnesses, source review, LaTeX builds and
PDF inspection; no tests that assert particular prose wording are introduced.

Completed: the primer's orientation, thermodynamic walkthrough, formal-method
explanation, notation, glossary and master table agree about both branches.
The explanatory sections distinguish chosen mathematical dynamics from their
empirical interpretation. The ledger's optional L1 target specifies matched
intermediate laws, composed channels, total entropy/heat/work accounting and
nontrivial witnesses, with an explicit stopping rule and no empirical prerequisite.

Validation: the two final LaTeX passes produce a 73-page primer with resolved
references, no LaTeX warnings and no overfull boxes (matching the zero-warning,
zero-overfull starting baseline). Visual checks cover the node/edge table,
four channels, information identity, heat balance and reciprocal example.
The staged freshness gate and a separate check against the unstaged diff and
dependency timestamps pass for all tracked PDFs. The arXiv freshness gate and
`git diff --check` pass. No publication source, Lean source, reference or
simulation artifact was changed by this follow-up.
