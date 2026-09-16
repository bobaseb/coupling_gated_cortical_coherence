# Proof companion: first implementation

## Intent

Build a reproducible, human-readable mathematical companion to the repository's
Lean development. This directory owns the entire exercise. The first release is
a bounded pilot; extending coverage must not require changing its architecture.

## Constraints

- Use the repository's pinned Lean and Mathlib, without changing either version.
- Extract elaborated statements and tactic states from Lean, not regular
  expressions over source or paraphrases of docstrings.
- Preserve implicit hypotheses, source locations, proof dependencies, and the
  before/after metavariable contexts. Term proofs remain covered without tactics.
- Keep mathematical explanations explicitly editorial; Lean checks the source
  proof, not the English translation.
- Keep extraction separate from rendering. A saved snapshot must suffice to
  rebuild LaTeX, without recompiling the development or running simulations.
- Do not modify mathematical declarations or the publication for this pilot.
- Start with shell/Lean tooling and the installed TeX toolchain; do not add a
  second Python project or change the simulation environment.

## Plan and success criteria

1. Write extraction regression fixtures and run them before implementation.
   Exercise branching tactics, implicit binders, term proofs, structure fields,
   anonymous examples, missing selections, and elaboration failure.
2. Implement a small Lean-native extractor against `v4.34.0-rc2`. Retain raw
   nested tactic records and distinguish source text from synthetic syntax.
3. Extract representative gluing, asymptotic, chain, and witness declarations.
   List the exact selected declarations and the remaining coverage limitations.
4. Write mathematical explanations checked against those proofs; generate the
   formal statement appendix and a small trace excerpt from the saved JSON.
5. Compile a linked PDF, verify reproducible rendering and source freshness,
   and document extraction, rendering, testing, and extension commands.

The pilot succeeds when all selected declarations have real extracted records,
the regression tests pass, the PDF compiles without missing glyphs or unresolved
references, and changing an input is detected by the freshness check. Whole-library
coverage and automatic proof narration remain later stages.
