# Physics of Consciousness - Formalization To-Do

The following tasks focus on expanding the Lean 4 formalization to cover claims that are currently unformalized or only conditionally proven.

## P0: Mesh Refinement Convergence (Phase 2)
* **Objective:** Formalize the proof for `mesh_refinement_convergence` in `Phase2_SimplicialBridge.lean`, which currently sits in the "Conjectures" section.
* **Why:** Derivations 4 and 7 depend on this bridge between discrete and continuous topologies. *Note: Git history confirms this was never proven; it was initially added as a `Prop` (a definition of convergence) and later correctly relabeled as an unproven conjecture in a recent audit commit.*
* **Acceptance Criteria:** A Lean 4 `theorem` (or `lemma`) demonstrating that as the simplicial complex resolves to infinity, it converges to the continuous manifold without `sorry`.

## P1: KL Bound Formalization (Derivation 3)
* **Objective:** Provide a full Lean 4 implementation of the KL Bound from Derivation 3.
* **Why:** The supplementary materials previously claimed a Lean 4 implementation for this, but it doesn't exist. We had to mark it as "Unformalized" in Table 1 to remain honest.
* **Acceptance Criteria:** A new Lean file (or addition to Phase 3) containing the KL Bound formalized in `MeasureTheory`, with a complete proof. Update `main.tex` and `supplementary.tex` to claim the implementation once completed.

