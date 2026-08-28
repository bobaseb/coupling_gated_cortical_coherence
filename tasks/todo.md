# Physics of Consciousness - Formalization To-Do

The following tasks focus on expanding the Lean 4 formalization to cover claims that are currently unformalized or only conditionally proven.

## P0: Mesh Refinement Convergence (Phase 2)
* **Objective:** Formalize the proof for `mesh_refinement_convergence` in `Phase2_SimplicialBridge.lean`, which currently sits in the "Conjectures" section.
* **Why:** Derivations 4 and 7 depend on this bridge between discrete and continuous topologies.
* **Acceptance Criteria:** A Lean 4 `theorem` (or `lemma`) demonstrating that as the simplicial complex resolves to infinity, it converges to the continuous manifold without `sorry`.

## P1: KL Bound Formalization (Derivation 3)
* **Objective:** Provide a full Lean 4 implementation of the KL Bound from Derivation 3.
* **Why:** The supplementary materials previously claimed a Lean 4 implementation for this, but it doesn't exist. We had to mark it as "Unformalized" in Table 1 to remain honest.
* **Acceptance Criteria:** A new Lean file (or addition to Phase 3) containing the KL Bound formalized in `MeasureTheory`, with a complete proof. Update `main.tex` and `supplementary.tex` to claim the implementation once completed.

## P2: Elevate Phase 7 Hardware Comparison to Theorem
* **Objective:** Upgrade the conditional lemmas in `Phase7_HardwareComparison.lean` into full theorems.
* **Why:** The paper wants to assert a strong theorem: "Continuous vs. Rigid Topology" as a disqualifying factor for silicon-based rigid hardware, but currently the code only contains conditional lemmas. 
* **Acceptance Criteria:** Refactor the codebase to either prove the conditionals universally, or wrap the lemmas in a generalized theorem that matches the strong narrative claim in the paper. Once completed, revert Table 1 in `main.tex` to label Phase 7 as "Theorem".
