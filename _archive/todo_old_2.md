# Physics of Consciousness: Refactoring Plan

## Intent
Address critical theoretical leaps in the current manuscript and Lean formalization. The goal is to ground the theory in solid physics without overextending into teleology or philosophy, and to ensure the mathematical proofs are genuinely rigorous.

The focus is on:
1. Clarifying that topological boundaries (defects) are necessary but **not sufficient** for agency.
2. Re-framing the Principle of Least Action as a dynamical attractor state, not a "Darwinian survival drive."
3. Positioning the continuous EM field theory as an emerging paradigm (via Earl Miller's work) rather than established dogma.
4. Purging the Lean 4 codebase of `sorry` blocks, unchecked axioms, and circular definitions to ensure the physics derivations are mathematically sound.

## Constraints & Principles
- **SDD/TDD:** All changes to Lean files must compile without errors or warnings.
- **No Teleology:** Physics does not have "intent". Systems evolve toward attractor states; they do not "try to survive".

---

## Task List

### Phase 1: Manuscript Refactoring (`main.tex`)
- [ ] **1.1 Fix Symmetry Breaking & Agency (Section 3):** Revise the text to explicitly state that while spontaneous symmetry breaking creates necessary topological boundaries (distinguishing 'inside' from 'outside'), this alone does not create an agent. A topological defect in a crystal is not conscious. Define what additional non-equilibrium dynamics are required for sufficiency.
- [ ] **1.2 Reframe Principle of Least Action (Section 5):** Remove teleological language ("trying to survive", "forced to mirror"). Reframe structural resonance as a deterministic consequence of systems evolving along paths of least action to minimize entropy production. It is a physical imperative/attractor state, not a biological drive.
- [ ] **1.3 Contextualize EM Fields (Section 6 & 7):** Acknowledge that macroscopic EM field theory (ephaptic coupling) as the primary substrate of mind is an emerging view, not standard neuroscience consensus. Explicitly cite Earl Miller's work to ground this shift.
- [ ] **1.4 Tone Down "Inevitability":** Soften the language claiming a "strict causal chain" and absolute "mathematical inevitability". Present the work as a rigorous physical framework for predictive processing, rather than a finalized proof of consciousness.

### Phase 2: Lean 4 Formalization Cleanup (`*.lean`)
- [ ] **2.1 Audit Codebase:** Search through all `.lean` files (e.g., `kuramoto.lean`, `entropy.lean`, etc.) to map out all instances of `sorry` and unproven axioms.
- [ ] **2.2 Eliminate Circular Axioms:** Review typeclasses and structures to ensure we aren't defining away the physics (e.g., assuming phase-locking by definition rather than deriving it from the coupling matrix).
- [ ] **2.3 Complete the Proofs:** Write the actual mathematical proofs for the dynamics. (e.g., deriving the Kuramoto potential correctly, proving Landauer's bound from continuous measure theory without relying on axiomatic shortcuts).

### Phase 3: Verification
- [ ] Run `lake build` and verify that the Lean project compiles with zero `sorry` warnings.
- [ ] Recompile `main.tex` into a new `main.pdf` and review the narrative flow.
