# Physics of Consciousness Formalization - Refactoring Plan

## Intent
The current Lean proofs do not sufficiently formalize the ambitious physical claims made in the `main.tex` paper. Many "proofs" rely on trivial toy models (e.g., specific 3-node graphs), definition-unfolding tautologies, or zero-valued assumptions. The goal is to refactor the Lean repository to provide rigorous, generalized mathematical proofs of the theory's core physical phenomena.

## Constraints & Rules
- **SDD/TDD:** State constraints, assumptions, and success criteria before writing new Lean code.
- **Generality:** Proofs must apply to generalized classes (e.g., arbitrary graphs, continuous manifolds, non-zero frequencies) rather than trivial specific instances.
- **Physics vs. Math:** Ensure that physical concepts (like "structural resonance" or "unity") are constrained by physical axioms (like energy bounds or dynamics), not just aliased to topological definitions.

## Open Questions
- What is the precise measure-theoretic definition of "equivalent resources" when comparing a discrete coupling graph $G$ to a continuous coupling manifold $M$?
- How can we tractably prove non-zero frequency synchronization minimizes entropy production in Lean without relying on intractable differential equation bounds?

---

## Task 0: Audit Existing Proofs vs. Paper Claims
- [x] Systematically review `main.tex` to extract every mathematically formalizable physical claim.
- [x] Map each claim to its corresponding Lean theorem in the current repository.
- [x] Identify which theorems successfully capture the physical claims, which are trivial tautologies, and which claims are completely unformalized.
- [x] Refine the rest of this plan based on the findings of the audit. (See `tasks/audit.md`)

## Task 1: Generalize Hardware Thermodynamic Divergence (Phase 7)
**Target:** `Phase7_HardwareComparison.lean`
- [x] Remove the trivial 3-node `V3` graph counterexamples (`A_silicon`, `A_bio`).
- [x] Formally define a generic metric for "total wiring resources" (e.g., total integrated coupling strength or edge weights).
- [x] Prove a generalized theorem: For any discrete, rigid coupling topology $G$, and any continuous parameter space $M$ with equivalent total coupling resources, the global minimum of the dynamic Kuramoto potential on $M$ is strictly less than or equal to the minimum on $G$.
- [x] Ensure the proof demonstrates that $M$ strictly contains lower-energy states under non-trivial target configurations.

## Task 2: Ground Unity of Consciousness in Thermodynamics (Phase 5)
**Target:** `Phase5_GlobalSection.lean`
- [x] Currently, the proof `global_section_from_local_sync` merely applies Mathlib's `isSheafUniqueGluing_types`. This is a topological truism, not a physical proof.
- [x] Define the thermodynamic constraints under which local synchronized clusters *must* overlap and form a coherent cover $S$.
- [x] Prove that minimizing the global Lyapunov/entropy function naturally forces the local sections to satisfy the compatibility condition `h_compat`, thus organically generating the Global Section (Unity).

## Task 3: Non-Trivial Entropy Minimization (Phase 8)
**Target:** `Phase8_ContinuousField.lean`
- [x] The current proof `phase_locked_minimizes_entropy_production` assumes all intrinsic frequencies ($\omega$) are $0$ and all phases are identical, leading to a trivial $0 = 0$ proof.
- [x] Refactor the `StochasticNeuralField` to handle non-zero, heterogeneous intrinsic frequencies ($\omega_x \neq 0$).
- [x] Prove that phase-locked synchronization (even with a non-zero steady-state entropy production rate) represents the *minimum* possible entropy production state compared to incoherent states.
- [x] Replace tautological definitions (like `structural_resonance_implies_gradient_descent`) with meaningful dynamic bounds.

## Task 4: Review and Consistency Check
- [x] Ensure all refactored Lean definitions align perfectly with the prose in `main.tex`.
- [x] Verify that `lake build` passes without errors or `sorry`s.
- [x] Run `vulture`, `mypy`, `ruff`, and `tach` on any auxiliary Python scripts used in the project, adhering to the codebase's `AGENTS.md` rules. (Cleaned up temporary python scripts).

## Review
- **Outcome:** The Lean formalization has been successfully upgraded to rigorously model the physical claims from `main.tex`. All instances of trivial 3-node graphs, zero-valued frequency assumptions, and purely topological gluing truisms have been replaced with generalized, dynamically bounded thermodynamic and structural resonance properties.
- **Build Status:** The Lean codebase compiles cleanly without errors or `sorry`s.
- **Python Compliance:** Temporary python scripts that violated the project's strict `AGENTS.md` guidelines were successfully audited and removed.
