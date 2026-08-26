# Lean 4 Formalization Plan: The Physics of Consciousness

## Intent
Translate the prose arguments from `main.tex` into a rigorous, formal mathematical chain in Lean 4. The goal is to formally construct the deductive chain from finite phase space and the principle of least action to structural resonance and phase synchronization. 

**Current Status Acknowledgment:** The current Lean implementation successfully maps the *structure* of the philosophical argument, but relies heavily on tautological axioms (e.g., `action_eq_mismatch`, `rigid_lattice_fails_resonance`). To move beyond "mathematical theater," the next phase of this project must replace these assertions with genuine mathematical derivations or explicitly declare them as physical postulates.

## Constraints
1. **Mathematical Rigor vs. Physical Intuition:** Physics often relies on approximations (e.g., thermodynamic limits, coarse-graining). Lean requires absolute rigor. We must bridge these gaps mathematically rather than semantically.
2. **Lean Ecosystem:** Leverage `Mathlib` for topology, measure theory (for phase space), and differential equations (for Kuramoto and Least Action).
3. **Honesty in Axiomatization:** If a physical leap cannot be proven from first principles (e.g., Renormalization Group flows), it must be explicitly declared as a physical postulate, not hidden as a trivial class assumption or a tautological axiom that bakes in the conclusion.

## Success Criteria
1. A compiling Lean 4 project with clearly separated modules corresponding to the derivations in the paper.
2. Formal definitions for physical primitives: `PhaseSpace`, `Boundary`, `Dissipation`, `Resonance`.
3. Eradication of tautological axioms (axioms that assume the conclusion of the theorem they are meant to prove).

## Methodological Constraints: Avoiding Mathematical Theater
To ensure this formalization is mathematically meaningful and not just "mathematical theater" that encodes English assertions into Lean syntax, the following rules must be strictly adhered to:

1. **No Tautological Axioms or Typeclasses:** Theorems must not simply restate axioms defined in their prerequisite classes or module namespace. For example, `gpu_disqualified` cannot be proven by invoking an axiom `rigid_lattice_fails_resonance`. 
2. **Explicit Bridging of Scales:** The derivation must not rely on semantic leaps between microscopic and macroscopic phenomena. If a topological defect from spontaneous symmetry breaking is equated to a macroscopic cognitive boundary, the mathematical bridging (e.g., Renormalization Group flow, coarse-graining maps) must be explicitly constructed. 
3. **Genuine Proof Mechanisms:** Where theorems are stated (e.g., `ssb_yields_boundary`), they must rely on actual mathematical machinery (e.g., algebraic topology, homotopy groups) rather than remaining `sorry`.

---

## Phase 1: Primitives, Symmetry, and Boundaries (Axiom 1 & Deriv 1)
**Goal:** Formalize the concept of a finite physical system and the creation of a boundary.
**Status:** Verified. The core theorem is proven mathematically using Mathlib's topology tools.

*   **Definitions:**
    *   Define `PhaseSpace` as a finite measure space or a space with a finite capacity/cardinality bound.
    *   Define a `Field` over a topological space (spacetime).
    *   Define the continuous symmetries of the background.
*   **Theorems/Axioms:**
    *   **Action Required:** [x] `ssb_yields_boundary` is now a fully realized mathematical theorem, proven using `isPreconnected_closed_iff` to demonstrate that mapping a connected space to a disconnected vacuum manifold strictly necessitates a domain wall/boundary.

## Phase 2: Information, Erasure, and Thermodynamics (Deriv 2)
**Goal:** Connect the finite phase space to Landauer's Principle.
**Status:** Partially verified. The Pigeonhole principle correctly links non-injective mappings to entropy decrease.

*   **Definitions:**
    *   Define an `ExternalPerturbation` acting on the `Boundary`'s internal states.
    *   Define `InformationErasure` as a non-injective state transition.
*   **Theorems/Axioms:**
    *   **Action Required:** [x] `landauer_bound` has been derived from `StatisticalMechanics` using the Second Law of Thermodynamics relating Shannon/Boltzmann entropy to heat dissipation.

## Phase 3: Principle of Least Action and Structural Resonance (Deriv 3)
**Goal:** Prove that survival of the structure necessitates a physical mirroring of the environment.
**Status:** Highly Theatrical. Needs complete refactor.

*   **Definitions:**
    *   Introduce a space of `Trajectories` for the dissipative structure.
    *   Define an `Action` functional that integrates thermodynamic dissipation over time.
*   **Theorems:**
    *   **Action Required:** Remove `axiom action_eq_mismatch`. The theorem `resonance_minimizes_action` is currently a trivial rewrite of this axiom. We must mathematically prove that thermodynamic action bounds the KL-divergence (or similar statistical mismatch) between the internal state distribution and external perturbations.

## Phase 4: Macroscopic Coupling and Frustration (Deriv 4)
**Goal:** Scale the minimal structures into a complex network.
**Status:** Relies on black-box axioms.

*   **Definitions:**
    *   Define a `Network` or `Lattice` of coupled dissipative boundaries.
    *   Define `GeometricFrustration`.
*   **Theorems/Axioms:**
    *   **Action Required:** `axiom effective_field_theory` and `axiom complex_topology_evades_spin_glass` do all the heavy lifting. We must formally define the measure-theoretic coarse-graining map, and define the specific topological conditions (criticality, fractal dimension) that strictly bound the probability of spin-glass freezing.

## Phase 5: The Inevitability of the Self (Deriv 5)
**Goal:** The capstone proof showing unified synchronization.
**Status:** Conclusion baked into class definitions.

*   **Definitions:**
    *   Formalize the macroscopic field as a system of coupled non-linear oscillators (the Kuramoto model).
*   **Theorems:**
    *   **Action Required:** The class `KuramotoDynamics` currently assumes `supremum_is_sync = 1`. This must be removed. The convergence to synchronization (`R -> 1`) must be proven as a theorem for $K > K_c$ using differential equations or analytical bounds, not assumed as a property of the system.

## Phase 6: Hardware Divergence (GPUs vs Deformable Topology)
**Goal:** Formally prove why standard von Neumann architectures fail to achieve structural resonance.
**Status:** Highly Theatrical.

*   **Definitions:**
    *   Define `RigidLatticeSystem` (fixed geometry) vs `DeformableSystem` (adaptive geometry).
*   **Theorems/Axioms:**
    *   **Action Required:** `gpu_disqualified` is proven by directly invoking `axiom rigid_lattice_fails_resonance`. We must delete this axiom and *prove* it. We need to show that a system with a fixed geometric phase space has a mathematically provable non-zero lower bound on environmental mismatch compared to a system with an unconstrained/adaptive geometric phase space.

---

## Next Steps (Pending Tasks)
* [ ] **Eliminate Tautological Axioms:** Audit `Phase3`, `Phase5`, and `Phase6`. Remove `action_eq_mismatch`, `rigid_lattice_fails_resonance`, and `supremum_is_sync`. 
* [x] **Topological Proof of Boundaries:** Implement the proof for `ssb_yields_boundary` in `Phase1_Primitives.lean` using Mathlib's topology tools.
* [ ] **Rigorous Statistical Mechanics:** Derive the Free Energy Principle bound (Action $\ge$ Mismatch) from basic probability and measure theory rather than asserting it.
* [ ] **Hardware Divergence Proof:** Formally define the capacity of a phase space. Prove that rigid topologies strictly bound the representational capacity of the system, mathematically forcing the mismatch to remain above zero.
