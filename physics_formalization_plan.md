# Plan: Transitioning to Real Physics Formalization

To transform this repository from an "ontological checker" into a **rigorous physical formalization**, we must bridge the gap between abstract topological axioms and concrete dynamical physics (Lagrangians, statistical mechanics, equations of motion). We also must formally prove the remaining `sorry`s and `axiom`s.

Here is the step-by-step roadmap to achieve this.

## 1. Eliminate Hidden Axioms and `sorry`s (Immediate Fixes)

The current proofs rely on unproven gaps that undermine the mathematical rigor.

*   **Phase 1: Functor Laws in `probabilityPresheaf`**
    *   **Task:** Remove the `sorry` in `map_comp`. 
    *   **Action:** Prove that composing two restriction maps (`FiniteMeasure.comap`) on nested open sets is equivalent to a single restriction map. This requires standard measure theory lemmas in Mathlib regarding `comap`.
*   **Phase 5: The Isomorphism `sorry`**
    *   **Task:** Remove the `sorry` in `global_section_from_local_sync`.
    *   **Action:** The proof currently obtains a unique gluing over `iSup S.cover`. We must explicitly use the fact that `S.is_cover : iSup S.cover = ⊤` to cast (via `eqToHom`) the glued section into `(probabilityPresheaf X).obj (op ⊤)`.
*   **Phase 5: The Sheaf Axiom**
    *   **Task:** Remove `axiom probability_is_sheaf : TopCat.Presheaf.IsSheaf (probabilityPresheaf X)`.
    *   **Action:** Axioms in Lean are dangerous because they can introduce logical inconsistencies if they are false. We must prove this as a `theorem`. Gluing local finite measures into a global finite measure on a topological space generally relies on extension theorems (like Carathéodory's or Riesz-Markov-Kakutani). 

## 2. Introduce Action Principles (Phase 1 & 2) [COMPLETED]

Real physics derives phenomena from the Principle of Least Action, not just topological assertions.

*   **Task:** Define a specific Field Lagrangian. [COMPLETED]
*   **Action:** Currently, `BoundaryField` is just a continuous map, and we define topological defects topologically. We have introduced:
    1.  A field state $\phi(x)$.
    2.  An Action principles class bounding Total, Kinetic, and Potential energies.
    3.  A specific `DynamicalVacuum` strictly tied to the minima of $V(\phi)$.
*   **Goal:** Derive *spontaneous symmetry breaking* dynamically. [COMPLETED - theorem `spontaneous_symmetry_breaking`] Prove that minimizing the action $S[\phi]$ (Euler-Lagrange equations) forces the field into the vacuum manifold, generating the topological defects.


## 3. Rigorous Thermodynamic Coupling (Phase 2 & 3)

The link between the continuous field and the discrete Kuramoto model is currently arbitrary (the `edge_weight` is defined as an integral but lacking physical constraints).

*   **Task:** Formalize Landauer's Principle dynamically.
*   **Action:** In `Phase3`, you prove `entropy_decrease` when a map is non-injective (erasure). We need to link this to the Stress-Energy Tensor `T` in `Phase 1/2`. We must prove a theorem: *If entropy decreases (non-injective state transition), the divergence of the heat flux component of $T$ must be strictly positive.* $\nabla_\mu Q^\mu \ge k_B T \ln 2$.
*   **Task:** Derive, rather than assume, Structural Resonance. 
*   **Action:** Show that a system bound by Landauer's heat limit will minimize its action by adapting its internal state $\phi_{int}$ to minimize the gradient with external perturbations $\phi_{ext}$. This formalizes "Predictive Processing" as a physical thermodynamic necessity.

## 4. Derive the Kuramoto Model from Field Dynamics

The Kuramoto equations in `Phase 3` are currently declared out of thin air.

*   **Task:** Prove that the macroscopic limit of the field interactions simplifies to the Kuramoto model.
*   **Action:** Show that when multiple discrete defect boundaries are weakly coupled via the continuous metric field (ephaptic coupling), their phase dynamics $\theta_i$ naturally obey $\dot{\theta_i} = \omega_i + K \sum \sin(\theta_j - \theta_i)$ as an approximation of the field's Hamiltonian flow.

## Summary of Success Criteria

When complete, the theory will flow strictly from:
`Action Principle + Manifold Topology -> Euler Lagrange Eq -> Defect Generation -> Thermodynamic Heat Bounds -> Field Synchronization (Kuramoto) -> Sheaf Gluing (Unified Self)`.

All `sorry`s and `axiom`s will be replaced by rigorous Mathlib-backed theorems.
