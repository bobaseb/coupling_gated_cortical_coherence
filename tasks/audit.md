# Audit: Existing Proofs vs. Paper Claims

## 1. Symmetry Breaking & Boundary Inevitability (Derivation 1)
- **Claim:** Continuous symmetries of the field break spontaneously, inevitably creating a topological defect that forms a boundary.
- **Lean Mapping:** `spontaneous_symmetry_breaking`, `defect_inevitability`, `boundary_defect_forces_interior_vacuum_break` in `Phase1_Primitives.lean`.
- **Status:** Currently axiomatized/formalized as basic logical implications, but relies heavily on type signatures rather than detailed field-theoretic geometry. Sufficient for a topological foundation but abstract.

## 2. Thermodynamic Constraint & Dissipation (Derivation 2)
- **Claim:** Because phase space is finite, absorbing external perturbations requires overwriting internal states, invoking Landauer's principle and ensuring the boundary is a non-equilibrium dissipative structure.
- **Lean Mapping:** `landauers_principle`, `boundary_is_dissipative`, `dissipative_implies_heat` in `Phase3_MeasureThermodynamics.lean` and `Phase3_CombinatorialThermodynamics.lean`.
- **Status:** Successfully captures combinatorial definitions of entropy and erasure. `boundary_is_dissipative` asserts erasure requires energy dissipation. This is a solid, albeit discrete, formalization.

## 3. Structural Resonance & Least Action (Derivation 3)
- **Claim:** System follows paths of least action to minimize entropy production, structurally deforming its internal geometry to match external perturbations.
- **Lean Mapping:** `structural_resonance_implies_gradient_descent` in `Phase8_ContinuousField.lean`.
- **Status:** **Trivial Tautology.** Currently defined tautologically or weakly without meaningful dynamical bounds. Needs refactoring to show genuine structural resonance as an attractor (Task 3).

## 4. Macroscopic Unity & Kuramoto (Derivation 4 & 5)
- **Claim:** Kuramoto synchronization past a critical threshold glues local states into a unified global section (Unity of Consciousness).
- **Lean Mapping:** `phase_locked_minimizes_potential` in `Phase4_KuramotoDynamics.lean`; `global_section_from_local_sync` in `Phase5_GlobalSection.lean`.
- **Status:** **Topological Truism.** `global_section_from_local_sync` merely applies Mathlib's `isSheafUniqueGluing_types` assuming compatibility, instead of proving that physical thermodynamic constraints *force* this compatibility (Task 2).

## 5. Reflexivity and Self (Derivation 6)
- **Claim:** The field folds to map its own boundary to minimize internal thermodynamic friction, generating a "Self".
- **Lean Mapping:** `reflexive_topology_implies_self` in `Phase6_ReflexiveTopology.lean`.
- **Status:** Partially formalized. Relies heavily on axiomatic structures rather than deriving reflexivity purely from the least-action thermodynamic principles. 

## 6. Continuous Stochastic Thermodynamics (Derivation 7)
- **Claim:** The field dynamically minimizes an explicit entropy production functional. Phase locked state is the minimum.
- **Lean Mapping:** `phase_locked_minimizes_entropy_production` in `Phase8_ContinuousField.lean`.
- **Status:** **Trivial 0=0 Proof.** Assumes intrinsic frequencies are 0 and all phases are identical. It fails to formalize non-trivial heterogeneous frequencies and dynamic gradient descent (Task 3).

## 7. Hardware Thermodynamics (Corollary)
- **Claim:** Continuous biological fields strictly minimize entropy more effectively than rigid, discrete silicon lattices, given equal resources.
- **Lean Mapping:** `bio_strictly_better_than_rigid` in `Phase7_HardwareComparison.lean`.
- **Status:** **Trivial Counterexample.** Currently relies on a trivial 3-node `V3` graph counterexample. It does not prove the general case of any discrete graph vs continuous manifold (Task 1).

## Refinement of Plan
The audit confirms the existing goals in `tasks/todo.md`.
