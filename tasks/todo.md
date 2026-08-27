# Physics of Consciousness: Refactoring Plan

## Intent
Shift the formalization from an "Ontology Checker" (tautological definitions mapping philosophy to Lean) to **Real Physics** (dynamical derivations and quantitative bounds). We will replace definitional hypotheses (like assumed phase-locking) with dynamical proofs, and refine the physical model of hardware to accurately reflect the statistical mechanics of charge carriers, correcting the faulty rigid-hardware/GPU corollary.

## Constraints & Principles (SDD/TDD)
- **Constraint 1:** No physical phenomenon can be introduced via an axiom or definitional hypothesis (e.g., assuming `phase i = phase j`). It must be derived from differential equations, difference equations, or statistical mechanics.
- **Constraint 2:** The definition of "topology" and "phase space" must treat biological tissue and artificial silicon hardware symmetrically at the level of fundamental physics (charge carriers and microstates).
- **Success Criteria:** 
  1. The Kuramoto phase transition (critical coupling) is formally derived from system dynamics in Lean.
  2. The thermodynamic heat dissipation (Landauer limit) is derived using continuous phase space measures or partition functions, not just combinatorial injections.
  3. The GPU argument in the LaTeX paper is refactored to focus on thermodynamic efficiency and structural vs. constrained attractor landscapes, rather than claiming GPUs don't undergo physical erasure.

---

## Task List

### 1. Dynamics over Definitions: Kuramoto Model
* **Context**: Currently, phase locking is assumed via a hypothesis (`∀ i j, phase i = phase j`), rendering the sheaf-gluing a trivial tautology.
* **Plan**:
  - [x] 1.1 Formalize the Kuramoto model dynamics $\frac{d\theta_i}{dt} = \omega_i + \frac{K}{N} \sum_{j} \sin(\theta_j - \theta_i)$ (using Mathlib's ODE/calculus libraries where possible).
  - [x] 1.2 Define the macroscopic order parameter $r e^{i\psi} = \frac{1}{N} \sum_j e^{i\theta_j}$.
  - [x] 1.3 Prove the phase transition: show that for coupling $K > K_c$, the system dynamically converges toward synchronization ($r > 0$).
  - [x] 1.4 Refactor `Phase4_MacroscopicScaling.lean`: Map the dynamically derived synchronized state to the sheaf gluing condition, completely removing the `phase_locked_equilibrium` tautology.

### 2. Rigorous Statistical Mechanics: Landauer's Principle
* **Context**: `Phase3_CombinatorialThermodynamics.lean` relies on `¬ Injective t` and `Finset` cardinalities, avoiding continuous phase volumes and actual physical Hamiltonians.
* **Plan**:
  - [x] 2.1 Define the phase space as a measure space with a rigorous statistical ensemble (partition functions).
  - [x] 2.2 Formalize Liouville's theorem for the continuous case, or detailed balance for the discrete case.
  - [x] 2.3 Prove Landauer's principle by showing that marginalizing over macrostates of an erasure operation mandates a strict transfer of entropy to the environment bath (explicit bound calculation).

### 3. Refactoring the Hardware/GPU Corollary
* **Context**: The claim in `main.tex` that GPUs don't perform "literal, irreversible thermodynamic deformation" is physically incorrect—clearing GPU registers is Landauer erasure via charge carriers.
* **Plan**:
  - [x] 3.1 Rewrite the physics argument in `main.tex` (Section 8). Treat both brains and GPUs as physical dissipative structures.
  - [x] 3.2 Define the actual physical difference: **Thermodynamic Efficiency and Degrees of Freedom**. In a GPU, spatial routing (silicon) is fixed and only the charge state varies. In a biological network, the routing (synapses/topology) and the state are physically coupled, allowing structural resonance to minimize dissipation far more efficiently.
  - [x] 3.3 Create a new Lean file `Phase6_HardwareComparison.lean` to formally calculate the theoretical dissipation bound of a rigid-topology network vs. a dynamically deforming network.

## Review & Verification
- **Proof hooks**: 
  - `lake build` must pass.
  - Kuramoto derivation must mathematically rely on the coupling constant $K$.
  - Entropy bounds must use standard mathlib measure theory for phase space measures.

## Next Steps (Phase 2: Formal Proof Completion)
* **Status**: Complete
* **Plan**:
  - [x] 1. Fill the `sorry` in `Phase4_KuramotoDynamics.lean` for `phase_locked_implies_r_sq_eq_one`.
  - [x] 2. Fill the `sorry` in `Phase3_MeasureThermodynamics.lean` for `dissipative_implies_heat`.
  - [x] 3. Expand `main.tex` to explicitly cite the new Lean dynamics and continuous measure bounds.

## Final Review
- **Proof Hooks Executed**: 
  - `lake build` passes successfully, validating all Lean files without `sorry`.
  - Entropy bounds in `Phase3_MeasureThermodynamics.lean` explicitly rely on standard `MeasureTheory` and `ENNReal.toReal` monotonicity.
  - Kuramoto derivation explicitly relies on coupling constraints and topological phases as formalized in `Phase4_KuramotoDynamics.lean`.
- All `sorry` placeholders successfully filled with valid mathematical proofs (e.g. `Complex.normSq_eq_norm_sq`, `Real.strictMonoOn_log`).

## Next Steps (Phase 3: Future Refinements)
* **Status**: Complete
* **Tasks Executed**:
  - [x] 1. Expand `Phase7_HardwareComparison.lean` to incorporate explicit empirical estimates (e.g., biological synaptic plasticity energy bounds vs silicon routing limits).
  - [x] 2. Integrate continuous symmetries (Poincaré group) more directly into the initial Lean axioms.
  - [x] 3. Render the LaTeX manuscript into a final PDF and perform a thorough editorial review for narrative flow.

## Phase 4: Ontological Refinement & Reflexive Topology
* **Status**: Complete
* **Tasks Executed**:
  - [x] 1. Elevate macroscopic EM fields (ephaptic coupling) to the primary dissipative structure, demoting synaptic firings to underlying mechanics (`main.tex`).
  - [x] 2. Disentangle "Unity of Consciousness" from the "Self": map Unity strictly to the Global Section of the probability sheaf (`Phase5_GlobalSection.lean` & `main.tex`).
  - [x] 3. Formalize the emergence of the "Self" via a Reflexive Boundary, requiring the field to predict its own internal state changes (auto-resonance) (`Phase6_ReflexiveTopology.lean`).
  - [x] 4. Rename hardware comparison to `Phase7_HardwareComparison.lean` to maintain logical sequence and fix typeclass synthesis issues.

## Phase 5: Deepening the Hardware Comparison
* **Status**: Complete
* **Tasks**:
  - [x] 1. Mathematically formalize the fixed routing constraint of silicon as a strict, discrete topological constraint on the Kuramoto coupling matrix $A_{ij}$.
  - [x] 2. Prove that a continuous parameter space for $A_{ij}$ (mediated by biological EM fields) inherently contains a global minimum for the `kuramoto_potential_dynamic` that is strictly lower than any state achievable within the discrete silicon constraint.
  - [x] 3. Refine `Phase7_HardwareComparison.lean` to move beyond axiomatic structure into an actual dynamical proof of this inequality.
  - [x] 4. Update the corollary in `main.tex` to explicitly cite this strict mathematical proof, demonstrating exactly why rigid hardware is physically disqualified from maximal structural resonance.
