# Lean Formalization Plan 3.0: Action Items

## Intent
Implement the Hybrid "Coarse-Grained" Architecture (Plan 3.0) which uses Algebraic Topology (Simplicial Complexes) to bridge the continuous manifold (Phase 1) to combinatorial thermodynamics (Phase 3) and Sheaf theory (Phase 4/5). This replaces the Fokker-Planck PDE approach to allow for exact Lean proofs without placeholders.

## Constraints
- Ensure strict Lean 4 rigor using Mathlib.
- All deprecated Lean modules (the PDE-based Phase2-6) should be archived to `_archive/`.
- Match existing code styles and limit cyclomatic complexity (below 10).

## Plan

### Step 0: Migration
- [x] Move deprecated PDE-based `Phase2_Thermodynamics.lean`, `Phase3_StructuralResonance.lean`, `Phase4_MacroscopicCoupling.lean`, `Phase5_Inevitability.lean`, `Phase6_MutualRecursion.lean` to `_archive/` (rename to `v2_...` to avoid collision).
- [x] Update `PhysicsOfConsciousness.lean` to reflect new modules.

### Step 1: Phase 1 (The Stage)
- [x] Update `Phase1_Primitives.lean`: define electrodynamic fields and probability distributions as a Presheaf over the topological space.

### Step 2: Phase 2 (The Bridge)
- [x] Create `Phase2_SimplicialBridge.lean`.
- [x] Discretize the continuous manifold using a Simplicial Complex (nodes, edges, faces).
- [x] Map the continuous Stress-Energy Tensor ($T_{\mu\nu}$) to discrete weights on the edges of the simplicial complex.

### Step 3: Phase 3 (The Engine)
- [x] Create `Phase3_CombinatorialThermodynamics.lean`.
- [x] Port Landauer erasure proofs from `_archive/old_Phase2_Thermodynamics.lean`.
- [x] Port Kuramoto gradient descent proofs from `_archive/old_Phase5_Inevitability.lean`.
- [x] Apply these proofs to the finite state transitions of the simplicial complex.

### Step 4: Phase 4 & 5 (Macroscopic Scaling & The Self)
- [x] Create `Phase4_MacroscopicScaling.lean`: link the synchronized discrete states to local sections of the probability presheaf, defining restriction maps and showing adjacent local sections agree.
- [x] Create `Phase5_GlobalSection.lean`: prove the existence of a Global Section (The Self) based on the agreement of local sections.

## Review
- [x] Verify everything compiles successfully (`lake build`).
- [x] Ensure all axioms and `sorry`s are limited strictly to the agreed boundaries.
