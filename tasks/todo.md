# Lean 4 Formalization: Remaining Action Items

## Intent
Address the final three mathematical gaps in the formalization plan to complete the translation of the Physics of Consciousness framework into a fully rigorous Lean 4 deductive chain.

## Constraints
- Ensure strict Lean 4 rigor using Mathlib.
- Maintain the boundary between what can be proven dynamically and what must be structured as a carefully scoped axiom.

## Plan

### Step 1: Phase 1 (Primitives) - Ginzburg-Landau Trapping
- [x] Investigate the feasibility of formalizing the Kibble-Zurek mechanism or Ginzburg-Landau dynamics in Lean.
- [x] Prove (or strictly structure) that physical dynamics under an energy functional inevitably trap the system in a non-trivial homotopy class upon symmetry breaking, replacing the broad `symmetry_breaking_yields_defects` postulate.

### Step 2: Phase 2 (Thermodynamics) - Landauer Limit Bridge
- [x] Refactor `Phase2_Thermodynamics.lean` to rigorously derive the relationship between Shannon/Boltzmann entropy decrease and physical heat dissipation.
- [x] Eliminate any unproved axioms that arbitrarily bridge abstract logical states and physical microstates.

### Step 3: Phase 4 (Macroscopic Coupling) - Spin-Glass Proof
- [ ] Replace the `topology_bounds_spin_glass` axiom with an actual mathematical construction or theorem.
- [ ] Prove that specific topological conditions (small-world, criticality) restrict the energy landscape's local minima, bounding the probability of spin-glass freezing.

## Review
- [ ] Verify everything compiles.
- [ ] Finalize `lessons.md`.
