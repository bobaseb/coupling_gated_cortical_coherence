# Eradicating Mathematical Theater from Physics of Consciousness

## Intent
Strip out all tautological axioms, dummy variables, and semantic mathiness from the Lean codebase, and replace them with rigorous, genuine mathematical formalizations of physical concepts (homotopy groups, ODEs, thermodynamic phase space). 

## Constraints
1. **No Tautologies:** Proofs must not assume their conclusions as axioms or typeclass properties.
2. **Lean 4 Rigor:** New definitions must utilize Mathlib components (e.g., AlgebraicTopology, DifferentialEquations) to enforce rigor.
3. **Fail Fast:** If a mathematical concept is beyond current formalization capacity, state it explicitly as a named `axiom` or `postulate` rather than hiding it behind trivial properties.

## Success Criteria
1. The project successfully compiles with Lean 4.
2. `Phase1` uses Homotopy groups for topological defects.
3. `Phase4` defines network topology correctly (no `True` assignments).
4. `Phase5` removes `monotone` and `no_spurious_fixed_points` from `KuramotoDynamics`, pointing towards ODE analysis.
5. `Phase6` accurately formalizes hardware divergence without assuming a static maximum capacity $C$ and an environment of $C+1$.

## Plan

### Step 1: Strip Tautologies (Cleanup)
- [x] Edit `Phase4_MacroscopicCoupling.lean`: Remove `is_small_world := True` and `exhibits_criticality := True`. Turn them into opaque properties or structures.
- [x] Edit `Phase5_Inevitability.lean`: Strip `monotone`, `bounded`, and `no_spurious_fixed_points` from the `KuramotoDynamics` class. Delete the trivial `kuramoto_phase_transition` proof based on the Monotone Convergence Theorem.
- [x] Edit `Phase6_HardwareDivergence.lean`: Remove the $C < C+1$ proof (`gpu_disqualified`).

### Step 2: Refactor Phase 1 (Topological Defects)
- [x] Introduce Homotopy / Fundamental Group concepts from Mathlib to `Phase1_Primitives.lean`.
- [x] Redefine `ssb_yields_boundary` to require a non-trivial homotopy group mapping to a broken vacuum, replacing the trivial Intermediate Value Theorem approach.

### Step 3: Refactor Phase 4 & 5 (Kuramoto ODEs)
- [x] Define the Kuramoto order parameter properly in `Phase5_Inevitability.lean`.
- [x] State the dynamical limit as a conjecture/axiom based on ODEs, explicitly acknowledging that full PDE/ODE stability analysis might exceed current Mathlib limits, but defining the *structure* of the ODE correctly.

### Step 4: Refactor Phase 6 (Hardware Divergence)
- [x] Define thermodynamic deformation vs logic state erasure.
- [x] Construct a rigorous physical bound that distinguishes rigid lattices from deformable topology.

## Review
- [x] Verify everything compiles.
- [x] Update `lessons.md` with lessons learned about mathematical theater.
