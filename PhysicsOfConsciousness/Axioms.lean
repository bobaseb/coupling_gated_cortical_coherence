/-
  Axioms.lean — Explicit Physical Postulates

  This file collects all irreducible physical assumptions in the formalization.
  These are distinct from mathematical theorems (which must be proved) and from
  structural class fields (which encode definitional properties).

  **Design rule:** An entry belongs here iff:
    (a) It is an empirical physical law with no purely mathematical proof, OR
    (b) It is a modelling choice that fixes a free parameter of the theory.

  Anything that *is* a mathematical theorem (Jensen's inequality, Brouwer's
  fixed-point theorem, etc.) must NOT appear here — it belongs in the relevant
  Phase file as a `theorem` or `lemma` proved from Mathlib.

  **Status legend:**
    [IRREDUCIBLE]  — Cannot be derived from mathematical primitives; genuinely axiomatic.
    [MODELLING]    — A convenient simplification; could be weakened with more work.
    [OPEN]         — Believed irreducible but not yet confirmed; flag for review.
-/

import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.ContinuousMap.Basic

namespace PhysicsOfConsciousness

-- ============================================================
-- §1  Thermodynamics
-- ============================================================

/- 
  NOTE: The following two axioms (Landauer's Principle and Phase Space Locality) 
  are provided to establish the physical intuition and theoretical context. 
  They are commented out because they are not actively invoked in the Lean proofs 
  (for instance, Landauer's bound is derived constructively from statistical 
  mechanics in Phase 3).
-/
/-
/--
[IRREDUCIBLE] **Landauer's Principle.**
Erasing one bit of information in a system at temperature T dissipates at least
k_B · T · ln 2 joules as heat.

*Why irreducible:* This is a consequence of the Second Law of Thermodynamics
applied to information processing. It connects Shannon entropy to
thermodynamic entropy. It is a physical postulate — not a mathematical theorem —
because it requires identifying logical bit-erasure with a physical
thermodynamic process.

*Reference:* Landauer (1961), "Irreversibility and Heat Generation in the
Computing Process", IBM Journal of Research and Development.
-/
axiom landauer_principle (k_B T : ℝ) (hT : T > 0) (hk : k_B > 0) :
  ∀ (bits_erased : ℕ),
    (bits_erased : ℝ) * k_B * T * Real.log 2 > 0

/--
[IRREDUCIBLE] **Phase Space Locality.**
A physically localized subsystem (bounded region of spacetime) has a finite,
compact phase space.

*Why irreducible:* This is a modelling assumption grounded in quantum mechanics
(finite Hilbert space dimension for bounded energy in a bounded volume) and
classical statistical mechanics. No purely topological argument can guarantee
compactness from first principles without additional physical structure.
-/
axiom phase_space_is_compact {X : Type*} [TopologicalSpace X]
  (_h_local : LocallyCompactSpace X) -- The system has locally compact state space
  (_h_bounded : ∃ K : Set X, IsCompact K ∧ ∀ x : X, x ∈ K) -- and is bounded
  : CompactSpace X
  -/

-- ============================================================
-- §2  Dynamics — Invariant Measure and Section Agreement
-- ============================================================

-- (Removed `section_agrees_of_phase_eq_physical` as it was successfully derived in Task 6)

-- Cross-reference: `landauer_heat_eq` (heat dissipation = T × ΔS_bath) is declared
-- in Phase3_CombinatorialThermodynamics.lean as a standalone axiom.
-- Status: [IRREDUCIBLE] — physical postulate linking info theory to thermodynamics.
--
-- Historical: `phase_invariant_periodic` (invariant measure is 2π-periodic) and
-- `sync_to_section_eq` (local section = restricted invariant measure) were once
-- standalone axioms in Phase4_MacroscopicScaling.lean, then class fields of
-- `LocalSectionSynchronization`. Both are **gone** as of 2026-08-30 (open item
-- O19): they named a *global* section, so the class supplied the object the
-- gluing theorem was supposed to produce. `sync_to_section_eq` is now a theorem
-- (`ThermodynamicCover.sync_to_section_eq`) about the section
-- `probability_glue_unique` constructs; the periodicity condition survives only
-- as a hypothesis of the constructor `LocalSectionSynchronization.ofInvariantMeasure`,
-- which packages the old shape for the witnesses built that way.
--
-- What replaced them: `LocalSectionSynchronization.section_agrees_of_phase_eq`,
-- the condition that patches at a common phase agree on their overlaps.
-- Status: [MODELLING] — could be derived from dynamics with more infrastructure.
-- Unlike its predecessors it quantifies only over single patches and single
-- overlaps, so it presupposes no global object.

-- ============================================================
-- §3  Phase-Locking Bridge
-- ============================================================

-- ============================================================
-- §4  Field Theory
-- ============================================================

/-
  NOTE: The Least-Action Principle below is provided for physical context. 
  It is not actively invoked in the proofs because the mathematical consequence 
  of this principle (that structural resonance follows a gradient flow on the 
  entropy functional) is directly proved as a theorem in Phase 8 
  (`gradient_flow_implies_entropy_decrease`).
-/
/-
/--
[MODELLING] **Least-Action Principle.**
The physical trajectory of the coupled field is a stationary point of the
action functional S[φ] = ∫ L(φ, ∂φ) dt dx.

*Why here:* The principle of least action is a foundational postulate of
classical and quantum field theory. It cannot be derived from more primitive
mathematical assumptions — it is an empirical organizing principle.

*Scope:* Used in Phase 8 to justify that structural resonance follows gradient
flow on the entropy production functional.

*Status:* The formal statement is: any physically realized trajectory `theta`
minimizes the action `S[theta]` over all competing smooth trajectories.
Formalizing the action functional over the continuous neural field requires
Sobolev space infrastructure not yet present in this formalization.
-/
-- The formal statement requires Sobolev space infrastructure not yet present.
-- We state it as: every physical trajectory is a stationary point of the action
-- with respect to smooth compactly supported variations.
-- Type signature uses a generic action functional S : (M → ℝ → ℝ) → ℝ.
axiom principle_of_least_action
    {M : Type*} [MeasureTheory.MeasureSpace M]
    (S : (M → ℝ → ℝ) → ℝ)       -- The action functional
    (physical_trajectory : M → ℝ → ℝ) -- The physical field trajectory
    : ∀ (variation : M → ℝ → ℝ),
        HasDerivAt (fun ε => S (fun x t => physical_trajectory x t + ε * variation x t)) 0 0
-/

-- ============================================================
-- §5  Removed axioms (soundness record)
-- ============================================================

/-
  `spontaneous_symmetry_breaking_pointwise_min` was declared here until
  2026-08-29. It was **inconsistent** and has been removed.

  The statement was:

      axiom spontaneous_symmetry_breaking_pointwise_min
        {Spacetime ValueSpace} [TopologicalSpace Spacetime] [TopologicalSpace ValueSpace]
        {PotentialEnergy : (ContinuousMap Spacetime ValueSpace) → ℝ}
        (V : ValueSpace → ℝ) (phi : ContinuousMap Spacetime ValueSpace)
        (v0 : ValueSpace) (h_v0_vac : ∀ v', V v0 ≤ V v')
        (h_pot_eq : PotentialEnergy phi = V v0) :
        ∀ x, V (phi x) = V v0

  `PotentialEnergy` is implicit and occurs only in the hypothesis, so it can be
  instantiated with `fun _ => V v0`, discharging `h_pot_eq` by `rfl` and giving
  the conclusion for an arbitrary `phi`. With `V := fun v => v^2`, `v0 := 0`,
  `Spacetime := Unit` and `phi := const 1` this proves `1 = 0`.

  Replacement: `ActionPrinciples` (in `Phase1_Primitives.lean`) now defines
  `PotentialEnergy` as the integral of the pointwise potential, and
  `pointwise_vacuum_of_global_min` is a **theorem** proved from
  `MeasureTheory.integral_eq_zero_iff_of_nonneg`. The conclusion is `∀ᵐ`.

  Two further axioms were removed in the same pass for the same reason —
  each pinned a *free class field* across every instance of its class, and so
  was refutable by exhibiting an instance that violates it:

  * `landauer_heat_eq` (was in `Phase3_CombinatorialThermodynamics.lean`) is now
    the field `StatisticalMechanics.heat_eq`.
  * `kl_bound_axiom` (was in `Phase3_KLBound.lean`) is now the field
    `StructuralResonance.kl_bound`.

  **Design rule added as a result:** a physical postulate that mentions a class
  field must be a *field of that class* (an obligation on instances), never a
  standalone `axiom` quantified over all instances. A standalone axiom is only
  safe when every symbol it constrains is bound by the axiom itself.
-/

end PhysicsOfConsciousness
