/-
  Phase 4: Macroscopic Scaling via Sheaf Theory
  
  This module formalizes:
  1. The projection of synchronized discrete states back onto the continuous probability presheaf.
  2. The compatibility of these local sections (restriction map agreement) guaranteed by 
     the phase-locking proven in Phase 3 & 4.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase2_SimplicialBridge
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase4_KuramotoDynamics
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure

open CategoryTheory TopologicalSpace MeasureTheory
open Opposite

namespace PhysicsOfConsciousness

universe u

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X]

/--
A cover of `X` by local regions, each carrying a phase and a local section of the
probability presheaf.

**Soundness note.** `phase_invariant_periodic` and `sync_to_section_eq` were
previously declared as standalone `axiom`s quantified over `[S :
LocalSectionSynchronization X]`. That is the same defect that made
`landauer_heat_eq` and `kl_bound_axiom` inconsistent: a standalone axiom that
pins *free fields* of a class constrains every instance of that class, including
instances built to violate it, so it is refutable as soon as the presheaf has
two distinct global sections. Carrying them as fields makes them obligations on
each instance instead — which is what a modelling assumption should be.
-/
class LocalSectionSynchronization (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X] where
  I : Type u
  cover : I → Opens X
  is_cover : iSup cover = ⊤
  
  -- Each discrete node i has a local section of probability, corresponding to its phase
  phase : I → ℝ
  
  sync_to_section : (i : I) → (probabilityPresheaf X).obj (op (cover i))
  
  -- The physical invariant measure parameterized by a macroscopic phase.
  phase_invariant_measure : ℝ → (probabilityPresheaf X).obj (op ⊤)

  /-- [MODELLING] Periodic phase invariance: the invariant measure depends only on
      the physical phase state, which is 2π-periodic. Could be derived from full
      dynamical-systems invariance theory. -/
  phase_invariant_periodic : ∀ x y, Real.cos (x - y) = 1 →
    phase_invariant_measure x = phase_invariant_measure y

  /-- [MODELLING] The local section is the restriction of the phase's invariant
      measure to the local cover. -/
  sync_to_section_eq : ∀ i, sync_to_section i =
    (probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op
      (phase_invariant_measure (phase i))

-- Phase-locked equilibrium means all nodes have the same phase modulo 2pi.
def phase_locked_equilibrium [S : LocalSectionSynchronization X] : Prop :=
  ∀ i j, Real.cos (S.phase i - S.phase j) = 1

-- Theorem: If two oscillators have the same phase (i.e. perfectly correlated),
-- their invariant measures over their respective regions are identical on the intersection.
theorem section_agrees_of_phase_eq [S : LocalSectionSynchronization X] (i j : S.I) (h_eq : Real.cos (S.phase i - S.phase j) = 1) :
  (probabilityPresheaf X).map (homOfLE (inf_le_left : S.cover i ⊓ S.cover j ≤ S.cover i)).op (S.sync_to_section i) =
  (probabilityPresheaf X).map (homOfLE (inf_le_right : S.cover i ⊓ S.cover j ≤ S.cover j)).op (S.sync_to_section j) := by
  rw [S.sync_to_section_eq i, S.sync_to_section_eq j]
  have h_meas_eq : S.phase_invariant_measure (S.phase i) = S.phase_invariant_measure (S.phase j) := S.phase_invariant_periodic _ _ h_eq
  rw [h_meas_eq]
  have H1 : (probabilityPresheaf X).map (homOfLE (le_top : S.cover i ≤ ⊤)).op ≫ (probabilityPresheaf X).map (homOfLE (inf_le_left : S.cover i ⊓ S.cover j ≤ S.cover i)).op = (probabilityPresheaf X).map (homOfLE (le_top : S.cover i ⊓ S.cover j ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    rfl
  have H2 : (probabilityPresheaf X).map (homOfLE (le_top : S.cover j ≤ ⊤)).op ≫ (probabilityPresheaf X).map (homOfLE (inf_le_right : S.cover i ⊓ S.cover j ≤ S.cover j)).op = (probabilityPresheaf X).map (homOfLE (le_top : S.cover i ⊓ S.cover j ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    rfl
  have H1_apply : (probabilityPresheaf X).map (homOfLE (inf_le_left : S.cover i ⊓ S.cover j ≤ S.cover i)).op ((probabilityPresheaf X).map (homOfLE (le_top : S.cover i ≤ ⊤)).op (S.phase_invariant_measure (S.phase j))) = 
    ((probabilityPresheaf X).map (homOfLE (le_top : S.cover i ≤ ⊤)).op ≫ (probabilityPresheaf X).map (homOfLE (inf_le_left : S.cover i ⊓ S.cover j ≤ S.cover i)).op) (S.phase_invariant_measure (S.phase j)) := rfl
  have H2_apply : (probabilityPresheaf X).map (homOfLE (inf_le_right : S.cover i ⊓ S.cover j ≤ S.cover j)).op ((probabilityPresheaf X).map (homOfLE (le_top : S.cover j ≤ ⊤)).op (S.phase_invariant_measure (S.phase j))) = 
    ((probabilityPresheaf X).map (homOfLE (le_top : S.cover j ≤ ⊤)).op ≫ (probabilityPresheaf X).map (homOfLE (inf_le_right : S.cover i ⊓ S.cover j ≤ S.cover j)).op) (S.phase_invariant_measure (S.phase j)) := rfl
  rw [H1_apply, H2_apply, H1, H2]

-- Prove that if the system reaches a phase-locked equilibrium, the local sections overlap perfectly.
theorem overlap_agreement [S : LocalSectionSynchronization X] (h_sync : phase_locked_equilibrium (S := S)) :
  ∀ (i j : S.I),
    (probabilityPresheaf X).map (homOfLE (inf_le_left : S.cover i ⊓ S.cover j ≤ S.cover i)).op (S.sync_to_section i) =
    (probabilityPresheaf X).map (homOfLE (inf_le_right : S.cover i ⊓ S.cover j ≤ S.cover j)).op (S.sync_to_section j) := by
  intro i j
  apply section_agrees_of_phase_eq
  exact h_sync i j

-- Prove that the purely dynamic phase locking implies structural equilibrium
theorem phase_locked_implies_equilibrium (S : LocalSectionSynchronization X)
  (h_dyn_lock : is_phase_locked S.phase) : phase_locked_equilibrium (S := S) := by
  intro i j
  exact h_dyn_lock i j

end PhysicsOfConsciousness
