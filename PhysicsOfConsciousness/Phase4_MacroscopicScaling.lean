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

**All the data is local.** `cover`, `phase` and `sync_to_section` mention only
the individual patches; no global object appears anywhere in the class. That is
the point of the present shape, and it was not always so — see the two notes
below.

**Soundness note (2026-08-29).** `phase_invariant_periodic` and
`sync_to_section_eq` were once declared as standalone `axiom`s quantified over
`[S : LocalSectionSynchronization X]`. That is the same defect that made
`landauer_heat_eq` and `kl_bound_axiom` inconsistent: a standalone axiom that
pins *free fields* of a class constrains every instance of that class, including
instances built to violate it, so it is refutable as soon as the presheaf has
two distinct global sections. Carrying them as fields made them obligations on
each instance instead — which is what a modelling assumption should be.

**Emergence note (2026-08-30, open item O19).** Carrying them as fields fixed the
soundness problem and created a different one. The class used to hold a field
`phase_invariant_measure : ℝ → (probabilityPresheaf X).obj (op ⊤)` — a *global*
section — together with `sync_to_section_eq`, which declared every local section
to be a restriction of it. The global object therefore existed before the sheaf
condition was ever invoked, and `global_section_from_thermodynamics` could only
be read as a uniqueness statement: it ruled out competitors to an object the
instance had already supplied. Derivation 5 claims more than that.

Both fields are now gone. What replaces them is `section_agrees_of_phase_eq`,
which says only that patches *at the same phase agree where they overlap* — a
condition on the local data alone, with no global section in sight. The common
measure is then produced by the sheaf condition
(`ThermodynamicCover.invariantMeasure`) and `sync_to_section_eq` is recovered as
a *theorem* (`ThermodynamicCover.sync_to_section_eq`). The old shape is not lost:
`LocalSectionSynchronization.ofInvariantMeasure` rebuilds it as a constructor,
which is exactly the statement that it was a special case all along.
-/
class LocalSectionSynchronization (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X] where
  I : Type u
  cover : I → Opens X
  is_cover : iSup cover = ⊤
  
  -- Each discrete node i has a local section of probability, corresponding to its phase
  phase : I → ℝ
  
  sync_to_section : (i : I) → (probabilityPresheaf X).obj (op (cover i))

  /-- [MODELLING] **Synchronised patches agree where they overlap.** Two patches
      whose phases coincide modulo `2π` assign the same local probability to the
      region they share.

      This is the physical content of Derivation 5 and it is an obligation on
      each instance, not a theorem: nothing in the development derives it from
      the dynamics. What it does *not* do is presuppose the conclusion. Every
      symbol in it ranges over a single patch or a single overlap; unlike the
      `sync_to_section_eq` field it replaced, it never mentions a section over
      `⊤`. -/
  section_agrees_of_phase_eq : ∀ i j, Real.cos (phase i - phase j) = 1 →
    (probabilityPresheaf X).map (homOfLE (inf_le_left : cover i ⊓ cover j ≤ cover i)).op
        (sync_to_section i) =
      (probabilityPresheaf X).map (homOfLE (inf_le_right : cover i ⊓ cover j ≤ cover j)).op
        (sync_to_section j)

/--
The **old class shape, as a constructor**: a `2π`-periodic family of global
invariant measures indexed by phase, with each local section defined to be a
restriction of the member its patch's phase selects.

Keeping it as a constructor rather than deleting it records two things. It is the
proof that the weakened class is genuinely *weaker* — every instance of the old
shape is still an instance — and it keeps the witnesses that were built that way
(`Examples.lean` §4, §13) working unchanged, so the strengthening in `Examples.lean`
§14 can be compared against them rather than replacing them.

What it does not do is let an instance built this way claim the emergence
reading. For such an instance the glued section is the family member it started
from, which is what `Examples.lean` §13's `cortexCoverTwisted_glued` computes.
-/
@[instance_reducible]
noncomputable def LocalSectionSynchronization.ofInvariantMeasure
    (I : Type u) (cover : I → Opens X) (is_cover : iSup cover = ⊤) (phase : I → ℝ)
    (M : ℝ → (probabilityPresheaf X).obj (op ⊤))
    (M_periodic : ∀ x y, Real.cos (x - y) = 1 → M x = M y) :
    LocalSectionSynchronization X where
  I := I
  cover := cover
  is_cover := is_cover
  phase := phase
  sync_to_section := fun i =>
    (probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op (M (phase i))
  section_agrees_of_phase_eq := by
    intro i j h_eq
    have h_meas_eq : M (phase i) = M (phase j) := M_periodic _ _ h_eq
    rw [h_meas_eq]
    have H1 : (probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op ≫
        (probabilityPresheaf X).map (homOfLE (inf_le_left : cover i ⊓ cover j ≤ cover i)).op =
        (probabilityPresheaf X).map (homOfLE (le_top : cover i ⊓ cover j ≤ ⊤)).op := by
      rw [← Functor.map_comp]; rfl
    have H2 : (probabilityPresheaf X).map (homOfLE (le_top : cover j ≤ ⊤)).op ≫
        (probabilityPresheaf X).map (homOfLE (inf_le_right : cover i ⊓ cover j ≤ cover j)).op =
        (probabilityPresheaf X).map (homOfLE (le_top : cover i ⊓ cover j ≤ ⊤)).op := by
      rw [← Functor.map_comp]; rfl
    have H1_apply :
        (probabilityPresheaf X).map (homOfLE (inf_le_left : cover i ⊓ cover j ≤ cover i)).op
            ((probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op (M (phase j))) =
          ((probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op ≫
            (probabilityPresheaf X).map
              (homOfLE (inf_le_left : cover i ⊓ cover j ≤ cover i)).op) (M (phase j)) := rfl
    have H2_apply :
        (probabilityPresheaf X).map (homOfLE (inf_le_right : cover i ⊓ cover j ≤ cover j)).op
            ((probabilityPresheaf X).map (homOfLE (le_top : cover j ≤ ⊤)).op (M (phase j))) =
          ((probabilityPresheaf X).map (homOfLE (le_top : cover j ≤ ⊤)).op ≫
            (probabilityPresheaf X).map
              (homOfLE (inf_le_right : cover i ⊓ cover j ≤ cover j)).op) (M (phase j)) := rfl
    rw [H1_apply, H2_apply, H1, H2]

-- Phase-locked equilibrium means all nodes have the same phase modulo 2pi.
def phase_locked_equilibrium [S : LocalSectionSynchronization X] : Prop :=
  ∀ i j, Real.cos (S.phase i - S.phase j) = 1

-- Prove that if the system reaches a phase-locked equilibrium, the local sections overlap perfectly.
theorem overlap_agreement [S : LocalSectionSynchronization X] (h_sync : phase_locked_equilibrium (S := S)) :
  ∀ (i j : S.I),
    (probabilityPresheaf X).map (homOfLE (inf_le_left : S.cover i ⊓ S.cover j ≤ S.cover i)).op (S.sync_to_section i) =
    (probabilityPresheaf X).map (homOfLE (inf_le_right : S.cover i ⊓ S.cover j ≤ S.cover j)).op (S.sync_to_section j) :=
  fun i j => S.section_agrees_of_phase_eq i j (h_sync i j)

-- Prove that the purely dynamic phase locking implies structural equilibrium
theorem phase_locked_implies_equilibrium (S : LocalSectionSynchronization X)
  (h_dyn_lock : is_phase_locked S.phase) : phase_locked_equilibrium (S := S) := by
  intro i j
  exact h_dyn_lock i j

end PhysicsOfConsciousness
