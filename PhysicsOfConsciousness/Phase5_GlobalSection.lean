/-
  Phase 5: Unity of Consciousness as a Global Section
  
  This module formalizes:
  1. The "Unity of Consciousness" as the existence of a Global Section of the probability sheaf.
  2. The inevitable emergence of this section via sheaf gluing conditions.
-/

import PhysicsOfConsciousness.Phase4_MacroscopicScaling
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

open CategoryTheory TopologicalSpace MeasureTheory
open Opposite

namespace PhysicsOfConsciousness

universe u

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X]

theorem probability_is_sheaf : TopCat.Presheaf.IsSheaf (probabilityPresheaf X) :=
  (TopCat.Presheaf.sheafify (probabilityPresheaf_pre X)).property

noncomputable def GlobalSection := (probabilityPresheaf X).obj (op ⊤)

theorem global_section_from_local_sync [S : LocalSectionSynchronization X] (h_sync : phase_locked_equilibrium (S := S)) :
  ∃! s : GlobalSection (X := X), 
    ∀ i : S.I, (probabilityPresheaf X).map (homOfLE (le_top : S.cover i ≤ ⊤)).op s = S.sync_to_section i := by
  have h_compat : TopCat.Presheaf.IsCompatible (probabilityPresheaf X) S.cover S.sync_to_section := by
    intro i j
    exact overlap_agreement h_sync i j
  have h_sheaf_gluing := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types (probabilityPresheaf X)).mp probability_is_sheaf
  have ⟨s, hs, h_uniq⟩ := h_sheaf_gluing S.cover S.sync_to_section h_compat
  let e' : op (iSup S.cover) ⟶ op ⊤ := (eqToHom (by rw [S.is_cover])).op
  let s_top : GlobalSection (X := X) := (probabilityPresheaf X).map e' s
  use s_top
  constructor
  · intro i
    have H_map : (probabilityPresheaf X).map (homOfLE (le_top : S.cover i ≤ ⊤)).op s_top = 
                 ((probabilityPresheaf X).map e' ≫ (probabilityPresheaf X).map (homOfLE (le_top : S.cover i ≤ ⊤)).op) s := rfl
    rw [H_map, ← (probabilityPresheaf X).map_comp]
    have H_eq : e' ≫ (homOfLE (le_top : S.cover i ≤ ⊤)).op = (Opens.leSupr S.cover i).op := by apply Subsingleton.elim
    rw [H_eq]
    exact hs i
  · intro s' hs'
    let e_inv : op ⊤ ⟶ op (iSup S.cover) := (eqToHom (by rw [S.is_cover.symm])).op
    have H_s'_eq : s' = ((probabilityPresheaf X).map e_inv ≫ (probabilityPresheaf X).map e') s' := by
      rw [← (probabilityPresheaf X).map_comp]
      have h_id : e_inv ≫ e' = 𝟙 _ := by apply Subsingleton.elim
      rw [h_id, (probabilityPresheaf X).map_id]
      rfl
    rw [H_s'_eq]
    have H_apply : (probabilityPresheaf X).map e_inv s' = s := by
      apply h_uniq
      intro i
      have H_map2 : (probabilityPresheaf X).map (Opens.leSupr S.cover i).op ((probabilityPresheaf X).map e_inv s') = 
                    ((probabilityPresheaf X).map e_inv ≫ (probabilityPresheaf X).map (Opens.leSupr S.cover i).op) s' := rfl
      rw [H_map2, ← (probabilityPresheaf X).map_comp]
      have H_eq2 : e_inv ≫ (Opens.leSupr S.cover i).op = (homOfLE (le_top : S.cover i ≤ ⊤)).op := by apply Subsingleton.elim
      rw [H_eq2]
      exact hs' i
    change (probabilityPresheaf X).map e' ((probabilityPresheaf X).map e_inv s') = (probabilityPresheaf X).map e' s
    rw [H_apply]

end PhysicsOfConsciousness
