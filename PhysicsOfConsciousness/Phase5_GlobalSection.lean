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

class ThermodynamicCover (X : TopCat.{u}) [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X] 
  extends LocalSectionSynchronization X where
  I_fintype : Fintype I
  I_decidable : DecidableEq I
  A : I → I → ℝ
  A_symm : ∀ i j, A i j = A j i
  A_pos : ∀ i j, A i j > 0
  thermodynamic_equilibrium : 
    letI := I_fintype
    letI := I_decidable
    ∀ (theta : I → ℝ), 
      kuramoto_potential_dynamic (V := I) ⟨fun _ => 0, A, A_symm⟩ phase ≤ 
      kuramoto_potential_dynamic (V := I) ⟨fun _ => 0, A, A_symm⟩ theta

theorem global_section_from_thermodynamics [T : ThermodynamicCover X]
  (h_min_implies_lock : 
    letI := T.I_fintype
    letI := T.I_decidable
    (∀ theta, kuramoto_potential_dynamic (V := T.I) ⟨fun _ => 0, T.A, T.A_symm⟩ T.phase ≤ kuramoto_potential_dynamic (V := T.I) ⟨fun _ => 0, T.A, T.A_symm⟩ theta) → is_phase_locked T.phase) :
  ∃! s : GlobalSection (X := X), 
    ∀ i : T.I, (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op s = T.sync_to_section i := by
  have h_locked : is_phase_locked T.phase := h_min_implies_lock T.thermodynamic_equilibrium
  have h_eq : phase_locked_equilibrium (S := T.toLocalSectionSynchronization) := by
    intro i j; exact h_locked i j
  have h_compat : TopCat.Presheaf.IsCompatible (probabilityPresheaf X) T.cover T.sync_to_section := by
    intro i j
    exact overlap_agreement h_eq i j
  have h_sheaf_gluing := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types (probabilityPresheaf X)).mp probability_is_sheaf
  have ⟨s, hs, h_uniq⟩ := h_sheaf_gluing T.cover T.sync_to_section h_compat
  let e' : op (iSup T.cover) ⟶ op ⊤ := (eqToHom (by rw [T.is_cover])).op
  let s_top : GlobalSection (X := X) := (probabilityPresheaf X).map e' s
  use s_top
  constructor
  · intro i
    have H_map : (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op s_top = 
                 ((probabilityPresheaf X).map e' ≫ (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op) s := rfl
    rw [H_map, ← (probabilityPresheaf X).map_comp]
    have H_eq : e' ≫ (homOfLE (le_top : T.cover i ≤ ⊤)).op = (Opens.leSupr T.cover i).op := by apply Subsingleton.elim
    rw [H_eq]
    exact hs i
  · intro s' hs'
    let e_inv : op ⊤ ⟶ op (iSup T.cover) := (eqToHom (by rw [T.is_cover.symm])).op
    have H_s'_eq : s' = ((probabilityPresheaf X).map e_inv ≫ (probabilityPresheaf X).map e') s' := by
      rw [← (probabilityPresheaf X).map_comp]
      have h_id : e_inv ≫ e' = 𝟙 _ := by apply Subsingleton.elim
      rw [h_id, (probabilityPresheaf X).map_id]
      rfl
    rw [H_s'_eq]
    have H_apply : (probabilityPresheaf X).map e_inv s' = s := by
      apply h_uniq
      intro i
      have H_map2 : (probabilityPresheaf X).map (Opens.leSupr T.cover i).op ((probabilityPresheaf X).map e_inv s') = 
                    ((probabilityPresheaf X).map e_inv ≫ (probabilityPresheaf X).map (Opens.leSupr T.cover i).op) s' := rfl
      rw [H_map2, ← (probabilityPresheaf X).map_comp]
      have H_eq2 : e_inv ≫ (Opens.leSupr T.cover i).op = (homOfLE (le_top : T.cover i ≤ ⊤)).op := by apply Subsingleton.elim
      rw [H_eq2]
      exact hs' i
    change (probabilityPresheaf X).map e' ((probabilityPresheaf X).map e_inv s') = (probabilityPresheaf X).map e' s
    rw [H_apply]

end PhysicsOfConsciousness
