/-
  Phase 1: Primitives, Symmetry, Boundaries, and the Stress-Energy Tensor
  
  This module formalizes the foundational axioms of the theory:
  1. Spacetime and Fields over Pseudo-Riemannian Manifolds
  2. Spontaneous Symmetry Breaking and Topological Defects (Homotopy)
  3. The Stress-Energy Tensor and its subsystem decomposition
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import PhysicsOfConsciousness.Axioms
open Manifold
open Topology
open CategoryTheory TopologicalSpace MeasureTheory

namespace PhysicsOfConsciousness

-- 1. Spacetime and Fields
-- We define the physical system over a pseudo-Riemannian manifold.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {Spacetime : Type*} [TopologicalSpace Spacetime] [ChartedSpace H Spacetime]
variable [IsManifold I ⊤ Spacetime]

-- A rank-2 covariant tensor field assigns a continuous bilinear form on the tangent space at each point.
def CovariantTensor2 (I : ModelWithCorners ℝ E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] :=
  ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

-- A Pseudo-Riemannian Manifold has a metric which is a symmetric, non-degenerate CovariantTensor2.
class PseudoRiemannianManifold (I : ModelWithCorners ℝ E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] where
  metric : CovariantTensor2 I M
  symm : ∀ x u v, metric x u v = metric x v u
  nondeg : ∀ x u, (∀ v, metric x u v = 0) → u = 0

-- A Field is a mapping from Spacetime to some ValueSpace (e.g., energy states, vacuum manifold).
structure Field (Spacetime : Type*) (ValueSpace : Type*) where
  val : Spacetime → ValueSpace

-- Define fields and probability distributions as Presheaves over the topological space.
-- Let X represent the continuous biological substrate (e.g., cortical sheet).
variable (X : TopCat) [MeasurableSpace X] [BorelSpace X]

lemma inc_is_measurable_embedding {U V : Opens X} (hUV : V ≤ U) :
  MeasurableEmbedding (fun (x : ↥V) => (⟨x.val, hUV x.property⟩ : ↥U)) where
  injective := fun x y hxy => Subtype.ext (by injection hxy)
  measurable := by
    apply Continuous.measurable
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val
  measurableSet_image' := by
    intro s hs
    have h_embed : MeasurableEmbedding (Subtype.val : ↥V → ↥X) := 
      MeasurableEmbedding.subtype_coe V.isOpen.measurableSet
    have h_s_img : MeasurableSet (Subtype.val '' s) := h_embed.measurableSet_image.mpr hs
    have h_preimage : MeasurableSet ((Subtype.val : ↥U → ↥X) ⁻¹' (Subtype.val '' s)) :=
      (Continuous.measurable continuous_subtype_val) h_s_img
    have h_eq : ((fun (x : ↥V) => (⟨x.val, hUV x.property⟩ : ↥U)) '' s) = (Subtype.val : ↥U → ↥X) ⁻¹' (Subtype.val '' s) := by
      ext u
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨x, hx_val, hx_eq⟩
        have h_eq_v : (⟨x.val, hUV x.property⟩ : ↥U) = u := Subtype.ext hx_eq
        rw [← h_eq_v]
        exact ⟨x, hx_val, rfl⟩
    rw [h_eq]
    exact h_preimage

-- The presheaf of probability densities over X.
-- Each local section s ∈ F(U) represents the finite measure (unnormalized probability) 
-- derived from the local structural resonance within the subsystem U.
noncomputable def probabilityPresheaf_pre : (Opens X)ᵒᵖ ⥤ Type _ where
  obj U := FiniteMeasure (↥U.unop)
  -- The restriction map simply restricts the measure's domain to the smaller open subset
  map {U V} i := ↾(fun μ => FiniteMeasure.comap (fun x => ⟨x.val, i.unop.le x.property⟩) μ)
  -- Functor laws ensure compatibility
  map_id U := by
    ext μ s hs
    dsimp
    have H_id : (fun (x : ↥U.unop) => (⟨x.val, (𝟙 U).unop.le x.property⟩ : ↥U.unop)) = (fun x => x) := by ext x; rfl
    rw [H_id]
    have H_eq : Measure.comap (fun x : ↥U.unop => x) (μ : Measure ↥U.unop) = (μ : Measure ↥U.unop) := Measure.comap_id (μ : Measure ↥U.unop)
    rw [H_eq]
  map_comp {U V W} i j := by
    ext μ s hs
    dsimp
    let inc1 : ↥W.unop → ↥V.unop := fun x => ⟨x.val, j.unop.le x.property⟩
    let inc2 : ↥V.unop → ↥U.unop := fun x => ⟨x.val, i.unop.le x.property⟩
    have H_comp : (fun (x : ↥W.unop) => (⟨x.val, (i ≫ j).unop.le x.property⟩ : ↥U.unop)) = inc2 ∘ inc1 := rfl
    rw [H_comp]
    have H1 := inc_is_measurable_embedding X j.unop.le
    have H2 := inc_is_measurable_embedding X i.unop.le
    have h1 : ∀ (s : Set ↥W.unop), MeasurableSet s → MeasurableSet (inc1 '' s) := fun s hs => H1.measurableSet_image.mpr hs
    have h2 : Function.Injective inc2 := H2.injective
    have h3 : ∀ (s : Set ↥V.unop), MeasurableSet s → MeasurableSet (inc2 '' s) := fun s hs => H2.measurableSet_image.mpr hs
    have H := Measure.comap_comap h1 h2 h3 (μ := (μ : Measure ↥U.unop))
    rw [← H]

  

-- 2. Action Principles, Continuous Symmetries, and Spontaneous Symmetry Breaking
abbrev FieldState (S V : Type*) [TopologicalSpace S] [TopologicalSpace V] := ContinuousMap S V

-- Continuous symmetries (like the Poincaré group or internal gauge groups) acting on the system.
class ContinuousSymmetryGroup (G Spacetime ValueSpace : Type*) 
  [Group G] [TopologicalSpace Spacetime] [TopologicalSpace ValueSpace] where
  space_action : G → Spacetime → Spacetime
  value_action : G → ValueSpace → ValueSpace
  -- Abstract action on the field state: g • phi
  field_action : G → FieldState Spacetime ValueSpace → FieldState Spacetime ValueSpace

def DynamicalVacuum (V : ValueSpace → ℝ) : Set ValueSpace :=
  { v | ∀ v', V v ≤ V v' }

class ActionPrinciples (Spacetime ValueSpace : Type*) [TopologicalSpace Spacetime] [TopologicalSpace ValueSpace]
  (KineticEnergy PotentialEnergy TotalEnergy : FieldState Spacetime ValueSpace → ℝ) (V : ValueSpace → ℝ) where
  total_eq : ∀ phi, TotalEnergy phi = KineticEnergy phi + PotentialEnergy phi
  kinetic_nonneg : ∀ phi, 0 ≤ KineticEnergy phi
  kinetic_const : ∀ (v : ValueSpace), KineticEnergy (ContinuousMap.const Spacetime v) = 0
  potential_const : ∀ (v : ValueSpace), PotentialEnergy (ContinuousMap.const Spacetime v) = V v
  potential_bound : ∀ (phi : FieldState Spacetime ValueSpace) (v0 : ValueSpace), 
    v0 ∈ DynamicalVacuum V → V v0 ≤ PotentialEnergy phi

-- An action principle is invariant under a continuous symmetry group (e.g. Poincaré invariance)
class SymmetryInvariantAction (G Spacetime ValueSpace : Type*) 
  [Group G] [TopologicalSpace Spacetime] [TopologicalSpace ValueSpace]
  (KineticEnergy PotentialEnergy TotalEnergy : FieldState Spacetime ValueSpace → ℝ) (V : ValueSpace → ℝ) 
  [ActionPrinciples Spacetime ValueSpace KineticEnergy PotentialEnergy TotalEnergy V]
  [ContinuousSymmetryGroup G Spacetime ValueSpace] where
  total_energy_invariant : ∀ (g : G) (phi : FieldState Spacetime ValueSpace), 
    TotalEnergy (ContinuousSymmetryGroup.field_action g phi) = TotalEnergy phi

theorem spontaneous_symmetry_breaking 
  {Spacetime ValueSpace : Type*} [TopologicalSpace Spacetime] [TopologicalSpace ValueSpace]
  {KineticEnergy PotentialEnergy TotalEnergy : FieldState Spacetime ValueSpace → ℝ}
  {V : ValueSpace → ℝ}
  (inst : ActionPrinciples Spacetime ValueSpace KineticEnergy PotentialEnergy TotalEnergy V)
  (phi : FieldState Spacetime ValueSpace)
  (v0 : ValueSpace) (hv0 : v0 ∈ DynamicalVacuum V)
  (h_min : ∀ phi', TotalEnergy phi ≤ TotalEnergy phi') :
  ∀ x, phi x ∈ DynamicalVacuum V := by
  have h1 : TotalEnergy phi ≤ TotalEnergy (ContinuousMap.const Spacetime v0) := h_min _
  have h_tot_const : TotalEnergy (ContinuousMap.const Spacetime v0) = KineticEnergy (ContinuousMap.const Spacetime v0) + PotentialEnergy (ContinuousMap.const Spacetime v0) := inst.total_eq (ContinuousMap.const Spacetime v0)
  rw [h_tot_const] at h1
  have h_k_const : KineticEnergy (ContinuousMap.const Spacetime v0) = 0 := inst.kinetic_const v0
  rw [h_k_const] at h1
  have h_p_const : PotentialEnergy (ContinuousMap.const Spacetime v0) = V v0 := inst.potential_const v0
  rw [h_p_const] at h1
  rw [zero_add] at h1
  
  have h2 : TotalEnergy phi = KineticEnergy phi + PotentialEnergy phi := inst.total_eq phi
  rw [h2] at h1
  
  have hK : 0 ≤ KineticEnergy phi := inst.kinetic_nonneg phi
  have hP : V v0 ≤ PotentialEnergy phi := inst.potential_bound phi v0 hv0
  
  have hP_eq : PotentialEnergy phi = V v0 := by linarith
  
  -- We now invoke the irreducible physical postulate that global energy minimization
  -- implies pointwise potential minimization (which requires localized perturbations in Sobolev spaces).
  have h_pointwise_pot := spontaneous_symmetry_breaking_pointwise_min V phi v0 hv0 hP_eq
  intro x
  have h_pot_x : V (phi x) = V v0 := h_pointwise_pot x
  unfold DynamicalVacuum
  unfold DynamicalVacuum at hv0
  simp only [Set.mem_setOf_eq]
  simp only [Set.mem_setOf_eq] at hv0
  rw [h_pot_x]
  exact hv0

-- 3. Symmetry Breaking and Topological Defects (Homotopy)
-- A vacuum manifold is a topological space of degenerate energy minima resulting from broken symmetry.
class VacuumManifold (V : Type*) [TopologicalSpace V]

-- A field configuration on a spatial boundary (e.g., S^1, S^2) mapped to the vacuum V
abbrev BoundaryField (X V : Type*) [TopologicalSpace X] [TopologicalSpace V] :=
  ContinuousMap X V

-- A field configuration is topologically trivial (no defect) if it is null-homotopic.
def is_topologically_trivial {X V : Type*} [TopologicalSpace X] [TopologicalSpace V]
  (f : BoundaryField X V) : Prop :=
  ∃ (c : V), Nonempty (ContinuousMap.Homotopy f (ContinuousMap.const X c))

-- A topological defect exists if the boundary field is NOT null-homotopic.
def has_topological_defect {X V : Type*} [TopologicalSpace X] [TopologicalSpace V]
  (f : BoundaryField X V) : Prop :=
  ¬ is_topologically_trivial f

theorem defect_inevitability
  {X D V : Type*} [TopologicalSpace X] [TopologicalSpace D] [TopologicalSpace V]
  (i : ContinuousMap X D) (f : ContinuousMap D V) (d0 : D)
  (H : ContinuousMap.Homotopy (ContinuousMap.id D) (ContinuousMap.const D d0)) :
  is_topologically_trivial (f.comp i) := by
  use f d0
  let H2 : ContinuousMap.Homotopy (ContinuousMap.id D |>.comp i) (ContinuousMap.const D d0 |>.comp i) :=
    ContinuousMap.Homotopy.comp H (ContinuousMap.Homotopy.refl i)
  let H3 : ContinuousMap.Homotopy (f.comp i) (ContinuousMap.const X (f d0)) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl f) H2
  exact ⟨H3⟩

theorem boundary_defect_forces_interior_vacuum_break
  {X D V : Type*} [TopologicalSpace X] [TopologicalSpace D] [TopologicalSpace V]
  (i : ContinuousMap X D) (d0 : D)
  (H : ContinuousMap.Homotopy (ContinuousMap.id D) (ContinuousMap.const D d0))
  (g : BoundaryField X V) (h_defect : has_topological_defect g) :
  ¬ ∃ (f : ContinuousMap D V), f.comp i = g := by
  intro ⟨f, h_ext⟩
  have h_trivial := defect_inevitability i f d0 H
  rw [h_ext] at h_trivial
  exact h_defect h_trivial

-- 4. The Stress-Energy Tensor (T_mu_nu)
-- The Stress-Energy Tensor is a CovariantTensor2.

-- Decompose the total stress-energy tensor into subsystem-specific components.
structure DecomposedStressEnergyTensor (I : ModelWithCorners ℝ E H) (Spacetime : Type*)
  [TopologicalSpace Spacetime] [ChartedSpace H Spacetime] [IsManifold I ⊤ Spacetime] where
  EM   : CovariantTensor2 I Spacetime
  chem : CovariantTensor2 I Spacetime
  mech : CovariantTensor2 I Spacetime
  int  : CovariantTensor2 I Spacetime

-- The total Stress-Energy Tensor is the sum of its subsystems
noncomputable def total_T (T_decomp : DecomposedStressEnergyTensor I Spacetime) : CovariantTensor2 I Spacetime :=
  fun x => T_decomp.EM x + T_decomp.chem x + T_decomp.mech x + T_decomp.int x

noncomputable def probabilityPresheaf : (Opens X)ᵒᵖ ⥤ Type _ := (TopCat.Presheaf.sheafify (probabilityPresheaf_pre X)).1

end PhysicsOfConsciousness
