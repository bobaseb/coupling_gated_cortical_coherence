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
noncomputable def probabilityPresheaf : (Opens X)ᵒᵖ ⥤ Type _ where
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

  
-- 2. Symmetry Breaking and Topological Defects (Homotopy)
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

-- 3. The Stress-Energy Tensor (T_mu_nu)
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

end PhysicsOfConsciousness
