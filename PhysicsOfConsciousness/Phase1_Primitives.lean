/-
  Phase 1: Primitives, Symmetry, Boundaries, and the Stress-Energy Tensor
  
  This module formalizes the foundational axioms of the theory:
  1. Spacetime and Fields over Pseudo-Riemannian Manifolds
  2. Spontaneous Symmetry Breaking and Topological Defects (Homotopy)
  3. The Stress-Energy Tensor and its subsystem decomposition
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

/--
Structure of the action functional.

**Change of formulation (soundness fix).** Earlier versions took
`potential_const` and `potential_bound` as *assumed* fields and left
`PotentialEnergy` otherwise unconstrained, deferring the step "global energy
minimum ⇒ pointwise vacuum" to the axiom
`spontaneous_symmetry_breaking_pointwise_min`. That axiom was **inconsistent**:
its `PotentialEnergy` parameter was implicit and occurred only in the
hypothesis `PotentialEnergy phi = V v0`, so instantiating it with the constant
function `fun _ => V v0` discharged the hypothesis by `rfl` and yielded the
conclusion for *every* field. With `V := fun v => v^2`, `v0 := 0` and
`phi := const 1` that gives `1 = 0`.

The fix is to say what a potential energy functional actually *is*: the integral
of the pointwise potential against a background measure. With
`potential_integral` in place, `potential_const` and `potential_bound` become
derivable (see below), and pointwise minimization becomes a **theorem**
(`pointwise_vacuum_of_global_min`) rather than a postulate.
-/
class ActionPrinciples (Spacetime ValueSpace : Type*)
  [TopologicalSpace Spacetime] [MeasurableSpace Spacetime] [TopologicalSpace ValueSpace]
  (KineticEnergy PotentialEnergy TotalEnergy : FieldState Spacetime ValueSpace → ℝ)
  (V : ValueSpace → ℝ) (mu : Measure Spacetime) where
  total_eq : ∀ phi, TotalEnergy phi = KineticEnergy phi + PotentialEnergy phi
  kinetic_nonneg : ∀ phi, 0 ≤ KineticEnergy phi
  kinetic_const : ∀ (v : ValueSpace), KineticEnergy (ContinuousMap.const Spacetime v) = 0
  /-- The potential energy of a field is the integral of the pointwise potential. -/
  potential_integral : ∀ (phi : FieldState Spacetime ValueSpace),
    PotentialEnergy phi = ∫ x, V (phi x) ∂mu
  /-- The pointwise potential of any field configuration is integrable. -/
  potential_integrable : ∀ (phi : FieldState Spacetime ValueSpace),
    Integrable (fun x => V (phi x)) mu

section ActionPrinciplesConsequences
variable {Spacetime ValueSpace : Type*}
  [TopologicalSpace Spacetime] [MeasurableSpace Spacetime] [TopologicalSpace ValueSpace]
  {KineticEnergy PotentialEnergy TotalEnergy : FieldState Spacetime ValueSpace → ℝ}
  {V : ValueSpace → ℝ} {mu : Measure Spacetime} [IsProbabilityMeasure mu]

/-- Formerly an assumed field: the potential energy of a constant field is the
    potential at that value. Now derived from `potential_integral`. -/
theorem potential_const
    (inst : ActionPrinciples Spacetime ValueSpace KineticEnergy PotentialEnergy TotalEnergy V mu)
    (v : ValueSpace) :
    PotentialEnergy (ContinuousMap.const Spacetime v) = V v := by
  rw [inst.potential_integral]
  simp

/-- Formerly an assumed field: the potential energy of any field is at least the
    vacuum value. Now derived by monotonicity of the integral. -/
theorem potential_bound
    (inst : ActionPrinciples Spacetime ValueSpace KineticEnergy PotentialEnergy TotalEnergy V mu)
    (phi : FieldState Spacetime ValueSpace) (v0 : ValueSpace)
    (hv0 : v0 ∈ DynamicalVacuum V) :
    V v0 ≤ PotentialEnergy phi := by
  rw [inst.potential_integral]
  have h_le : ∀ x, V v0 ≤ V (phi x) := fun x => hv0 (phi x)
  calc V v0 = ∫ _x : Spacetime, V v0 ∂mu := by simp
    _ ≤ ∫ x, V (phi x) ∂mu :=
        integral_mono (integrable_const _) (inst.potential_integrable phi) h_le

/--
**Pointwise vacuum from global energy minimization.** [THEOREM — formerly an axiom]

If the potential energy functional attains the vacuum value `V v0`, then the
field takes vacuum values almost everywhere.

*Proof.* `g x := V (phi x) - V v0` is pointwise non-negative (since `v0`
minimizes `V`) and has integral zero, so `g = 0` almost everywhere by
`integral_eq_zero_iff_of_nonneg`.

The conclusion is `∀ᵐ`, not `∀`: a field may deviate from the vacuum on a
null set without changing its energy. This is the mathematically correct
statement; the earlier `∀ x` version was one of the reasons the axiomatic
formulation was unsound.
-/
theorem pointwise_vacuum_of_global_min
    (inst : ActionPrinciples Spacetime ValueSpace KineticEnergy PotentialEnergy TotalEnergy V mu)
    (phi : FieldState Spacetime ValueSpace) (v0 : ValueSpace)
    (hv0 : v0 ∈ DynamicalVacuum V)
    (h_pot_eq : PotentialEnergy phi = V v0) :
    ∀ᵐ x ∂mu, V (phi x) = V v0 := by
  have h_le : ∀ x, V v0 ≤ V (phi x) := fun x => hv0 (phi x)
  set g : Spacetime → ℝ := fun x => V (phi x) - V v0 with hg
  have hg_nonneg : 0 ≤ g := fun x => sub_nonneg.mpr (h_le x)
  have hg_int : Integrable g mu := (inst.potential_integrable phi).sub (integrable_const _)
  have hg_zero : ∫ x, g x ∂mu = 0 := by
    rw [hg, integral_sub (inst.potential_integrable phi) (integrable_const _)]
    rw [← inst.potential_integral, h_pot_eq]
    simp
  have := (integral_eq_zero_iff_of_nonneg hg_nonneg hg_int).mp hg_zero
  filter_upwards [this] with x hx
  have : V (phi x) - V v0 = 0 := hx
  linarith

end ActionPrinciplesConsequences

-- An action principle is invariant under a continuous symmetry group (e.g. Poincaré invariance)
class SymmetryInvariantAction (G Spacetime ValueSpace : Type*) 
  [Group G] [TopologicalSpace Spacetime] [MeasurableSpace Spacetime] [TopologicalSpace ValueSpace]
  (KineticEnergy PotentialEnergy TotalEnergy : FieldState Spacetime ValueSpace → ℝ) (V : ValueSpace → ℝ) 
  (mu : Measure Spacetime)
  [ActionPrinciples Spacetime ValueSpace KineticEnergy PotentialEnergy TotalEnergy V mu]
  [ContinuousSymmetryGroup G Spacetime ValueSpace] where
  total_energy_invariant : ∀ (g : G) (phi : FieldState Spacetime ValueSpace), 
    TotalEnergy (ContinuousSymmetryGroup.field_action g phi) = TotalEnergy phi

/--
**Spontaneous symmetry breaking.** A field that globally minimizes the total
energy sits in the vacuum manifold almost everywhere.

Formerly this theorem invoked the axiom
`spontaneous_symmetry_breaking_pointwise_min`, which was inconsistent (see the
`ActionPrinciples` doc-string). It is now **axiom-free**: the pointwise step is
`pointwise_vacuum_of_global_min`, proved from
`MeasureTheory.integral_eq_zero_iff_of_nonneg`.

The conclusion is almost-everywhere rather than everywhere. A field can leave
the vacuum on a `mu`-null set without changing its energy, so `∀ x` is simply
false at this level of generality; recovering it needs continuity of `V ∘ phi`
plus full support for `mu`.
-/
theorem spontaneous_symmetry_breaking 
  {Spacetime ValueSpace : Type*}
  [TopologicalSpace Spacetime] [MeasurableSpace Spacetime] [TopologicalSpace ValueSpace]
  {KineticEnergy PotentialEnergy TotalEnergy : FieldState Spacetime ValueSpace → ℝ}
  {V : ValueSpace → ℝ} {mu : Measure Spacetime} [IsProbabilityMeasure mu]
  (inst : ActionPrinciples Spacetime ValueSpace KineticEnergy PotentialEnergy TotalEnergy V mu)
  (phi : FieldState Spacetime ValueSpace)
  (v0 : ValueSpace) (hv0 : v0 ∈ DynamicalVacuum V)
  (h_min : ∀ phi', TotalEnergy phi ≤ TotalEnergy phi') :
  ∀ᵐ x ∂mu, phi x ∈ DynamicalVacuum V := by
  have h1 : TotalEnergy phi ≤ TotalEnergy (ContinuousMap.const Spacetime v0) := h_min _
  rw [inst.total_eq (ContinuousMap.const Spacetime v0), inst.kinetic_const v0,
      potential_const inst v0, zero_add, inst.total_eq phi] at h1
  have hK : 0 ≤ KineticEnergy phi := inst.kinetic_nonneg phi
  have hP : V v0 ≤ PotentialEnergy phi := potential_bound inst phi v0 hv0
  have hP_eq : PotentialEnergy phi = V v0 := by linarith
  filter_upwards [pointwise_vacuum_of_global_min inst phi v0 hv0 hP_eq] with x hx
  show ∀ v', V (phi x) ≤ V v'
  intro v'
  rw [hx]
  exact hv0 v'

-- 3. Symmetry Breaking and Topological Defects (Homotopy)
-- The set of degenerate energy minima is `DynamicalVacuum V`, defined above; an empty
-- marker class `VacuumManifold` also lived here, carrying no fields and used by nothing.
-- It was deleted rather than filled in: it asserted nothing, so no theorem could rest on
-- it, and its presence suggested the development had a notion of vacuum manifold that it
-- did not have.

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

/--
If the interior `D` is contractible, every boundary field that *extends* over it
is null-homotopic.

**Renamed from `defect_inevitability`.** The old name asserted the opposite of
what the statement says: this proves *triviality* of extendable configurations,
not the inevitability of defects. Nothing in this file shows that a defect must
exist; the direction that carries the physical argument is the contrapositive,
`boundary_defect_forces_interior_vacuum_break` below, which says a boundary
defect *obstructs* extension over a contractible interior.
-/
theorem contractible_interior_forces_trivial_boundary
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

/-! ### The `π₀` obstruction: a field joining two vacuum components must leave the vacuum

Derivation 1 is titled "Symmetry Breaking and the Inevitability of Boundaries",
and until now the file proved neither half of the inevitability. What it had was
`pointwise_vacuum_of_global_min` — an energy minimiser sits in the vacuum almost
everywhere — and `boundary_defect_forces_interior_vacuum_break`, which says a
boundary defect *obstructs extension* over a contractible interior. Neither
produces a defect. The sentence carrying the section's actual content, that
topology dictates the creation of defects, was asserted.

This is that sentence, at the level of `π₀`. It is the domain-wall case of the
Kibble mechanism: if the vacuum manifold `M` is disconnected and a continuous
field on a connected substrate takes values in two different components of `M`,
then somewhere it is not in `M` at all. The excluded region is the wall.

The proof is three lines and uses no physics: the continuous image of a
connected space is connected, a connected subset of `M` lies inside one
component of `M`, and the field's range is such a subset if it never leaves `M`.
That the argument is elementary is the point — it is elementary in the physics
literature too, and what was missing here was the statement, not the difficulty.

**Scope, deliberately.** Only `π₀`. The higher cases — `π₁ ≠ 0` forcing vortex
lines, `π₂ ≠ 0` forcing monopoles — are the rest of Kibble's classification, and
`Mathlib/Topology/Homotopy/HomotopyGroup.lean` would support at least the next
one. They are **available and not taken**, because the manuscript's argument uses
domain walls and nothing else, and a theorem the paper does not use is a theorem
whose hypotheses nobody checks.

Note also what this is *not*. `has_topological_defect` above is the
null-homotopy notion, which is about maps into `M` that cannot be contracted
*within* `M`; the theorems here are about a field that cannot stay in `M` at
all. The two are different obstructions and neither implies the other.
-/

/-- **Domain walls are forced.** If no preconnected subset of `M` contains both
`phi x₁` and `phi x₂` — which is what it means for those two values to lie in
different connected components of `M` — then the field leaves `M` somewhere.

Stated with the separation hypothesis rather than with `connectedComponentIn`
because this is the form a witness can discharge directly: exhibit the reason no
connected piece of the vacuum manifold spans both values.
`exists_notMem_of_connectedComponentIn` below is the same theorem in the
standard phrasing.

No hypothesis mentions energy, a potential, or a symmetry. The content is that
connectedness of the substrate plus disconnectedness of the vacuum manifold
forces the field out of the vacuum, whatever put it there. -/
theorem exists_notMem_of_no_common_preconnected
    {X V : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace V]
    (M : Set V) (phi : X → V) (h_cont : Continuous phi) (x₁ x₂ : X)
    (h_sep : ∀ S : Set V, IsPreconnected S → S ⊆ M → phi x₁ ∈ S → phi x₂ ∉ S) :
    ∃ x, phi x ∉ M := by
  by_contra hcon
  have hall : ∀ x, phi x ∈ M := fun x => not_not.mp fun h => hcon ⟨x, h⟩
  have h_img : IsPreconnected (Set.range phi) := by
    have h := (isPreconnected_univ (α := X)).image phi h_cont.continuousOn
    rwa [Set.image_univ] at h
  exact h_sep (Set.range phi) h_img (Set.range_subset_iff.mpr hall) ⟨x₁, rfl⟩ ⟨x₂, rfl⟩

/-- **The same theorem in the standard phrasing.** If `phi x₂` is not in the
connected component of `M` containing `phi x₁`, the field leaves `M`.

Derived from `exists_notMem_of_no_common_preconnected` because
`connectedComponentIn M (phi x₁)` is itself a preconnected subset of `M`
containing `phi x₁`, and it is the largest one. -/
theorem exists_notMem_of_connectedComponentIn
    {X V : Type*} [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace V]
    (M : Set V) (phi : X → V) (h_cont : Continuous phi) (x₁ x₂ : X)
    (h_sep : phi x₂ ∉ connectedComponentIn M (phi x₁)) :
    ∃ x, phi x ∉ M := by
  refine exists_notMem_of_no_common_preconnected M phi h_cont x₁ x₂ fun S hS hSM hx₁ hx₂ => ?_
  exact h_sep (hS.subset_connectedComponentIn hx₁ hSM hx₂)

theorem boundary_defect_forces_interior_vacuum_break
  {X D V : Type*} [TopologicalSpace X] [TopologicalSpace D] [TopologicalSpace V]
  (i : ContinuousMap X D) (d0 : D)
  (H : ContinuousMap.Homotopy (ContinuousMap.id D) (ContinuousMap.const D d0))
  (g : BoundaryField X V) (h_defect : has_topological_defect g) :
  ¬ ∃ (f : ContinuousMap D V), f.comp i = g := by
  intro ⟨f, h_ext⟩
  have h_trivial := contractible_interior_forces_trivial_boundary i f d0 H
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
