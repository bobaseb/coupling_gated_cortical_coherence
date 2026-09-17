import PhysicsOfConsciousness.Phase4_MacroscopicScaling
import PhysicsOfConsciousness.Phase1_MeasureGluing
import PhysicsOfConsciousness.Phase5_ContentDynamics
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

omit [TriangulatedManifold ↥X] in
theorem probability_is_sheaf : TopCat.Presheaf.IsSheaf (probabilityPresheaf X) :=
  (TopCat.Presheaf.sheafify (probabilityPresheaf_pre X)).property

noncomputable def GlobalSection := (probabilityPresheaf X).obj (op ⊤)

/-! ## The gluing lemma, with no physics in it

`probability_glue_unique` is the sheaf condition and nothing else: a family of
local probability sections that agrees on overlaps comes from exactly one
section over `⊤`. It is stated separately from `ThermodynamicCover` so that the
division of labour in Derivation 5 is visible in the source — this lemma
supplies the *mathematics*, and the class supplies the *hypothesis* that a
synchronised cover has an agreeing family (`section_agrees_of_phase_eq`).

Both halves matter, and it is worth being precise about which is which.
Existence of the common measure is a theorem about the presheaf: it is where
"the patches are locally consistent" turns into "there is one global object".
Uniqueness is what makes that object *the* state rather than a choice. Before
2026-08-30 only the second half was doing any work, because the class carried
the global object as a field.
-/

omit [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X] in
/-- **A compatible family of local sections of a sheaf glues to a unique global
one.** No hypothesis here mentions phases, coupling, equilibrium — or measures:
this is the sheaf property, transported from `iSup cover` to `⊤` along
`h_cover`.

It is stated for an arbitrary sheaf of types rather than for
`probabilityPresheaf` because Derivation 5 is not the only gluing this
development performs: `Phase5_TwistedGluing.lean` glues families that agree on
overlaps only up to a phase, over a presheaf of local states that carries the
phase. `probability_glue_unique` below is the instance Derivation 5 uses. -/
theorem sheaf_glue_unique {F : (Opens X)ᵒᵖ ⥤ Type u} (hF : TopCat.Presheaf.IsSheaf F)
    {I : Type u} (cover : I → Opens X)
    (h_cover : iSup cover = ⊤)
    (s : (i : I) → F.obj (op (cover i)))
    (h_compat : ∀ i j,
      F.map (homOfLE (inf_le_left : cover i ⊓ cover j ≤ cover i)).op (s i) =
      F.map (homOfLE (inf_le_right : cover i ⊓ cover j ≤ cover j)).op (s j)) :
    ∃! g : F.obj (op ⊤),
      ∀ i : I, F.map (homOfLE (le_top : cover i ≤ ⊤)).op g = s i := by
  have h_sheaf_gluing :=
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types F).mp hF
  have ⟨g, hg, h_uniq⟩ := h_sheaf_gluing cover s h_compat
  let e' : op (iSup cover) ⟶ op ⊤ := (eqToHom (by rw [h_cover])).op
  let g_top : F.obj (op ⊤) := F.map e' g
  use g_top
  constructor
  · intro i
    have H_map : F.map (homOfLE (le_top : cover i ≤ ⊤)).op g_top =
                 (F.map e' ≫
                   F.map (homOfLE (le_top : cover i ≤ ⊤)).op) g := rfl
    rw [H_map, ← F.map_comp]
    have H_eq : e' ≫ (homOfLE (le_top : cover i ≤ ⊤)).op = (Opens.leSupr cover i).op := by
      apply Subsingleton.elim
    rw [H_eq]
    exact hg i
  · intro g' hg'
    let e_inv : op ⊤ ⟶ op (iSup cover) := (eqToHom (by rw [h_cover.symm])).op
    have H_g'_eq : g' = (F.map e_inv ≫ F.map e') g' := by
      rw [← F.map_comp]
      have h_id : e_inv ≫ e' = 𝟙 _ := by apply Subsingleton.elim
      rw [h_id, F.map_id]
      rfl
    rw [H_g'_eq]
    have H_apply : F.map e_inv g' = g := by
      apply h_uniq
      intro i
      have H_map2 : F.map (Opens.leSupr cover i).op
            (F.map e_inv g') =
          (F.map e_inv ≫
            F.map (Opens.leSupr cover i).op) g' := rfl
      rw [H_map2, ← F.map_comp]
      have H_eq2 : e_inv ≫ (Opens.leSupr cover i).op = (homOfLE (le_top : cover i ≤ ⊤)).op := by
        apply Subsingleton.elim
      rw [H_eq2]
      exact hg' i
    change F.map e' (F.map e_inv g') =
      F.map e' g
    rw [H_apply]

omit [TriangulatedManifold ↥X] in
/-- **Derivation 5's gluing lemma**: a compatible family of local probability
sections comes from exactly one section over `⊤`.

What it does *not* establish: that any particular physical system produces a
compatible family. That is `LocalSectionSynchronization.section_agrees_of_phase_eq`,
which is an instance obligation. -/
theorem probability_glue_unique {I : Type u} (cover : I → Opens X)
    (h_cover : iSup cover = ⊤)
    (s : (i : I) → (probabilityPresheaf X).obj (op (cover i)))
    (h_compat : ∀ i j,
      (probabilityPresheaf X).map (homOfLE (inf_le_left : cover i ⊓ cover j ≤ cover i)).op (s i) =
      (probabilityPresheaf X).map (homOfLE (inf_le_right : cover i ⊓ cover j ≤ cover j)).op (s j)) :
    ∃! g : GlobalSection (X := X),
      ∀ i : I, (probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op g = s i :=
  sheaf_glue_unique probability_is_sheaf cover h_cover s h_compat

/--
Structure bundling a cover with a coupling matrix that has already reached
thermodynamic equilibrium.

**What the field asks, and how it can now be met.** `thermodynamic_equilibrium`
says the cover's phase configuration minimises the reduced Kuramoto potential.
It remains a *field* — an obligation each instance discharges — because that is
the standing rule for a postulate mentioning a class field, and because the
statement is false of arbitrary configurations. What has changed is that an
instance no longer has to assume it of a phase field that was built locked.
`ThermodynamicCover.ofConvergentTrajectory` (`Phase5_EquilibriumBridge.lean`)
discharges the field from `kuramoto_tendsto_global_minimum`: hand it a Kuramoto
trajectory whose initial data lies within a quarter turn and below the energy
threshold, and it builds a cover whose phase field is that trajectory's limit.
`Examples.lean` §17.1 is such a cover, on three sites, from initial data that is
not phase-locked and a trajectory with no closed form.

That was open item **O20**, and it is closed in the direction the item asked
about. Two things it does not cover. The hypotheses of the bridge are genuinely
restrictive — splay and twisted states are equilibria of the same flow, so no
theorem says every trajectory arrives — and the cover's *other* physical
hypothesis, `LocalSectionSynchronization.section_agrees_of_phase_eq`, is
untouched by any dynamics in this development.
-/
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

/-- **Every `ThermodynamicCover` sits at a phase-locked configuration.** This is
forced, not assumed: `thermodynamic_equilibrium` says the phase field minimises
the reduced Kuramoto potential, and the minimisers of that functional are
exactly the locked states.

It does *not* say the phase field is constant. `theta i` and `theta j` may
differ by any multiple of `2π`, and `Examples.lean` §13 exhibits an instance
where they do. What it says is that no instance can be at a configuration where
the phases differ in any way a measure is allowed to see. -/
theorem ThermodynamicCover.phase_locked (T : ThermodynamicCover X) :
    is_phase_locked T.phase := by
  let := T.I_fintype
  let := T.I_decidable
  exact potential_min_implies_phase_locked ⟨fun _ => 0, T.A, T.A_symm⟩ T.A_pos T.phase
    T.thermodynamic_equilibrium

/-- **Derivation 5.** A cover at thermodynamic equilibrium determines exactly one
global probability section, and that section restricts to the cover's local data.

The chain is: `thermodynamic_equilibrium` forces the phase field to be locked
(`ThermodynamicCover.phase_locked`); locking makes the family agree on overlaps
(`overlap_agreement`, from the instance obligation
`section_agrees_of_phase_eq`); an agreeing family glues uniquely
(`probability_glue_unique`).

**What carries physical content.** Two hypotheses, both instance obligations and
both flagged as such: that the cover is at the potential minimum, and that
synchronised patches agree on overlaps. Given those, existence and uniqueness of
the global section are mathematics.

The first of the two is no longer an assumption on every instance. A cover built
by `ThermodynamicCover.ofConvergentTrajectory` (`Phase5_EquilibriumBridge.lean`)
derives it from a dynamics that reaches the minimum, and `Examples.lean` §17.1
is such a cover. The second remains an assumption on every instance, here and
everywhere.

**What is no longer assumed.** Until 2026-08-30 the class carried the global
section as a field and declared the local sections to be its restrictions, so
this theorem could only rule out competitors to an object already supplied. It
now produces the object. See `ThermodynamicCover.sync_to_section_eq` for the old
field in its new status, and `Examples.lean` §14 for a cover where the glued
section is not any of the data the instance was built from. -/
theorem global_section_from_thermodynamics [T : ThermodynamicCover X] :
  ∃! s : GlobalSection (X := X), 
    ∀ i : T.I, (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op s = T.sync_to_section i :=
  probability_glue_unique T.cover T.is_cover T.sync_to_section
    (overlap_agreement (S := T.toLocalSectionSynchronization) fun i j => T.phase_locked i j)

/-! ## The invariant measure, as a conclusion

The three declarations below are the answer to open item **O19**, which asked
whether Derivation 5's gluing was an emergence theorem or merely a uniqueness
theorem. Under the class shape in force until 2026-08-30 it was the latter: the
field `phase_invariant_measure` handed every instance a global section, and
`sync_to_section_eq` declared the local data to be its restrictions.

Both fields are gone. `invariantMeasure` is *defined* as the section the sheaf
condition produces, and `sync_to_section_eq` — the old field, verbatim in
content — is now a theorem about it. Nothing in an instance mentions a global
object; the global object is what the theorem is for.

**What this does not fix.** The remaining hypotheses of Derivation 5 are
unchanged, and they are the physical ones: that the cover sits at the potential
minimum, and that synchronised patches agree where they overlap. The change made
here is to what follows from them, not to how much is assumed. (The first
hypothesis is separately addressed by `Phase5_EquilibriumBridge.lean`, which
derives it on a class of initial data; that is a different change, made later,
and it leaves the second exactly where it is.)
-/

open scoped Classical in
/-- **The invariant measure of a cover at equilibrium**: the unique global
probability section its patches glue to.

Derived, not carried. This is the declaration that used to be a class field. -/
noncomputable def ThermodynamicCover.invariantMeasure (T : ThermodynamicCover X) :
    GlobalSection (X := X) :=
  (@global_section_from_thermodynamics X _ _ _ T).choose

/-- **The old class field, now a theorem.** Every local section of a cover at
equilibrium *is* the restriction of one global measure — the cover's
`invariantMeasure`.

This is the exact statement `sync_to_section_eq` used to assume. Its content is
unchanged and its status is not: it is a consequence of the local agreement
condition and the sheaf property, and the measure it names is constructed rather
than supplied. -/
theorem ThermodynamicCover.sync_to_section_eq (T : ThermodynamicCover X) (i : T.I) :
    T.sync_to_section i =
      (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op T.invariantMeasure :=
  ((@global_section_from_thermodynamics X _ _ _ T).choose_spec.1 i).symm

/-- The invariant measure is the *only* global section restricting to the cover's
local data — the uniqueness half of Derivation 5, stated on the constructed
object. -/
theorem ThermodynamicCover.invariantMeasure_unique (T : ThermodynamicCover X)
    (s : GlobalSection (X := X))
    (hs : ∀ i : T.I, (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op s
      = T.sync_to_section i) :
    s = T.invariantMeasure :=
  (@global_section_from_thermodynamics X _ _ _ T).choose_spec.2 s hs

section MeasureRepresentation

open Set

omit [TriangulatedManifold ↥X]

/-- Restrict an actual finite spatial measure to an open subset, without
renormalizing its mass. -/
noncomputable def measureOnOpen (μ : FiniteMeasure X) (U : Opens X) : FiniteMeasure U :=
  FiniteMeasure.comap Subtype.val μ

/-- Every local finite measure can be extended by zero to the ambient space
and recovered on its patch. Ambient representatives add no outside-patch data
requirement to finite-measure gluing. -/
theorem measureOnOpen_map_subtype (U : Opens X) (μ : FiniteMeasure U) :
    measureOnOpen (μ.map (Subtype.val : U → X)) U = μ := by
  apply FiniteMeasure.toMeasure_injective
  exact (MeasurableEmbedding.subtype_coe U.isOpen.measurableSet).comap_map (μ : Measure U)

/-- The global sheaf section represented by a finite measure. This map alone
asserts neither surjectivity onto all sections nor mass-one normalization. -/
noncomputable def globalSectionOfMeasure (μ : FiniteMeasure X) : GlobalSection (X := X) :=
  (TopCat.Presheaf.toSheafify (probabilityPresheaf_pre X)).app (op ⊤)
    (measureOnOpen μ ⊤)

/-- Restriction of measures agrees with the original presheaf's restriction. -/
theorem measureOnOpen_restrict (μ : FiniteMeasure X) {U V : Opens X} (h : V ≤ U) :
    (probabilityPresheaf_pre X).map (homOfLE h).op (measureOnOpen μ U) =
      measureOnOpen μ V := by
  apply FiniteMeasure.toMeasure_injective
  change ((μ : Measure X).comap (Subtype.val : U → X)).comap
    (fun x : V => (⟨x.val, h x.property⟩ : U)) = (μ : Measure X).comap Subtype.val
  exact Measure.comap_comap (inc_is_measurable_embedding X h).measurableSet_image'
    Subtype.val_injective (MeasurableEmbedding.subtype_coe U.isOpen.measurableSet).measurableSet_image' (μ : Measure X)

/-- Sheafification preserves the restrictions of an actual finite measure. -/
theorem globalSectionOfMeasure_restrict (μ : FiniteMeasure X) (U : Opens X) :
    (probabilityPresheaf X).map (homOfLE (le_top : U ≤ ⊤)).op (globalSectionOfMeasure μ) =
      (TopCat.Presheaf.toSheafify (probabilityPresheaf_pre X)).app (op U) (measureOnOpen μ U) := by
  have h := congrArg (fun f => f (measureOnOpen μ ⊤))
    ((TopCat.Presheaf.toSheafify (probabilityPresheaf_pre X)).naturality
      (homOfLE (le_top : U ≤ ⊤)).op)
  change _ = (probabilityPresheaf X).map (homOfLE (le_top : U ≤ ⊤)).op
    (globalSectionOfMeasure μ) at h
  exact h.symm.trans (congrArg (fun m : FiniteMeasure U =>
    (TopCat.Presheaf.toSheafify (probabilityPresheaf_pre X)).app (op U) m)
    (measureOnOpen_restrict μ (le_top : U ≤ ⊤)))

/-- Equality as restricted measures suffices for equality of patch measures.
No converse from equality of sheaf germs is used. -/
theorem measureOnOpen_eq_of_restrict_eq {μ ν : FiniteMeasure X} (U : Opens X)
    (h : (μ : Measure X).restrict U = (ν : Measure X).restrict U) :
    measureOnOpen μ U = measureOnOpen ν U := by
  apply FiniteMeasure.toMeasure_injective
  have he : MeasurableEmbedding (Subtype.val : U → X) := MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hpre : (Subtype.val : U → X) ⁻¹' (U : Set X) = univ := by
    ext x
    simp
  have h' := congrArg (fun m : Measure X => m.comap (Subtype.val : U → X)) h
  simpa only [he.comap_restrict, hpre, Measure.restrict_univ, measureOnOpen, FiniteMeasure.toMeasure_comap] using h'

/-- A thermodynamic cover with compatible finite-measure representatives glues
to the sheaf image of an actual finite measure. Its raw measure restrictions
uniquely determine that measure by `SpatialMeasure.finite_glue_unique`.

The finite family is already supplied by the cover. The hypotheses additionally
supply local finite-measure representatives and their agreement as measures;
this is not a representation theorem for arbitrary sections on arbitrary spaces.
The representative measures' values outside their respective patches are unused,
so local measures extended by zero provide the same data. No global measure,
normalization, or biological interpretation is assumed. -/
theorem ThermodynamicCover.existsUnique_measure_representation
    [TriangulatedManifold X] (T : ThermodynamicCover X)
    (μ : T.I → FiniteMeasure X)
    (hcompat : ∀ i j, (μ i : Measure X).restrict (T.cover i ∩ T.cover j) =
      (μ j : Measure X).restrict (T.cover i ∩ T.cover j))
    (hlocal : ∀ i, T.sync_to_section i =
      (probabilityPresheaf X).map (homOfLE (le_top : T.cover i ≤ ⊤)).op
        (globalSectionOfMeasure (μ i))) :
    ∃! ν : FiniteMeasure X,
      (∀ i, (ν : Measure X).restrict (T.cover i) =
        (μ i : Measure X).restrict (T.cover i)) ∧
      globalSectionOfMeasure ν = T.invariantMeasure := by
  let := T.I_fintype
  have hcover : ⋃ i, (T.cover i : Set X) = univ := by
    simpa only [Opens.coe_iSup, Opens.coe_top] using
      congrArg (fun U : Opens X => (U : Set X)) T.is_cover
  obtain ⟨ν, hν, huniq⟩ := SpatialMeasure.finite_glue_unique
    (fun i => (T.cover i : Set X)) (fun i => (T.cover i).isOpen.measurableSet)
    hcover μ hcompat
  refine ⟨ν, ⟨hν, T.invariantMeasure_unique _ ?_⟩, fun ξ hξ => huniq ξ hξ.1⟩
  intro i
  rw [hlocal i, globalSectionOfMeasure_restrict, globalSectionOfMeasure_restrict,
    measureOnOpen_eq_of_restrict_eq (T.cover i) (hν i)]

#print axioms ThermodynamicCover.existsUnique_measure_representation

end MeasureRepresentation

/-! ## Approximate gluing by selection on a finite spatial substrate

This is Route A of L4: local finite measures are represented by their nonnegative
site masses, with the uniform metric on restrictions. Nonnegative subordinate
weights summing to one select a profile. The selection is not an exact extension
of inconsistent data, and the sheaf theorem above retains exact compatibility.

The constant is `C(N) = 1` for every cover multiplicity `N`, stronger than an
`N * ε` estimate: convex weights sum to one rather than to the number of active
patches. This is a statement in the uniform mass metric, not total variation or
an arbitrary sheaf metric. `Examples/Phase5.lean` realizes these profiles as
actual probability-sheaf sections via the existing three-site mass dictionary.
-/

namespace ApproximateGluing

open scoped NNReal

section FiniteProfiles

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- Uniform distance between the restrictions to `U`. It is the metric on
`U → ℝ≥0`, pulled back to ambient profiles; off-`U` values are ignored. -/
noncomputable def profileDist (U : Set α) (f g : α → ℝ≥0) : ℝ :=
  letI := Fintype.ofFinite U
  dist (fun x : U => f x) (fun x : U => g x)

theorem profileDist_le_iff {U : Set α} {f g : α → ℝ≥0} {ε : ℝ}
    (hε : 0 ≤ ε) :
    profileDist U f g ≤ ε ↔ ∀ x ∈ U, dist (f x) (g x) ≤ ε := by
  let := Fintype.ofFinite U
  exact (dist_pi_le_iff hε).trans Subtype.forall

/-- All overlaps of the same supplied family are within the declared tolerance.
On a finite discrete substrate these are local finite measures. This predicate
supplies no process producing their approximate agreement. -/
def Compatible (U : ι → Set α) (s : ι → α → ℝ≥0) (ε : ℝ≥0) : Prop :=
  ∀ i j, profileDist (U i ∩ U j) (s i) (s j) ≤ ε

omit [Fintype ι] in
/-- **The two agreement predicates are one predicate.** `profileDist` on an
overlap bounds exactly the pointwise distances across it, so a compatible family
of mass profiles is a compatible family of signed contents in the sense of
`Phase5_ContentDynamics`, at the same tolerance. The observation dynamics of
that module therefore acts on the families these theorems accept. It produces no
agreement: the hypothesis is still supplied. -/
theorem compatible_pointwise {U : ι → Set α} {s : ι → α → ℝ≥0} {ε : ℝ≥0}
    (h : Compatible U s ε) :
    LocalContent.Compatible U (fun i x => (s i x : ℝ)) ε := by
  intro i j x hi hj
  have hx := (profileDist_le_iff ε.coe_nonneg).1 (h i j) x ⟨hi, hj⟩
  simpa [NNReal.dist_eq] using hx

/-- A nonnegative partition of unity subordinate to the finite cover. Data stay
bare; support and normalization are properties, not assumed error bounds. No
smooth partition on a continuous substrate is constructed here. -/
def IsPartition (U : ι → Set α) (w : ι → α → ℝ≥0) : Prop :=
  (∀ i x, x ∉ U i → w i x = 0) ∧ ∀ x, ∑ i, w i x = 1

/-- Pointwise weighted selection. Nonnegative site masses represent a finite
measure on the finite discrete substrate; total mass need not be one. -/
noncomputable def select (w s : ι → α → ℝ≥0) : α → ℝ≥0 :=
  fun x => ∑ i, w i x * s i x

omit [Fintype α] in
/-- Normalized subordinate weights imply coverage. They do not choose which
cover or weights are physically appropriate. -/
theorem IsPartition.covers {U : ι → Set α} {w : ι → α → ℝ≥0}
    (hw : IsPartition U w) (x : α) : ∃ i, x ∈ U i := by
  by_contra h
  have hz : ∑ i, w i x = 0 := Finset.sum_eq_zero fun i _ =>
    hw.1 i x (fun hx => h ⟨i, hx⟩)
  rw [hw.2 x] at hz
  exact one_ne_zero hz

omit [Fintype α] in
/-- Off-patch extensions cannot influence a subordinate selection. This is the
locality check needed when patch profiles are stored as ambient functions. -/
theorem select_eq_of_eqOn {U : ι → Set α} {w s t : ι → α → ℝ≥0}
    (hw : IsPartition U w) (hst : ∀ i, Set.EqOn (s i) (t i) (U i)) :
    select w s = select w t := by
  classical
  funext x
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ U i
  · rw [hst i hx]
  · rw [hw.1 i x hx, zero_mul, zero_mul]

private theorem weighted_dist_le (w a : ι → ℝ≥0) (c ε : ℝ≥0)
    (hw : ∑ i, w i = 1) (ha : ∀ i, w i ≠ 0 → dist (a i) c ≤ ε) :
    dist (∑ i, w i * a i) c ≤ ε := by
  have hw' : ∑ i, (w i : ℝ) = 1 := by exact_mod_cast hw
  have hc : (c : ℝ) = ∑ i, (w i : ℝ) * c := by
    rw [← Finset.sum_mul, hw', one_mul]
  change |(↑(∑ i, w i * a i) : ℝ) - c| ≤ ε
  simp only [NNReal.coe_sum, NNReal.coe_mul]
  rw [hc, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(w i : ℝ) * a i - (w i : ℝ) * c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (w i : ℝ) * ε := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : w i = 0
      · simp [hi]
      · rw [← mul_sub, abs_mul, abs_of_nonneg (w i).coe_nonneg]
        exact mul_le_mul_of_nonneg_left (ha i hi) (w i).coe_nonneg
    _ = ε := by rw [← Finset.sum_mul, hw', one_mul]

/-- A partition selects a profile within `ε` of every patch on that patch.
The modulus comes from convexity and the uniform overlap metric. It establishes
approximation, not exact extension, and assumes all pairs are checked. -/
theorem select_close {U : ι → Set α} {w s : ι → α → ℝ≥0} {ε : ℝ≥0}
    (hw : IsPartition U w) (hs : Compatible U s ε) (i : ι) :
    profileDist (U i) (select w s) (s i) ≤ ε := by
  apply (profileDist_le_iff ε.coe_nonneg).2
  intro x hx
  apply weighted_dist_le (fun j => w j x) (fun j => s j x) (s i x) ε (hw.2 x)
  intro j hj
  have hxj : x ∈ U j := by
    by_contra h
    exact hj (hw.1 j x h)
  exact (profileDist_le_iff ε.coe_nonneg).1 (hs j i) x ⟨hxj, hx⟩

/-- **Selection replaces uniqueness with a sharp `ε` diameter.** Any two
subordinate partitions select profiles at uniform distance at most `ε`:
`C(N) = 1` independently of cover multiplicity. Normalization is essential to
this estimate. It does not bound arbitrary approximate sections unless their
fitting tolerance is also specified, or justify a content interpretation. -/
theorem select_dist_le {U : ι → Set α} {w v s : ι → α → ℝ≥0} {ε : ℝ≥0}
    (hw : IsPartition U w) (hv : IsPartition U v) (hs : Compatible U s ε) :
    dist (select w s) (select v s) ≤ ε := by
  apply (dist_pi_le_iff ε.coe_nonneg).2
  intro x
  rw [dist_comm]
  apply weighted_dist_le (fun i => v i x) (fun i => s i x) (select w s x) ε (hv.2 x)
  intro i hi
  have hx : x ∈ U i := by
    by_contra h
    exact hi (hv.1 i x h)
  rw [dist_comm]
  exact (profileDist_le_iff ε.coe_nonneg).1 (select_close hw hs i) x hx

omit [Fintype ι] in
/-- **Arbitrary fits have diameter `2δ`** in the uniform metric when each fits
every patch to tolerance `δ` and the patches cover. Pairwise compatibility alone
specifies neither those candidates nor their fitting tolerance. -/
theorem approximate_diameter_le {U : ι → Set α} {s : ι → α → ℝ≥0}
    {g h : α → ℝ≥0} {δ : ℝ≥0} (hc : ∀ x, ∃ i, x ∈ U i)
    (hg : ∀ i, profileDist (U i) g (s i) ≤ δ)
    (hh : ∀ i, profileDist (U i) h (s i) ≤ δ) :
    dist g h ≤ 2 * (δ : ℝ) := by
  apply (dist_pi_le_iff (by positivity)).2
  intro x
  obtain ⟨i, hi⟩ := hc x
  have hgx := (profileDist_le_iff δ.coe_nonneg).1 (hg i) x hi
  have hhx := (profileDist_le_iff δ.coe_nonneg).1 (hh i) x hi
  calc
    dist (g x) (h x) ≤ dist (g x) (s i x) + dist (h x) (s i x) :=
      dist_triangle_right _ _ _
    _ ≤ 2 * (δ : ℝ) := by linarith

/-- Zero overlap error recovers exact, unique gluing of finite mass profiles.
For positive error, the same conclusion is false even on the three-site cortex;
this does not relax the exact hypothesis of `sheaf_glue_unique`. -/
theorem select_glue_unique {U : ι → Set α} {w s : ι → α → ℝ≥0}
    (hw : IsPartition U w) (hs : Compatible U s 0) :
    ∃! g : α → ℝ≥0, ∀ i, Set.EqOn g (s i) (U i) := by
  have hfit : ∀ i, profileDist (U i) (select w s) (s i) ≤ (0 : ℝ≥0) :=
    select_close hw hs
  refine ⟨select w s, ?_, ?_⟩
  · intro i x hx
    exact dist_le_zero.mp ((profileDist_le_iff (by norm_num)).1 (hfit i) x hx)
  · intro g hg
    apply dist_le_zero.mp
    have hgfit : ∀ i, profileDist (U i) g (s i) ≤ (0 : ℝ≥0) := by
      intro i
      apply (profileDist_le_iff (by norm_num)).2
      intro x hx
      simp [hg i hx]
    simpa using approximate_diameter_le hw.covers hgfit hfit

/-- A supplied `L`-Lipschitz feature varies by at most `Lε` across selections.
An interpretation at resolution `δ` must additionally justify its decoder and
`Lε ≤ δ`; this theorem neither chooses content nor equates nearby experiences. -/
theorem feature_dist_le {U : ι → Set α} {w v s : ι → α → ℝ≥0} {ε : ℝ≥0}
    {Y : Type*} [PseudoMetricSpace Y] {L : ℝ≥0} {F : (α → ℝ≥0) → Y}
    (hF : LipschitzWith L F) (hw : IsPartition U w) (hv : IsPartition U v)
    (hs : Compatible U s ε) :
    dist (F (select w s)) (F (select v s)) ≤ (L : ℝ) * ε :=
  (hF.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (select_dist_le hw hv hs) L.coe_nonneg)

end FiniteProfiles

end ApproximateGluing

end PhysicsOfConsciousness
