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

omit [TriangulatedManifold ↥X] in
/-- **A compatible family of local probability sections glues to a unique global
one.** No hypothesis here mentions phases, coupling or equilibrium: this is the
sheaf property of `probabilityPresheaf`, transported from `iSup cover` to `⊤`
along `h_cover`.

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
      ∀ i : I, (probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op g = s i := by
  have h_sheaf_gluing :=
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types (probabilityPresheaf X)).mp
      probability_is_sheaf
  have ⟨g, hg, h_uniq⟩ := h_sheaf_gluing cover s h_compat
  let e' : op (iSup cover) ⟶ op ⊤ := (eqToHom (by rw [h_cover])).op
  let g_top : GlobalSection (X := X) := (probabilityPresheaf X).map e' g
  use g_top
  constructor
  · intro i
    have H_map : (probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op g_top =
                 ((probabilityPresheaf X).map e' ≫
                   (probabilityPresheaf X).map (homOfLE (le_top : cover i ≤ ⊤)).op) g := rfl
    rw [H_map, ← (probabilityPresheaf X).map_comp]
    have H_eq : e' ≫ (homOfLE (le_top : cover i ≤ ⊤)).op = (Opens.leSupr cover i).op := by
      apply Subsingleton.elim
    rw [H_eq]
    exact hg i
  · intro g' hg'
    let e_inv : op ⊤ ⟶ op (iSup cover) := (eqToHom (by rw [h_cover.symm])).op
    have H_g'_eq : g' = ((probabilityPresheaf X).map e_inv ≫ (probabilityPresheaf X).map e') g' := by
      rw [← (probabilityPresheaf X).map_comp]
      have h_id : e_inv ≫ e' = 𝟙 _ := by apply Subsingleton.elim
      rw [h_id, (probabilityPresheaf X).map_id]
      rfl
    rw [H_g'_eq]
    have H_apply : (probabilityPresheaf X).map e_inv g' = g := by
      apply h_uniq
      intro i
      have H_map2 : (probabilityPresheaf X).map (Opens.leSupr cover i).op
            ((probabilityPresheaf X).map e_inv g') =
          ((probabilityPresheaf X).map e_inv ≫
            (probabilityPresheaf X).map (Opens.leSupr cover i).op) g' := rfl
      rw [H_map2, ← (probabilityPresheaf X).map_comp]
      have H_eq2 : e_inv ≫ (Opens.leSupr cover i).op = (homOfLE (le_top : cover i ≤ ⊤)).op := by
        apply Subsingleton.elim
      rw [H_eq2]
      exact hg' i
    change (probabilityPresheaf X).map e' ((probabilityPresheaf X).map e_inv g') =
      (probabilityPresheaf X).map e' g
    rw [H_apply]

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

end PhysicsOfConsciousness
