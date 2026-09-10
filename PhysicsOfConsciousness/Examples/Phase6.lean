/-
  Examples/Phase6.lean — the reflexive boundary: the Self as a non-trivial attractor

  §10, on the three-site cortex of `Examples/Cortex.lean`. It first pierces the
  sheafification — `massEquivOn` proves that over any open of the cortex the
  sections of the probability sheaf are exactly the mass profiles on that open,
  read as densities against counting measure — and then builds the metric from
  those measures rather than from nothing. The self-prediction map goes through
  the one-site avatar, so it contracts by exactly half of what the avatar sees
  without being constant, with a unique fixed point, and its contraction
  constant is read off `K` and `D` rather than stipulated.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Phase6_ReflexiveTopology
import PhysicsOfConsciousness.Phase8_ContinuousField
import PhysicsOfConsciousness.Examples.Cortex

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 10. The reflexive boundary: the Self as a non-trivial attractor

`reflexive_topology_implies_self` (Derivation 6, the Self) is the Banach fixed-point
theorem with every physical commitment pushed into a hypothesis: `GlobalSection X` is
*assumed* to be a nonempty complete metric space, and `predict` is *assumed* to contract.
`GlobalSection` is defined as the sections over `⊤` of a
sheafification — a subtype of families of germs — so nothing about it is a measure until
that layer is pierced, and an earlier pass discharged the metric hypothesis with the 0/1
metric. That witness was honest but empty: `contracting_implies_const` (kept below) proves
that under the 0/1 metric *every* `ContractingWith K` map with `K < 1` is constant, so on
that model the Self was the constant section.

This section replaces it. The work is in four stages.

* **The germ–measure dictionary.** On this discrete substrate every point has a smallest
  open neighbourhood, so "mass carried at `x`" is a well-defined map out of the stalk at
  `x` (`stalkMass`, built as `colimit.desc` of `massCocone`; the cocone law is exactly
  that restriction preserves the mass at a point). Reading a section's germ at each site of
  an open `U` gives `densityOn`, and `massEquivOn U` proves this a **bijection** onto the
  mass profiles on `U`: injective because a germ on a discrete space is determined by its
  restriction to the point (`stalkMass_injective`), surjective because any prescribed
  profile is realized by a finite measure (`massMeasureOn`, `sectionOfMassOn`). Sections of
  the probability sheaf over `U` *are* the finite measures on `U`, read as densities against
  counting measure; `density`, `massMeasure`, `sectionOfMass` and `massEquiv` are the case
  `U = ⊤`, kept under their own names because there the profile is indexed by `Site`
  outright. Nothing in Mathlib supplied this: `TopCat.Presheaf.sheafify` has no adjunction
  and no `isIso_toSheafify`, so the inverse had to be constructed. Until 2026-08-30 only
  the `⊤` case existed, which is what forced §14 to write its patch-local sections as
  restrictions of global measures (open item **O21**).
* **The metric.** `gsMetric` transports the metric of `Site → ℝ≥0` along `density`: the
  distance between two sections is the largest difference of the masses their measures put
  on a site: the uniform distance between their densities. (On a finite substrate that is
  equivalent to the total-variation distance of the measures, within a factor of the number
  of sites, but it is not equal to it — total variation sums the differences where this
  takes their maximum. Nothing below uses the comparison.) It is complete
  (`gsComplete`, via surjectivity of `density`, not via "Cauchy sequences are eventually
  constant"), and `exists_dist_lt_one` exhibits distinct sections at distance `1/2`, which
  is exactly the hypothesis `contracting_implies_const` needs and no longer has.
* **The Self, through the avatar** (rebuilt 2026-08-31 for work item W5). The
  self-prediction map is no longer written down beside the boundary: `avatarRead` is the
  single number a section over the avatar region carries, `avatarReadout` turns it into a
  global state, and `cortexReflexive.predict` is their composite by definition. So the
  dynamics reads the avatar or it does not exist. `cortexPredict_dist` gives the exact
  contraction factor — one half *of what the avatar sees*, the loss off the avatar region
  being the fold, stated rather than hidden; `cortexPredict_not_const` that it is not
  constant; `cortexPredict_fixed` and `cortexPredict_fixed_unique` name the fixed point and
  prove it the only one, Banach uniqueness re-derived by hand. The previous witness
  `relax s = ½ s + ½ baseline` (removed 2026-08-31; the W5 pass note in `tasks/todo.md`
  records it) cannot be used here: it reads every site, so it does not factor through a
  one-site avatar, which is exactly the defect W5 names.
* **The rate, from `K` and `D`.** `cortexTau`, `cortexSupercritical` and
  `cortexResonanceRate` place the witness at `K = 3`, `D = 1`, `τ = 2 log 2`, where
  `resonanceRate 3 1 τ` is exactly the `1/2` the read-out achieves, and `cortexHasSelf`
  is obtained from `self_of_supercritical` — from `K > critical_coupling 1 = 2` rather
  than from a numeral in the hypothesis. `cortexSubcritical_not_contracting` is the other
  half: the *same* map at `K = 1` has no Banach argument at all.
* **The avatar** (added 2026-08-30 for open item O2). `cortexReflexive_resonant`
  discharges `ReflexiveBoundary.IsRestrictionResonance`, and `cortexReflexive_restrict_ne`
  checks it is not empty here — the avatar region separates two of the substrate's states.
  `cortexState_eq_readout_restrict` is what the fixed-point equation now says: the Self is
  its own avatar reading, extended. `siteReflexive` is one avatar per site; their regions
  cover, so `cortex_eq_of_avatar_eq` reconstructs the global state from the local readings
  alone. `cortexBlind` is the same boundary with a constant avatar: still a legal
  `ReflexiveBoundary`, but no longer with the same Self — `cortexBlind_self_ne` proves
  `cortexState` is *not* a fixed point of the blinded map, and
  `cortexBlind_existsUnique_self` names the one it does have, a state stipulated in advance
  of the field. `cortexBlind_not_determined` exhibits two distinct states it cannot tell
  apart.

**What this still does not establish.** `avatarReadout` is a modelling choice: nothing in
the development derives it from field dynamics, and the identification of this substrate's
coupling with `K = 3` is a choice of units for the witness rather than a measurement — what
W5 removed is the *stipulation of the rate*, not the stipulation of the map. The
Lévy–Prokhorov
metric named in the header of `Phase6_ReflexiveTopology.lean` is *not* what is constructed
here, and the substitution is not cosmetic: on this substrate `μ ↦ ½μ + ½μ₀` is **not** a
Lévy–Prokhorov contraction (two measures of mass 5 sitting at different sites stay at
Lévy–Prokhorov distance 1 under it, because the thickening of a set by `ε < 1` is the set
itself), and Mathlib has no completeness result for that metric to build on. The uniform
distance between densities is what this substrate actually supports; it and Lévy–Prokhorov
agree on small scales and differ in the large, and no claim about their equivalence is made
or used here.
-/

section ReflexiveSelf

open CategoryTheory.Limits
open scoped NNReal

/-! ### The germ–measure dictionary -/

/-- The probability presheaf on the cortex, before sheafification, with its type spelled
out so that the presheaf API is available by dot notation. -/
noncomputable abbrev Fpre : TopCat.Presheaf (Type) Cortex := probabilityPresheaf_pre Cortex

/-- Presheaf restriction, with the types spelled out. -/
noncomputable def res {U V : Opens ↥Cortex} (hle : V ≤ U) (μ : FiniteMeasure ↥U) :
    FiniteMeasure ↥V := Fpre.map (homOfLE hle).op μ

/-- Restricting a finite measure along an inclusion of opens preserves the mass carried by
a point of the smaller open. This is the whole content of the dictionary below. -/
lemma restrict_singleton_mass {U V : Opens ↥Cortex} (hle : V ≤ U) (x : Site) (hxV : x ∈ V)
    (μ : FiniteMeasure ↥U) :
    (res hle μ) {(⟨x, hxV⟩ : ↥V)} = μ {(⟨x, hle hxV⟩ : ↥U)} := by
  rw [res]
  have hemb := inc_is_measurable_embedding Cortex hle
  show ⇑(FiniteMeasure.comap (fun y : ↥V => (⟨y.val, hle y.property⟩ : ↥U)) μ) {(⟨x, hxV⟩ : ↥V)}
      = ⇑μ {(⟨x, hle hxV⟩ : ↥U)}
  rw [FiniteMeasure.coeFn_def, FiniteMeasure.coeFn_def]
  simp only [FiniteMeasure.toMeasure_comap]
  rw [hemb.comap_apply]
  congr 2
  rw [Set.image_singleton]

/-- The mass a local finite measure puts on one point of its domain. -/
noncomputable def massAt (V : Opens ↥Cortex) (x : Site) (hx : x ∈ V) (μ : FiniteMeasure ↥V) :
    ℝ≥0 := μ {(⟨x, hx⟩ : ↥V)}

lemma massAt_res {U V : Opens ↥Cortex} (hle : V ≤ U) (x : Site) (hxV : x ∈ V)
    (μ : FiniteMeasure ↥U) : massAt V x hxV (res hle μ) = massAt U x (hle hxV) μ :=
  restrict_singleton_mass hle x hxV μ

/-- The cocone over the neighbourhood diagram at `x` given by "mass carried at `x`".
`massAt_res` is exactly the cocone law. -/
noncomputable def massCocone (x : ↥Cortex) : Cocone ((OpenNhds.inclusion x).op ⋙ Fpre) where
  pt := ℝ≥0
  ι :=
  { app := fun V => ↾(fun (μ : FiniteMeasure ↥(V.unop.1)) => massAt V.unop.1 x V.unop.2 μ)
    naturality := by
      intro U V i
      ext μ
      have hle : V.unop.1 ≤ U.unop.1 := leOfHom ((OpenNhds.inclusion x).map i.unop)
      have hmap : (OpenNhds.inclusion x).op.map i = (homOfLE hle).op := Subsingleton.elim _ _
      have key : (((OpenNhds.inclusion x).op ⋙ Fpre).map i μ : FiniteMeasure ↥(V.unop.1))
          = res hle μ := by
        rw [Functor.comp_map, hmap]; rfl
      show massAt V.unop.1 x V.unop.2 (((OpenNhds.inclusion x).op ⋙ Fpre).map i μ)
        = massAt U.unop.1 x U.unop.2 μ
      rw [key]
      exact massAt_res hle x V.unop.2 μ }

/-- The mass a germ at `x` carries at `x`. This is the map out of the stalk that the
sheafification hides; it exists because restriction preserves point masses. -/
noncomputable def stalkMass (x : ↥Cortex) : Fpre.stalk x → ℝ≥0 :=
  colimit.desc _ (massCocone x)

lemma stalkMass_germ (V : Opens ↥Cortex) (x : Site) (hx : x ∈ V) (μ : FiniteMeasure ↥V) :
    stalkMass x (Fpre.germ V x hx μ) = massAt V x hx μ :=
  ConcreteCategory.congr_hom (colimit.ι_desc (massCocone x) (op ⟨V, hx⟩)) μ

/-- The singleton open around a site — the smallest neighbourhood, which exists because the
topology is discrete. Every germ is represented on it. -/
def sing (x : Site) : Opens ↥Cortex := ⟨{x}, isOpen_discrete _⟩

theorem memSing (x : Site) : x ∈ sing x := rfl

theorem sing_le {x : Site} {U : Opens ↥Cortex} (hx : x ∈ U) : sing x ≤ U := by
  intro y hy
  have : y = x := hy
  subst this
  exact hx

instance singSubsingleton (x : Site) : Subsingleton ↥(sing x) :=
  ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩

/-- A finite measure on a one-point open is determined by the mass it puts on that point. -/
lemma sing_measure_ext (x : Site) (m m' : FiniteMeasure ↥(sing x))
    (h : massAt (sing x) x (memSing x) m = massAt (sing x) x (memSing x) m') : m = m' := by
  refine FiniteMeasure.eq_of_forall_apply_eq _ _ ?_
  intro s _
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
  · simp [FiniteMeasure.coeFn_def]
  · have hs : s = {(⟨x, memSing x⟩ : ↥(sing x))} := by
      ext b
      simp only [Set.mem_singleton_iff]
      refine ⟨fun _ => Subsingleton.elim b _, fun _ => ?_⟩
      have : a = b := Subsingleton.elim a b
      exact this ▸ ha
    rw [hs]
    exact h

/-- Germs on a discrete space are determined by the mass they carry: restrict a
representative to the smallest neighbourhood, where a finite measure is one number. -/
lemma stalkMass_injective (x : Site) : Function.Injective (stalkMass x) := by
  intro a b hab
  obtain ⟨U, hU, μ, rfl⟩ := Fpre.exists_germ_eq a
  obtain ⟨V, hV, ν, rfl⟩ := Fpre.exists_germ_eq b
  have eU := Fpre.germ_res_apply (homOfLE (sing_le hU)) x (memSing x) μ
  have eV := Fpre.germ_res_apply (homOfLE (sing_le hV)) x (memSing x) ν
  have hab' : massAt U x hU μ = massAt V x hV ν :=
    (stalkMass_germ U x hU μ).symm.trans (hab.trans (stalkMass_germ V x hV ν))
  rw [← eU, ← eV]
  congr 1
  refine sing_measure_ext x _ _ ?_
  exact (massAt_res (sing_le hU) x (memSing x) μ).trans
    (hab'.trans (massAt_res (sing_le hV) x (memSing x) ν).symm)

theorem memTop (x : Site) : x ∈ (⊤ : Opens ↥Cortex) := trivial

/-- The **density** of a section over an arbitrary open, read at a site that open contains:
the mass its germ carries there.

Stated at an arbitrary `U` because `stalkMass` is: nothing in the dictionary needs the
section to be global. Until 2026-08-30 the construction half below was built at `⊤` only,
which forced `Examples.lean` §14 to write its patch-local sections as restrictions of
global measures; that was open item **O21**. -/
noncomputable def densityOn {U : Opens ↥Cortex} (s : (probabilityPresheaf Cortex).obj (op U))
    (x : Site) (hx : x ∈ U) : ℝ≥0 := stalkMass x (s.1 ⟨x, hx⟩)

/-- The density of a **global** section, as a function of the site alone: `densityOn` at
`⊤`, where the membership proof carries no information. -/
noncomputable def density (s : GlobalSection (X := Cortex)) : Site → ℝ≥0 :=
  fun x => densityOn s x (memTop x)

/-- **Restriction moves no mass**, at any pair of opens. True by `rfl`: restriction in the
sheafification is restriction of the germ family, so the germ at a point of the smaller
open is unchanged. -/
theorem densityOn_res {U V : Opens ↥Cortex} (hVU : V ≤ U)
    (s : (probabilityPresheaf Cortex).obj (op U)) (x : Site) (hx : x ∈ V) :
    densityOn ((probabilityPresheaf Cortex).map (homOfLE hVU).op s) x hx
      = densityOn s x (hVU hx) := rfl

/-- The case of `densityOn_res` where the larger open is `⊤`, stated against `density`. -/
theorem densityOn_restrict {U : Opens ↥Cortex} (hU : U ≤ ⊤)
    (s : GlobalSection (X := Cortex)) (x : Site) (hx : x ∈ U) :
    densityOn ((probabilityPresheaf Cortex).map (homOfLE hU).op s) x hx = density s x := rfl

/-- **A section over an open is determined by its density on that open.** The injectivity
half of the dictionary, at an arbitrary `U`: a germ on a discrete space is recovered from
the mass it carries (`stalkMass_injective`), and a section is its family of germs. -/
theorem densityOn_injective {U : Opens ↥Cortex}
    {s t : (probabilityPresheaf Cortex).obj (op U)}
    (h : ∀ x (hx : x ∈ U), densityOn s x hx = densityOn t x hx) : s = t := by
  apply Subtype.ext
  funext y
  exact stalkMass_injective y.1 (h y.1 y.2)

/-- The density of a section glued from an honest local measure is that measure's mass
function. This is the bridge between the sheafified world and the measure world, at an
arbitrary open. -/
lemma densityOn_sheafify {U : Opens ↥Cortex} (μ : FiniteMeasure ↥U) (x : Site) (hx : x ∈ U) :
    densityOn ((TopCat.Presheaf.toSheafify Fpre).app (op U) μ) x hx = massAt U x hx μ :=
  stalkMass_germ U x hx μ

lemma Phi_sheafify (μ : FiniteMeasure ↥(⊤ : Opens ↥Cortex)) (x : Site) :
    density ((TopCat.Presheaf.toSheafify Fpre).app (op ⊤) μ) x
      = μ {(⟨x, memTop x⟩ : ↥(⊤ : Opens ↥Cortex))} :=
  densityOn_sheafify μ x (memTop x)

lemma Phi_injective : Function.Injective density :=
  fun _ _ h => densityOn_injective fun x _ => congrFun h x

instance : Nonempty Site := ⟨Site.mid⟩

instance : MeasurableSingletonClass Site := ⟨fun x => (isOpen_discrete {x}).measurableSet⟩

noncomputable instance opensFintype (U : Opens ↥Cortex) : Fintype ↥U := Fintype.ofFinite _

instance opensSingleton (U : Opens ↥Cortex) : MeasurableSingletonClass ↥U :=
  ⟨fun z => by
    have h : MeasurableSet ((Subtype.val : ↥U → Site) ⁻¹' {z.1}) :=
      measurable_subtype_coe (measurableSet_singleton z.1)
    have himg : (Subtype.val : ↥U → Site) ⁻¹' {z.1} = {z} := by
      ext b
      exact ⟨fun hb => Subtype.ext hb, fun hb => congrArg Subtype.val hb⟩
    rwa [himg] at h⟩

/-- The unit point mass at a point of an open, as a finite measure on that open. -/
noncomputable def diracFM {U : Opens ↥Cortex} (y : ↥U) : FiniteMeasure ↥U :=
  ⟨Measure.dirac y, inferInstance⟩

/-- The finite measure on an open with prescribed mass at each of its sites. The profile is
given on all of `Site`; what it says off `U` is invisible, which is what lets a patch be
handed a profile defined everywhere without thereby carrying global data. -/
noncomputable def massMeasureOn (U : Opens ↥Cortex) (w : Site → ℝ≥0) : FiniteMeasure ↥U :=
  ∑ y : ↥U, w y.1 • diracFM y

lemma fm_sum_apply {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (S : Finset ι)
    (f : ι → FiniteMeasure Ω) (s : Set Ω) : (∑ i ∈ S, f i) s = ∑ i ∈ S, (f i) s := by
  classical
  induction S using Finset.induction with
  | empty => simp [FiniteMeasure.coeFn_def]
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, FiniteMeasure.coeFn_add]
      rfl

lemma diracFM_apply {U : Opens ↥Cortex} (y z : ↥U) :
    diracFM y {z} = if y = z then 1 else 0 := by
  rw [FiniteMeasure.coeFn_def]
  show ((Measure.dirac y) {z}).toNNReal = _
  rw [Measure.dirac_apply' _ (measurableSet_singleton z)]
  by_cases h : y = z <;> simp [h, Set.indicator]

lemma massMeasureOn_apply (U : Opens ↥Cortex) (w : Site → ℝ≥0) (x : Site) (hx : x ∈ U) :
    massAt U x hx (massMeasureOn U w) = w x := by
  show (massMeasureOn U w) {(⟨x, hx⟩ : ↥U)} = w x
  rw [massMeasureOn, fm_sum_apply, Finset.sum_eq_single (⟨x, hx⟩ : ↥U)]
  · rw [FiniteMeasure.smul_apply, diracFM_apply]
    simp
  · intro b _ hb
    rw [FiniteMeasure.smul_apply, diracFM_apply]
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The section over `U` with prescribed mass at each of its sites.** The surjectivity
half of the dictionary, at an arbitrary open: no global measure is involved, and nothing
outside `U` is chosen. -/
noncomputable def sectionOfMassOn (U : Opens ↥Cortex) (w : Site → ℝ≥0) :
    (probabilityPresheaf Cortex).obj (op U) :=
  (TopCat.Presheaf.toSheafify Fpre).app (op U) (massMeasureOn U w)

@[simp] lemma densityOn_sectionOfMassOn (U : Opens ↥Cortex) (w : Site → ℝ≥0)
    (x : Site) (hx : x ∈ U) : densityOn (sectionOfMassOn U w) x hx = w x :=
  (densityOn_sheafify (massMeasureOn U w) x hx).trans (massMeasureOn_apply U w x hx)

open scoped Classical in
/-- A profile given on `U` only, extended to all of `Site` by zero — the bookkeeping that
lets `sectionOfMassOn`, whose argument is a profile on the whole substrate, realize a
profile that exists only on `U`. -/
noncomputable def extendW {U : Opens ↥Cortex} (w : ↥U → ℝ≥0) : Site → ℝ≥0 :=
  fun x => if hx : x ∈ U then w ⟨x, hx⟩ else 0

lemma extendW_apply {U : Opens ↥Cortex} (w : ↥U → ℝ≥0) (y : ↥U) : extendW w y.1 = w y :=
  dite_eq_left y.2

/-- **Sections over `U` are the mass profiles on `U`.** The dictionary at an arbitrary
open, in the form that says both halves at once. `massEquiv` is the case `U = ⊤`, stated
against `Site → ℝ≥0` because there the two indexings agree.

Note what the *inverse* discards: `sectionOfMassOn U w` depends on `w` only through its
values on `U`, which is why the equivalence is stated on `↥U → ℝ≥0` and not on
`Site → ℝ≥0`. A profile handed to a patch says nothing about the patch. -/
noncomputable def massEquivOn (U : Opens ↥Cortex) :
    (probabilityPresheaf Cortex).obj (op U) ≃ (↥U → ℝ≥0) :=
  Equiv.ofBijective (fun s y => densityOn s y.1 y.2)
    ⟨fun _ _ h => densityOn_injective fun x hx => congrFun h ⟨x, hx⟩,
     fun w => ⟨sectionOfMassOn U (extendW w), by
       funext y
       show densityOn (sectionOfMassOn U (extendW w)) y.1 y.2 = w y
       rw [densityOn_sectionOfMassOn, extendW_apply]⟩⟩

/-- The finite measure on the whole substrate with prescribed mass at each site. -/
noncomputable def massMeasure (w : Site → ℝ≥0) : FiniteMeasure ↥(⊤ : Opens ↥Cortex) :=
  massMeasureOn ⊤ w

lemma massMeasure_apply (w : Site → ℝ≥0) (x : Site) :
    massAt ⊤ x (memTop x) (massMeasure w) = w x :=
  massMeasureOn_apply ⊤ w x (memTop x)

/-- The global section with prescribed mass at each site. -/
noncomputable def sectionOfMass (w : Site → ℝ≥0) : GlobalSection (X := Cortex) :=
  sectionOfMassOn ⊤ w

@[simp] lemma Phi_sectionOfMass (w : Site → ℝ≥0) : density (sectionOfMass w) = w :=
  funext fun x => densityOn_sectionOfMassOn ⊤ w x (memTop x)

lemma Phi_surjective : Function.Surjective density :=
  fun w => ⟨sectionOfMass w, Phi_sectionOfMass w⟩

/-- **Global sections are measures.** On the three-site substrate the sections of the
sheafified probability presheaf over `⊤` correspond exactly to the finite measures on it,
read off as densities against counting measure. The case `U = ⊤` of `massEquivOn`, kept
under its own name because `density` is indexed by `Site` rather than by `↥⊤`. -/
noncomputable def massEquiv : GlobalSection (X := Cortex) ≃ (Site → ℝ≥0) :=
  Equiv.ofBijective density ⟨Phi_injective, Phi_surjective⟩

/-! ### The metric, from the measures rather than from nothing -/

/-- The metric on global sections: the largest difference between the masses the two glued
measures put on a site: the uniform distance between their densities. -/
noncomputable instance gsMetric : MetricSpace (GlobalSection (X := Cortex)) :=
  MetricSpace.induced density Phi_injective inferInstance

lemma gs_dist_eq (s t : GlobalSection (X := Cortex)) : dist s t = dist (density s) (density t) := rfl

lemma gs_dist_sectionOfMass (w w' : Site → ℝ≥0) :
    dist (sectionOfMass w) (sectionOfMass w') = dist w w' := by
  rw [gs_dist_eq, Phi_sectionOfMass, Phi_sectionOfMass]

/-- Completeness, proved from the dictionary: a Cauchy sequence of sections is a Cauchy
sequence of densities, its limit density is realized by a section, and the section
converges. Not "every Cauchy sequence is eventually constant". -/
instance gsComplete : CompleteSpace (GlobalSection (X := Cortex)) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hPhi : CauchySeq (fun n => density (u n)) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun m hm n hn => hN m hm n hn⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hPhi
  refine ⟨sectionOfMass L, ?_⟩
  rw [Metric.tendsto_atTop] at hL ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hL ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hd : dist (u n) (sectionOfMass L) = dist (density (u n)) L := by
    rw [gs_dist_eq, Phi_sectionOfMass]
  rw [hd]
  exact hN n hn

/-- The substrate has at least one global state: the phase-0 section of §4. -/
instance : Nonempty (GlobalSection (X := Cortex)) := ⟨globalSect 0⟩

/-- **The metric is not the 0/1 metric.** Distinct sections sit at distance `1/2`, which is
precisely what `contracting_implies_const` below needs and cannot get here. -/
theorem exists_dist_lt_one :
    ∃ s t : GlobalSection (X := Cortex), s ≠ t ∧ dist s t = 1/2 := by
  refine ⟨sectionOfMass (fun _ => 0), sectionOfMass (fun _ => 1/2), ?_, ?_⟩
  · intro h
    have := congrArg (fun u => density u Site.mid) h
    rw [Phi_sectionOfMass, Phi_sectionOfMass] at this
    norm_num at this
  · rw [gs_dist_sectionOfMass, dist_pi_const, NNReal.dist_eq]
    push_cast
    norm_num

/-! ### The 0/1 metric, kept as the record of why the old witness was empty -/

open scoped Classical in
/-- The 0/1 metric on global sections. Nothing about the space is used. It is no longer an
instance; `contracting_implies_const` is why. -/
@[instance_reducible]
noncomputable def gsDiscreteMetric : MetricSpace (GlobalSection (X := Cortex)) where
  dist x y := if x = y then 0 else 1
  dist_self x := by simp
  dist_comm x y := by split_ifs <;> simp_all
  dist_triangle x y z := by split_ifs <;> simp_all
  eq_of_dist_eq_zero := by
    intro x y h
    by_contra hne
    simp only [hne, ite_false] at h
    norm_num at h

section DiscreteMetric

attribute [local instance 10000] gsDiscreteMetric

open scoped Classical in
theorem gsDist_of_ne {x y : GlobalSection (X := Cortex)} (h : x ≠ y) : dist x y = 1 := by
  show (if x = y then (0:ℝ) else 1) = 1
  simp [h]

open scoped Classical in
theorem gsDist_le_one (x y : GlobalSection (X := Cortex)) : dist x y ≤ 1 := by
  show (if x = y then (0:ℝ) else 1) ≤ 1
  split_ifs <;> norm_num

/-- **The price of the 0/1 metric, made explicit.** Every contraction on it is constant, so
the contraction hypothesis of `reflexive_topology_implies_self` could only ever be
discharged there in the trivial way. This is the theorem the rest of this section exists to
avoid; `exists_dist_lt_one` shows its hypothesis fails for `gsMetric`. -/
theorem contracting_implies_const {K : NNReal} (hK : K < 1)
    (f : GlobalSection (X := Cortex) → GlobalSection (X := Cortex))
    (hf : LipschitzWith K f) (x y : GlobalSection (X := Cortex)) : f x = f y := by
  by_contra hne
  have h1 : dist (f x) (f y) ≤ (K : ℝ) * dist x y := hf.dist_le_mul x y
  rw [gsDist_of_ne hne] at h1
  have h2 : (K : ℝ) * dist x y ≤ (K : ℝ) := by
    calc (K : ℝ) * dist x y ≤ (K : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (gsDist_le_one x y) K.coe_nonneg
      _ = (K : ℝ) := mul_one _
  have h3 : (K : ℝ) < 1 := by exact_mod_cast hK
  linarith

end DiscreteMetric

/-! ### The Self -/

/-- The density of the phase-`t` global section: all its mass sits at the shared site,
with the amplitude `(1 + cos t)⁺` of §4. -/
lemma Phi_globalSect (t : ℝ) (x : Site) :
    density (globalSect t) x = if x = Site.mid then Real.toNNReal (1 + Real.cos t) else 0 := by
  have h := Phi_sheafify (phaseMeasure t) x
  rw [show density (globalSect t) x = density ((TopCat.Presheaf.toSheafify Fpre).app (op ⊤)
      (phaseMeasure t)) x from rfl, h, phaseMeasure, FiniteMeasure.smul_apply]
  have hd : (midDirac : FiniteMeasure ↥(⊤ : Opens ↥Cortex)) {(⟨x, memTop x⟩ : ↥(⊤ : Opens ↥Cortex))}
      = if midPt = (⟨x, memTop x⟩ : ↥(⊤ : Opens ↥Cortex)) then 1 else 0 :=
    diracFM_apply midPt ⟨x, memTop x⟩
  rw [hd]
  by_cases hx : x = Site.mid
  · subst hx
    simp [midPt]
  · have : midPt ≠ (⟨x, memTop x⟩ : ↥(⊤ : Opens ↥Cortex)) := by
      intro hcon
      exact hx (congrArg Subtype.val hcon).symm
    simp [this, hx]

/-- The phase-0 global section, typed as a `GlobalSection` so that `gsMetric` is found.
This is the baseline the field relaxes toward, and the Self it converges to. -/
noncomputable def cortexState : GlobalSection (X := Cortex) := globalSect 0

lemma Phi_cortexState (x : Site) :
    density cortexState x = if x = Site.mid then 2 else 0 := by
  rw [cortexState, Phi_globalSect]
  simp only [Real.cos_zero]
  split_ifs <;> norm_num

/-- The phase-π section: the envelope `(1 + cos t)⁺` vanishes, so the field carries no
mass anywhere. -/
noncomputable def cortexSilent : GlobalSection (X := Cortex) := globalSect Real.pi

lemma Phi_cortexSilent (x : Site) : density cortexSilent x = 0 := by
  rw [cortexSilent, Phi_globalSect]
  simp only [Real.cos_pi]
  norm_num

/-- The two extreme phase sections of §4 are two apart: the metric reads off the amplitude
difference, so distances here are amplitudes and not bookkeeping. -/
theorem dist_cortexSilent_cortexState : dist cortexSilent cortexState = 2 := by
  refine le_antisymm ?_ ?_
  · rw [gs_dist_eq, dist_pi_le_iff (by norm_num)]
    intro x
    rw [Phi_cortexSilent, Phi_cortexState, NNReal.dist_eq]
    split_ifs <;> push_cast <;> norm_num
  · have h := dist_le_pi_dist (density cortexSilent) (density cortexState) Site.mid
    rw [← gs_dist_eq] at h
    rw [Phi_cortexSilent, Phi_cortexState] at h
    simpa [NNReal.dist_eq] using h

/-! #### The avatar, and the map it induces

The self-prediction map is no longer written down and then attached to a boundary. Since
the W5 redesign (2026-08-31) a `ReflexiveBoundary` carries the avatar's *write* and its
*read-out*, and `predict` is their composite, so the map has to be built **through the
avatar region** or it cannot be built at all. That is what forces the shape of what
follows: `avatarRead` is the one number a section over the avatar region carries,
`avatarReadout` turns that number into a global state, and everything proved about the
dynamics below is proved about `cortexReflexive.predict`, which is their composite by
definition.

The previous witness — `relax s = ½ s + ½ baseline`, removed 2026-08-31 and recorded in
the W5 pass note of `tasks/todo.md` — cannot be used here any more, and the reason is
exactly the defect W5 names: it reads `density s x` at
*every* site, so it does not factor through a one-site avatar, and a map that does not
read the avatar has a fixed point that cannot depend on it. -/

/-- The avatar region: the shared site `mid`, the one point both patches of §4 see. -/
def avatarPatch : Opens ↥Cortex := ⟨{Site.mid}, isOpen_discrete _⟩

theorem memAvatarPatch : Site.mid ∈ avatarPatch := rfl

/-- **The avatar's reading, as a number.** By `massEquivOn` a section over `avatarPatch`
*is* the mass it carries at the shared site; this is that mass. The avatar is
one-dimensional, and this is the precise sense in which. -/
noncomputable def avatarRead (a : (probabilityPresheaf Cortex).obj (op avatarPatch)) : ℝ≥0 :=
  densityOn a Site.mid memAvatarPatch

/-- **The read-out.** From the single number the avatar carries, a global state: all the
mass at the shared site, at the amplitude halfway between what the avatar reports and the
baseline `2`. Dissipative — half the discrepancy is discarded at each step — and a
genuine function of the avatar's reading, which is what makes the fixed point below
depend on it. -/
noncomputable def avatarReadout (a : (probabilityPresheaf Cortex).obj (op avatarPatch)) :
    GlobalSection (X := Cortex) :=
  sectionOfMass (fun x => if x = Site.mid then (avatarRead a + 2) / 2 else 0)

/-- A reflexive boundary on the three-site cortex. `auto_resonance` is the presheaf
restriction to the avatar region, so the avatar's state does track the global field —
which the class itself never requires — and `readout` is the relaxation above, so the
self-model runs on the avatar and on nothing else. -/
noncomputable def cortexReflexive : ReflexiveBoundary Cortex where
  avatar_region := avatarPatch
  auto_resonance := fun s =>
    (probabilityPresheaf Cortex).map (homOfLE (le_top : avatarPatch ≤ ⊤)).op s
  readout := avatarReadout

/-- The induced predictive model. Derived from the boundary rather than chosen beside it;
kept under its own name because Derivation 6 in the manuscript refers to it. -/
noncomputable def cortexPredict : PredictiveModel Cortex := cortexReflexive.predictive_model

/-- What the avatar reports about a global state is that state's mass at the shared site.
`densityOn_restrict`, and nothing else. -/
lemma avatarRead_restrict (s : GlobalSection (X := Cortex)) :
    avatarRead (cortexReflexive.auto_resonance s) = density s Site.mid :=
  densityOn_restrict (le_top : avatarPatch ≤ ⊤) s Site.mid memAvatarPatch

lemma cortexPredict_eq (s : GlobalSection (X := Cortex)) :
    cortexReflexive.predict s =
      sectionOfMass (fun y => if y = Site.mid then (density s Site.mid + 2) / 2 else 0) := by
  show avatarReadout (cortexReflexive.auto_resonance s) = _
  simp only [avatarReadout, avatarRead_restrict]

/-- The prediction in closed form: everything it knows about `s` is `density s Site.mid`.
The fold is visible here — two states agreeing at the shared site have the same
prediction, whatever they do elsewhere. -/
@[simp] lemma Phi_cortexPredict (s : GlobalSection (X := Cortex)) (x : Site) :
    density (cortexReflexive.predict s) x =
      if x = Site.mid then (density s Site.mid + 2) / 2 else 0 := by
  rw [cortexPredict_eq, Phi_sectionOfMass]

/-- The prediction at the avatar site: the only value the read-out is not forced to send
to zero, and the one the contraction below is about. -/
lemma Phi_cortexPredict_mid (s : GlobalSection (X := Cortex)) :
    density (cortexReflexive.predict s) Site.mid = (density s Site.mid + 2) / 2 := by
  rw [Phi_cortexPredict]; simp

lemma Phi_cortexState_mid : density cortexState Site.mid = 2 := by
  rw [Phi_cortexState]; simp

lemma nnreal_dist_avg (a b c : ℝ≥0) : dist ((a + c)/2) ((b + c)/2) = dist a b / 2 := by
  rw [NNReal.dist_eq, NNReal.dist_eq]
  push_cast
  rw [show ((a:ℝ) + c)/2 - ((b:ℝ) + c)/2 = ((a:ℝ) - b)/2 by ring, abs_div]
  norm_num

lemma cortexPredict_lipschitz : LipschitzWith (1/2) cortexReflexive.predict := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [gs_dist_eq]
  push_cast
  have hb : (0:ℝ) ≤ 1/2 * dist s t := by positivity
  rw [dist_pi_le_iff hb]
  intro x
  rw [Phi_cortexPredict, Phi_cortexPredict]
  have h1 : dist (density s Site.mid) (density t Site.mid) ≤ dist s t := by
    rw [gs_dist_eq]; exact dist_le_pi_dist _ _ Site.mid
  split_ifs with hx
  · rw [nnreal_dist_avg]
    linarith
  · rw [dist_self]
    exact hb

/-- **The contraction factor is exactly one half of what the avatar sees** — both
inequalities, not merely an upper bound. It is *not* half the distance between the states:
the read-out is blind off the avatar region, so two states differing only away from `mid`
have the same prediction. That loss is the fold, stated rather than hidden; the removed
`relax` had no such loss precisely because it did not factor through an avatar. -/
theorem cortexPredict_dist (s t : GlobalSection (X := Cortex)) :
    dist (cortexReflexive.predict s) (cortexReflexive.predict t) =
      dist (density s Site.mid) (density t Site.mid) / 2 := by
  have hnn : (0:ℝ) ≤ dist (density s Site.mid) (density t Site.mid) / 2 := by positivity
  refine le_antisymm ?_ ?_
  · rw [gs_dist_eq, dist_pi_le_iff hnn]
    intro x
    rw [Phi_cortexPredict, Phi_cortexPredict]
    split_ifs with hx
    · rw [nnreal_dist_avg]
    · rw [dist_self]; exact hnn
  · have h := dist_le_pi_dist (density (cortexReflexive.predict s))
      (density (cortexReflexive.predict t)) Site.mid
    rw [← gs_dist_eq, Phi_cortexPredict_mid, Phi_cortexPredict_mid, nnreal_dist_avg] at h
    exact h

/-- **The map is not constant** — the exact failure of `contracting_implies_const` on this
metric, and the check that the avatar is doing something: the silent field and the
baseline report different numbers, so they get different predictions. -/
theorem cortexPredict_not_const :
    cortexReflexive.predict cortexSilent ≠ cortexReflexive.predict cortexState := by
  intro h
  have h' : density (cortexReflexive.predict cortexSilent) Site.mid
      = density (cortexReflexive.predict cortexState) Site.mid := by rw [h]
  rw [Phi_cortexPredict_mid, Phi_cortexPredict_mid, Phi_cortexSilent, Phi_cortexState_mid] at h'
  have := congrArg NNReal.toReal h'
  push_cast at this
  norm_num at this

theorem cortexPredict_fixed : cortexReflexive.predict cortexState = cortexState := by
  apply Phi_injective
  funext x
  rw [Phi_cortexPredict, Phi_cortexState_mid, Phi_cortexState]
  split_ifs with hx
  · apply NNReal.coe_injective; push_cast; norm_num
  · rfl

/-- The fixed point is unique, proved directly rather than quoted from Banach: a section
that predicts itself carries mass `2` at the shared site and nothing anywhere else. -/
theorem cortexPredict_fixed_unique (s : GlobalSection (X := Cortex))
    (h : cortexReflexive.predict s = s) : s = cortexState := by
  have hd : ∀ x, density s x = if x = Site.mid then (density s Site.mid + 2) / 2 else 0 := by
    intro x
    rw [← Phi_cortexPredict s x, h]
  have hmid : density s Site.mid = 2 := by
    have hm : density s Site.mid = (density s Site.mid + 2) / 2 := by
      rw [← Phi_cortexPredict_mid s, h]
    apply NNReal.coe_injective
    push_cast
    have h2 := congrArg NNReal.toReal hm
    push_cast at h2
    linarith
  apply Phi_injective
  funext x
  rw [hd x, hmid, Phi_cortexState]
  split_ifs with hx
  · apply NNReal.coe_injective; push_cast; norm_num
  · rfl

/-! #### The contraction rate, from the coupling and the noise

`cortexPredict_lipschitz` gives the constant `1/2`, and the second half of W5 is that
`1/2` must not be the physical hypothesis: a map defined to average with a baseline
contracts by a half because it was defined to, which is a fact about the definition.
`resonanceRate K D τ = exp(-(K - 2D)τ/2)` of `Phase6_ReflexiveTopology` is the mean-field
relaxation factor instead, and the substrate is placed at `K = 3`, `D = 1` — so
`K_c = critical_coupling 1 = 2` and the cortex is supercritical — with one relaxation step
of duration `τ = 2 log 2`, at which the rate is exactly the `1/2` the read-out achieves.

**What is being witnessed, and what is not.** The identification of this three-site
substrate's coupling with `K = 3` is a choice of units for the witness, not a measurement;
nothing here derives a coupling constant from the cortex. What is witnessed is that the
hypotheses of `self_of_supercritical` are jointly satisfiable on a substrate whose map is
provably non-constant, so the theorem is not vacuous — and `cortexHasSelf` below now comes
out of `K > K_c`, with the numeral appearing only in the Lipschitz obligation the
substrate discharges. `cortexSubcritical_not_contracting` is the other half: on the *same*
map, at `K = 1`, the rate is not a contraction rate and Derivation 6's argument is gone. -/

/-- The witness's relaxation step, chosen so that the mean-field rate at `K = 3`, `D = 1`
is exactly the half the read-out achieves. -/
noncomputable def cortexTau : ℝ := 2 * Real.log 2

theorem cortexTau_pos : 0 < cortexTau := by
  have h : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [cortexTau]; linarith

/-- The witness sits above Sakaguchi's threshold: `K = 3 > 2 = critical_coupling 1`. -/
theorem cortexSupercritical : critical_coupling 1 < 3 := by
  rw [critical_coupling]; norm_num

theorem cortexResonanceRate : resonanceRate 3 1 cortexTau = 1/2 := by
  apply NNReal.coe_injective
  rw [coe_resonanceRate]
  push_cast
  rw [critical_coupling, cortexTau,
    show -((3:ℝ) - 2 * 1) * (2 * Real.log 2) / 2 = -Real.log 2 by ring,
    Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  norm_num

theorem cortexPredict_lipschitz_rate :
    LipschitzWith (resonanceRate 3 1 cortexTau) cortexReflexive.predict := by
  rw [cortexResonanceRate]; exact cortexPredict_lipschitz

/-- The contraction, with the rate read off `K` and `D` rather than stipulated. -/
theorem cortexPredict_contracting :
    ContractingWith (resonanceRate 3 1 cortexTau) cortexReflexive.predict :=
  ⟨resonanceRate_lt_one cortexTau_pos cortexSupercritical, cortexPredict_lipschitz_rate⟩

/-- Derivation 6, applied to the witness: the Self exists and is unique on a substrate
where the metric is the uniform distance between the glued measures' densities, the map
factors through a one-site avatar, and the contraction follows from the coupling exceeding
`K_c = 2D`. -/
theorem cortexHasSelf : ∃! s : GlobalSection (X := Cortex),
    cortexReflexive.predict s = s :=
  self_of_supercritical cortexTau_pos cortexSupercritical cortexReflexive
    cortexPredict_lipschitz_rate

/-- The fixed point named — and, by `cortexPredict_fixed_unique`, the only one. -/
theorem cortexFixedPoint : cortexReflexive.predict cortexState = cortexState :=
  cortexPredict_fixed

/-- **Below the threshold the argument is unavailable on this very substrate.** The map is
unchanged; only the parameters the rate is read from have moved, to `K = 1 ≤ 2 = K_c`. At
that rate `ContractingWith` is false, so Banach supplies nothing. This does not say the
cortex has no fixed point below threshold — `cortexPredict_fixed` is still there — it says
this route to it is closed, which is the honest content of a threshold claim. -/
theorem cortexSubcritical_not_contracting :
    ¬ ContractingWith (resonanceRate 1 1 cortexTau) cortexReflexive.predict :=
  not_contractingWith_resonanceRate cortexTau_pos.le
    (by rw [critical_coupling]; norm_num) _

/-! ### The avatar reads the field — and what it costs when it does not

`cortexReflexive` is built with the presheaf restriction as its `auto_resonance`, which is
what made open item **O2** a bookkeeping item rather than a research one: the constraint
was known satisfiable before it was stated. What was missing then is that nothing
*required* it, and no theorem mentioned the field.
`ReflexiveBoundary.IsRestrictionResonance` and `ReflexiveBoundary.eq_of_avatar_eq` supply
the requirement and the theorem; W5 then made the predictive map itself run through the
avatar, so the blinded boundary no longer even has the same dynamics. This block
discharges both halves on the cortex and exhibits what the blinding costs.

The non-degeneracy check is the one that matters. A resonance condition is empty on a
substrate whose avatar region cannot tell two field states apart, so
`cortexReflexive_restrict_ne` is proved before anything is claimed for it: the silent field
and the baseline differ *at the avatar site*, not merely somewhere.
-/

/-- **The avatar region is not blind.** The silent field and the baseline differ at the
shared site, which is the whole of the avatar region — so the resonance condition below is
a constraint on this substrate and not a formality. -/
theorem cortexReflexive_restrict_ne :
    cortexReflexive.restrictToAvatar cortexSilent ≠ cortexReflexive.restrictToAvatar cortexState := by
  intro h
  have h2 : density cortexSilent Site.mid = density cortexState Site.mid :=
    (densityOn_restrict (le_top : avatarPatch ≤ ⊤) cortexSilent Site.mid memAvatarPatch).symm.trans
      ((congrArg (fun a => densityOn a Site.mid memAvatarPatch) h).trans
        (densityOn_restrict (le_top : avatarPatch ≤ ⊤) cortexState Site.mid memAvatarPatch))
  rw [Phi_cortexSilent, Phi_cortexState] at h2
  norm_num at h2

/-- **The resonance condition holds here**, by construction and by `rfl`: the avatar's
state is the field's own restriction. This is what makes `IsRestrictionResonance` a
satisfiable requirement rather than an exclusion. -/
theorem cortexReflexive_resonant : cortexReflexive.IsRestrictionResonance := fun _ => rfl

theorem cortexReflexive_avatar_separates :
    cortexReflexive.auto_resonance cortexSilent ≠ cortexReflexive.auto_resonance cortexState := by
  rw [cortexReflexive_resonant cortexSilent, cortexReflexive_resonant cortexState]
  exact cortexReflexive_restrict_ne

/-- **The Self is its own avatar reading, extended.** `self_eq_readout_restrict` on the
witness: the baseline section is recovered from the single number the shared site carries.
This is the statement Derivation 6 could not make before W5 — under the old structure
`predict` was unrelated to `restrictToAvatar`, so no fixed point said anything about the
field's restriction. -/
theorem cortexState_eq_readout_restrict :
    cortexState = cortexReflexive.readout (cortexReflexive.restrictToAvatar cortexState) :=
  ReflexiveBoundary.self_eq_readout_restrict _ cortexReflexive_resonant cortexPredict_fixed

/-- The Self is in the range of the read-out: a global state reconstructed from a section
over one site. The low-dimensional fold of the module header, on the witness. -/
theorem cortexState_mem_range_readout : cortexState ∈ Set.range cortexReflexive.readout :=
  ReflexiveBoundary.self_mem_range_readout _ cortexPredict_fixed

/-! #### A covering family of avatars, and the field they reconstruct -/

/-- One avatar per site, each reading the field on its own smallest neighbourhood and
putting back what it read. Their regions cover the substrate, which is what
`eq_of_avatar_eq` needs; a single avatar on one site could never determine the field
elsewhere. The read-outs play no part in that theorem — it consumes only the readings —
and are supplied because a boundary is not a boundary without one. -/
noncomputable def siteReflexive (x : Site) : ReflexiveBoundary Cortex where
  avatar_region := sing x
  auto_resonance := fun s => (probabilityPresheaf Cortex).map (homOfLE (le_top : sing x ≤ ⊤)).op s
  readout := fun a => sectionOfMass (fun y => if y = x then densityOn a x (memSing x) else 0)

theorem siteReflexive_resonant (x : Site) : (siteReflexive x).IsRestrictionResonance :=
  fun _ => rfl

theorem sing_cover : (⨆ x : Site, sing x) = (⊤ : Opens ↥Cortex) := by
  ext y
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  exact ⟨y, rfl⟩

/-- **Unity, reconstructed from the localized self-encodings.** Two global states whose
avatars read the same at every site are the same state. The avatars are local — each sees
one site — and no access to the global section is used; the sheaf condition does the rest. -/
theorem cortex_eq_of_avatar_eq {s t : GlobalSection (X := Cortex)}
    (h : ∀ x, (siteReflexive x).auto_resonance s = (siteReflexive x).auto_resonance t) : s = t :=
  ReflexiveBoundary.eq_of_avatar_eq siteReflexive siteReflexive_resonant sing_cover h

/-- Derivation 6 on the witness, with the avatar doing work: the Self exists, and it is the
only global state producing its avatar readings. -/
theorem cortexSelfEncoded : ∃ s : GlobalSection (X := Cortex),
    cortexReflexive.predict s = s ∧
      ∀ t : GlobalSection (X := Cortex),
        (∀ x, (siteReflexive x).auto_resonance t = (siteReflexive x).auto_resonance s) → t = s :=
  ReflexiveBoundary.self_eq_of_avatar_eq siteReflexive siteReflexive_resonant sing_cover
    cortexReflexive cortexPredict_contracting

/-- Naming the Self of the previous theorem: it is `cortexState`, and the avatars pin it
down. Combines `cortexPredict_fixed_unique` (the fixed point is the baseline) with the
reconstruction. -/
theorem cortexState_determined_by_avatars (t : GlobalSection (X := Cortex))
    (h : ∀ x, (siteReflexive x).auto_resonance t = (siteReflexive x).auto_resonance cortexState) :
    t = cortexState :=
  cortex_eq_of_avatar_eq h

/-! #### The blind boundary, and the Self it loses

Before W5 this block ended with `cortexBlind_hasSelf`: the blinded boundary had *the same*
Self, by the *same* proof, from the *same* contraction hypothesis, and that was the
recorded defect of Derivation 6. It cannot be stated now. `cortexBlind` has a different
predictive map — a constant one — and `cortexBlind_self_ne` proves that the cortex's Self
is not a fixed point of it. -/

/-- The same avatar region and the same read-out as `cortexReflexive`, with an avatar that
ignores the field and reports the silent state's reading whatever the field is doing. A
legal `ReflexiveBoundary`: the structure still has nothing to object with, which is why
the predicate is needed. -/
noncomputable def cortexBlind : ReflexiveBoundary Cortex :=
  cortexReflexive.constResonance (cortexReflexive.auto_resonance cortexSilent)

theorem cortexBlind_not_resonant : ¬ cortexBlind.IsRestrictionResonance :=
  ReflexiveBoundary.constResonance_not_isRestrictionResonance _ _ cortexReflexive_restrict_ne

/-- **The Self does not survive the blinding.** `cortexState` predicts itself under the
cortex's own self-model (`cortexPredict_fixed`) and does not under the blinded one, whose
only fixed point is the state the stipulated avatar reading extends to. This is the
theorem that replaces `cortexBlind_hasSelf`, and it says the opposite. -/
theorem cortexBlind_self_ne : ¬ cortexBlind.predict cortexState = cortexState := by
  refine ReflexiveBoundary.not_self_of_constResonance _ _ ?_
  show cortexReflexive.predict cortexSilent ≠ cortexState
  intro h
  have h2 : density (cortexReflexive.predict cortexSilent) Site.mid
      = density cortexState Site.mid := by rw [h]
  rw [Phi_cortexPredict_mid, Phi_cortexSilent, Phi_cortexState_mid] at h2
  have := congrArg NNReal.toReal h2
  push_cast at this
  norm_num at this

/-- The blinded boundary does have a unique fixed point, and naming it is the point: it is
`cortexReflexive.predict cortexSilent`, the state the avatar's stipulated contents extend
to, fixed in advance of anything the field does. No metric, no completeness and no
contraction are used — Banach is not being applied, because there is no dynamics left to
apply it to. -/
theorem cortexBlind_existsUnique_self :
    ∃! s : GlobalSection (X := Cortex), cortexBlind.predict s = s :=
  ReflexiveBoundary.constResonance_existsUnique_self _ _

/-- …and the reconstruction genuinely fails there: two *distinct* global states with
identical avatar readings. This is the exact statement `cortex_eq_of_avatar_eq` buys, and
the exact price of dropping the predicate. -/
theorem cortexBlind_not_determined :
    ∃ s t : GlobalSection (X := Cortex), s ≠ t ∧
      cortexBlind.auto_resonance s = cortexBlind.auto_resonance t := by
  refine ⟨cortexSilent, cortexState, ?_, rfl⟩
  intro h
  have h2 : density cortexSilent Site.mid = density cortexState Site.mid := by rw [h]
  rw [Phi_cortexSilent, Phi_cortexState] at h2
  norm_num at h2

end ReflexiveSelf

end Examples
end PhysicsOfConsciousness
