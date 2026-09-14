/-
  Examples/Phase5.lean — covers whose gluing is not decoration

  Four witnesses over the cortex of `Examples/Cortex.lean`, each answering a
  different way the first cover could be too easy. §13 carries a phase field
  that is not constant and patches whose densities genuinely differ. §14 builds
  its two patches from independently chosen mass profiles, so the glued section
  is none of the data the instance carries. §17.1 hands Derivation 5 a phase
  field that a trajectory *reached* — the one from `Examples/Phase4.lean` §17 —
  rather than one assumed at equilibrium. §20 reads the overlap-agreement
  hypothesis and shows what it forbids.
-/

import PhysicsOfConsciousness.Phase4_RotatingFrame
import PhysicsOfConsciousness.Phase5_EquilibriumBridge
import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Examples.Cortex
import PhysicsOfConsciousness.Examples.Phase4
import PhysicsOfConsciousness.Examples.Phase6

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 13. A cover with a non-constant phase, and why it cannot be more than that

  Open item O5 asked for a `ThermodynamicCover` "at a non-constant minimum of
  the Kuramoto potential", because §4's witness locks every patch at phase `0`,
  which is what makes `thermodynamic_equilibrium` discharge and leaves the
  gluing with nothing to do.

  The answer has two halves, and the negative one is the more informative.

  * **The class shape forbids a genuinely non-constant phase.**
    `thermodynamic_equilibrium` demands a global minimum of the reduced
    Kuramoto potential, and `potential_min_iff_phase_locked` says the minimisers
    of that functional are *exactly* the phase-locked configurations. So
    `ThermodynamicCover.phase_locked` holds of every instance: the phases may
    differ, but only by multiples of `2π`, which the periodicity hypothesis of
    `LocalSectionSynchronization.ofInvariantMeasure` then erases at the level of
    measures. `cortexCoverTwisted_glued` draws the conclusion — the section
    Derivation 5 glues here is the one this witness was built from. This is the
    same kind of result as `contracting_implies_const` in §10: a recorded proof
    that the witness below is as strong as the current class permits, not a
    witness that could be improved by trying harder.

    That last step is a property of *this* witness, not of the theorem. It is
    built through `ofInvariantMeasure`, the constructor packaging the class's
    old shape, in which a global measure was an input. §14 drops the constructor
    and the conclusion with it.
  * **Within that limit, this is the strongest witness available**, and it is
    strictly stronger than §4's on three counts. The phase field is *not* the
    constant function (`twistPhase_not_const`: the second patch is one full turn
    ahead). The invariant measure spreads mass over all three sites with three
    *different* densities (`richDensity_zero_not_uniform`), instead of §4's
    single point mass at the shared site, so the two patches carry genuinely
    different local data — mass `2` at `left` for one, mass `3` at `right` for
    the other — and the overlap agreement on `{mid}` is an equation between two
    separately computed numbers rather than a syntactic identity. And the
    densities are read off the sections themselves, through `densityOn`, rather
    than assumed.

  What is still assumed, exactly as in §4: that the configuration is at the
  potential minimum. Nothing here runs a dynamics.

  What *was* also assumed here, and is not any more, is the existence of the
  global measure — see §14 and open item O19.
-/

/-- The invariant density carried by phase `t`: mass on every site, and a
different amount on each. The `cos` makes the family genuinely depend on `t`
(`richDensity_not_const`) while staying `2π`-periodic, which is what
`ofInvariantMeasure` demands. -/
noncomputable def richDensity (t : ℝ) : Site → ℝ≥0
  | Site.left  => Real.toNNReal (1 + Real.cos t)
  | Site.mid   => 1
  | Site.right => Real.toNNReal (2 + Real.cos t)

/-- The global section carrying that density. Specified by its densities through
§10's `sectionOfMass`, not manipulated through the sheafification — which is
what made §4's witness a single scaled Dirac. -/
noncomputable def richSection (t : ℝ) : GlobalSection (X := Cortex) :=
  sectionOfMass (richDensity t)

@[simp] theorem density_richSection (t : ℝ) : density (richSection t) = richDensity t :=
  Phi_sectionOfMass _

/-- 2π-periodicity, which is what `ofInvariantMeasure` demands. -/
theorem richDensity_periodic {x y : ℝ} (h : Real.cos (x - y) = 1) :
    richDensity x = richDensity y := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp h
  have hx : x = y + (n : ℝ) * (2 * Real.pi) := by linarith [hn]
  have hcos : Real.cos x = Real.cos y := by rw [hx, Real.cos_add_int_mul_two_pi]
  funext s
  cases s <;> simp [richDensity, hcos]

/-- Non-degeneracy: the invariant measure really varies with the phase. -/
theorem richDensity_not_const : richDensity 0 ≠ richDensity Real.pi := by
  intro h
  have hl := congrFun h Site.left
  simp [richDensity] at hl

theorem richDensity_zero_left : richDensity 0 Site.left = 2 := by
  simp [richDensity]
  norm_num

theorem richDensity_zero_mid : richDensity 0 Site.mid = 1 := rfl

theorem richDensity_zero_right : richDensity 0 Site.right = 3 := by
  simp [richDensity]
  norm_num

/-- Non-degeneracy across the substrate: the glued state is not a multiple of
counting measure, so the two patches see different amounts of mass. -/
theorem richDensity_zero_not_uniform :
    richDensity 0 Site.left ≠ richDensity 0 Site.mid ∧
    richDensity 0 Site.mid ≠ richDensity 0 Site.right := by
  rw [richDensity_zero_left, richDensity_zero_mid, richDensity_zero_right]
  constructor <;> norm_num

/-! ### The phase field -/

/-- A phase field that is *not* the constant function: the second patch sits one
full turn ahead of the first. By `ThermodynamicCover.phase_locked` this is as far
from constant as any instance can get. -/
noncomputable def twistPhase : Bool → ℝ
  | false => 0
  | true  => 2 * Real.pi

theorem twistPhase_not_const : twistPhase false ≠ twistPhase true := by
  show (0 : ℝ) ≠ 2 * Real.pi
  have := Real.pi_pos
  intro h
  linarith

theorem twistPhase_locked : is_phase_locked twistPhase := by
  intro i j
  cases i <;> cases j <;> simp [twistPhase, Real.cos_two_pi]

/-! ### The witness

Declared as `def`s rather than `instance`s: §4's `cortexSync` and `cortexCover`
are the instances for `Cortex`, and a second pair would make instance search
silently pick between two different covers of the same substrate. They are
`@[instance_reducible]` so that `ThermodynamicCover.mk` can see through
`cortexSyncTwisted` to `I = Bool`, and are applied explicitly below. -/

@[instance_reducible]
noncomputable def cortexSyncTwisted : LocalSectionSynchronization Cortex :=
  LocalSectionSynchronization.ofInvariantMeasure Bool patch patch_cover twistPhase richSection
    (fun _ _ h => by unfold richSection; rw [richDensity_periodic h])

/-- The same uniform unit coupling as §4. `thermodynamic_equilibrium` is
discharged by `phase_locked_minimizes_potential'` — the generalisation of §4's
appeal to `phase_locked_minimizes_potential`, which only covered `theta ≡ 0`. -/
@[instance_reducible]
noncomputable def cortexCoverTwisted : ThermodynamicCover Cortex where
  toLocalSectionSynchronization := cortexSyncTwisted
  I_fintype := inferInstanceAs (Fintype Bool)
  I_decidable := inferInstanceAs (DecidableEq Bool)
  A := fun _ _ => 1
  A_symm := fun _ _ => rfl
  A_pos := fun _ _ => one_pos
  thermodynamic_equilibrium := fun theta =>
    phase_locked_minimizes_potential' (V := Bool)
      ⟨fun _ => 0, fun _ _ => 1, fun _ _ => rfl⟩ (fun _ _ => one_pos)
      twistPhase twistPhase_locked theta

/-! ### Reading the local data

§4 could say nothing about what its patch-local sections contained; §10's
`stalkMass` makes that readable at any open, not just at `⊤`. -/

theorem left_mem_patch_false : Site.left ∈ patch false := by
  show Site.left ≠ Site.right
  decide

theorem mid_mem_patch_false : Site.mid ∈ patch false := by
  show Site.mid ≠ Site.right
  decide

theorem mid_mem_patch_true : Site.mid ∈ patch true := by
  show Site.mid ≠ Site.left
  decide

theorem right_mem_patch_true : Site.right ∈ patch true := by
  show Site.right ≠ Site.left
  decide

/-- The first patch carries mass `2` at `left`, a site the second patch does not
contain. -/
theorem twisted_density_left :
    densityOn (cortexCoverTwisted.sync_to_section false) Site.left left_mem_patch_false = 2 := by
  have h : densityOn (cortexCoverTwisted.sync_to_section false) Site.left left_mem_patch_false
      = density (richSection 0) Site.left := rfl
  rw [h, density_richSection]
  exact richDensity_zero_left

/-- The second patch carries mass `3` at `right`, a site the first patch does not
contain — and it does so at phase `2π`, where `richDensity_periodic` is what
identifies the density with the phase-`0` one. -/
theorem twisted_density_right :
    densityOn (cortexCoverTwisted.sync_to_section true) Site.right right_mem_patch_true = 3 := by
  have h : densityOn (cortexCoverTwisted.sync_to_section true) Site.right right_mem_patch_true
      = density (richSection (2 * Real.pi)) Site.right := rfl
  rw [h, density_richSection,
    richDensity_periodic (x := 2 * Real.pi) (y := 0) (by simp)]
  exact richDensity_zero_right

theorem twisted_overlap_mass_false :
    densityOn (cortexCoverTwisted.sync_to_section false) Site.mid mid_mem_patch_false = 1 := by
  have h : densityOn (cortexCoverTwisted.sync_to_section false) Site.mid mid_mem_patch_false
      = density (richSection 0) Site.mid := rfl
  rw [h, density_richSection]
  exact richDensity_zero_mid

theorem twisted_overlap_mass_true :
    densityOn (cortexCoverTwisted.sync_to_section true) Site.mid mid_mem_patch_true = 1 := by
  have h : densityOn (cortexCoverTwisted.sync_to_section true) Site.mid mid_mem_patch_true
      = density (richSection (2 * Real.pi)) Site.mid := rfl
  rw [h, density_richSection,
    richDensity_periodic (x := 2 * Real.pi) (y := 0) (by simp)]
  exact richDensity_zero_mid

/-- The overlap agreement `overlap_agreement` proves abstractly, computed: both
patches put mass `1` on the shared site `mid`, from separately computed
densities. -/
theorem twisted_overlap_agrees :
    densityOn (cortexCoverTwisted.sync_to_section false) Site.mid mid_mem_patch_false
      = densityOn (cortexCoverTwisted.sync_to_section true) Site.mid mid_mem_patch_true :=
  twisted_overlap_mass_false.trans twisted_overlap_mass_true.symm

/-! ### The Phase 5 conclusions on this witness -/

/-- The non-constant phase field is still phase-locked, and this is *forced* by
`thermodynamic_equilibrium`, not chosen: `ThermodynamicCover.phase_locked`
applies to every instance. Together with `twistPhase_not_const` this is exactly
the scope of the answer to O5 — non-constant as a function, locked as a physical
state. -/
theorem cortexCoverTwisted_phase_locked : is_phase_locked cortexCoverTwisted.phase :=
  cortexCoverTwisted.phase_locked

/-- Derivation 5 on the twisted cover: the two patch-local sections, which now
carry different mass profiles, glue to a unique global section. -/
example : ∃! s : GlobalSection (X := Cortex),
    ∀ i : Bool, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : cortexCoverTwisted.cover i ≤ ⊤)).op s
      = cortexCoverTwisted.sync_to_section i :=
  @global_section_from_thermodynamics Cortex _ _ _ cortexCoverTwisted

/-- …and that unique section is `richSection 0` — the measure the instance was
*built from*, since `cortexSyncTwisted` goes through
`LocalSectionSynchronization.ofInvariantMeasure`. The gluing determined it; it
did not produce it.

That is a property of this witness, not of Derivation 5: the theorem is now
stated with no global object among its hypotheses (open item O19), and §14
exhibits a cover for which the glued section is none of the data the instance
carries. -/
theorem cortexCoverTwisted_glued (s : GlobalSection (X := Cortex))
    (hs : ∀ i : Bool, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : patch i ≤ ⊤)).op s = cortexCoverTwisted.sync_to_section i) :
    s = richSection 0 := by
  have hR : ∀ i : Bool, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : cortexCoverTwisted.cover i ≤ ⊤)).op (richSection 0)
      = cortexCoverTwisted.sync_to_section i := by
    intro i
    show (probabilityPresheaf Cortex).map (homOfLE (le_top : patch i ≤ ⊤)).op (richSection 0)
      = (probabilityPresheaf Cortex).map (homOfLE (le_top : patch i ≤ ⊤)).op
          (richSection (twistPhase i))
    unfold richSection
    rw [richDensity_periodic (x := (0 : ℝ)) (y := twistPhase i)
      (by cases i <;> simp [twistPhase, Real.cos_two_pi])]
  rw [cortexCoverTwisted.invariantMeasure_unique s hs,
    cortexCoverTwisted.invariantMeasure_unique _ hR]

/-! ## 14. Emergence: a cover whose global state is not among its data

  §4 and §13 both build their local sections by restricting one global measure
  the instance carries, because that is what the old shape of
  `LocalSectionSynchronization` required. Open item **O19** was the observation
  that this made `global_section_from_thermodynamics` a uniqueness theorem: the
  global object existed before the sheaf condition was consulted, and
  `cortexCoverTwisted_glued` computes that the gluing returns it unchanged.

  The class no longer has that shape. Its only condition on the local data is
  `section_agrees_of_phase_eq` — synchronised patches agree where they overlap —
  and the common measure is produced by `probability_glue_unique`. This section
  is the witness that the difference is real.

  **The construction.** Two patches, two *different* mass profiles: `leftW`
  reports `(2, 1, 7)` across the three sites, `rightW` reports `(5, 1, 3)`. Each
  patch's local section is built from its own profile, and the two profiles are
  not equal (`patchW_ne`). They agree only where it is required of them — the
  shared site `mid`, where both carry mass `1` (`glued_overlap_mass_false`,
  `glued_overlap_mass_true`), which is what discharges the class field, by
  computation rather than by functoriality.

  **What the gluing produces.** The unique global section is `sectionOfMass
  gluedW` with profile `(2, 1, 3)`: the first patch's reading of `left`, the
  second's of `right`. It is **neither** of the profiles the instance was built
  from (`gluedW_ne_leftW`, `gluedW_ne_rightW`), and neither of them restricts
  correctly to both patches (`leftW_glues_nothing`, `rightW_glues_nothing`). So
  no measure appearing in the construction is the answer, and the section the
  theorem returns carries information no single patch had. That is the emergence
  reading of Derivation 5, on a witness.

  **What is still assumed** on *this* cover, unchanged from §4 and §13: that the
  configuration is at the potential minimum, and that the patches agree on their
  overlap. The first is what §17.1 removes, by rebuilding this construction on
  three patches over a phase field a trajectory reaches; the second it does not. The second is now the *only* thing the class asks of the local data,
  and here it is discharged by computing two numbers rather than by declaring the
  sections to be restrictions of something.

  **The caveat that used to stand here is gone.** Until 2026-08-30 the local sections
  were still *defined* by restricting a measure on all of `Cortex`, because §10's
  germ–measure dictionary was built at `⊤`; that was open item **O21**. The
  dictionary is now built at an arbitrary open, so `sync_to_section i` is
  `sectionOfMassOn (patch i) (patchW i)` — a section over the patch, constructed
  from the patch's own profile, with no measure on `Cortex` appearing anywhere in
  the instance. `glued_section_eq_restrict` records that the object did not change
  when the construction did, so the computations below are the same ones.

  The profiles are still functions on all of `Site`, and deliberately differ off
  their own patches (`leftW` puts mass `7` at `right`, which the first patch cannot
  see): `sectionOfMassOn` reads a profile only on its own open, so those values are
  invisible to the section, and their presence is what makes the profiles
  unmistakable for the global state.
-/

section GluedCover

open CategoryTheory.Limits

/-! ### Two patches with independent local data

Two lemmas that used to open this block are gone, and their absence is the point.
`restrict_eq_of_density_eqOn` compared two *global* sections by their densities on a
patch, and `restrict_restrict` collapsed a restriction of a restriction; both were needed
only because the local sections were restrictions of global measures. §10's dictionary is
now built at an arbitrary open (**O21**), so `densityOn_injective` and `densityOn_res`
say the same things about sections that were never global, and the detour is unnecessary.
-/

/-- The mass profile the first patch reports. Its value at `right` is invisible
to that patch, and is chosen different from `rightW`'s so that the profile
cannot be mistaken for the glued state. -/
noncomputable def leftW : Site → ℝ≥0
  | Site.left  => 2
  | Site.mid   => 1
  | Site.right => 7

/-- The mass profile the second patch reports. It agrees with `leftW` at the
shared site `mid` and nowhere else. -/
noncomputable def rightW : Site → ℝ≥0
  | Site.left  => 5
  | Site.mid   => 1
  | Site.right => 3

noncomputable def patchW : Bool → Site → ℝ≥0
  | false => leftW
  | true  => rightW

/-- Non-degeneracy: the two patches carry genuinely different data. -/
theorem patchW_ne : patchW false ≠ patchW true := by
  intro h
  have := congrFun h Site.left
  norm_num [patchW, leftW, rightW] at this

/-- The agreement the class field asks for, as a computation: the profiles
coincide on every overlap, which for the two distinct patches is the single
site `mid`. -/
theorem patchW_agree (i j : Bool) (x : Site) (hx : x ∈ (patch i ⊓ patch j : Opens ↥Cortex)) :
    patchW i x = patchW j x := by
  obtain ⟨h1, h2⟩ := hx
  cases i <;> cases j <;> cases x <;> simp_all [patch, patchW, leftW, rightW]

/-- The cover. Nothing global is stored: each patch's section is built from that
patch's own profile, and `section_agrees_of_phase_eq` is discharged by
`patchW_agree`. -/
@[instance_reducible]
noncomputable def cortexSyncGlued : LocalSectionSynchronization Cortex where
  I := Bool
  cover := patch
  is_cover := patch_cover
  phase := fun _ => 0
  sync_to_section := fun i => sectionOfMassOn (patch i) (patchW i)
  section_agrees_of_phase_eq := by
    intro i j _
    refine densityOn_injective (fun x hx => ?_)
    rw [densityOn_res, densityOn_res, densityOn_sectionOfMassOn, densityOn_sectionOfMassOn]
    exact patchW_agree i j x hx

/-- The same uniform unit coupling as §4, at the same phase-`0` configuration. -/
@[instance_reducible]
noncomputable def cortexCoverGlued : ThermodynamicCover Cortex where
  toLocalSectionSynchronization := cortexSyncGlued
  I_fintype := inferInstanceAs (Fintype Bool)
  I_decidable := inferInstanceAs (DecidableEq Bool)
  A := fun _ _ => 1
  A_symm := fun _ _ => rfl
  A_pos := fun _ _ => one_pos
  thermodynamic_equilibrium := fun theta =>
    phase_locked_minimizes_potential (V := Bool)
      ⟨fun _ => 0, fun _ _ => 1, fun _ _ => rfl⟩ (fun _ _ => one_pos) theta

/-! ### Reading the local data -/

/-- **The rebuild changed the construction, not the object.** The patch-local section built
directly from `patchW i` on `patch i` is the very section the old shape produced by
restricting a global measure to that patch.

Recorded so that O21's refactor is auditable: every computation below would read the same
either way, and what changed is that no measure on all of `Cortex` is mentioned anywhere in
the instance. It also says the earlier shape was a special case rather than a different
witness, which is the same thing `LocalSectionSynchronization.ofInvariantMeasure` records
one level up. -/
theorem glued_section_eq_restrict (i : Bool) :
    cortexCoverGlued.sync_to_section i
      = (probabilityPresheaf Cortex).map (homOfLE (le_top : patch i ≤ ⊤)).op
          (sectionOfMass (patchW i)) := by
  refine densityOn_injective (fun x hx => ?_)
  show densityOn (sectionOfMassOn (patch i) (patchW i)) x hx = _
  rw [densityOn_sectionOfMassOn, densityOn_restrict, Phi_sectionOfMass]

theorem glued_density_left :
    densityOn (cortexCoverGlued.sync_to_section false) Site.left left_mem_patch_false = 2 := by
  show densityOn (sectionOfMassOn (patch false) (patchW false)) Site.left left_mem_patch_false = 2
  rw [densityOn_sectionOfMassOn]
  rfl

theorem glued_density_right :
    densityOn (cortexCoverGlued.sync_to_section true) Site.right right_mem_patch_true = 3 := by
  show densityOn (sectionOfMassOn (patch true) (patchW true)) Site.right right_mem_patch_true = 3
  rw [densityOn_sectionOfMassOn]
  rfl

theorem glued_overlap_mass_false :
    densityOn (cortexCoverGlued.sync_to_section false) Site.mid mid_mem_patch_false = 1 := by
  show densityOn (sectionOfMassOn (patch false) (patchW false)) Site.mid mid_mem_patch_false = 1
  rw [densityOn_sectionOfMassOn]
  rfl

theorem glued_overlap_mass_true :
    densityOn (cortexCoverGlued.sync_to_section true) Site.mid mid_mem_patch_true = 1 := by
  show densityOn (sectionOfMassOn (patch true) (patchW true)) Site.mid mid_mem_patch_true = 1
  rw [densityOn_sectionOfMassOn]
  rfl

/-- The overlap agreement, computed: both patches put mass `1` on the shared
site, from two separately defined profiles. This is what discharges
`section_agrees_of_phase_eq` for this instance — §4 and §13 got it from
functoriality instead, because their sections were restrictions of one measure
by construction. -/
theorem glued_overlap_agrees :
    densityOn (cortexCoverGlued.sync_to_section false) Site.mid mid_mem_patch_false
      = densityOn (cortexCoverGlued.sync_to_section true) Site.mid mid_mem_patch_true :=
  glued_overlap_mass_false.trans glued_overlap_mass_true.symm

/-! ### What the gluing produces -/

/-- The density the two patches force on any section that restricts to both:
each patch dictates the sites it contains. -/
noncomputable def gluedW : Site → ℝ≥0
  | Site.left  => 2
  | Site.mid   => 1
  | Site.right => 3

/-- A section restricting to the cover's local data has each patch's density on
that patch. -/
theorem glued_density_of (s : GlobalSection (X := Cortex))
    (hs : ∀ i : Bool, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : cortexCoverGlued.cover i ≤ ⊤)).op s = cortexCoverGlued.sync_to_section i)
    (i : Bool) (x : Site) (hx : x ∈ patch i) : density s x = patchW i x := by
  have hL : densityOn ((probabilityPresheaf Cortex).map
      (homOfLE (le_top : cortexCoverGlued.cover i ≤ ⊤)).op s) x hx = density s x := rfl
  rw [← hL, hs i]
  show densityOn (sectionOfMassOn (patch i) (patchW i)) x hx = _
  rw [densityOn_sectionOfMassOn]

/-- **The glued section, computed.** Any section restricting to both patches has
profile `(2, 1, 3)`. -/
theorem glued_eq_sectionOfMass (s : GlobalSection (X := Cortex))
    (hs : ∀ i : Bool, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : cortexCoverGlued.cover i ≤ ⊤)).op s = cortexCoverGlued.sync_to_section i) :
    s = sectionOfMass gluedW := by
  apply Phi_injective
  rw [Phi_sectionOfMass]
  funext x
  cases x
  · exact glued_density_of s hs false Site.left left_mem_patch_false
  · exact glued_density_of s hs false Site.mid mid_mem_patch_false
  · exact glued_density_of s hs true Site.right right_mem_patch_true

/-- Derivation 5 on this cover: the two patch-local sections glue to a unique
global section. -/
example : ∃! s : GlobalSection (X := Cortex),
    ∀ i : Bool, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : cortexCoverGlued.cover i ≤ ⊤)).op s
      = cortexCoverGlued.sync_to_section i :=
  @global_section_from_thermodynamics Cortex _ _ _ cortexCoverGlued

/-- The invariant measure the sheaf condition produces for this cover. -/
theorem cortexCoverGlued_invariantMeasure :
    cortexCoverGlued.invariantMeasure = sectionOfMass gluedW :=
  glued_eq_sectionOfMass _ (fun i => (cortexCoverGlued.sync_to_section_eq i).symm)

/-! ### …and it is not any of the data -/

/-- The glued state is not the first patch's profile. -/
theorem gluedW_ne_leftW : sectionOfMass gluedW ≠ sectionOfMass leftW := by
  intro h
  have := congrArg (fun u => density u Site.right) h
  rw [Phi_sectionOfMass, Phi_sectionOfMass] at this
  norm_num [gluedW, leftW] at this

/-- Nor the second's. -/
theorem gluedW_ne_rightW : sectionOfMass gluedW ≠ sectionOfMass rightW := by
  intro h
  have := congrArg (fun u => density u Site.left) h
  rw [Phi_sectionOfMass, Phi_sectionOfMass] at this
  norm_num [gluedW, rightW] at this

/-- Stronger than the inequality: the first patch's profile does not restrict to
the cover's local data at all — it fails on the *other* patch. So it is not a
competing solution that uniqueness has to rule out; it is not a solution. -/
theorem leftW_glues_nothing :
    ¬ (∀ i : Bool, (probabilityPresheaf Cortex).map
        (homOfLE (le_top : cortexCoverGlued.cover i ≤ ⊤)).op (sectionOfMass leftW)
      = cortexCoverGlued.sync_to_section i) := by
  intro h
  have := glued_density_of _ h true Site.right right_mem_patch_true
  rw [Phi_sectionOfMass] at this
  norm_num [leftW, patchW, rightW] at this

/-- The same for the second patch's profile. Between them, this and
`leftW_glues_nothing` say that the global state Derivation 5 returns was not
supplied to it. -/
theorem rightW_glues_nothing :
    ¬ (∀ i : Bool, (probabilityPresheaf Cortex).map
        (homOfLE (le_top : cortexCoverGlued.cover i ≤ ⊤)).op (sectionOfMass rightW)
      = cortexCoverGlued.sync_to_section i) := by
  intro h
  have := glued_density_of _ h false Site.left left_mem_patch_false
  rw [Phi_sectionOfMass] at this
  norm_num [leftW, patchW, rightW] at this

end GluedCover

/-! ## 17.1 A cover whose equilibrium is reached rather than assumed

  §17 produces a phase configuration; this section hands it to Derivation 5.

  Every `ThermodynamicCover` before this one — §4, §13, §14 — discharged
  `thermodynamic_equilibrium` the same way: its phase field was constant, or
  constant up to `2π`, *by construction*, and `phase_locked_minimizes_potential`
  then applied. The configuration Derivation 5 needs was therefore assumed on
  every instance, which is what open item **O20** recorded. Nothing was wrong
  with those witnesses; they simply could not answer the question of whether a
  system *arrives* at the configuration the class demands.

  `trioCover` answers it. Its phase field is `trioLimit`, which is not written
  down anywhere: it is the limit of `trioTraj`, a trajectory obtained from
  `is_kuramoto_trajectory_exists` and never solved, starting at the
  unsynchronised configuration `(0, 0, ½)` (`trioCover_start_not_locked`). Its
  `thermodynamic_equilibrium` field comes from
  `ThermodynamicCover.ofConvergentTrajectory`
  (`Phase5_EquilibriumBridge.lean`), which reads it off
  `kuramoto_tendsto_global_minimum`. The coupling matrix of the cover is the
  coupling matrix of `trioSys`, so the system whose equilibrium the class
  asserts and the system whose trajectory is run are the same system.

  **What is still assumed.** The cover's other physical hypothesis,
  `section_agrees_of_phase_eq`. It is discharged here the way §14 discharges it —
  by computing that the patch profiles agree on their overlaps — and no dynamics
  in this development bears on it. Derivation 5 rests on two physical
  hypotheses; on this witness one of them is now a theorem.

  **The local data is built §14's way, not §4's.** The three patches carry three
  different profiles, each constructed on its own open by `sectionOfMassOn`, so
  no measure on all of `Cortex` appears in the instance. The section they glue to
  has profile `(2, 1, 3)` and is none of them (`trioW_ne_glued`): the emergence
  reading of Derivation 5 and the derived-equilibrium reading hold of the same
  cover.

  **Geometry.** Three patches, `trioPatch i` being everything except the site
  `siteOf i`. Each pair overlaps in the remaining single site, so all three
  pairwise overlaps are nonempty and distinct — the profiles are constrained on
  every site by two patches at once, which is what pins the glued state to
  `(2, 1, 3)`.
-/

section TrioCover

/-- The trajectory of §17, named rather than existentially quantified, so that a
cover can be built on its limit. -/
noncomputable def trioTraj : ℝ → Fin 3 → ℝ :=
  (is_kuramoto_trajectory_exists trioSys 0 trioStart).choose

lemma trioTraj_traj : is_kuramoto_trajectory trioSys trioTraj :=
  (is_kuramoto_trajectory_exists trioSys 0 trioStart).choose_spec.1

lemma trioTraj_zero : trioTraj 0 = trioStart :=
  (is_kuramoto_trajectory_exists trioSys 0 trioStart).choose_spec.2

lemma trioTraj_small : 2 * potentialExcess trioSys (trioTraj 0) < 1 := by
  rw [trioTraj_zero]; exact trioStart_small

lemma trioTraj_init : ∀ i j, |trioTraj 0 i - trioTraj 0 j| ≤ Real.pi / 2 := by
  rw [trioTraj_zero]; exact trioStart_init

/-- **The configuration the trajectory reaches.** There is no formula for it:
`kuramoto_tendsto_global_minimum` builds it as `θ(0) + ∫₀^∞ θ̇`, and
three-oscillator Kuramoto has no closed-form solution. -/
noncomputable def trioLimit : Fin 3 → ℝ :=
  (kuramoto_tendsto_global_minimum trioSys trioSys_omega one_pos trioSys_coupling
    trioTraj trioTraj_traj trioTraj_small trioTraj_init).choose

lemma trioLimit_tendsto (i : Fin 3) :
    Tendsto (fun t => trioTraj t i) atTop (𝓝 (trioLimit i)) :=
  (kuramoto_tendsto_global_minimum trioSys trioSys_omega one_pos trioSys_coupling
    trioTraj trioTraj_traj trioTraj_small trioTraj_init).choose_spec.1 i

/-! ### The three patches -/

/-- The three sites, indexed by `Fin 3`. -/
def siteOf : Fin 3 → Site
  | 0 => Site.left
  | 1 => Site.mid
  | 2 => Site.right

/-- Patch `i` is everything except site `i`. Two distinct patches overlap in the
one remaining site, so every pairwise overlap is nonempty. -/
def trioPatch (i : Fin 3) : Opens ↥Cortex :=
  ⟨{x : Site | x ≠ siteOf i}, isOpen_discrete _⟩

theorem trioPatch_cover : iSup trioPatch = ⊤ := by
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  cases x
  · exact ⟨1, show Site.left ≠ Site.mid by decide⟩
  · exact ⟨0, show Site.mid ≠ Site.left by decide⟩
  · exact ⟨0, show Site.right ≠ Site.left by decide⟩

/-- The overlap of two distinct patches is the third site, and in particular is
nonempty — the gluing performed below is a genuine three-patch gluing. -/
theorem trioPatch_overlap_01 :
    (trioPatch 0 ⊓ trioPatch 1 : Opens ↥Cortex) = ⟨{Site.right}, isOpen_discrete _⟩ := by
  ext x; cases x <;> simp [trioPatch, siteOf]

/-! ### Three profiles that agree only where they must -/

/-- The profile every patch reports at every site it can see. -/
noncomputable def trioGlued : Site → ℝ≥0
  | Site.left => 2
  | Site.mid => 1
  | Site.right => 3

/-- What patch `i` reports at the one site it cannot see. Chosen different from
`trioGlued` there, so that no patch's profile is the global state. -/
noncomputable def trioHidden : Fin 3 → ℝ≥0
  | 0 => 7
  | 1 => 9
  | 2 => 5

/-- Patch `i`'s mass profile: the common profile everywhere it can see, and a
value of its own at the site it cannot. -/
noncomputable def trioW (i : Fin 3) (x : Site) : ℝ≥0 :=
  if x = siteOf i then trioHidden i else trioGlued x

/-- The agreement the class field asks for: on an overlap, neither patch is at
its blind site, so both report the common profile. -/
theorem trioW_agree (i j : Fin 3) (x : Site)
    (hx : x ∈ (trioPatch i ⊓ trioPatch j : Opens ↥Cortex)) : trioW i x = trioW j x := by
  obtain ⟨h1, h2⟩ := hx
  rw [trioW, trioW, ite_eq_right (h1 : x ≠ siteOf i), ite_eq_right (h2 : x ≠ siteOf j)]

/-- Non-degeneracy: no patch's profile is the common one. -/
theorem trioW_ne_glued (i : Fin 3) : trioW i ≠ trioGlued := by
  intro h
  have h1 := congrFun h (siteOf i)
  rw [trioW, ite_eq_left (rfl : siteOf i = siteOf i)] at h1
  fin_cases i <;> norm_num [trioHidden, trioGlued, siteOf] at h1

/-- …and the three profiles are pairwise different, so the cover carries three
genuinely independent readings. -/
theorem trioW_ne_01 : trioW 0 ≠ trioW 1 := by
  intro h
  have h1 := congrFun h Site.left
  rw [trioW, trioW, ite_eq_left (show Site.left = siteOf 0 from rfl),
    ite_eq_right (show Site.left ≠ siteOf 1 by decide)] at h1
  norm_num [trioHidden, trioGlued] at h1

/-! ### The cover -/

/-- Three patches, three profiles, phase field the limit of §17's trajectory.

Nothing global is stored: `sync_to_section i` is built on `trioPatch i` from
`trioW i` alone, and `section_agrees_of_phase_eq` is discharged by
`trioW_agree`, by computation rather than by functoriality. -/
@[instance_reducible]
noncomputable def trioSyncOf (ph : Fin 3 → ℝ) : LocalSectionSynchronization Cortex where
  I := Fin 3
  cover := trioPatch
  is_cover := trioPatch_cover
  phase := ph
  sync_to_section := fun i => sectionOfMassOn (trioPatch i) (trioW i)
  section_agrees_of_phase_eq := by
    intro i j _
    refine densityOn_injective (fun x hx => ?_)
    rw [densityOn_res, densityOn_res, densityOn_sectionOfMassOn, densityOn_sectionOfMassOn]
    exact trioW_agree i j x hx

/-- The local data of §17.1, at the phase field §17's trajectory reaches.

The phase field is a parameter (`trioSyncOf`) because §17.2 runs the same three
patches at a different coupling and therefore at a different limit. Nothing in
the overlap-agreement proof mentions the phase — the patches agree because their
profiles agree, not because they are synchronised — which is exactly why the
parameter costs nothing. -/
@[instance_reducible]
noncomputable def trioSync : LocalSectionSynchronization Cortex := trioSyncOf trioLimit

/-- **The witness.** A `ThermodynamicCover` whose `thermodynamic_equilibrium`
field is discharged by a convergence argument.

The coupling is `trioSys`'s, the phase field is the limit of `trioTraj`, and the
equilibrium hypothesis is read off `kuramoto_tendsto_global_minimum` through
`ThermodynamicCover.ofConvergentTrajectory`. No phase field here is constant by
construction, and no minimality is asserted of a configuration the instance was
placed at. -/
@[instance_reducible]
noncomputable def trioCover : ThermodynamicCover Cortex :=
  ThermodynamicCover.ofConvergentTrajectory trioSync
    (inferInstanceAs (Fintype (Fin 3))) (inferInstanceAs (DecidableEq (Fin 3)))
    (inferInstanceAs (Nonempty (Fin 3)))
    trioSys trioSys_omega one_pos trioSys_coupling
    trioTraj trioTraj_traj trioTraj_small trioTraj_init trioLimit_tendsto

/-! ### What the witness establishes -/

/-- The cover's phase field is the limit of a trajectory whose initial
configuration is **not** phase-locked. This is the whole point: the class field
is discharged about a state the system arrives at, not one it was placed at. -/
theorem trioCover_start_not_locked : ¬ is_phase_locked (trioTraj 0) := by
  rw [trioTraj_zero]; exact trioStart_not_locked

theorem trioCover_reached (i : Fin 3) :
    Tendsto (fun t => trioTraj t i) atTop (𝓝 (trioCover.phase i)) := trioLimit_tendsto i

/-- `ThermodynamicCover.phase_locked` on this instance. Unlike §4 and §13, where
lockedness held because the phase field was built locked, here it is a
*consequence* of the dynamics: the trajectory's excess tends to zero. -/
theorem trioCover_phase_locked : is_phase_locked trioCover.phase :=
  trioCover.phase_locked

/-- The equilibrium field itself, stated in the open. -/
theorem trioCover_equilibrium (theta : Fin 3 → ℝ) :
    kuramoto_potential_dynamic trioSys trioLimit
      ≤ kuramoto_potential_dynamic trioSys theta :=
  (kuramoto_limit_minimizes trioSys trioSys_omega one_pos trioSys_coupling
    trioTraj trioTraj_traj trioTraj_small trioTraj_init trioLimit trioLimit_tendsto).2 theta

/-- Derivation 5 on this cover: the three patch-local sections glue to a unique
global section. -/
example : ∃! s : GlobalSection (X := Cortex),
    ∀ i : Fin 3, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : trioCover.cover i ≤ ⊤)).op s
      = trioCover.sync_to_section i :=
  @global_section_from_thermodynamics Cortex _ _ _ trioCover

/-- Every patch reads the glued section as its own profile, on its own open. -/
theorem trioCover_density_of (s : GlobalSection (X := Cortex))
    (hs : ∀ i : Fin 3, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : trioCover.cover i ≤ ⊤)).op s = trioCover.sync_to_section i)
    (i : Fin 3) (x : Site) (hx : x ∈ trioPatch i) : density s x = trioW i x := by
  have hL : densityOn ((probabilityPresheaf Cortex).map
      (homOfLE (le_top : trioCover.cover i ≤ ⊤)).op s) x hx = density s x := rfl
  rw [← hL, hs i]
  show densityOn (sectionOfMassOn (trioPatch i) (trioW i)) x hx = _
  rw [densityOn_sectionOfMassOn]

/-- **The glued state, computed**: profile `(2, 1, 3)`, which by `trioW_ne_glued`
is none of the three profiles the instance carries. -/
theorem trioCover_glued_eq (s : GlobalSection (X := Cortex))
    (hs : ∀ i : Fin 3, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : trioCover.cover i ≤ ⊤)).op s = trioCover.sync_to_section i) :
    s = sectionOfMass trioGlued := by
  apply Phi_injective
  rw [Phi_sectionOfMass]
  funext x
  have key : ∀ (i : Fin 3) (hx : x ∈ trioPatch i), density s x = trioGlued x := by
    intro i hx
    rw [trioCover_density_of s hs i x hx, trioW, ite_eq_right (hx : x ≠ siteOf i)]
  cases x
  · exact key 1 (show Site.left ≠ Site.mid by decide)
  · exact key 0 (show Site.mid ≠ Site.left by decide)
  · exact key 0 (show Site.right ≠ Site.left by decide)

/-- The invariant measure Derivation 5 produces for this cover. -/
theorem trioCover_invariantMeasure :
    trioCover.invariantMeasure = sectionOfMass trioGlued :=
  trioCover_glued_eq _ (fun i => (trioCover.sync_to_section_eq i).symm)

/-! ### 17.2 The same three sites at the chain's coupling

`Chain.E78` asks for a cover that is *reached* by a relaxation whose coupling is
at least the mean-field constant `K` the coherent regime names. The joint witness
runs at `K = 3`, and `trioCover` runs at unit coupling, so it does not answer.

`trioCover3` is the same construction at coupling `3`. The numerical content is
unchanged and this is not a coincidence: the excess and the threshold both scale
with the coupling, so `2 · excess < a` reduces to `cos ½ > ¾` at every coupling
strength. The initial data, the arc condition and the profiles are §17's.
-/

/-- Three sites at the mean-field coupling of the chain's witness. -/
noncomputable def trioSys3 : KuramotoSystem (Fin 3) where
  omega := fun _ => 0
  A := fun _ _ => 3
  symm := fun _ _ => rfl

lemma trioSys3_omega : ∀ i, trioSys3.omega i = 0 := fun _ => rfl

lemma trioSys3_coupling : ∀ i j, (3:ℝ) ≤ trioSys3.A i j := fun _ _ => le_rfl

/-- The excess of `(0, 0, ½)` at coupling `3`: three times §17's, since every
pair contributes three times as much. -/
lemma trioStart_excess3 :
    potentialExcess trioSys3 trioStart = 6 * (1 - Real.cos (1/2)) := by
  rw [potentialExcess_eq]
  simp only [trioSys3, trioStart, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [show (0:ℝ) - 0 = 0 by ring, show (1:ℝ)/2 - 0 = 1/2 by ring,
    show (0:ℝ) - 1/2 = -(1/2) by ring, show (1:ℝ)/2 - 1/2 = 0 by ring]
  rw [Real.cos_neg, Real.cos_zero]
  ring

/-- …and it is still below the threshold, on the same estimate `cos ½ > ¾`. The
coupling cancels: at strength `c` the condition reads `2 · c · 2(1 − cos ½) < c`.
-/
lemma trioStart_small3 : 2 * potentialExcess trioSys3 trioStart < 3 := by
  rw [trioStart_excess3]
  linarith [cos_half_gt]

/-- The trajectory at coupling `3`, named rather than existentially quantified. -/
noncomputable def trioTraj3 : ℝ → Fin 3 → ℝ :=
  (is_kuramoto_trajectory_exists trioSys3 0 trioStart).choose

lemma trioTraj3_traj : is_kuramoto_trajectory trioSys3 trioTraj3 :=
  (is_kuramoto_trajectory_exists trioSys3 0 trioStart).choose_spec.1

lemma trioTraj3_zero : trioTraj3 0 = trioStart :=
  (is_kuramoto_trajectory_exists trioSys3 0 trioStart).choose_spec.2

lemma trioTraj3_small : 2 * potentialExcess trioSys3 (trioTraj3 0) < 3 := by
  rw [trioTraj3_zero]; exact trioStart_small3

lemma trioTraj3_init : ∀ i j, |trioTraj3 0 i - trioTraj3 0 j| ≤ Real.pi / 2 := by
  rw [trioTraj3_zero]; exact trioStart_init

/-- The configuration it reaches. As at unit coupling, there is no formula for
it. -/
noncomputable def trioLimit3 : Fin 3 → ℝ :=
  (kuramoto_tendsto_global_minimum trioSys3 trioSys3_omega (by norm_num) trioSys3_coupling
    trioTraj3 trioTraj3_traj trioTraj3_small trioTraj3_init).choose

lemma trioLimit3_tendsto (i : Fin 3) :
    Tendsto (fun t => trioTraj3 t i) atTop (𝓝 (trioLimit3 i)) :=
  (kuramoto_tendsto_global_minimum trioSys3 trioSys3_omega (by norm_num) trioSys3_coupling
    trioTraj3 trioTraj3_traj trioTraj3_small trioTraj3_init).choose_spec.1 i

/-- **The cover the chain's n7 → n8 edge asks for.** Coupling `3` everywhere,
phase field the limit of a trajectory from unsynchronised initial data, and
`thermodynamic_equilibrium` read off that convergence. -/
@[instance_reducible]
noncomputable def trioCover3 : ThermodynamicCover Cortex :=
  ThermodynamicCover.ofConvergentTrajectory (trioSyncOf trioLimit3)
    (inferInstanceAs (Fintype (Fin 3))) (inferInstanceAs (DecidableEq (Fin 3)))
    (inferInstanceAs (Nonempty (Fin 3)))
    trioSys3 trioSys3_omega (by norm_num) trioSys3_coupling
    trioTraj3 trioTraj3_traj trioTraj3_small trioTraj3_init trioLimit3_tendsto

/-- **It is reached, at coupling `3`.** This is what `Chain.E78` consumes: a
cover whose patches are coupled at least as strongly as the mean field, and
whose equilibrium configuration is arrived at rather than assumed. -/
theorem trioCover3_reachedByRelaxation :
    trioCover3.IsReachedByRelaxation 3 :=
  ThermodynamicCover.ofConvergentTrajectory_isReachedByRelaxation (X := Cortex)
    (trioSyncOf trioLimit3) (inferInstanceAs (Fintype (Fin 3)))
    (inferInstanceAs (DecidableEq (Fin 3))) (inferInstanceAs (Nonempty (Fin 3)))
    trioSys3 trioSys3_omega (by norm_num) trioSys3_coupling
    trioTraj3 trioTraj3_traj trioTraj3_small trioTraj3_init trioLimit3_tendsto

/-- The initial configuration is not phase-locked at this coupling either: it is
the same configuration. -/
theorem trioCover3_start_not_locked : ¬ is_phase_locked (trioTraj3 0) := by
  rw [trioTraj3_zero]; exact trioStart_not_locked

/-- **The fence for the coupling floor.** `trioCover` is a perfectly good cover
whose equilibrium is reached, and it does *not* satisfy the predicate at `3`:
unit coupling is not mean-field coupling. Without this, `E78`'s floor could be
read as decoration. -/
theorem trioCover_not_reachedByRelaxation_three :
    ¬ trioCover.IsReachedByRelaxation 3 := by
  intro h
  have h3 : (3:ℝ) ≤ 1 := h.2.1 (0 : Fin 3) (0 : Fin 3)
  linarith

end TrioCover

/-! ## 20. The overlap-agreement hypothesis: what it says, and what it forbids

`LocalSectionSynchronization.section_agrees_of_phase_eq` is Derivation 5's second
physical hypothesis and the one no dynamics in this development bears on. It is
ranked second in `tasks/todo.md` and stays a hypothesis; what this section adds is
a precise reading of it and a check that it is a restriction rather than a
formality.

**The reading.** `restrict_eq_iff_densityOn_eqOn` turns the categorical statement
— two patch-local sections have the same restriction to the overlap — into the
pointwise one: *the two patches assign the same mass to every site they share*.
Nothing is hidden in the sheafification. So the hypothesis says exactly this: two
patches whose phases agree modulo `2π` carry the same local density where they
overlap.

**What it forbids.** `overlap_agreement_fails` exhibits `§4`'s two-patch cover
carrying a single phase and two profiles that differ at the shared site. Every
other requirement of `LocalSectionSynchronization` is met by that data — the
patches cover `Cortex` (`patch_cover`), the sections are honest sections over
their patches — and the class field is *false* of it. Synchronised patches that
disagree about their shared region are therefore excluded by an assumption, not
by the mathematics: it is the assumption that phase-locking carries local content
with it, which is the framework's claim and not its theorem.

Contrast `§17.1`. There the three profiles are pairwise different
(`trioW_ne_01`) and the field still holds, because they differ only where the
patches do not meet. Agreement on overlaps does not mean the patches carry the
same content — that is the room in which `F2`'s content question lives — it means
they do not contradict each other about the region they share.
-/

section OverlapAgreementReading

/-- **The categorical condition, read pointwise.** Two sections over two opens
have the same restriction to the overlap exactly when their densities agree at
every site of the overlap.

Both directions are the density dictionary of `§14`: `densityOn_res` says
restriction moves no mass, and `densityOn_injective` says a section over an open
is determined by its density there. -/
theorem restrict_eq_iff_densityOn_eqOn {U V : Opens ↥Cortex}
    (s : (probabilityPresheaf Cortex).obj (op U))
    (t : (probabilityPresheaf Cortex).obj (op V)) :
    (probabilityPresheaf Cortex).map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s
        = (probabilityPresheaf Cortex).map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op t
      ↔ ∀ x (hx : x ∈ (U ⊓ V : Opens ↥Cortex)),
          densityOn s x hx.1 = densityOn t x hx.2 := by
  constructor
  · intro h x hx
    have h' := congrArg (fun u => densityOn u x hx) h
    rwa [densityOn_res, densityOn_res] at h'
  · intro h
    refine densityOn_injective fun x hx => ?_
    rw [densityOn_res, densityOn_res]
    exact h x hx

/-- The two patch-local sections of the fence: patch `false` reports mass `1`
everywhere it can see, patch `true` reports mass `2`. -/
noncomputable def disagreeingSection (i : Bool) :
    (probabilityPresheaf Cortex).obj (op (patch i)) :=
  sectionOfMassOn (patch i) (fun _ => if i then 2 else 1)

/-- **The hypothesis is a restriction.** `§4`'s cover, one phase for both patches,
and two profiles that differ at the site the patches share: the class field
`section_agrees_of_phase_eq` is *false* of this data.

Everything else a `LocalSectionSynchronization` asks for is present — the patches
cover the substrate and each section is a section over its own patch — so what
this rules out is exactly the assumption, and nothing else. Derivation 5's second
physical hypothesis is therefore doing work: it excludes synchronised patches
that disagree about their shared region, and no theorem here excludes them. -/
theorem overlap_agreement_fails :
    ¬ (∀ i j : Bool, Real.cos ((fun _ : Bool => (0:ℝ)) i - (fun _ : Bool => (0:ℝ)) j) = 1 →
        (probabilityPresheaf Cortex).map
            (homOfLE (inf_le_left : patch i ⊓ patch j ≤ patch i)).op (disagreeingSection i)
          = (probabilityPresheaf Cortex).map
            (homOfLE (inf_le_right : patch i ⊓ patch j ≤ patch j)).op (disagreeingSection j)) := by
  intro h
  have hmid : Site.mid ∈ (patch false ⊓ patch true : Opens ↥Cortex) :=
    ⟨show Site.mid ≠ Site.right by decide, show Site.mid ≠ Site.left by decide⟩
  have hagree := (restrict_eq_iff_densityOn_eqOn _ _).1
    (h false true (by simp)) Site.mid hmid
  rw [disagreeingSection, disagreeingSection, densityOn_sectionOfMassOn,
    densityOn_sectionOfMassOn] at hagree
  exact absurd hagree (by norm_num)

/-- The cover in the fence is a genuine cover, so the failure above is not a
failure to be a cover. -/
theorem disagreeing_cover : iSup patch = ⊤ := patch_cover

end OverlapAgreementReading

/-! ## 21. Approximate overlap agreement: selection, its constant, and its cliff

§20 reads the exact hypothesis and shows that it forbids something. This section
asks the next question: if the patches agree only to within `ε`, what is left?

The general answer is `Phase5_GlobalSection`'s `ApproximateGluing` namespace —
Route A of the `tasks/todo.md` item, selection by a partition of unity, in the
uniform metric on site masses. This section is its witness on the same three
patches §17.1 glues, and the reason the bound is not vacuous.

* **The family.** `apxW ε` is §17.1's data with patch `0` reporting `ε` more
  mass than the others at every site it can see. Every pairwise overlap is
  therefore off by exactly `ε` or by nothing, which is `apxW_compatible`.
* **The positive half.** `lowW` and `highW` are two partitions subordinate to the
  same cover — every site is assigned to the lowest, respectively the highest,
  indexed patch that contains it. They select global states at distance exactly
  `ε` (`apx_select_dist`), so the constant `C(N) = 1` of `select_dist_le` is
  attained at cover multiplicity two and cannot be improved.
* **The negative half.** For every positive `ε` that same family has no exact
  global section at all (`apx_no_global_section`): patches `0` and `1` both see
  `right` and disagree there. Approximate compatibility is therefore a strictly
  weaker hypothesis than the sheaf condition, and what selection returns is a
  choice among states none of which glues the data.
* **The two regressions.** `apxW_not_compatible_zero` and
  `apxSection_overlap_fails` keep the approximate family from being passed off
  as an exact one — it fails the class field of §20 exactly as the fence there
  does. `chainW` agrees to `ε` on the overlaps `(0,1)` and `(1,2)` and not on
  `(0,2)`; its selections are `2ε` apart (`chainW_select_dist_gt`), so checking
  a spanning subfamily of the overlaps does not give the conclusion.
* **The exact case is not disturbed.** `trioW_compatible` records §17.1's family
  at `ε = 0`, and `trioW_glue_unique` recovers its unique glued profile from
  the selection theorem. What the sheaf condition asks of a fixed family is
  pairwise agreement of the masses on overlaps, and nothing here weakens
  `sheaf_glue_unique`, `ThermodynamicCover` or the chain.
* **What an interpretation would additionally need.** `totalMass_apx_dist_le`
  is the selection dependence of a readout with a supplied Lipschitz constant.
  The `2ε` in `totalMass_apx_dist` shows the readout does move with the choice,
  so this is a resolution condition and not a triviality. It chooses no decoder
  and identifies nothing with content.

The state space here is finite spatial mass profiles, where restriction is
functorial. Nothing in this section produces agreement, selects the cover or
the weights, or extends to content marginals.
-/

section ApproximateOverlap

open ApproximateGluing

/-- The three patches of §17.1 as bare sets of sites, which is what the finite
selection theorems are stated over. -/
def trioSet (i : Fin 3) : Set Site := {x : Site | x ≠ siteOf i}

theorem mem_trioSet {i : Fin 3} {x : Site} : x ∈ trioSet i ↔ x ≠ siteOf i := Iff.rfl

theorem trioSet_eq_patch (i : Fin 3) : trioSet i = (trioPatch i : Set Site) := rfl

theorem right_mem_trioSet_zero : Site.right ∈ trioSet 0 := show Site.right ≠ Site.left by decide

theorem right_mem_trioSet_one : Site.right ∈ trioSet 1 := show Site.right ≠ Site.mid by decide

theorem mid_mem_trioSet_zero : Site.mid ∈ trioSet 0 := show Site.mid ≠ Site.left by decide

theorem mid_mem_trioSet_two : Site.mid ∈ trioSet 2 := show Site.mid ≠ Site.right by decide

/-! ### An `ε`-compatible family -/

/-- §17.1's data with one patch reporting `ε` more mass everywhere it can see.
The blind-site values are untouched, so this is a perturbation of the overlap
agreement alone. -/
noncomputable def apxW (ε : ℝ≥0) (i : Fin 3) (x : Site) : ℝ≥0 :=
  if x = siteOf i then trioHidden i else trioGlued x + (if i = 0 then ε else 0)

theorem apxW_off (ε : ℝ≥0) (i : Fin 3) {x : Site} (hx : x ≠ siteOf i) :
    apxW ε i x = trioGlued x + (if i = 0 then ε else 0) := ite_eq_right hx

theorem apxW_zero_right (ε : ℝ≥0) : apxW ε 0 Site.right = trioGlued Site.right + ε := by
  simp [apxW, siteOf]

theorem apxW_one_right (ε : ℝ≥0) : apxW ε 1 Site.right = trioGlued Site.right := by
  simp [apxW, siteOf]

/-- The two patches that both see `right` differ there by exactly `ε`: the family
is off by the full tolerance on one of its three overlaps. -/
theorem apxW_right_dist (ε : ℝ≥0) :
    dist (apxW ε 0 Site.right) (apxW ε 1 Site.right) = (ε : ℝ) := by
  rw [apxW_zero_right, apxW_one_right, NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_left,
    abs_of_nonneg ε.coe_nonneg]

/-- **The family is `ε`-compatible.** On an overlap neither patch is at its blind
site, so the two readings differ by the offset of at most `ε` carried by patch
`0`. This is a hypothesis about supplied data; no dynamics produces it. -/
theorem apxW_compatible (ε : ℝ≥0) : Compatible trioSet (apxW ε) ε := by
  intro i j
  refine (profileDist_le_iff ε.coe_nonneg).2 ?_
  rintro x ⟨hi, hj⟩
  rw [apxW_off ε i hi, apxW_off ε j hj, NNReal.dist_eq]
  push_cast
  split_ifs <;> simp [abs_of_nonneg, ε.coe_nonneg]

/-! ### Two partitions of unity, and the distance between what they select -/

/-- The lowest-indexed patch containing a site: `mid` and `right` go to patch
`0`, `left` to patch `1`. -/
def lowIdx : Site → Fin 3
  | Site.left => 1
  | Site.mid => 0
  | Site.right => 0

/-- The highest-indexed patch containing a site: `left` and `mid` go to patch
`2`, `right` to patch `1`. -/
def highIdx : Site → Fin 3
  | Site.left => 2
  | Site.mid => 2
  | Site.right => 1

/-- Selection by a site-to-patch assignment: unit weight on the assigned patch.
A partition of unity is more general; these two are enough to show that the
`ε` of `select_dist_le` is attained. -/
noncomputable def pickW (p : Site → Fin 3) : Fin 3 → Site → ℝ≥0 :=
  fun i x => if p x = i then 1 else 0

noncomputable def lowW : Fin 3 → Site → ℝ≥0 := pickW lowIdx

noncomputable def highW : Fin 3 → Site → ℝ≥0 := pickW highIdx

theorem select_pickW (p : Site → Fin 3) (s : Fin 3 → Site → ℝ≥0) (x : Site) :
    select (pickW p) s x = s (p x) x := by
  simp [select, pickW, Finset.sum_ite_eq]

theorem pickW_isPartition {p : Site → Fin 3} (hp : ∀ x, x ∈ trioSet (p x)) :
    IsPartition trioSet (pickW p) := by
  refine ⟨fun i x hx => ?_, fun x => ?_⟩
  · refine ite_eq_right fun h => hx ?_
    rw [← h]
    exact hp x
  · simp [pickW, Finset.sum_ite_eq]

theorem lowW_isPartition : IsPartition trioSet lowW :=
  pickW_isPartition fun x => by cases x <;> exact mem_trioSet.2 (by decide)

theorem highW_isPartition : IsPartition trioSet highW :=
  pickW_isPartition fun x => by cases x <;> exact mem_trioSet.2 (by decide)

theorem select_lowW_apxW (ε : ℝ≥0) (x : Site) :
    select lowW (apxW ε) x = trioGlued x + (if x = Site.left then 0 else ε) := by
  rw [lowW, select_pickW]
  cases x <;> simp [apxW, lowIdx, siteOf, trioGlued]

theorem select_highW_apxW (ε : ℝ≥0) (x : Site) :
    select highW (apxW ε) x = trioGlued x := by
  rw [highW, select_pickW]
  cases x <;> simp [apxW, highIdx, siteOf, trioGlued]

/-- **The `ε` of the selection theorem is attained.** Two partitions subordinate
to the same three patches select profiles at uniform distance exactly `ε`, so
`C(N) = 1` is sharp here and no smaller constant is available at multiplicity
two. -/
theorem apx_select_dist (ε : ℝ≥0) :
    dist (select lowW (apxW ε)) (select highW (apxW ε)) = (ε : ℝ) := by
  refine le_antisymm (select_dist_le lowW_isPartition highW_isPartition (apxW_compatible ε)) ?_
  have h := dist_le_pi_dist (select lowW (apxW ε)) (select highW (apxW ε)) Site.mid
  rwa [select_lowW_apxW, select_highW_apxW,
    ite_eq_right (by decide : ¬ Site.mid = Site.left), NNReal.dist_eq, NNReal.coe_add,
    add_sub_cancel_left, abs_of_nonneg ε.coe_nonneg] at h

/-! ### The same data in the probability sheaf -/

/-- Patch `i`'s reading, as an actual section over that patch. -/
noncomputable def apxSection (ε : ℝ≥0) (i : Fin 3) :
    (probabilityPresheaf Cortex).obj (op (trioPatch i)) :=
  sectionOfMassOn (trioPatch i) (apxW ε i)

/-- The global state a partition selects, as an actual global section. -/
noncomputable def apxSelectSection (w : Fin 3 → Site → ℝ≥0) (ε : ℝ≥0) :
    GlobalSection (X := Cortex) :=
  sectionOfMass (select w (apxW ε))

/-- The selection bound, transported to the sheaf's own metric. -/
theorem apxSelectSection_dist_le (ε : ℝ≥0) :
    dist (apxSelectSection lowW ε) (apxSelectSection highW ε) ≤ (ε : ℝ) := by
  rw [apxSelectSection, apxSelectSection, gs_dist_sectionOfMass]
  exact select_dist_le lowW_isPartition highW_isPartition (apxW_compatible ε)

/-- **Approximate compatibility does not glue.** For every positive `ε` no global
section restricts to this family: patches `0` and `1` both see `right` and report
masses differing by `ε` there. Selection replaces a gluing that does not exist,
and `sheaf_glue_unique` keeps its exact hypothesis. -/
theorem apx_no_global_section (ε : ℝ≥0) (hε : 0 < ε) :
    ¬ ∃ s : GlobalSection (X := Cortex), ∀ i,
        (probabilityPresheaf Cortex).map (homOfLE (le_top : trioPatch i ≤ ⊤)).op s
          = apxSection ε i := by
  rintro ⟨s, hs⟩
  have hr0 : Site.right ∈ trioPatch 0 := right_mem_trioSet_zero
  have hr1 : Site.right ∈ trioPatch 1 := right_mem_trioSet_one
  have h0 : density s Site.right = apxW ε 0 Site.right := by
    rw [← densityOn_restrict (le_top : trioPatch 0 ≤ ⊤) s Site.right hr0, hs 0]
    exact densityOn_sectionOfMassOn _ _ _ hr0
  have h1 : density s Site.right = apxW ε 1 Site.right := by
    rw [← densityOn_restrict (le_top : trioPatch 1 ≤ ⊤) s Site.right hr1, hs 1]
    exact densityOn_sectionOfMassOn _ _ _ hr1
  rw [apxW_zero_right] at h0
  rw [apxW_one_right] at h1
  have hgap : (ε : ℝ) = 0 := by
    have hz := congrArg NNReal.toReal (h0.symm.trans h1)
    push_cast at hz
    linarith
  exact hε.ne' (by exact_mod_cast hgap)

/-! ### Two regressions -/

/-- **Approximate agreement is not exact agreement.** The tolerance cannot be
dropped to zero for any positive `ε`. -/
theorem apxW_not_compatible_zero (ε : ℝ≥0) (hε : 0 < ε) :
    ¬ Compatible trioSet (apxW ε) 0 := by
  intro h
  have h01 := h 0 1
  rw [NNReal.coe_zero] at h01
  have h' := (profileDist_le_iff le_rfl).1 h01 Site.right
    ⟨right_mem_trioSet_zero, right_mem_trioSet_one⟩
  rw [apxW_right_dist] at h'
  exact absurd h' (not_le.2 (by exact_mod_cast hε))

/-- …and the class field of §20 is false of it, so the approximate family cannot
be presented to `LocalSectionSynchronization` as synchronised local data. -/
theorem apxSection_overlap_fails (ε : ℝ≥0) (hε : 0 < ε) :
    ¬ ∀ i j : Fin 3,
        (probabilityPresheaf Cortex).map
            (homOfLE (inf_le_left : trioPatch i ⊓ trioPatch j ≤ trioPatch i)).op (apxSection ε i)
          = (probabilityPresheaf Cortex).map
            (homOfLE (inf_le_right : trioPatch i ⊓ trioPatch j ≤ trioPatch j)).op
              (apxSection ε j) := by
  intro h
  have hr : Site.right ∈ (trioPatch 0 ⊓ trioPatch 1 : Opens ↥Cortex) :=
    ⟨right_mem_trioSet_zero, right_mem_trioSet_one⟩
  have hagree := (restrict_eq_iff_densityOn_eqOn _ _).1 (h 0 1) Site.right hr
  rw [apxSection, apxSection, densityOn_sectionOfMassOn, densityOn_sectionOfMassOn,
    apxW_zero_right, apxW_one_right] at hagree
  have hgap : (ε : ℝ) = 0 := by
    have hz := congrArg NNReal.toReal hagree
    push_cast at hz
    linarith
  exact hε.ne' (by exact_mod_cast hgap)

/-- A family whose discrepancy sits at `mid`, the one site patch `1` cannot see.
The overlaps `(0,1)` and `(1,2)` are therefore exact, and they span the cover's
nerve without touching the overlap `(0,2)` where the data disagree. -/
noncomputable def chainW (ε : ℝ≥0) (i : Fin 3) (x : Site) : ℝ≥0 :=
  if x = siteOf i then trioHidden i
  else trioGlued x + (if i = 0 ∧ x = Site.mid then 2 * ε else 0)

/-- The two adjacent overlaps agree exactly, hence to within any tolerance. -/
theorem chainW_adjacent_ok (ε : ℝ≥0) :
    profileDist (trioSet 0 ∩ trioSet 1) (chainW ε 0) (chainW ε 1) ≤ (ε : ℝ) ∧
      profileDist (trioSet 1 ∩ trioSet 2) (chainW ε 1) (chainW ε 2) ≤ (ε : ℝ) := by
  constructor <;>
    refine (profileDist_le_iff ε.coe_nonneg).2 ?_ <;>
    · rintro x ⟨hi, hj⟩
      revert hi hj
      cases x <;> simp [chainW, trioSet, siteOf, trioGlued, ε.coe_nonneg]

theorem chainW_zero_mid (ε : ℝ≥0) : chainW ε 0 Site.mid = trioGlued Site.mid + 2 * ε := by
  simp [chainW, siteOf]

theorem chainW_two_mid (ε : ℝ≥0) : chainW ε 2 Site.mid = trioGlued Site.mid := by
  simp [chainW, siteOf]

/-- **Checking a spanning subfamily of the overlaps is not checking the family.**
The remaining overlap is off by `2ε`, so the hypothesis of `select_dist_le` fails
here even though every adjacent pair passes. -/
theorem chainW_not_compatible (ε : ℝ≥0) (hε : 0 < ε) : ¬ Compatible trioSet (chainW ε) ε := by
  intro h
  have h' := (profileDist_le_iff ε.coe_nonneg).1 (h 0 2) Site.mid
    ⟨mid_mem_trioSet_zero, mid_mem_trioSet_two⟩
  rw [chainW_zero_mid, chainW_two_mid, NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_left,
    abs_of_nonneg (by positivity)] at h'
  have hpos : (0 : ℝ) < ε := by exact_mod_cast hε
  push_cast at h'
  linarith

theorem select_lowW_chainW (ε : ℝ≥0) (x : Site) :
    select lowW (chainW ε) x = trioGlued x + (if x = Site.mid then 2 * ε else 0) := by
  rw [lowW, select_pickW]
  cases x <;> simp [chainW, lowIdx, siteOf, trioGlued]

theorem select_highW_chainW (ε : ℝ≥0) (x : Site) :
    select highW (chainW ε) x = trioGlued x := by
  rw [highW, select_pickW]
  cases x <;> simp [chainW, highIdx, siteOf, trioGlued]

/-- …and the conclusion fails with it: the two selections are `2ε` apart. -/
theorem chainW_select_dist_gt (ε : ℝ≥0) (hε : 0 < ε) :
    (ε : ℝ) < dist (select lowW (chainW ε)) (select highW (chainW ε)) := by
  have h := dist_le_pi_dist (select lowW (chainW ε)) (select highW (chainW ε)) Site.mid
  rw [select_lowW_chainW, select_highW_chainW, ite_eq_left rfl, NNReal.dist_eq, NNReal.coe_add,
    add_sub_cancel_left, abs_of_nonneg (by positivity)] at h
  have hpos : (0 : ℝ) < ε := by exact_mod_cast hε
  push_cast at h
  linarith

/-! ### The exact case, unchanged -/

/-- §17.1's family is the `ε = 0` case: exact pairwise agreement of the masses on
every overlap, which is what the sheaf condition asks of a fixed family. -/
theorem trioW_compatible : Compatible trioSet trioW 0 := by
  intro i j
  refine (profileDist_le_iff le_rfl).2 ?_
  rintro x ⟨hi, hj⟩
  rw [trioW_agree i j x ⟨hi, hj⟩]
  simp

theorem select_trioW : select lowW trioW = trioGlued := by
  funext x
  rw [lowW, select_pickW]
  cases x <;> simp [trioW, lowIdx, siteOf, trioGlued]

/-- **Zero tolerance recovers exact gluing**, on the witness that already had it:
the selection is the glued profile of §17.1 and is the only profile fitting all
three patches. -/
theorem trioW_glue_unique : ∃! g : Site → ℝ≥0, ∀ i, Set.EqOn g (trioW i) (trioSet i) :=
  select_glue_unique lowW_isPartition trioW_compatible

/-! ### A readout with a supplied Lipschitz constant -/

/-- Total mass on the substrate: a readout of the selected state, not a model of
anything read out by cortex. -/
noncomputable def totalMass (f : Site → ℝ≥0) : ℝ :=
  (f Site.left : ℝ) + f Site.mid + f Site.right

theorem totalMass_lipschitz : LipschitzWith 3 totalMass := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  have h : ∀ x : Site, |(f x : ℝ) - g x| ≤ dist f g := fun x => by
    rw [← NNReal.dist_eq]; exact dist_le_pi_dist f g x
  have hl := h Site.left
  have hm := h Site.mid
  have hr := h Site.right
  have habs := abs_add_three ((f Site.left : ℝ) - g Site.left)
    ((f Site.mid : ℝ) - g Site.mid) ((f Site.right : ℝ) - g Site.right)
  rw [Real.dist_eq, totalMass, totalMass,
    show ((3 : ℝ≥0) : ℝ) = 3 by norm_num,
    show (f Site.left : ℝ) + f Site.mid + f Site.right
        - ((g Site.left : ℝ) + g Site.mid + g Site.right)
        = ((f Site.left : ℝ) - g Site.left) + ((f Site.mid : ℝ) - g Site.mid)
          + ((f Site.right : ℝ) - g Site.right) by ring]
  linarith

/-- **The readout inherits the selection bound.** Its variation across partitions
is at most `L ε`. An interpretation at resolution `δ` must supply the decoder and
argue `L ε ≤ δ`; this theorem supplies neither. -/
theorem totalMass_apx_dist_le (ε : ℝ≥0) :
    dist (totalMass (select lowW (apxW ε))) (totalMass (select highW (apxW ε))) ≤ 3 * (ε : ℝ) := by
  have h := feature_dist_le totalMass_lipschitz lowW_isPartition highW_isPartition
    (apxW_compatible ε)
  rwa [show ((3 : ℝ≥0) : ℝ) = 3 by norm_num] at h

/-- …and it is not a triviality: the readout genuinely moves with the choice of
partition, by `2ε` out of the `3ε` the Lipschitz bound permits. -/
theorem totalMass_apx_dist (ε : ℝ≥0) :
    dist (totalMass (select lowW (apxW ε))) (totalMass (select highW (apxW ε))) = 2 * (ε : ℝ) := by
  rw [totalMass, totalMass, select_lowW_apxW, select_lowW_apxW, select_lowW_apxW,
    select_highW_apxW, select_highW_apxW, select_highW_apxW,
    ite_eq_left rfl, ite_eq_right (by decide : ¬ Site.mid = Site.left),
    ite_eq_right (by decide : ¬ Site.right = Site.left), Real.dist_eq]
  push_cast
  rw [show (trioGlued Site.left : ℝ) + 0 + ((trioGlued Site.mid : ℝ) + ε)
      + ((trioGlued Site.right : ℝ) + ε)
      - ((trioGlued Site.left : ℝ) + (trioGlued Site.mid : ℝ) + (trioGlued Site.right : ℝ))
      = 2 * ε by ring]
  exact abs_of_nonneg (by positivity)


#print axioms ApproximateGluing.select_close
#print axioms ApproximateGluing.select_dist_le
#print axioms ApproximateGluing.approximate_diameter_le
#print axioms ApproximateGluing.select_glue_unique
#print axioms ApproximateGluing.feature_dist_le
#print axioms apxW_compatible
#print axioms apx_select_dist
#print axioms apxSelectSection_dist_le
#print axioms apx_no_global_section
#print axioms apxW_not_compatible_zero
#print axioms apxSection_overlap_fails
#print axioms chainW_not_compatible
#print axioms chainW_select_dist_gt
#print axioms trioW_glue_unique
#print axioms totalMass_apx_dist_le
#print axioms totalMass_apx_dist

end ApproximateOverlap

end Examples
end PhysicsOfConsciousness
