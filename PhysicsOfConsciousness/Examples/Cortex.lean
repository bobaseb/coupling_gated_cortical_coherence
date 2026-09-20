/-
  Examples/Cortex.lean — the three-site cortex, and the first thermodynamic cover

  §4 of the witnesses. It is on its own because three later files are built on
  it: `Examples/Phase6.lean` puts a metric and a Self on this substrate,
  `Examples/Phase5.lean` covers it twice more, and the overlap-agreement
  reading is stated over its patches. The substrate is `Fin 3` with two
  overlapping patches, and the sections are built from a phase-dependent
  invariant measure, so `LocalSectionSynchronization` and `ThermodynamicCover`
  are inhabited before anything is proved about them.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase4_KuramotoDynamics
import PhysicsOfConsciousness.Phase5_EquilibriumBridge
import PhysicsOfConsciousness.Phase5_GlobalSection

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 4. A thermodynamic cover: two overlapping patches on a three-site substrate

  This is the witness that was missing until now. `LocalSectionSynchronization`
  and `ThermodynamicCover` carry the gluing hypotheses of Derivation 5, and
  `global_section_from_thermodynamics` is stated for an arbitrary instance of the
  latter; until an instance existed, that theorem was conditional on a structure
  of unknown realizability.

  The substrate is deliberately the smallest one that is not degenerate: three
  sites, covered by two *overlapping* open patches, so the gluing that the
  theorem performs is a genuine two-patch gluing across a nonempty intersection
  rather than a relabelling of a single global section.

  **What the witness does and does not establish.** It shows the class is
  inhabitable, so Derivation 5's conclusions are not vacuous. It does not show
  that a *biological* cortex satisfies the class: the phase field here is
  constant (every patch already locked at phase 0), which is what makes
  `thermodynamic_equilibrium` discharge from `phase_locked_minimizes_potential`.
  Getting a physical system to that configuration is the content of the informal
  dynamical argument in the manuscript, not of this file.
-/

/-- Three sites. `mid` is the one shared by both patches. -/
inductive Site : Type
  | left | mid | right
  deriving DecidableEq

instance : Fintype Site :=
  ⟨{Site.left, Site.mid, Site.right}, by intro x; cases x <;> decide⟩

/-- Discrete topology, and the Borel σ-algebra it generates — so `BorelSpace`
    holds by `rfl` rather than by a compatibility argument. -/
instance : TopologicalSpace Site := ⊥
instance : DiscreteTopology Site := ⟨rfl⟩
instance : MeasurableSpace Site := borel Site
instance : BorelSpace Site := ⟨rfl⟩

/-- The substrate as an object of `TopCat`.

    **The name is shorthand, not a claim.** `Site` is the three-element type
    `left | mid | right` under the discrete topology; `Chain.lean` gives it
    counting measure normalized to a probability measure, and takes its coupling
    to be the constant kernel at `K = 3`, `D = 1`. Every `cortex`-prefixed
    definition here and in `Chain.lean` inherits that scope. This is the
    development's running example substrate, and it is the one on which
    `chain_hypotheses_jointly_satisfiable` discharges all eight edges at once —
    which establishes that their conjunction is inhabited, and nothing further.
    It is not a model of cortex, and no witness over it identifies the double
    well, the register, the mesh and the cover as one physical system.

    `abbrev` (not `def`) so that the `MeasurableSpace`/`BorelSpace` instances
    above are found through the coercion `↥Cortex`. -/
abbrev Cortex : TopCat.{0} := TopCat.of Site

/-- A triangulation. As documented on `TriangulatedManifold`, the class does not
    tie `edge_region` to `complex`; here we make them agree anyway — the region
    of the edge `{u, v}` is the pair `{u, v}` itself, which is open (discrete
    topology) and symmetric on the nose. -/
instance : TriangulatedManifold ↥Cortex where
  V := Site
  complex := { faces := Set.univ, downward_closed := fun _ _ => trivial }
  embedding := id
  edge_region := fun u v => {u, v}
  edge_region_symm := fun u v => Set.pair_comm u v

/-- Two patches: everything but `right`, and everything but `left`. They cover
    `Cortex` and overlap exactly in `mid`. -/
def patch : Bool → Opens ↥Cortex
  | false => ⟨{x : Site | x ≠ Site.right}, isOpen_discrete _⟩
  | true  => ⟨{x : Site | x ≠ Site.left}, isOpen_discrete _⟩

theorem patch_cover : iSup patch = ⊤ := by
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  cases x
  · exact ⟨false, show Site.left ≠ Site.right by decide⟩
  · exact ⟨false, show Site.mid ≠ Site.right by decide⟩
  · exact ⟨true, show Site.right ≠ Site.left by decide⟩

/-- The cover is a genuine one: the two patches meet, and meet in one site. -/
theorem patch_overlap : (patch false ⊓ patch true : Opens ↥Cortex) = ⟨{Site.mid}, isOpen_discrete _⟩ := by
  ext x
  cases x <;> simp [patch]

/-- The shared site, viewed as a point of the whole substrate. -/
def midPt : ↥(⊤ : Opens ↥Cortex) := ⟨Site.mid, trivial⟩

noncomputable def midDirac : FiniteMeasure ↥(⊤ : Opens ↥Cortex) :=
  ⟨Measure.dirac midPt, inferInstance⟩

/-- The invariant measure attached to a macroscopic phase `t`: unit mass at the
    shared site, scaled by `(1 + cos t)⁺`.

    The point of the `cos` is that the family genuinely *depends* on the phase
    (see `phaseMeasure_not_const`). A constant family would satisfy
    the periodicity hypothesis of `ofInvariantMeasure` for trivial reasons and
    would witness nothing. -/
noncomputable def phaseMeasure (t : ℝ) : FiniteMeasure ↥(⊤ : Opens ↥Cortex) :=
  (Real.toNNReal (1 + Real.cos t)) • midDirac

theorem midDirac_mass : midDirac Set.univ = 1 := by
  rw [FiniteMeasure.coeFn_def]
  simp [midDirac]

theorem phaseMeasure_mass (t : ℝ) :
    (phaseMeasure t) Set.univ = Real.toNNReal (1 + Real.cos t) := by
  rw [phaseMeasure, FiniteMeasure.smul_apply, midDirac_mass, smul_eq_mul, mul_one]

/-- Non-degeneracy: the invariant measure really varies with the phase. -/
theorem phaseMeasure_not_const : phaseMeasure 0 ≠ phaseMeasure Real.pi := by
  intro h
  have h2 : (phaseMeasure 0) Set.univ = (phaseMeasure Real.pi) Set.univ := by rw [h]
  rw [phaseMeasure_mass, phaseMeasure_mass, Real.cos_zero, Real.cos_pi] at h2
  norm_num at h2

/-- 2π-periodicity, which is what `ofInvariantMeasure` demands. -/
theorem phaseMeasure_periodic {x y : ℝ} (h : Real.cos (x - y) = 1) :
    phaseMeasure x = phaseMeasure y := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp h
  have hx : x = y + (n : ℝ) * (2 * Real.pi) := by linarith [hn]
  rw [phaseMeasure, phaseMeasure, hx, Real.cos_add_int_mul_two_pi]

/-- The global section of the sheafified probability presheaf carried by phase
    `t`: the germ family of `phaseMeasure t`. -/
noncomputable def globalSect (t : ℝ) : (probabilityPresheaf Cortex).obj (op ⊤) :=
  (TopCat.Presheaf.toSheafify (probabilityPresheaf_pre Cortex)).app (op ⊤) (phaseMeasure t)

/-- All patches locked at phase 0, each carrying the restriction of the global
    invariant measure.

    Built through `LocalSectionSynchronization.ofInvariantMeasure`, the
    constructor that packages the class's *old* shape — a `2π`-periodic family
    of global measures, with the local sections defined to be its restrictions.
    That is what makes the overlap agreement hold by functoriality here rather
    than by a computation, and it is also why this witness cannot exhibit the
    emergence reading of Derivation 5: the global object is an input. §14 is the
    witness that does not have that defect. -/
noncomputable instance cortexSync : LocalSectionSynchronization Cortex :=
  LocalSectionSynchronization.ofInvariantMeasure Bool patch patch_cover (fun _ => 0) globalSect
    (fun _ _ h => by unfold globalSect; rw [phaseMeasure_periodic h])

/-- Uniform coupling `3` between the two patches. The configuration `phase = 0`
    is a global minimum of the Kuramoto potential by
    `phase_locked_minimizes_potential`, so `thermodynamic_equilibrium` is
    discharged rather than assumed here. -/
noncomputable instance cortexCover : ThermodynamicCover Cortex where
  toLocalSectionSynchronization := cortexSync
  I_fintype := inferInstanceAs (Fintype Bool)
  I_decidable := inferInstanceAs (DecidableEq Bool)
  A := fun _ _ => 3
  A_symm := fun _ _ => rfl
  A_pos := fun _ _ => by norm_num
  thermodynamic_equilibrium := fun theta =>
    phase_locked_minimizes_potential (V := Bool)
      ⟨fun _ => 0, fun _ _ => 3, fun _ _ => rfl⟩ (fun _ _ => by norm_num) theta

/-- The cover used by the reflexive witness is also reached at the chain's
coupling. The constant zero trajectory suffices because its phase field is the
already synchronized limit; this establishes reachability, not dynamical
selection from an incoherent state. -/
theorem cortexCover_reachedByRelaxation_three :
    cortexCover.IsReachedByRelaxation 3 := by
  refine ⟨by norm_num, (fun _ _ => le_rfl), (fun _ _ => 0), ?_, ?_, ?_, ?_⟩
  · intro i t
    simpa using hasDerivAt_const t (0 : ℝ)
  · simp [potentialExcess, kuramoto_potential_dynamic]
  · intro i j
    simpa using (div_nonneg Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 2))
  · intro i
    change Tendsto (fun _ : ℝ => 0) atTop (𝓝 0)
    exact tendsto_const_nhds

/-- Derivation 5, applied to the witness: the two patch-local sections glue to a
    unique global section. Not vacuous — `cortexCover` above is a real instance. -/
example : ∃! s : GlobalSection (X := Cortex),
    ∀ i : Bool, (probabilityPresheaf Cortex).map
      (homOfLE (le_top : cortexCover.cover i ≤ ⊤)).op s = cortexCover.sync_to_section i :=
  global_section_from_thermodynamics (X := Cortex)

/-! ## 4.1 The cover that asks nothing: one patch per site

§4's two patches overlap at the shared site, so its instance of
`section_agrees_of_phase_eq` is a constraint on the local data. This cover is
the other case. Each site gets its own patch; the patches cover the substrate
and meet nowhere; and the obligation is discharged for *every* assignment of
local sections, because there is no region on which any two of them are
compared.

The consequence is the one `Phase5_GlobalSection.lean` §"What an empty overlap
asks of a cover" states in general, here on a substrate that also carries the
honest cover. Both are `ThermodynamicCover`s at the same coupling and the same
locked phase field; one of them makes a claim about the system and the other
records a partition of it. The class does not distinguish them, which is why
`HasNonemptyOverlaps` is stated and why a cover has to be argued for rather than
chosen.
-/

/-- One patch per site: the finest cover the discrete topology admits. -/
def shard (x : Site) : Opens ↥Cortex := ⟨{x}, isOpen_discrete _⟩

theorem shard_cover : iSup shard = ⊤ := by
  ext z
  simp only [Opens.coe_iSup, Set.mem_iUnion, Opens.coe_top, Set.mem_univ, iff_true]
  exact ⟨z, rfl⟩

/-- Distinct shards meet nowhere. -/
theorem shard_disjoint {x y : Site} (h : x ≠ y) : shard x ⊓ shard y = ⊥ := by
  ext z
  simp only [Opens.coe_inf, Set.mem_inter_iff, Opens.coe_bot, Set.mem_empty_iff_false, iff_false,
    not_and]
  intro hx hy
  exact h (hx.symm.trans hy)

/-- The shard cover, at phase zero on every patch, carrying arbitrary local
data. Nothing relates the three sections, and nothing has to. -/
@[instance_reducible]
noncomputable def shardSync (s : (x : Site) → (probabilityPresheaf Cortex).obj (op (shard x))) :
    LocalSectionSynchronization Cortex :=
  LocalSectionSynchronization.ofDisjointCover Site shard shard_cover
    (fun _ _ h => shard_disjoint h) (fun _ => 0) s

/-- …and it reaches thermodynamic equilibrium exactly as §4's cover does: the
phase field is constant, so `phase_locked_minimizes_potential` discharges the
field at the chain's coupling. Both physical hypotheses of Derivation 5 are
therefore met, for every tuple of local data. -/
@[instance_reducible]
noncomputable def shardCover (s : (x : Site) → (probabilityPresheaf Cortex).obj (op (shard x))) :
    ThermodynamicCover Cortex where
  toLocalSectionSynchronization := shardSync s
  I_fintype := inferInstanceAs (Fintype Site)
  I_decidable := inferInstanceAs (DecidableEq Site)
  A := fun _ _ => 3
  A_symm := fun _ _ => rfl
  A_pos := fun _ _ => by norm_num
  thermodynamic_equilibrium := fun theta =>
    phase_locked_minimizes_potential (V := Site)
      ⟨fun _ => 0, fun _ _ => 3, fun _ _ => rfl⟩ (fun _ _ => by norm_num) theta

/-- **Derivation 5 on the shard cover.** A unique global section, for every
tuple of local data — so the conclusion separates no system from any other. The
theorem is unchanged and true; what this instance shows is how much of it the
cover decides. -/
theorem shardCover_glued (s : (x : Site) → (probabilityPresheaf Cortex).obj (op (shard x))) :
    ∃! g : GlobalSection (X := Cortex),
      ∀ x : Site, (probabilityPresheaf Cortex).map (homOfLE (le_top : shard x ≤ ⊤)).op g = s x :=
  @global_section_from_thermodynamics Cortex _ _ _ (shardCover s)

/-- The shard cover fails the non-degeneracy condition. -/
theorem shardSync_not_hasNonemptyOverlaps
    (s : (x : Site) → (probabilityPresheaf Cortex).obj (op (shard x))) :
    ¬ (shardSync s).HasNonemptyOverlaps :=
  fun h => h Site.left Site.mid (show Site.left ≠ Site.mid by decide)
    (shard_disjoint (show Site.left ≠ Site.mid by decide))

/-- …and §4's cover meets it: its two patches share the middle site, so its
agreement obligation compares sections over a region that has a point in it. -/
theorem cortexSync_hasNonemptyOverlaps : cortexSync.HasNonemptyOverlaps := by
  intro i j _ h
  have hmem : Site.mid ∈ (cortexSync.cover i ⊓ cortexSync.cover j) := by
    show Site.mid ∈ (patch i ⊓ patch j : Opens ↥Cortex)
    cases i <;> cases j <;> exact ⟨by simp [patch], by simp [patch]⟩
  rw [h] at hmem
  simp at hmem

#print axioms shard_cover
#print axioms shard_disjoint
#print axioms shardCover_glued
#print axioms shardSync_not_hasNonemptyOverlaps
#print axioms cortexSync_hasNonemptyOverlaps

end Examples
end PhysicsOfConsciousness
