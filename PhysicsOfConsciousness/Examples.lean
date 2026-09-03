/-
  Examples.lean — Non-vacuity witnesses

  Every physical postulate in this development is now carried as a *class field*
  rather than a standalone `axiom` (see `Axioms.lean` §5 for why: the standalone
  formulations were inconsistent). That change is only an improvement if the
  classes can actually be inhabited — an uninhabitable class makes every theorem
  about it vacuously true, which is no better than an inconsistent axiom.

  This file discharges that obligation for the finite-state parts of the theory
  by exhibiting concrete instances.

  **Coverage — every class carrying a physical postulate is now inhabited.**
    ✓ `StatisticalMechanics` — a one-bit erasure model with a genuine bath.
    ✓ `StructuralResonance`  — a perfectly-resonant system (KL = 0), and a detuned
      one with KL = log 2 > 0 that attains the bound with equality (§2).
    ✓ `ActionPrinciples`     — a scalar field on a one-point spacetime.
    ✓ `PredictiveDissipation` — two systems over one correlated two-bit law (§18):
      a frozen signal, whose memory is entirely predictive and which is permitted
      to dissipate nothing, and a scrambled one, whose memory predicts nothing and
      which is *forced* to dissipate its whole mutual information.
    ✓ `LocalSectionSynchronization` / `ThermodynamicCover` — two overlapping
      patches on a three-site substrate, with sections of the sheafified
      probability presheaf built from a phase-dependent invariant measure (§4);
      a second cover in §13 whose phase field is not constant and whose patches
      carry genuinely different local densities; and a third in §14 whose two
      patches are built from independently chosen mass profiles, so that the
      glued section is none of the data the instance carries.

  §5 additionally exercises the Phase 8 gradient-flow link on a two-site
  substrate: counting measure, a non-zero gradient, and an explicit non-constant
  flow along which entropy production decays as `e^{-2t}`.

  §6 witnesses `IsRegularTriangulation` (`Phase2_MeshConvergence`) with the uniform
  partition of `[0,1)`, and runs `mesh_refinement_convergence` on it. Its
  disjoint-yet-covering-yet-anchored conditions are in tension, so an instance is
  the only proof they are simultaneously satisfiable.

  §7 witnesses the rotating-frame reduction (`Phase4_RotatingFrame`) on a
  two-oscillator system with a common natural frequency, running
  `rotating_frame_chain` with every hypothesis discharged, and exhibits a system
  for which the full Kuramoto potential provably has no minimum.

  §8 witnesses both halves of `Phase7_Rigidity`: a three-site substrate wired to
  the one maximally anti-correlated pair, where `is_strictly_suboptimal` is
  *derived* from the wiring rather than assumed; and, on the real line, a
  single-site architecture carrying arbitrarily large weight yet registering
  exactly zero field correlation against a unit patch that registers one.

  §10 witnesses `ReflexiveBoundary` / `PredictiveModel` (`Phase6_ReflexiveTopology`)
  and the three ambient instances `reflexive_topology_implies_self` assumes about
  `GlobalSection`. It first pierces the sheafification: `massEquivOn` proves that over
  *any* open of the three-site cortex the sections of the probability sheaf are exactly
  the mass profiles on that open, read as densities against counting measure;
  `massEquiv` is the case `U = ⊤`. The metric is then the
  uniform distance between their densities, complete, and the self-prediction map is
  built through the one-site avatar — `avatarRead` then `avatarReadout`, composed by
  `ReflexiveBoundary.predict` — so it contracts by exactly one half of what the avatar
  sees (`cortexPredict_dist`) without being constant (`cortexPredict_not_const`), with a
  unique fixed point (`cortexPredict_fixed_unique`). The contraction constant is read off
  `K` and `D` rather than stipulated: `cortexResonanceRate` places the witness at `K = 3`,
  `D = 1`, `τ = 2 log 2`, and `cortexHasSelf` comes out of `K > critical_coupling 1`,
  while `cortexSubcritical_not_contracting` records that at `K = 1` the same map has no
  Banach argument at all. The earlier 0/1 metric is kept as `gsDiscreteMetric`, and
  `contracting_implies_const` records why it was empty. What is still not established is
  that any field dynamics produces this particular read-out, or that this substrate's
  coupling is `3`: the parameters are a choice of units for the witness.

  §13 answers open item O5 with both halves of an answer: a `ThermodynamicCover`
  whose phase field is *not* the constant function and whose two patches carry
  different mass profiles, read off the sections themselves through `densityOn`;
  and the record of why it cannot be improved on — `ThermodynamicCover.phase_locked`
  forces every instance to a phase-locked configuration. Built through
  `LocalSectionSynchronization.ofInvariantMeasure`, it also inherits that
  constructor's limitation: the glued section is the measure it was built from.

  §14 answers open item O19, which is the other limitation. The class no longer
  carries a global section, so this cover's two patches are built from two
  *different* mass profiles that agree only on the site they share. The gluing
  returns a third profile, and neither input restricts correctly to both patches
  (`leftW_glues_nothing`, `rightW_glues_nothing`): the global state is produced
  by the sheaf condition rather than supplied to it.

  Every declaration in this file depends only on `propext`, `Classical.choice`
  and `Quot.sound`.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase1_PhaseSpaceCapacity
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_KLBound
import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Phase5_EquilibriumBridge
import PhysicsOfConsciousness.Phase6_ReflexiveTopology
import PhysicsOfConsciousness.Phase8_ContinuousField
import PhysicsOfConsciousness.Phase2_MeshConvergence
import PhysicsOfConsciousness.Phase4_RotatingFrame
import PhysicsOfConsciousness.Phase7_Rigidity
import PhysicsOfConsciousness.Phase8_SelfConsistency
import PhysicsOfConsciousness.Phase3_PredictiveThermodynamics
import PhysicsOfConsciousness.Phase3_LandauerBridge

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 1. A one-bit erasure system satisfying Landauer's heat equation -/

/-- Temperature 1, and every operation dumps exactly `log 2` of heat — which is
    what `heat_eq` will force, given the bath below. -/
noncomputable instance boolThermo : Thermodynamics Bool where
  heat_dissipation := fun _ => Real.log 2
  temperature := 1
  temperature_pos := by norm_num

/-- The bath starts in one known state and ends anywhere in a two-state space:
    exactly one bit of bath entropy per operation.

    `U t` is a genuine bijection of `Bool × Bool`. It routes the system's state
    into the bath (`(s, false) ↦ (t false, s)`), which is what lets a
    non-injective `t` coexist with globally reversible dynamics — the Norton /
    Shenker point the manuscript makes in Derivation 2. -/
instance boolBath : BipartiteEnvironment Bool where
  bath := Bool
  dec_bath := inferInstance
  U := fun t p => (if p.2 = false then t false else !(t false), p.1)
  U_inj := by decide
  initial_bath := fun _ => {false}
  final_bath := fun _ => Finset.univ
  h_evolve := by
    intro t p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_singleton] at hq
    simp only [Finset.mem_product, Finset.mem_univ, and_true, hq.2]
    exact Finset.mem_image.mpr ⟨false, Finset.mem_univ _, rfl⟩
  h_bath_nonempty := fun _ => ⟨false, Finset.mem_singleton_self _⟩

noncomputable instance boolStatMech : StatisticalMechanics Bool where
  heat_eq := by
    intro t
    show Real.log 2 = 1 * (boltzmann_entropy (Finset.univ : Finset Bool)
                            - boltzmann_entropy ({false} : Finset Bool))
    simp [boltzmann_entropy]

/-- Sanity check: the general theory, applied to this instance, reproduces the
    expected physics — erasing a bit dissipates strictly positive heat. -/
example : heat_dissipation (fun _ => false : Bool → Bool) > 0 :=
  landauers_principle _ (by
    intro h
    exact absurd (h (a₁ := true) (a₂ := false) rfl) (by simp))

/-! ## 2. Structural resonance: a perfectly resonant system, and a detuned one

The first witness below has `KL = 0`, so it discharges `StructuralResonance.kl_bound`
trivially — `σ ≥ 0` is all that is being asked of it, and any system whatever would do. A
witness like that shows the class is inhabited and nothing else.

The second is the same one-bit eraser of §1 driven by an environment that is *not* matched
to it: the perturbation statistics are a point mass while the system's internal transition
statistics are uniform. There `KL = log 2 > 0`, the entropy production rate is
`log 2 > 0`, and the postulate is satisfied with **equality** (`boolDetuned_tight`). So the
bound is not merely consistent, it is attained: it cannot be strengthened to a strict
inequality, and it is doing real work rather than comparing a positive number to zero.

`boolDetuned` is a `def` rather than an `instance` because `boolResonance` already occupies
`StructuralResonance Bool`; the theorems are applied to it explicitly. -/

/-- Uniform internal statistics matched to uniform external statistics: the
    system has reached structural resonance, so KL = 0 and the postulate holds
    with room to spare. -/
noncomputable def uniformBool : ProbDist Bool where
  p := fun _ => 1/2
  nonneg := by intro i; norm_num
  sum_one := by simp

noncomputable instance boolResonance : StructuralResonance Bool where
  P_ext := uniformBool
  Q_int := uniformBool
  Q_int_pos := by intro i; norm_num [uniformBool]
  transition := id
  dt := 1
  dt_pos := one_pos
  kl_bound := by
    have hKL : KL uniformBool uniformBool = 0 := by
      unfold KL uniformBool
      simp
    show discrete_entropy_rate (σ := Bool) id ≥ KL uniformBool uniformBool / 1
    rw [hKL]
    rw [zero_div]
    have h : discrete_entropy_rate (σ := Bool) id = Real.log 2 / 1 := rfl
    rw [h, div_one]
    positivity

/-- A point mass at `true`: an environment that only ever presents one perturbation,
against internal statistics that are uniform. -/
noncomputable def diracTrue : ProbDist Bool where
  p := fun b => if b then 1 else 0
  nonneg := by intro i; cases i <;> norm_num
  sum_one := by rw [Fintype.sum_bool]; norm_num

theorem KL_diracTrue_uniform : KL diracTrue uniformBool = Real.log 2 := by
  unfold KL diracTrue uniformBool
  rw [Fintype.sum_bool]
  norm_num

/-- The one-bit eraser of §1 against a mismatched environment. Not an `instance`: `Bool`
already carries `boolResonance`. -/
@[instance_reducible] noncomputable def boolDetuned : StructuralResonance Bool where
  P_ext := diracTrue
  Q_int := uniformBool
  Q_int_pos := by intro i; norm_num [uniformBool]
  transition := fun _ => false
  dt := 1
  dt_pos := one_pos
  kl_bound := by
    show discrete_entropy_rate (σ := Bool) (fun _ => false) ≥ KL diracTrue uniformBool / 1
    rw [KL_diracTrue_uniform, div_one]
    have h : discrete_entropy_rate (σ := Bool) (fun _ => false) = Real.log 2 / 1 := rfl
    rw [h, div_one]

/-- The divergence is strictly positive: the environment and the system genuinely disagree. -/
theorem boolDetuned_KL_pos : 0 < KL boolDetuned.P_ext boolDetuned.Q_int := by
  show 0 < KL diracTrue uniformBool
  rw [KL_diracTrue_uniform]
  exact Real.log_pos one_lt_two

/-- And so is the entropy production rate it is being compared against. -/
theorem boolDetuned_sigma_pos :
    0 < discrete_entropy_rate (σ := Bool) boolDetuned.transition := by
  have h : discrete_entropy_rate (σ := Bool) boolDetuned.transition = Real.log 2 / 1 := rfl
  rw [h, div_one]
  exact Real.log_pos one_lt_two

/-- **The postulate is tight.** `KL = Δt · σ` exactly, so `StructuralResonance.kl_bound`
cannot be strengthened to a strict inequality — a one-bit erasure dissipating `log 2`
against a point-mass environment sits precisely on the bound. -/
theorem boolDetuned_tight :
    KL boolDetuned.P_ext boolDetuned.Q_int
      = boolDetuned.dt * discrete_entropy_rate (σ := Bool) boolDetuned.transition := by
  show KL diracTrue uniformBool = 1 * discrete_entropy_rate (σ := Bool) (fun _ => false)
  have h : discrete_entropy_rate (σ := Bool) (fun _ => false) = Real.log 2 / 1 := rfl
  rw [KL_diracTrue_uniform, h, div_one, one_mul]

/-- Derivation 3's bound, on the non-degenerate witness. -/
example : KL boolDetuned.P_ext boolDetuned.Q_int
    ≤ boolDetuned.dt * discrete_entropy_rate (σ := Bool) boolDetuned.transition :=
  @structural_resonance_bound Bool _ _ _ boolDetuned

/-- The discrete second law, on the same witness. -/
example : 0 ≤ discrete_entropy_rate (σ := Bool) boolDetuned.transition :=
  @discrete_entropy_rate_nonneg Bool _ _ _ boolDetuned

/-! ## 3. A scalar field on a one-point spacetime -/

/-- `V v = v²`, minimised at `v = 0`. Spacetime is a single point carrying the
    Dirac probability measure, so `∫ V (phi x) = V (phi ())`. -/
noncomputable instance unitAction :
    ActionPrinciples Unit ℝ (fun _ => 0) (fun phi => ∫ x, (phi x)^2 ∂(Measure.dirac ()))
      (fun phi => ∫ x, (phi x)^2 ∂(Measure.dirac ())) (fun v => v^2) (Measure.dirac ()) where
  total_eq := by intro phi; simp
  kinetic_nonneg := by intro phi; norm_num
  kinetic_const := by intro v; rfl
  potential_integral := by intro phi; rfl
  potential_integrable := by
    intro phi
    exact Integrable.of_finite

/-- The one-point spacetime really does witness the vacuum theorem: the constant
    zero field minimises the energy, and lands in the vacuum manifold. -/
example : (0 : ℝ) ∈ DynamicalVacuum (fun v : ℝ => v^2) := by
  intro v'
  simpa using sq_nonneg v'

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

/-- The substrate as an object of `TopCat`. `abbrev` (not `def`) so that the
    `MeasurableSpace`/`BorelSpace` instances above are found through the
    coercion `↥Cortex`. -/
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

/-! ## 5. The Phase 8 link, exercised on a concrete two-site substrate

  `Phase8_ContinuousField.lean` §7 shows that entropy production σ, read as a
  functional of the coupling kernel, is Fréchet differentiable with an explicit
  gradient, and transports the abstract descent theorems onto
  `entropy_production_rate` itself. Three things could still make that link
  hollow, and this section rules out each:

  * the bridge hypothesis `volume = Measure.count` might not be satisfiable
    alongside `Fintype`/`MeasureSpace`/`TopologicalSpace` — `duo_volume`
    discharges it by `rfl`;
  * `gradSigma` might be identically zero, making the "descent" trivial —
    `duo_grad` computes it to be `e^{-t}` off the diagonal;
  * the flow hypothesis `∀ t, HasDerivAt K_t (- gradSigma …) t` might have no
    non-constant solution — `duoFlow_hasDerivAt` exhibits one, and
    `duoFlow_not_const` shows it moves.

  The system: two sites, no natural frequencies, phases pinned at `0` and `π/2`
  (so the phase mismatch is maximal), diffusion `D = 2`. The coupling relaxes as
  `K(a,b) = K(b,a) = e^{-t}`, and σ decays as `e^{-2t}` — strictly, not merely
  monotonically (`sigma_duoFlow`, and the `StrictAnti` example below).
-/

inductive Duo : Type
  | a | b
  deriving DecidableEq

instance : Fintype Duo := ⟨{Duo.a, Duo.b}, by intro x; cases x <;> decide⟩
instance : TopologicalSpace Duo := ⊥

/-- Counting measure on the two sites — the hypothesis the bridge lemma needs. -/
noncomputable instance : MeasureSpace Duo :=
  { (⊤ : MeasurableSpace Duo) with volume := @Measure.count Duo ⊤ }

instance : MeasurableSingletonClass Duo := ⟨fun _ => trivial⟩

theorem duo_volume : (volume : Measure Duo) = Measure.count := rfl

lemma duo_sum {α : Type*} [AddCommMonoid α] (f : Duo → α) :
    ∑ y : Duo, f y = f Duo.a + f Duo.b := by
  show ∑ y ∈ ({Duo.a, Duo.b} : Finset Duo), f y = _
  rw [Finset.sum_pair (by decide)]

/-- Two sites, no natural drift, diffusion `D = 2`. -/
noncomputable def duoSys : StochasticNeuralField Duo where
  omega := fun _ => 0
  K := fun _ _ => 0
  tau := 1
  D := 2
  h_D_pos := by norm_num
  Omega_avg := 0

/-- Phases `0` and `π/2`: the mismatch `sin (θ_b − θ_a)` is `±1`, so the coupling
    entries genuinely feel the gradient. -/
noncomputable def duoTheta : Duo → ℝ
  | Duo.a => 0
  | Duo.b => Real.pi / 2

/-- The bridge fires: the differentiated functional is `entropy_production_rate`. -/
example (K : CouplingSpace Duo) :
    sigmaOfKernel duoSys duoTheta K = entropy_production_rate (duoSys.withKernel K) duoTheta :=
  sigmaOfKernel_eq_entropy_production_rate duo_volume duoSys duoTheta K

/-- Exponentially relaxing coupling: off-diagonal entries decay as `e^{-t}`,
    diagonal entries stay at `0` (their gradient component vanishes, since a site
    has no phase mismatch with itself). -/
noncomputable def duoFlow (t : ℝ) : CouplingSpace Duo :=
  WithLp.toLp 2 (fun p : Duo × Duo => if p.1 = p.2 then 0 else Real.exp (-t))

lemma duo_drift_a (t : ℝ) : drift duoSys duoTheta (duoFlow t) Duo.a = Real.exp (-t) := by
  simp [drift, duoSys, duoFlow, duoTheta, duo_sum]

lemma duo_drift_b (t : ℝ) : drift duoSys duoTheta (duoFlow t) Duo.b = -Real.exp (-t) := by
  simp [drift, duoSys, duoFlow, duoTheta, duo_sum]

/-- The gradient is *not* identically zero: off the diagonal it is `e^{-t}`. -/
lemma duo_grad (t : ℝ) (p : Duo × Duo) :
    (gradSigma duoSys duoTheta (duoFlow t)) p = if p.1 = p.2 then 0 else Real.exp (-t) := by
  obtain ⟨x, y⟩ := p
  cases x <;> cases y <;>
    simp [gradSigma, show duoSys.D = 2 from rfl, duoTheta, duo_drift_a, duo_drift_b]

/-- `duoFlow` really is a gradient flow of σ. -/
lemma duoFlow_hasDerivAt (t : ℝ) :
    HasDerivAt duoFlow (- gradSigma duoSys duoTheta (duoFlow t)) t := by
  have hg : HasDerivAt
      (fun t : ℝ => (fun p : Duo × Duo => if p.1 = p.2 then (0 : ℝ) else Real.exp (-t)))
      (fun p : Duo × Duo => if p.1 = p.2 then (0 : ℝ) else -Real.exp (-t)) t := by
    rw [hasDerivAt_pi]
    intro p
    by_cases h : p.1 = p.2
    · simp only [h, ite_true]
      exact hasDerivAt_const t 0
    · simp only [h, ite_false]
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
        simpa using ((hasDerivAt_id t).neg).exp
      exact hexp
  have hcomp := (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Duo × Duo => ℝ)).symm
      : (Duo × Duo → ℝ) ≃L[ℝ] CouplingSpace Duo).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt
      t hg
  have hEq : - gradSigma duoSys duoTheta (duoFlow t)
      = WithLp.toLp 2 (fun p : Duo × Duo => if p.1 = p.2 then (0 : ℝ) else -Real.exp (-t)) := by
    ext p
    have hp := duo_grad t p
    show -(gradSigma duoSys duoTheta (duoFlow t)) p = _
    rw [hp]
    by_cases h : p.1 = p.2 <;> simp [h]
  rw [hEq]
  exact hcomp

/-- Entropy production along the flow, in closed form: `σ(t) = e^{-2t}`. -/
theorem sigma_duoFlow (t : ℝ) :
    sigmaOfKernel duoSys duoTheta (duoFlow t) = Real.exp (-t) ^ 2 := by
  simp [sigmaOfKernel, duo_sum, duo_drift_a, duo_drift_b, show duoSys.D = 2 from rfl]
  ring

/-- The flow is not constant, so the descent statement is not about a fixed point. -/
theorem duoFlow_not_const : duoFlow 0 ≠ duoFlow 1 := by
  intro h
  have h2 : (duoFlow 0) (Duo.a, Duo.b) = (duoFlow 1) (Duo.a, Duo.b) := by rw [h]
  simp only [duoFlow, WithLp.ofLp_toLp, ite_false, show (Duo.a = Duo.b) = False by simp] at h2
  have := Real.exp_eq_exp.mp h2
  norm_num at this

/-- The Phase 8 link, applied: `entropy_production_rate` is non-increasing along
    this concrete flow. -/
example : Antitone (fun t => entropy_production_rate (duoSys.withKernel (duoFlow t)) duoTheta) :=
  entropy_production_antitone_of_gradient_flow duo_volume duoSys duoTheta duoFlow
    duoFlow_hasDerivAt

/-- And here the descent is strict, so `Antitone` is not being satisfied by a
    constant. -/
example : StrictAnti (fun t => sigmaOfKernel duoSys duoTheta (duoFlow t)) := by
  intro a b hab
  simp only [sigma_duoFlow, ← Real.exp_nat_mul]
  exact Real.exp_lt_exp.mpr (by push_cast; linarith)


/-! ## 6. A refining sequence of triangulations of `[0,1)`

`Phase2_MeshConvergence.mesh_refinement_convergence` proves that the discrete energy of a
sequence of `IsRegularTriangulation`s converges to the continuous energy. That is worth
nothing if `IsRegularTriangulation` cannot be inhabited — and its conditions do pull against
each other: the cells must be pairwise **disjoint** yet **cover** the region, while every
vertex must be **anchored** to each of its edges' regions. A vertex shared by two cells can
belong to at most one of them, which is exactly why `anchored` is stated with `closure`.

This section discharges the obligation with the uniform partition of `[0,1)` into `N`
half-open cells `[i/N, (i+1)/N)` on `N+1` vertices embedded at `i/N`, and then runs the
convergence theorem on it. The witness is checked to be non-degenerate in three ways:

* cells have measure `1/N`, so they are not empty (`gridCell_measure`);
* the mesh really shrinks — `m n = 1/(n+1) → 0`, not `0` from the start;
* the approximations really move: for the tent function `x ↦ |x - ½|` the discrete energy
  is `1/2` at `N = 1` and `1/4` at `N = 2`, so the limit is not being reached by a constant
  sequence (`tent_energy_one`, `tent_energy_two`).

The triangulation is one-dimensional. The sub-section "The grid as a
`DiscreteThermodynamics`" below carries it over to the discretization structure itself, but
still in one dimension: nothing here witnesses the case of a genuinely 2- or 3-dimensional
edge region.
-/


/-- The `i`-th cell of the uniform partition of `[0,1)` into `N` pieces. -/
def gridCell (N i : ℕ) : Set ℝ := Set.Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N)

/-- Faces: sets of pairwise-consecutive vertices. -/
def gridComplex (N : ℕ) : AbstractSimplicialComplex (Fin (N + 1)) where
  faces := {s | ∀ a ∈ s, ∀ b ∈ s, (a : ℕ) ≤ (b : ℕ) + 1 ∧ (b : ℕ) ≤ (a : ℕ) + 1}
  downward_closed := fun hs hts a ha b hb => hs a (hts ha) b (hts hb)

/-- The uniform triangulation of `[0,1)` by `N` cells and `N+1` vertices. -/
@[reducible] noncomputable def gridTriangulation (N : ℕ) : TriangulatedManifold ℝ where
  V := Fin (N + 1)
  complex := gridComplex N
  embedding := fun i => (i : ℕ) / N
  edge_region := fun u v =>
    if (u : ℕ) + 1 = (v : ℕ) then gridCell N u
    else if (v : ℕ) + 1 = (u : ℕ) then gridCell N v
    else ∅
  edge_region_symm := by
    intro u v
    split_ifs <;> first | rfl | omega

@[simp] theorem gridV (N : ℕ) : (gridTriangulation N).V = Fin (N + 1) := rfl

instance instFintypeGridV (N : ℕ) : Fintype (gridTriangulation N).V :=
  (inferInstance : Fintype (Fin (N + 1)))

instance instLinearOrderGridV (N : ℕ) : LinearOrder (gridTriangulation N).V :=
  (inferInstance : LinearOrder (Fin (N + 1)))

theorem gridCell_subset (N i : ℕ) (h : i + 1 ≤ N) : gridCell N i ⊆ Set.Ico (0:ℝ) 1 := by
  have hN : (0:ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  intro x hx
  rw [gridCell, Set.mem_Ico] at hx
  rw [Set.mem_Ico]
  constructor
  · refine le_trans ?_ hx.1
    positivity
  · refine lt_of_lt_of_le hx.2 ?_
    rw [div_le_one hN]
    exact_mod_cast h

theorem gridCell_dist (N i : ℕ) {x y : ℝ} (hx : x ∈ gridCell N i) (hy : y ∈ gridCell N i) :
    dist x y ≤ 1 / N := by
  rw [gridCell, Set.mem_Ico] at hx hy
  have h := Real.dist_le_of_mem_Icc (x := x) (y := y)
    ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩
  refine h.trans (le_of_eq ?_)
  ring

@[simp] theorem grid_edge_region (N : ℕ) (u v : Fin (N + 1)) :
    (gridTriangulation N).edge_region u v =
      if (u : ℕ) + 1 = (v : ℕ) then gridCell N u
      else if (v : ℕ) + 1 = (u : ℕ) then gridCell N v else ∅ := rfl

@[simp] theorem grid_embedding (N : ℕ) (u : Fin (N + 1)) :
    (gridTriangulation N).embedding u = (u : ℕ) / N := rfl

theorem gridCell_disjoint (N : ℕ) (hN : 0 < N) {i j : ℕ} (h : i ≠ j) :
    Disjoint (gridCell N i) (gridCell N j) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [gridCell, gridCell, Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 : ((i : ℝ) + 1) / N ≤ (j : ℝ) / N := by
      refine (div_le_div_iff_of_pos_right hNR).2 ?_
      exact_mod_cast hlt
    calc min (((i : ℝ) + 1) / N) (((j : ℝ) + 1) / N) ≤ ((i : ℝ) + 1) / N := min_le_left _ _
      _ ≤ (j : ℝ) / N := h1
      _ ≤ max ((i : ℝ) / N) ((j : ℝ) / N) := le_max_right _ _
  · have h1 : ((j : ℝ) + 1) / N ≤ (i : ℝ) / N := by
      refine (div_le_div_iff_of_pos_right hNR).2 ?_
      exact_mod_cast hlt
    calc min (((i : ℝ) + 1) / N) (((j : ℝ) + 1) / N) ≤ ((j : ℝ) + 1) / N := min_le_right _ _
      _ ≤ (i : ℝ) / N := h1
      _ ≤ max ((i : ℝ) / N) ((j : ℝ) / N) := le_max_left _ _

theorem grid_edge_region_lt (N : ℕ) {u v : Fin (N + 1)} (h : u < v) :
    (gridTriangulation N).edge_region u v =
      if (u : ℕ) + 1 = (v : ℕ) then gridCell N u else ∅ := by
  rw [grid_edge_region]
  have hvu : ¬((v : ℕ) + 1 = (u : ℕ)) := by
    rw [Fin.lt_def] at h; omega
  split_ifs <;> rfl

theorem gridRegular (N : ℕ) (hN : 0 < N) :
    IsRegularTriangulation (gridTriangulation N) (Set.Ico (0:ℝ) 1) where
  measurable_region := by
    intro u v
    rw [grid_edge_region]
    split_ifs <;> simp [gridCell]
  no_self_region := by
    intro u
    rw [grid_edge_region]
    split_ifs <;> first | rfl | omega
  face_of_complex := by
    intro u v hne
    have hcond : (u : Fin (N + 1)).val + 1 = (v : Fin (N + 1)).val ∨
        (v : Fin (N + 1)).val + 1 = (u : Fin (N + 1)).val := by
      by_contra hc
      rw [not_or] at hc
      rw [grid_edge_region] at hne
      split_ifs at hne with h1 h2
      · exact hc.1 h1
      · exact hc.2 h2
      · exact Set.not_nonempty_empty hne
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
  anchored := by
    intro u v hne
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    rw [grid_edge_region] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · rw [gridCell, closure_Ico (by intro hc; rw [div_eq_div_iff hNR.ne' hNR.ne'] at hc; linarith)]
      rw [grid_embedding, Set.mem_Icc]
      constructor
      · exact le_refl _
      · gcongr
        linarith
    · rw [gridCell, closure_Ico (by intro hc; rw [div_eq_div_iff hNR.ne' hNR.ne'] at hc; linarith)]
      rw [grid_embedding, Set.mem_Icc]
      have : ((u : Fin (N + 1)).val : ℝ) = ((v : Fin (N + 1)).val : ℝ) + 1 := by
        exact_mod_cast h2.symm
      rw [this]
      constructor
      · gcongr
        linarith
      · exact le_refl _
    · exact absurd hne Set.not_nonempty_empty
  disjoint_region := by
    intro u v u' v' huv huv' hne
    rw [grid_edge_region_lt N huv, grid_edge_region_lt N huv']
    split_ifs with h1 h2 h3
    · refine gridCell_disjoint N hN ?_
      intro hc
      refine hne ?_
      have huu : (u : Fin (N + 1)) = u' := Fin.ext hc
      have hvv : (v : Fin (N + 1)) = v' := Fin.ext (by omega)
      rw [huu, hvv]
    · exact Set.disjoint_empty _
    · exact Set.empty_disjoint _
    · exact Set.empty_disjoint _
  covers := by
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · refine Set.iUnion_subset fun u => Set.iUnion_subset fun v => ?_
      rw [grid_edge_region]
      split_ifs with h1 h2
      · exact gridCell_subset N _ (by have := (v : Fin (N + 1)).isLt; omega)
      · exact gridCell_subset N _ (by have := (u : Fin (N + 1)).isLt; omega)
      · exact Set.empty_subset _
    · rw [Set.mem_Ico] at hx
      have hxN : 0 ≤ x * N := mul_nonneg hx.1 (le_of_lt hNR)
      have h1 : (⌊x * N⌋₊ : ℝ) ≤ x * N := Nat.floor_le hxN
      have h2 : x * N < ⌊x * N⌋₊ + 1 := Nat.lt_floor_add_one _
      have hiN : ⌊x * N⌋₊ < N := by
        refine (Nat.floor_lt hxN).2 ?_
        calc x * N < 1 * N := by exact mul_lt_mul_of_pos_right hx.2 hNR
          _ = N := one_mul _
      refine Set.mem_iUnion.2 ⟨(⟨⌊x * N⌋₊, by omega⟩ : Fin (N + 1)),
        Set.mem_iUnion.2 ⟨(⟨⌊x * N⌋₊ + 1, by omega⟩ : Fin (N + 1)), ?_⟩⟩
      rw [grid_edge_region]
      split_ifs with h3 h4
      · rw [gridCell, Set.mem_Ico]
        refine ⟨(div_le_iff₀ hNR).2 ?_, (lt_div_iff₀ hNR).2 ?_⟩
        · exact h1
        · exact h2
      · simp at h3
      · simp at h3

theorem grid_fine (N : ℕ) (u v : Fin (N + 1)) {x y : ℝ}
    (hx : x ∈ (gridTriangulation N).edge_region u v)
    (hy : y ∈ (gridTriangulation N).edge_region u v) : dist x y ≤ 1 / N := by
  rw [grid_edge_region] at hx hy
  split_ifs at hx hy with h1 h2
  · exact gridCell_dist N _ hx hy
  · exact gridCell_dist N _ hx hy
  · exact absurd hx (Set.notMem_empty x)

theorem grid_mesh_refinement (f : ℝ → ℝ) (hf : UniformContinuous f) :
    Tendsto (fun n : ℕ => discreteEnergy (gridTriangulation (n + 1)) volume f) atTop
      (𝓝 (∫ x in Set.Ico (0:ℝ) 1, f x)) := by
  have hint : IntegrableOn f (Set.Ico (0:ℝ) 1) volume :=
    (hf.continuous.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  refine mesh_refinement_convergence volume f hf (by simp) hint
    (fun n => gridTriangulation (n + 1)) (fun n => gridRegular (n + 1) n.succ_pos)
    (fun n => 1 / ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat ?_
  intro n u v x hx y hy
  have h := grid_fine (n + 1) u v hx hy
  push_cast at h
  exact h

/-- Cells are non-degenerate: each has measure `1/N`. -/
theorem gridCell_measure (N : ℕ) (hN : 0 < N) (i : ℕ) :
    volume.real (gridCell N i) = 1 / N := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [gridCell, Real.volume_real_Ico_of_le (by gcongr; linarith)]
  field_simp
  ring

/-- The tent function `x ↦ |x - ½|`, Lipschitz hence uniformly continuous. -/
theorem tent_uniformContinuous : UniformContinuous (fun x : ℝ => |x - 1/2|) := by
  have h : (fun x : ℝ => |x - 1/2|) = fun x : ℝ => dist x (1/2) := by
    funext x; rw [Real.dist_eq]
  rw [h]
  exact (LipschitzWith.dist_left (1/2 : ℝ)).uniformContinuous

example : Tendsto
    (fun n : ℕ => discreteEnergy (gridTriangulation (n + 1)) volume (fun x => |x - 1/2|))
    atTop (𝓝 (∫ x in Set.Ico (0:ℝ) 1, |x - 1/2|)) :=
  grid_mesh_refinement _ tent_uniformContinuous

theorem tent_energy_one :
    discreteEnergy (gridTriangulation 1) volume (fun x => |x - 1/2|) = 1/2 := by
  simp [discreteEnergy, Fin.sum_univ_two, grid_edge_region, grid_embedding, gridCell]
  norm_num

theorem tent_energy_two :
    discreteEnergy (gridTriangulation 2) volume (fun x => |x - 1/2|) = 1/4 := by
  simp [discreteEnergy, Fin.sum_univ_three, grid_edge_region, grid_embedding, gridCell]
  norm_num

/-- The approximations genuinely move: refining the mesh changes the answer, so the
convergence above is not the trivial convergence of a constant sequence. -/
example : discreteEnergy (gridTriangulation 1) volume (fun x => |x - 1/2|)
    ≠ discreteEnergy (gridTriangulation 2) volume (fun x => |x - 1/2|) := by
  rw [tent_energy_one, tent_energy_two]
  norm_num

/-! ### The grid as a `DiscreteThermodynamics`

`DiscreteThermodynamics` now carries its own `IsRegularTriangulation` field, so its edge
weights are integrals over a geometrically constrained family of regions rather than over
arbitrary sets. That strengthening is worth nothing unless something satisfies it, and
until now the structure had **no instance anywhere in the development** — every theorem
about `edge_weight` was conditional on a structure not shown to be realizable.

This section supplies one, on the same uniform grid, and checks it is not degenerate:

* each consecutive edge carries weight exactly `1/N` (`gridThermo_edge_weight`), so the
  weights are positive and genuinely track the mesh;
* the weights sum to the total energy of the covered region — `½ ∑ᵤ ∑ᵥ w(u,v) = 1` for every
  `N` (`gridThermo_total`), which is `total_weight_eq_setIntegral` on this instance and is
  exactly what the everywhere-empty triangulation would violate;
* the scalar magnitude is a *choice*, and it matters: `gridThermo'` differs from
  `gridThermo` in that field alone, the partition theorem holds for both, and the coupling
  matrices differ on every edge (`gridThermo_magnitude_matters`). This is open item **O7**,
  decided and recorded on the field itself.

Two limitations, stated so they are not read as more than they are. The scalar magnitude is
`|T(∂,∂)|` on the one-dimensional tangent space, so it *is* a function of the stress-energy
tensor, but the tensor exhibited (`unitTensor`) is constant; nothing here witnesses a
spatially varying stress-energy. And the substrate is `ℝ` as a manifold over itself, so the
edge regions are intervals, not the 2- or 3-dimensional cells of the intended application.
-/

/-- The constant unit bilinear form on the tangent spaces of `ℝ`, used as a concrete
stress-energy tensor. -/
noncomputable def unitTensor : CovariantTensor2 (modelWithCornersSelf ℝ ℝ) ℝ :=
  fun _ => ContinuousLinearMap.mul ℝ ℝ

@[simp] theorem unitTensor_apply (x a b : ℝ) : unitTensor x a b = a * b := rfl

/-- The uniform grid, discretizing the constant unit stress-energy on `[0,1)`.

The triangulation and the model are explicit arguments of `DiscreteThermodynamics` — see
its doc-string — which is what lets a *sequence* of triangulations of the same space each
carry their own thermodynamics. -/
noncomputable def gridThermo (N : ℕ) (hN : 0 < N) :
    DiscreteThermodynamics (gridTriangulation N) (modelWithCornersSelf ℝ ℝ) where
  volume_measure := volume
  scalar_magnitude := fun T x => |T x (1:ℝ) (1:ℝ)|
  magnitude_nonneg := fun _ _ => abs_nonneg _
  region := Set.Ico 0 1
  regular := gridRegular N hN

@[simp] theorem gridThermo_magnitude (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (gridThermo N hN).scalar_magnitude unitTensor x = 1 := by
  show |unitTensor x (1:ℝ) (1:ℝ)| = 1
  rw [unitTensor_apply]
  norm_num

@[simp] theorem gridThermo_volume (N : ℕ) (hN : 0 < N) :
    (gridThermo N hN).volume_measure = volume := rfl

@[simp] theorem gridThermo_region (N : ℕ) (hN : 0 < N) :
    (gridThermo N hN).region = Set.Ico 0 1 := rfl

/-- Consecutive vertices are coupled with weight `1/N`: the weights are positive, and they
shrink with the mesh. -/
theorem gridThermo_edge_weight (N : ℕ) (hN : 0 < N) (u v : Fin (N + 1))
    (h : (u : ℕ) + 1 = (v : ℕ)) :
    DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor u v = 1 / N := by
  have hreg : (gridTriangulation N).edge_region u v = gridCell N u := by
    rw [grid_edge_region]
    simp [h]
  rw [DiscreteThermodynamics.edge_weight]
  simp only [gridThermo_magnitude, gridThermo_volume, hreg]
  rw [setIntegral_const, smul_eq_mul, mul_one]
  exact gridCell_measure N hN u

/-- **The coupling weights partition the energy.** `total_weight_eq_setIntegral` on this
instance: the whole coupling matrix sums to the energy of `[0,1)`, which is `1`, for every
`N`. Nothing is double counted by the overlapping double sum and nothing is left uncovered.
-/
theorem gridThermo_total (N : ℕ) (hN : 0 < N) :
    (1 / 2 : ℝ) * ∑ u, ∑ v,
        DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor u v = 1 := by
  have hfun : (gridThermo N hN).scalar_magnitude unitTensor = fun _ : ℝ => (1:ℝ) := by
    funext x
    exact gridThermo_magnitude N hN x
  have hint : IntegrableOn ((gridThermo N hN).scalar_magnitude unitTensor)
      (gridThermo N hN).region (gridThermo N hN).volume_measure := by
    rw [hfun, gridThermo_volume, gridThermo_region]
    exact integrableOn_const (by simp)
  rw [DiscreteThermodynamics.total_weight_eq_setIntegral (gridThermo N hN) unitTensor hint]
  simp only [gridThermo_magnitude, gridThermo_volume, gridThermo_region]
  rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ico_of_le (by norm_num)]
  norm_num

/-! #### The scalar magnitude is a modelling choice, and it is load-bearing

Open item **O7** asked whether `DiscreteThermodynamics.scalar_magnitude` — the scalar the
discretization reads off a stress-energy tensor, constrained only to be non-negative —
should be constrained further or marked as modelling. The decision, recorded on the field
itself in `Phase2_SimplicialBridge.lean`, is to keep it a choice. These three declarations
are the half of that decision that is a theorem rather than a comment.

`gridThermo'` is the *same* grid, the same tensor, the same regions and the same regularity
proof as `gridThermo`, differing in one field: it reads twice the magnitude. Both are legal
instances, and `gridThermo'_total` shows the structure theorem survives the change —
`total_weight_eq_setIntegral` holds for both, with the energy it partitions moving from `1`
to `2`. `gridThermo_magnitude_matters` shows the coupling matrix does not: the two induced
Kuramoto systems have different weights on every edge. So the choice is a physical input
with numerical consequences, not a formality — which is why it is marked and not removed.
-/

/-- A second thermodynamics on the same grid, reading twice the magnitude. Nothing else
differs, including the regularity proof. -/
noncomputable def gridThermo' (N : ℕ) (hN : 0 < N) :
    DiscreteThermodynamics (gridTriangulation N) (modelWithCornersSelf ℝ ℝ) where
  volume_measure := volume
  scalar_magnitude := fun T x => 2 * |T x (1:ℝ) (1:ℝ)|
  magnitude_nonneg := fun _ _ => by positivity
  region := Set.Ico 0 1
  regular := gridRegular N hN

@[simp] theorem gridThermo'_magnitude (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (gridThermo' N hN).scalar_magnitude unitTensor x = 2 := by
  show 2 * |unitTensor x (1:ℝ) (1:ℝ)| = 2
  rw [unitTensor_apply]
  norm_num

@[simp] theorem gridThermo'_volume (N : ℕ) (hN : 0 < N) :
    (gridThermo' N hN).volume_measure = volume := rfl

@[simp] theorem gridThermo'_region (N : ℕ) (hN : 0 < N) :
    (gridThermo' N hN).region = Set.Ico 0 1 := rfl

theorem gridThermo'_edge_weight (N : ℕ) (hN : 0 < N) (u v : Fin (N + 1))
    (h : (u : ℕ) + 1 = (v : ℕ)) :
    DiscreteThermodynamics.edge_weight (gridThermo' N hN) unitTensor u v = 2 / N := by
  have hreg : (gridTriangulation N).edge_region u v = gridCell N u := by
    rw [grid_edge_region]
    simp [h]
  rw [DiscreteThermodynamics.edge_weight]
  simp only [gridThermo'_magnitude, gridThermo'_volume, hreg]
  rw [setIntegral_const, smul_eq_mul, gridCell_measure N hN u]
  ring

/-- **The structure theorem is stable under the choice.** `total_weight_eq_setIntegral`
holds for the doubled magnitude too; what moves is the energy it partitions, from `1` to
`2`. Nothing about symmetry, the vanishing diagonal, or the coupling graph depends on which
scalar invariant is read. -/
theorem gridThermo'_total (N : ℕ) (hN : 0 < N) :
    (1 / 2 : ℝ) * ∑ u, ∑ v,
        DiscreteThermodynamics.edge_weight (gridThermo' N hN) unitTensor u v = 2 := by
  have hfun : (gridThermo' N hN).scalar_magnitude unitTensor = fun _ : ℝ => (2:ℝ) := by
    funext x
    exact gridThermo'_magnitude N hN x
  have hint : IntegrableOn ((gridThermo' N hN).scalar_magnitude unitTensor)
      (gridThermo' N hN).region (gridThermo' N hN).volume_measure := by
    rw [hfun, gridThermo'_volume, gridThermo'_region]
    exact integrableOn_const (by simp)
  rw [DiscreteThermodynamics.total_weight_eq_setIntegral (gridThermo' N hN) unitTensor hint]
  simp only [gridThermo'_magnitude, gridThermo'_volume, gridThermo'_region]
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ico_of_le (by norm_num)]
  norm_num

/-- **…and the numbers are not.** Two legal instances over the same triangulation, the same
tensor and the same regions give different coupling matrices. The scalar magnitude is
therefore a physical input the framework does not fix, and the induced Kuramoto system
depends on it — the exact content of the `[MODELLING]` marking on the field. -/
theorem gridThermo_magnitude_matters (N : ℕ) (hN : 0 < N) :
    DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor
        ⟨0, by omega⟩ ⟨1, by omega⟩
      ≠ DiscreteThermodynamics.edge_weight (gridThermo' N hN) unitTensor
        ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [gridThermo_edge_weight N hN _ _ rfl, gridThermo'_edge_weight N hN _ _ rfl]
  intro hc
  rw [div_eq_div_iff (by linarith) (by linarith)] at hc
  linarith

/-- A nonzero weight forces an actual face of the complex: on the grid, `face_of_weight_ne_zero`
says the coupling graph is the path graph the triangulation describes and nothing more. -/
example (N : ℕ) (hN : 0 < N) (u v : Fin (N + 1))
    (h : DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor u v ≠ 0) :
    ({u, v} : Finset (Fin (N + 1))) ∈ (gridTriangulation N).complex.faces :=
  DiscreteThermodynamics.face_of_weight_ne_zero (gridThermo N hN) unitTensor h


/-! ### 6.1 The rate, and what the abstract mesh cannot state

`Phase2_MeshConvergence` proves that the discrete energy *converges* to the
continuous energy; it proves no rate, and its header says why. The bound there is
`ε·μ(support)` with `ε` the modulus of continuity, which for a Lipschitz
integrand gives `O(1/N)` — while `simulations/mesh_refinement.py` measures
`O(1/N²)` on the same problem. Open item **O16** recorded the gap between the two.

The recorded obstacle was the wrong one. O16 said the missing piece was a
midpoint error term "`taylor_mean_remainder_lagrange` per cell". It is not:
Mathlib carries the **composite** trapezoidal bound already
(`trapezoidal_error_le_of_c2`, `Mathlib/MeasureTheory/Integral/IntervalIntegral/
TrapezoidalRule.lean`), so what was actually missing was the identification of
this development's `discreteEnergy` with Mathlib's `trapezoidal_integral`. That
identification is `grid_discreteEnergy_eq_trapezoidal`, and it is where all the
work below is: the double sum over `Fin (N+1) × Fin (N+1)` of edge-region
measures has to be collapsed to a sum over `Finset.range`.

With it, `grid_energy_error_le` gives `ζ/(12N²)` for a `C²` integrand, which is
the rate the simulation reports.

**The scope point, which O16 asked to be recorded either way.** This is a theorem
about *this grid*, not about `Mesh`. It cannot be stated at the level of
`Phase2_MeshConvergence`, because an abstract `Mesh` lives over a
`PseudoMetricSpace` on which no second derivative exists — there is nothing for
`ζ` to bound. Second-order accuracy is a property of a quadrature rule on an
interval, not of a partition of a metric space, and the development's generality
is what puts it out of reach in general rather than any missing Mathlib result.

One thing found in passing and worth recording: Mathlib's
`trapezoidal_error_le_of_c2` asks for the second-derivative bound at **every**
real `x`, not merely on `[[a,b]]`. Outside the interval the `derivWithin` is `0`
for lack of unique differentiability, so the hypothesis is still discharged
(`sq_iteratedDerivWithin_bound` does it), but the case split is an artefact of
the statement rather than of the mathematics.
-/

section MeshRate
open scoped Interval

theorem edge_measure_split (N : ℕ) (hN : 0 < N) (a b : ℕ) :
    volume.real (if a + 1 = b then gridCell N a else if b + 1 = a then gridCell N b else ∅)
      = (if a + 1 = b then 1 / (N:ℝ) else 0) + (if b + 1 = a then 1 / (N:ℝ) else 0) := by
  split_ifs with h1 h2
  · omega
  · rw [gridCell_measure N hN]; ring
  · rw [gridCell_measure N hN]; ring
  · simp

theorem sum_edge_measure (N : ℕ) {a : ℕ} (ha : a < N + 1) :
    ∑ b ∈ Finset.range (N + 1),
        ((if a + 1 = b then 1 / (N:ℝ) else 0) + (if b + 1 = a then 1 / (N:ℝ) else 0))
      = (if a < N then 1 / (N:ℝ) else 0) + (if 0 < a then 1 / (N:ℝ) else 0) := by
  rw [Finset.sum_add_distrib]
  have e1 : (∑ b ∈ Finset.range (N + 1), if a + 1 = b then 1 / (N:ℝ) else 0)
      = if a < N then 1 / (N:ℝ) else 0 := by
    have h : (∑ b ∈ Finset.range (N + 1), if a + 1 = b then 1 / (N:ℝ) else 0)
        = ∑ b ∈ Finset.range (N + 1), if b = a + 1 then 1 / (N:ℝ) else 0 :=
      Finset.sum_congr rfl fun b _ => if_congr eq_comm rfl rfl
    rw [h, Finset.sum_ite_eq' (Finset.range (N + 1)) (a + 1) (fun _ => 1 / (N:ℝ))]
    exact if_congr (by simp only [Finset.mem_range]; omega) rfl rfl
  have e2 : (∑ b ∈ Finset.range (N + 1), if b + 1 = a then 1 / (N:ℝ) else 0)
      = if 0 < a then 1 / (N:ℝ) else 0 := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp
    · have h : (∑ b ∈ Finset.range (N + 1), if b + 1 = a then 1 / (N:ℝ) else 0)
          = ∑ b ∈ Finset.range (N + 1), if b = a - 1 then 1 / (N:ℝ) else 0 :=
        Finset.sum_congr rfl fun b _ => if_congr (by omega) rfl rfl
      rw [h, Finset.sum_ite_eq' (Finset.range (N + 1)) (a - 1) (fun _ => 1 / (N:ℝ))]
      exact if_congr (by simp only [Finset.mem_range]; omega) rfl rfl
  rw [e1, e2]

/-- The discrete energy of the grid, as a sum over `range`. -/
theorem grid_discreteEnergy_eq_range (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) :
    discreteEnergy (gridTriangulation N) volume f
      = (1 / 2 : ℝ) * ∑ a ∈ Finset.range (N + 1),
          f ((a : ℝ) / N) * ((if a < N then 1 / (N:ℝ) else 0) + (if 0 < a then 1 / (N:ℝ) else 0)) := by
  have hE : discreteEnergy (gridTriangulation N) volume f
      = (1 / 2 : ℝ) * ∑ u : Fin (N + 1), ∑ v : Fin (N + 1),
          volume.real ((gridTriangulation N).edge_region u v) * f (((u : ℕ) : ℝ) / N) := rfl
  rw [hE]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun a => f ((a : ℝ) / N) *
    ((if a < N then 1 / (N:ℝ) else 0) + (if 0 < a then 1 / (N:ℝ) else 0))) (N + 1)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hinner : ∀ v : Fin (N + 1),
      volume.real ((gridTriangulation N).edge_region u v) * f (((u : ℕ) : ℝ) / N)
        = ((if (u:ℕ) + 1 = (v:ℕ) then 1 / (N:ℝ) else 0)
            + (if (v:ℕ) + 1 = (u:ℕ) then 1 / (N:ℝ) else 0)) * f (((u:ℕ) : ℝ) / N) := by
    intro v
    rw [grid_edge_region, edge_measure_split N hN]
  rw [Finset.sum_congr rfl (fun v _ => hinner v), ← Finset.sum_mul]
  rw [Fin.sum_univ_eq_sum_range (fun b =>
    (if (u:ℕ) + 1 = b then 1 / (N:ℝ) else 0) + (if b + 1 = (u:ℕ) then 1 / (N:ℝ) else 0)) (N + 1)]
  rw [sum_edge_measure N u.isLt]
  ring


/-- **The grid's discrete energy is Mathlib's composite trapezoidal rule** on `[0,1]`
with `N` cells. -/
theorem grid_discreteEnergy_eq_trapezoidal (m : ℕ) (f : ℝ → ℝ) :
    discreteEnergy (gridTriangulation (m + 1)) volume f
      = trapezoidal_integral f (m + 1) 0 1 := by
  have hNR : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [grid_discreteEnergy_eq_range (m + 1) (Nat.succ_pos m) f, trapezoidal_integral]
  have hsplit : ∀ a ∈ Finset.range (m + 2),
      f ((a : ℝ) / ((m : ℕ) + 1 : ℕ))
          * ((if a < m + 1 then 1 / (((m : ℕ) + 1 : ℕ) : ℝ) else 0)
             + (if 0 < a then 1 / (((m : ℕ) + 1 : ℕ) : ℝ) else 0))
        = (f ((a : ℝ) / ((m : ℝ) + 1)) * (if a < m + 1 then 1 / ((m : ℝ) + 1) else 0))
          + (f ((a : ℝ) / ((m : ℝ) + 1)) * (if 0 < a then 1 / ((m : ℝ) + 1) else 0)) := by
    intro a _
    push_cast
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hT : (∑ a ∈ Finset.range (m + 2),
        f ((a : ℝ) / ((m : ℝ) + 1)) * (if a < m + 1 then 1 / ((m : ℝ) + 1) else 0))
      = ∑ a ∈ Finset.range (m + 1), f ((a : ℝ) / ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
    rw [Finset.sum_range_succ]
    rw [ite_eq_right (lt_irrefl _), mul_zero, add_zero]
    exact Finset.sum_congr rfl fun a ha => by
      rw [ite_eq_left (Finset.mem_range.mp ha)]; ring
  have hU : (∑ a ∈ Finset.range (m + 2),
        f ((a : ℝ) / ((m : ℝ) + 1)) * (if 0 < a then 1 / ((m : ℝ) + 1) else 0))
      = ∑ i ∈ Finset.range (m + 1), f (((i : ℝ) + 1) / ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
    rw [Finset.sum_range_succ']
    rw [ite_eq_right (lt_irrefl 0), mul_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => by
      rw [ite_eq_left (Nat.succ_pos i)]; push_cast; ring
  rw [hT, hU, Finset.sum_range_succ' (fun a => f ((a : ℝ) / ((m : ℝ) + 1)) / ((m : ℝ) + 1)) m,
    Finset.sum_range_succ (fun i => f (((i : ℝ) + 1) / ((m : ℝ) + 1)) / ((m : ℝ) + 1)) m]
  have hz : ((0 : ℕ) : ℝ) / ((m : ℝ) + 1) = 0 := by norm_num
  have ho : (((m : ℝ) + 1)) / ((m : ℝ) + 1) = 1 := div_self hNR
  have hshift : ∀ i ∈ Finset.range m,
      f ((((i : ℕ) + 1 : ℕ) : ℝ) / ((m : ℝ) + 1)) / ((m : ℝ) + 1)
        = f (((i : ℝ) + 1) / ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
    intro i _; push_cast; ring
  rw [Finset.sum_congr rfl hshift, hz, ho]
  have hsum : ∀ k ∈ Finset.range m,
      f (0 + ((k : ℝ) + 1) * (1 - 0) / (((m + 1 : ℕ)) : ℝ))
        = f (((k : ℝ) + 1) / ((m : ℝ) + 1)) := by
    intro k _
    congr 1
    push_cast
    ring
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hsum, ← Finset.sum_div]
  push_cast
  field_simp
  ring


/-- **The O(1/N²) rate, on the concrete witness.** For a `C²` integrand with second
derivative bounded by `ζ`, the grid's discrete energy differs from the continuous
energy by at most `ζ/(12N²)`. -/
theorem grid_energy_error_le {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f [[(0:ℝ), 1]])
    {ζ : ℝ} (hζ : ∀ x, |iteratedDerivWithin 2 f [[(0:ℝ), 1]] x| ≤ ζ)
    {N : ℕ} (hN : 0 < N) :
    |discreteEnergy (gridTriangulation N) volume f - ∫ x in Set.Ico (0:ℝ) 1, f x|
      ≤ ζ / (12 * (N:ℝ) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have h := trapezoidal_error_le_of_c2 (a := 0) (b := 1) hf hζ (Nat.succ_pos m)
  rw [trapezoidal_error] at h
  have hint : (∫ x in (0:ℝ)..1, f x) = ∫ x in Set.Ico (0:ℝ) 1, f x := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioc]
  rw [grid_discreteEnergy_eq_trapezoidal m f, ← hint]
  refine h.trans (le_of_eq ?_)
  norm_num


/-- The identity, cross-checked against a value computed by hand: `tent_energy_two`
says the discrete energy of the tent function on two cells is `1/4`, and the
trapezoidal rule must therefore give `1/4` too. -/
example : trapezoidal_integral (fun x => |x - 1/2|) 2 0 1 = 1/4 :=
  (grid_discreteEnergy_eq_trapezoidal 1 _).symm.trans tent_energy_two

/-- The second derivative of `y ↦ y²`, bounded on all of `ℝ`, which is what
Mathlib's trapezoidal bound asks for. Outside `[0,1]` the set has no unique
differentiability, so the iterated `derivWithin` is `0` there. -/
theorem sq_iteratedDerivWithin_bound (x : ℝ) :
    |iteratedDerivWithin 2 (fun y : ℝ => y ^ 2) [[(0:ℝ), 1]] x| ≤ 2 := by
  by_cases hx : x ∈ [[(0:ℝ), 1]]
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      (by fun_prop) hx]
    have h2 : iteratedDeriv 2 (fun y : ℝ => y ^ 2) x = 2 := by simp
    rw [h2]; norm_num
  · have hnu : ¬ UniqueDiffWithinAt ℝ [[(0:ℝ), 1]] x := by
      intro h
      exact hx (by simpa [isCompact_uIcc.isClosed.closure_eq] using h.mem_closure)
    rw [iteratedDerivWithin_succ, derivWithin_zero_of_not_uniqueDiffWithinAt hnu]
    norm_num

/-- **A non-degenerate instance of the rate.** For `y ↦ y²` the bound is
`1/(6N²)`, and the integrand is not one the trapezoidal rule integrates exactly,
so the error is genuinely `Θ(1/N²)` rather than `0`. -/
theorem grid_energy_error_sq {N : ℕ} (hN : 0 < N) :
    |discreteEnergy (gridTriangulation N) volume (fun y => y ^ 2)
        - ∫ x in Set.Ico (0:ℝ) 1, x ^ 2| ≤ 1 / (6 * (N:ℝ) ^ 2) := by
  have h := grid_energy_error_le (f := fun y : ℝ => y ^ 2)
    (by fun_prop) sq_iteratedDerivWithin_bound hN
  refine h.trans (le_of_eq ?_)
  ring

/-- The constant case, where the trapezoidal rule is exact: the bound is `0`, so
the grid's discrete energy of a constant is *exactly* its integral. This also
checks the normalisation of the identity. -/
theorem grid_energy_const (c : ℝ) {N : ℕ} (hN : 0 < N) :
    discreteEnergy (gridTriangulation N) volume (fun _ => c)
      = ∫ _x in Set.Ico (0:ℝ) 1, c := by
  have hζ : ∀ x, |iteratedDerivWithin 2 (fun _ : ℝ => c) [[(0:ℝ), 1]] x| ≤ 0 := by
    intro x; rw [iteratedDerivWithin_const]; norm_num
  have h := grid_energy_error_le (f := fun _ : ℝ => c) contDiffOn_const hζ hN
  rw [zero_div] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))


/-- The integral the grid is approximating, for `y ↦ y²`. -/
theorem integral_sq_Ico : (∫ x in Set.Ico (0:ℝ) 1, x ^ 2) = 1 / 3 := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_pow]
  norm_num

/-- **The bound is attained**, at `N = 1`: one cell, `|1/2 − 1/3| = 1/6`, which is
exactly `ζ/(12N²)` for `ζ = 2`. So `grid_energy_error_sq` is not a vacuous
over-estimate, and the constant cannot be improved. -/
theorem grid_energy_error_sq_one :
    |discreteEnergy (gridTriangulation 1) volume (fun y => y ^ 2)
        - ∫ x in Set.Ico (0:ℝ) 1, x ^ 2| = 1 / 6 := by
  rw [grid_discreteEnergy_eq_trapezoidal 0 _, integral_sq_Ico, trapezoidal_integral]
  norm_num

end MeshRate

/-! ## 7. The rotating-frame reduction on a two-oscillator system

`Phase4_RotatingFrame` chains the two Kuramoto potentials, but only for systems
whose natural frequencies are identical, and only at configurations that
minimise the dynamic potential. Both are real restrictions, so the chain is
worth nothing unless something satisfies them. This section exhibits a system
that does, and — on the other side — a system for which the full potential
provably has no minimum at all, which is what forced the reduction in the first
place. -/

/-- Two oscillators, unit coupling, common natural frequency `Ω`. -/
noncomputable def pairSystem (Ω : ℝ) : KuramotoSystem Bool where
  omega := fun _ => Ω
  A := fun _ _ => 1
  symm := fun _ _ => rfl

/-- The fully synchronized trajectory: both phases advance at the common
frequency. -/
noncomputable def pairTrajectory (Ω : ℝ) : ℝ → Bool → ℝ := fun t _ => Ω * t

theorem pairTrajectory_is_trajectory (Ω : ℝ) :
    is_kuramoto_trajectory (pairSystem Ω) (pairTrajectory Ω) := by
  intro i t
  have h : HasDerivAt (fun t : ℝ => Ω * t) Ω t := by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hval : (pairSystem Ω).omega i
      + ∑ j, (pairSystem Ω).A i j
          * Real.sin (pairTrajectory Ω t j - pairTrajectory Ω t i) = Ω := by
    simp [pairSystem, pairTrajectory]
  rw [hval]
  exact h

/-- In the rotating frame the trajectory sits at the origin — where
`phase_locked_minimizes_potential` says the dynamic potential is minimised. -/
theorem rotate_pairTrajectory (Ω : ℝ) (t : ℝ) :
    rotate Ω (pairTrajectory Ω) t = fun _ => 0 := by
  funext i
  simp [rotate, pairTrajectory]

/-- **The chain fires.** Every hypothesis of `rotating_frame_chain` is
discharged concretely: the rotated trajectory solves the zero-frequency
equations, the dynamic potential is non-increasing along it, the original
phases are locked, and the order parameter is `1`. -/
theorem pair_rotating_frame_chain (Ω : ℝ) (t : ℝ) :
    is_kuramoto_trajectory (pairSystem Ω).reduced (rotate Ω (pairTrajectory Ω))
      ∧ deriv (fun t => kuramoto_potential_dynamic (pairSystem Ω)
            (rotate Ω (pairTrajectory Ω) t)) t ≤ 0
      ∧ is_phase_locked (pairTrajectory Ω t)
      ∧ order_parameter_r_sq (pairTrajectory Ω t) = 1 := by
  refine rotating_frame_chain (pairSystem Ω) Ω (fun _ => rfl) (fun _ _ => by
    simp [pairSystem]) (pairTrajectory Ω) (pairTrajectory_is_trajectory Ω) t ?_
  intro phi
  rw [rotate_pairTrajectory]
  exact phase_locked_minimizes_potential (pairSystem Ω) (fun _ _ => by
    simp [pairSystem]) phi

/-- The full potential really is non-constant along the reduction: at the
synchronized configuration it differs from its value at the origin exactly by
the frequency term. -/
example (Ω : ℝ) (t : ℝ) :
    kuramoto_potential (pairSystem Ω) (pairTrajectory Ω t)
      = kuramoto_potential_dynamic (pairSystem Ω) (rotate Ω (pairTrajectory Ω) t)
        - 2 * Ω * (Ω * t) := by
  rw [kuramoto_potential_eq_dynamic_sub, rotate_pairTrajectory]
  simp [kuramoto_potential_dynamic, pairSystem, pairTrajectory]
  ring

/-- **The other side.** With a non-zero natural frequency the full Kuramoto
potential is unbounded below, so "the phase-locked state minimises the Lyapunov
potential" is false of it — there is no minimum to attain. The hypothesis of
`kuramoto_potential_unbounded_below` is satisfiable. -/
example (C : ℝ) : ∃ theta : Bool → ℝ, kuramoto_potential (pairSystem 1) theta < C :=
  kuramoto_potential_unbounded_below (pairSystem 1) ⟨true, by simp [pairSystem]⟩ C

/-! ## 8. Wiring rigidity, and the continuum separation

`Phase7_Rigidity` claims two things that are worth nothing without instances:
that `is_strictly_suboptimal` — the hypothesis `Phase7_HardwareComparison` had to
assume — follows from a wiring pattern that misses the best pair, and that a
finitely-sited architecture registers nothing in the field functional. Both are
exhibited here. -/

/-- A three-site substrate whose only wire joins sites `0` and `1`. -/
def rigidWiring : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0)}

/-- Sites `0` and `2` are in phase; site `1` is in antiphase. The architecture's
one wire therefore joins the maximally *anti*-correlated pair, while the
perfectly correlated pair `(0, 2)` has no wire at all. -/
noncomputable def rigidPhases : Fin 3 → ℝ := fun i => if i = 1 then Real.pi else 0

theorem rigidWiring_bound :
    ∀ p ∈ rigidWiring, Real.cos (rigidPhases p.2 - rigidPhases p.1) ≤ -1 := by
  intro p hp
  fin_cases hp <;> simp [rigidPhases]

theorem rigid_unwired_better : (-1 : ℝ) < Real.cos (rigidPhases 2 - rigidPhases 0) := by
  simp [rigidPhases]

/-- The architecture can spend its whole budget, and the best it can buy is
`-1`: total anti-correlation. -/
theorem exists_rigid_coupling :
    ∃ A, RealizableIn rigidWiring 1 A ∧ totalCorrelation rigidPhases A = -1 := by
  obtain ⟨A, hA, hval⟩ :=
    exists_realizable_pair rigidWiring 1 zero_le_one rigidPhases 0 1
      (by decide) (by decide) (by decide)
  exact ⟨A, hA, by rw [hval]; simp [rigidPhases]⟩

/-- **The hypothesis is derived, and the gap is `2`.** Every coupling this
architecture can realize at unit budget is strictly suboptimal — no longer an
assumption — and an unconstrained reallocation of the same budget beats it by at
least `2`, the full swing from anti-correlation to correlation. -/
theorem rigid_architecture_is_beaten (A : Fin 3 → Fin 3 → ℝ)
    (hA : RealizableIn rigidWiring 1 A) :
    is_strictly_suboptimal A rigidPhases
      ∧ ∃ A', is_valid_coupling A' ∧ total_coupling_resources A' = 1
          ∧ totalCorrelation rigidPhases A' - totalCorrelation rigidPhases A ≥ 2 := by
  refine ⟨rigid_is_strictly_suboptimal rigidWiring 1 (-1) one_pos rigidPhases 0 2 A hA
      rigidWiring_bound rigid_unwired_better, ?_⟩
  obtain ⟨A', hvalid, hres, _, hgap⟩ :=
    rigid_gap rigidWiring 1 (-1) one_pos rigidPhases 0 2 (by decide) A hA
      rigidWiring_bound rigid_unwired_better
  refine ⟨A', hvalid, hres, ?_⟩
  have : (1 : ℝ) * (Real.cos (rigidPhases 2 - rigidPhases 0) - (-1)) = 2 := by
    simp [rigidPhases]; norm_num
  linarith [hgap, this.symm.le, this.le]

/-- Phase 7's reallocation lemma now fires with no assumed hypothesis: the
suboptimality it needs comes from the wiring. -/
theorem rigid_architecture_beaten_by_phase7 (A : Fin 3 → Fin 3 → ℝ)
    (hA : RealizableIn rigidWiring 1 A) :
    ∃ A_flex : Fin 3 → Fin 3 → ℝ, is_valid_coupling A_flex ∧
      total_coupling_resources A_flex = total_coupling_resources A ∧
      (∑ i, ∑ j, A_flex i j * Real.cos (rigidPhases j - rigidPhases i)) >
      (∑ i, ∑ j, A i j * Real.cos (rigidPhases j - rigidPhases i)) :=
  exists_better_coupling_allocation A rigidPhases hA.1
    (rigid_architecture_is_beaten A hA).1

/-! ### The continuum half -/

/-- A single-site architecture on the real line, carrying a thousand units of
coupling weight — all of it at the origin. -/
noncomputable def pointArchitecture : ℝ → ℝ → ℝ := fun x _ => if x = 0 then 1000 else 0

theorem pointArchitecture_sited : SitedOn ({0} : Finset ℝ) pointArchitecture := by
  intro x hx y
  simp only [pointArchitecture, ite_eq_right_iff]
  intro h
  exact absurd (by simp [h]) hx

/-- **Weight at a point buys nothing.** However large the coupling at the origin,
the field correlation is exactly zero — for every phase field. -/
theorem pointArchitecture_field_zero (theta : ℝ → ℝ) :
    fieldCorrelation volume theta pointArchitecture = 0 :=
  fieldCorrelation_sited_eq_zero volume {0} pointArchitecture pointArchitecture_sited theta

/-- A unit patch of unit-strength field coupling registers `1`. -/
theorem patch_field_one :
    fieldCorrelation volume (fun _ => 0) (patchKernel (Set.Ico (0 : ℝ) 1) 1) = 1 := by
  rw [fieldCorrelation_patchKernel volume _ measurableSet_Ico 1]
  simp

/-- The typed separation, instantiated: a `Finset ℝ` of sites against a set of
positive measure. -/
example (theta : ℝ → ℝ) :
    fieldCorrelation volume theta pointArchitecture
      < fieldCorrelation volume (fun _ => 0) (patchKernel (Set.Ico (0 : ℝ) 1) 1) :=
  sited_architecture_below_field_optimum volume {0} pointArchitecture pointArchitecture_sited
    theta (Set.Ico 0 1) measurableSet_Ico (by simp) (by simp) 1 one_pos

/-! ## 9. The mean-field threshold is a statement about coupling, not about size

`exhibits_phase_transition` compares `mean_field_coupling` — the kernel averaged
over both arguments — against `K_c = 2D`, and requires the substrate's `volume`
to be a probability measure. This section shows that both halves of that
sentence do work:

* `cellVolume_prob` / `cellSys_strength`: the hypothesis is satisfiable, and
  under it a constant kernel `K` has mean-field strength exactly `K`, so the
  predicate reduces to `K > 2D` — the inequality the Kuramoto derivation is
  about. The predicate is therefore neither vacuous nor trivially true: it holds
  of `cellSys 3` at `D = 1` and fails for `cellSys 1`.
* `duo_double_integral_const` / `duoWeak_inflated`: without the hypothesis it is
  false. On the counting-measure substrate `Duo` of §5 the *unnormalized* double
  integral of a constant kernel is `4K` rather than `K`, and `duoWeak` is a
  system whose coupling is a factor of two *below* threshold yet whose
  unnormalized double integral clears `2D`. Mass was doing the work, not
  coupling.

Nothing here proves `K_c = 2D`; that remains a stipulation validated
numerically. What is settled is that the predicate now says something whose
truth depends only on the physics.
-/

/-- Two sites again, but carrying the *normalized* counting measure. -/
inductive Cell : Type
  | l | r
  deriving DecidableEq

instance : Fintype Cell := ⟨{Cell.l, Cell.r}, by intro x; cases x <;> decide⟩
instance : TopologicalSpace Cell := ⊥

/-- Counting measure divided by the number of sites: a probability measure. -/
noncomputable instance : MeasureSpace Cell :=
  { (⊤ : MeasurableSpace Cell) with volume := (2 : ℝ≥0∞)⁻¹ • @Measure.count Cell ⊤ }

instance : MeasurableSingletonClass Cell := ⟨fun _ => trivial⟩

theorem cell_card : Fintype.card Cell = 2 := rfl

instance cellVolume_prob : IsProbabilityMeasure (volume : Measure Cell) := by
  constructor
  show ((2 : ℝ≥0∞)⁻¹ • @Measure.count Cell ⊤) Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul, Measure.count_univ]
  simp only [ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, cell_card]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- A uniformly coupled substrate of strength `c`, at noise `D = 1` — so the
threshold `K_c = 2D` sits at `2`. -/
noncomputable def cellSys (c : ℝ) : StochasticNeuralField Cell where
  omega := fun _ => 0
  K := fun _ _ => c
  tau := 1
  D := 1
  h_D_pos := one_pos
  Omega_avg := 0

/-- **The normalization is right.** Averaging a constant kernel over a
probability substrate returns the constant — no factor of the substrate's
size. -/
theorem cellSys_strength (c : ℝ) : mean_field_coupling (cellSys c) = c :=
  mean_field_coupling_const (cellSys c) c rfl

/-- Above threshold: `K = 3 > 2 = 2D`. -/
example : exhibits_phase_transition (cellSys 3) :=
  (exhibits_phase_transition_const_iff (cellSys 3) 3 rfl).mpr (by norm_num [cellSys])

/-- Below threshold: `K = 1 < 2 = 2D`. The predicate is not trivially true. -/
example : ¬ exhibits_phase_transition (cellSys 1) := fun h =>
  absurd ((exhibits_phase_transition_const_iff (cellSys 1) 1 rfl).mp h)
    (by norm_num [cellSys])

/-- On the unnormalized substrate of §5, a constant kernel integrates to four
times itself: the double integral picks up `(volume univ)² = 4`. -/
theorem duo_double_integral_const (c : ℝ) : (∫ _x : Duo, ∫ _y : Duo, c) = 4 * c := by
  rw [duo_volume]
  rw [integral_count (fun _ : Duo => ∫ _y : Duo, c ∂(Measure.count : Measure Duo))]
  simp only [integral_count, duo_sum]
  ring

/-- Half the coupling needed, and half the noise: `K = 1/2` against `K_c = 1`,
so this substrate is a factor of two *below* threshold. -/
noncomputable def duoWeak : StochasticNeuralField Duo where
  omega := fun _ => 0
  K := fun _ _ => 1/2
  tau := 1
  D := 1/2
  h_D_pos := by norm_num
  Omega_avg := 0

/-- **Why the hypothesis is not decoration.** `duoWeak`'s coupling is `1/2`
against a threshold of `1`, yet its unnormalized double integral is `2 > 1`.
Compared this way, the substrate crosses the threshold on mass alone — which is
what the earlier form of `exhibits_phase_transition` did. -/
theorem duoWeak_inflated :
    (∫ x : Duo, ∫ y : Duo, duoWeak.K x y) > critical_coupling duoWeak.D
      ∧ duoWeak.K Duo.a Duo.b < critical_coupling duoWeak.D := by
  constructor
  · show (∫ _x : Duo, ∫ _y : Duo, (1/2 : ℝ)) > critical_coupling (1/2 : ℝ)
    rw [duo_double_integral_const, critical_coupling]
    norm_num
  · show (1/2 : ℝ) < critical_coupling (1/2 : ℝ)
    rw [critical_coupling]
    norm_num

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

/-! ## 11. A double well: the symmetry, its breaking, and why the conclusion is a.e.

`§3` witnesses `ActionPrinciples` on a one-point spacetime with `V v = v²`. That
suffices to show the class is inhabitable and nothing more: the vacuum is a
single point, so there is no symmetry to break, and on a one-point spacetime
"almost everywhere" and "everywhere" coincide, so the theorem's actual
conclusion is invisible. This section fixes both.

The substrate is `Bool` carrying `Measure.dirac true` — a probability measure
whose support is one of the two points, so a field can deviate off the support
for free. The potential is the double well `V v = (v² - 1)²`, whose vacuum
manifold is `{-1, 1}`: **degenerate**, which is the premise the phrase
"spontaneous symmetry breaking" presupposes and which `§3`'s `v²` does not have.

Three things get proved here that were previously assumed or unstated.

* **`h_min` is discharged, not hypothesised.** `spontaneous_symmetry_breaking`
  takes `h_min : ∀ phi', TotalEnergy phi ≤ TotalEnergy phi'` as an assumption,
  and no compactness or direct-method argument anywhere in the development
  produces one. Here `wellSpike_global_min` proves it outright, so the theorem is
  applied to a system where its hypothesis is a fact.
* **The `∀ᵐ` cannot be strengthened to `∀`.** `wellSpike` sits at the vacuum on
  the support and at `0` off it; `wellSpike_ae_vacuum` holds and
  `wellSpike_not_everywhere_vacuum` proves the pointwise version *fails* for the
  same field. The doc-string on `pointwise_vacuum_of_global_min` says the old
  `∀ x` form "was one of the reasons the axiomatic formulation was unsound"; this
  is that claim as a theorem.
* **The symmetry classes are inhabited, and the symmetry is a real one.**
  `signSymmetry` is the `ℤ₂` action `v ↦ ±v` on the value space;
  `signInvariant` discharges `total_energy_invariant` because `(±v)² = v²`. The
  action is not trivial — `symmetry_swaps_vacua` sends one vacuum to the other —
  so `wellSpike` and its image have equal energy and differ
  (`wellSpike_partner_same_energy`, `wellSpike_partner_ne`): a symmetric
  functional with a non-symmetric minimiser, which is what symmetry breaking is.

**What this does not establish.** There is still no Noether theorem: nothing
constructs a conserved quantity from `signInvariant`, and `ℤ₂` is discrete, so
there is no one-parameter family to differentiate along in the first place. The
`Continuous` in `ContinuousSymmetryGroup` is a name, not a hypothesis — the class
carries no continuity or homomorphism law at all, which is why this instance is
cheap. And the spacetime is two points with a Dirac measure, so nothing here
exercises any geometry. -/

/-- The double well `V v = (v² - 1)²`. Vacuum manifold `{-1, 1}`. -/
noncomputable def wellV (v : ℝ) : ℝ := (v ^ 2 - 1) ^ 2

/-- Total energy on the two-point spacetime: the potential integrated against
`δ_true`, so only the value at `true` counts. -/
noncomputable def wellEnergy (phi : FieldState Bool ℝ) : ℝ :=
  ∫ x, wellV (phi x) ∂(Measure.dirac true)

noncomputable instance wellAction :
    ActionPrinciples Bool ℝ (fun _ => 0) wellEnergy wellEnergy wellV
      (Measure.dirac true) where
  total_eq := by intro phi; simp
  kinetic_nonneg := by intro phi; norm_num
  kinetic_const := by intro v; rfl
  potential_integral := by intro phi; rfl
  potential_integrable := by intro phi; exact Integrable.of_finite

@[simp] theorem wellEnergy_apply (phi : FieldState Bool ℝ) :
    wellEnergy phi = wellV (phi true) := by
  unfold wellEnergy; simp

/-- The vacuum is degenerate: both `1` and `-1` minimise, and they differ. This
is what `§3`'s single-well witness lacks. -/
theorem one_mem_vacuum : (1 : ℝ) ∈ DynamicalVacuum wellV := by
  intro v'; simp [wellV]; positivity

theorem neg_one_mem_vacuum : (-1 : ℝ) ∈ DynamicalVacuum wellV := by
  intro v'; simp [wellV]; positivity

theorem vacuum_degenerate :
    (1 : ℝ) ∈ DynamicalVacuum wellV ∧ (-1 : ℝ) ∈ DynamicalVacuum wellV
      ∧ (1 : ℝ) ≠ -1 :=
  ⟨one_mem_vacuum, neg_one_mem_vacuum, by norm_num⟩

theorem zero_not_mem_vacuum : (0 : ℝ) ∉ DynamicalVacuum wellV := by
  intro h
  have := h 1
  simp [wellV] at this
  linarith

/-- At the vacuum on the support of the measure, off it elsewhere. -/
noncomputable def wellSpike : FieldState Bool ℝ :=
  ⟨fun b => if b then 1 else 0, continuous_of_discreteTopology⟩

/-- **The minimisation hypothesis, discharged.** `h_min` of
`spontaneous_symmetry_breaking` is an assumption everywhere else in the
development; here it is a proof. -/
theorem wellSpike_global_min : ∀ phi', wellEnergy wellSpike ≤ wellEnergy phi' := by
  intro phi'
  rw [wellEnergy_apply, wellEnergy_apply]
  have h : wellV (wellSpike true) = 0 := by simp [wellSpike, wellV]
  rw [h]
  simp [wellV]
  positivity

/-- Derivation 1 applied to a system whose every hypothesis is proved. -/
theorem wellSpike_ae_vacuum :
    ∀ᵐ x ∂(Measure.dirac true), wellSpike x ∈ DynamicalVacuum wellV :=
  spontaneous_symmetry_breaking wellAction wellSpike 1 one_mem_vacuum wellSpike_global_min

/-- **And the almost-everywhere is necessary.** The same energy-minimising field
leaves the vacuum at `false`, which the measure does not see. -/
theorem wellSpike_not_everywhere_vacuum :
    ¬ ∀ b : Bool, wellSpike b ∈ DynamicalVacuum wellV := by
  intro h
  exact zero_not_mem_vacuum (by simpa [wellSpike] using h false)

/-- The `ℤ₂` sign symmetry `v ↦ ±v`, acting trivially on spacetime. The class
carries no law, so the content is entirely in `signInvariant` below. -/
noncomputable instance signSymmetry : ContinuousSymmetryGroup ℤˣ Bool ℝ where
  space_action := fun _ x => x
  value_action := fun g v => ((g : ℤ) : ℝ) * v
  field_action := fun g phi =>
    ⟨fun x => ((g : ℤ) : ℝ) * phi x, continuous_of_discreteTopology⟩

/-- **The energy really is invariant**, because `(±v)² = v²`. This is the first
instance of `SymmetryInvariantAction` in the development; the class previously
had none, and `main.tex` said so. -/
instance signInvariant :
    SymmetryInvariantAction ℤˣ Bool ℝ (fun _ => 0) wellEnergy wellEnergy wellV
      (Measure.dirac true) where
  total_energy_invariant := by
    intro g phi
    rw [wellEnergy_apply, wellEnergy_apply]
    show wellV (((g : ℤ) : ℝ) * phi true) = wellV (phi true)
    rcases Int.units_eq_one_or g with h | h <;> simp [h, wellV]

/-- The symmetry is not trivial on the vacuum: it exchanges the two minima. -/
theorem symmetry_swaps_vacua :
    ContinuousSymmetryGroup.value_action (G := ℤˣ) (Spacetime := Bool) (-1 : ℤˣ) (1 : ℝ)
      = -1 := by
  show ((((-1 : ℤˣ) : ℤ)) : ℝ) * 1 = -1
  norm_num

/-- **Symmetry breaking, exhibited.** The minimiser has a distinct image under a
symmetry of the energy, and the image has the same energy. So the minimiser is
not invariant even though the functional is. -/
theorem wellSpike_partner_same_energy :
    wellEnergy (ContinuousSymmetryGroup.field_action (-1 : ℤˣ) wellSpike)
      = wellEnergy wellSpike :=
  signInvariant.total_energy_invariant (-1 : ℤˣ) wellSpike

theorem wellSpike_partner_ne :
    (ContinuousSymmetryGroup.field_action (-1 : ℤˣ) wellSpike) true ≠ wellSpike true := by
  show ((((-1 : ℤˣ) : ℤ)) : ℝ) * wellSpike true ≠ wellSpike true
  simp [wellSpike]
  norm_num

/-! ### 11.1 The vacuum manifold is disconnected, and that forces a wall

  Everything above concerns the *energy* side of Derivation 1: a degenerate
  minimum, a symmetry that exchanges its two branches, and a minimiser that is
  not invariant. None of it produces a defect. The section's title claims
  inevitability of boundaries, and the theorem that delivers it is the `π₀`
  obstruction in `Phase1_Primitives.lean` §3 — which needs the vacuum manifold
  to be genuinely disconnected, and needs that to be proved rather than drawn.

  `wellVacuum_eq` computes the vacuum manifold of the double well outright:
  `DynamicalVacuum wellV = {-1, 1}`. Before this the file knew only that `1` and
  `-1` are in it and `0` is not, which leaves open that the set is larger and
  possibly connected. `wellVacuum_separated` then proves the disconnection in
  the form the theorem consumes: **no** preconnected subset of the vacuum
  manifold contains both minima, because a preconnected subset of `ℝ` is an
  interval and an interval spanning `-1` and `1` contains `0`, which is at the
  top of the barrier.

  `wellV_domain_wall` is the payoff and it quantifies over *every* field: any
  continuous field on any connected substrate that reaches `-1` somewhere and
  `1` somewhere else leaves the vacuum manifold at some point. No formula for
  the field appears, and none is needed — this is the sense in which the wall is
  inevitable rather than exhibited.

  **Non-vacuity is a separate question and is answered separately.** A theorem
  quantified over all fields is worthless if no field satisfies its hypotheses,
  so `kink` supplies one: the clipped identity on `ℝ`, at `-1` below `-1`, at
  `1` above `1`. `kink_leaves_vacuum` fires the theorem on it, and
  `kink_zero_notMem` locates the wall — at the origin, where the field sits at
  the top of the barrier — so the existence statement is not merely formal.
-/

section DomainWall

/-- **The vacuum manifold, computed.** `{-1, 1}` exactly: a minimiser has
`(v² - 1)² ≤ 0`, so `v² = 1`. -/
theorem wellVacuum_eq : DynamicalVacuum wellV = {-1, 1} := by
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have h1 : wellV v ≤ wellV 1 := h 1
    have h0 : wellV 1 = 0 := by norm_num [wellV]
    have hsq : (v ^ 2 - 1) ^ 2 ≤ 0 := by rw [h0] at h1; exact h1
    have hfac : (v - 1) * (v + 1) = 0 := by nlinarith [sq_nonneg (v ^ 2 - 1)]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (rfl | rfl)
    · exact neg_one_mem_vacuum
    · exact one_mem_vacuum

/-- **The disconnection, in the form the `π₀` theorem consumes.** No preconnected
subset of the vacuum manifold contains both minima.

In `ℝ` a preconnected set is order-convex, so one containing `-1` and `1`
contains the whole interval between them, and in particular `0` — which is the
top of the barrier, not a minimum. -/
theorem wellVacuum_separated (S : Set ℝ) (hS : _root_.IsPreconnected S)
    (hSM : S ⊆ DynamicalVacuum wellV) (h1 : (-1 : ℝ) ∈ S) : (1 : ℝ) ∉ S := by
  intro h2
  have h0 : (0 : ℝ) ∈ S :=
    hS.Icc_subset h1 h2 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  exact zero_not_mem_vacuum (hSM h0)

/-- **Derivation 1's central claim, as a theorem.** Every continuous field on a
connected substrate that sits at one vacuum somewhere and at the other somewhere
else leaves the vacuum manifold at some point.

The substrate `X` is arbitrary — any connected topological space — and the field
is arbitrary. Nothing is exhibited and nothing is solved: this is the
inevitability the section's title claims, and it holds of fields for which no
formula exists. -/
theorem wellV_domain_wall {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (phi : X → ℝ) (h_cont : Continuous phi) (a b : X)
    (ha : phi a = -1) (hb : phi b = 1) :
    ∃ x, phi x ∉ DynamicalVacuum wellV := by
  refine exists_notMem_of_no_common_preconnected _ phi h_cont a b fun S hS hSM haS => ?_
  rw [hb]
  rw [ha] at haS
  exact wellVacuum_separated S hS hSM haS

/-! #### A field that satisfies the hypotheses -/

/-- The clipped identity: `-1` below `-1`, `1` above `1`, and the straight climb
between them. A field connecting the two vacua, so the theorem above is not
quantifying over an empty class. -/
noncomputable def kink : ℝ → ℝ := fun x => max (-1) (min 1 x)

theorem kink_continuous : Continuous kink := by
  unfold kink
  exact continuous_const.max (continuous_const.min continuous_id)

@[simp] theorem kink_neg_one : kink (-1) = -1 := by norm_num [kink]

@[simp] theorem kink_one : kink 1 = 1 := by norm_num [kink]

@[simp] theorem kink_zero : kink 0 = 0 := by norm_num [kink]

/-- The theorem fires on a real substrate: `kink` cannot stay in the vacuum. -/
theorem kink_leaves_vacuum : ∃ x : ℝ, kink x ∉ DynamicalVacuum wellV :=
  wellV_domain_wall kink kink_continuous (-1) 1 kink_neg_one kink_one

/-- **And the wall is where one expects it.** At the origin the field is at the
top of the barrier. Recorded so that `kink_leaves_vacuum` is not merely a formal
existence statement. -/
theorem kink_zero_notMem : kink 0 ∉ DynamicalVacuum wellV := by
  rw [kink_zero]; exact zero_not_mem_vacuum

/-- The field really does connect the two components, rather than satisfying the
hypotheses degenerately: its two endpoint values are distinct minima. -/
theorem kink_connects_distinct_vacua :
    kink (-1) ∈ DynamicalVacuum wellV ∧ kink 1 ∈ DynamicalVacuum wellV
      ∧ kink (-1) ≠ kink 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [kink_neg_one]; exact neg_one_mem_vacuum
  · rw [kink_one]; exact one_mem_vacuum
  · rw [kink_neg_one, kink_one]; norm_num

end DomainWall

/-! ## 12. The last three structures without instances

Rule §2 of `PhysicsOfConsciousness/AGENTS.md` requires every structure carrying
physical content to be inhabited. These three were the remainder: nothing
headline rests on them, which is exactly why they went unnoticed. Each witness
is short; the `PlasticNeuralField` one is not, because it reuses the gradient
flow of §5 and therefore satisfies `is_gradient_descent` with a genuinely
decreasing σ rather than by being constant. -/

/-- A two-state stochastic matrix: the fair coin. -/
noncomputable def boolStochastic : StochasticMatrix Bool where
  P := fun _ _ => 1 / 2
  nonneg := by intro i j; norm_num
  sum_eq_one := by intro i; simp

/-- The plastic field on the `Duo` substrate of §5: the coupling kernel is the
gradient flow `duoFlow`, whose off-diagonal entries relax as `e^{-t}`. -/
noncomputable def duoPlastic : PlasticNeuralField Duo where
  toStochasticNeuralField := duoSys.withKernel (duoFlow 0)
  K_t := fun t x y => duoFlow t (x, y)
  h_K_init := rfl

/-- The witness is not degenerate: it satisfies `is_gradient_descent`, and §5
already showed the descent along `duoFlow` is *strict* (`σ(t) = e^{-2t}`), so
this is not `Antitone` discharged by a constant. -/
theorem duoPlastic_gradient_descent :
    is_gradient_descent duoPlastic (fun _ => duoTheta) := fun _ _ h =>
  entropy_production_antitone_of_gradient_flow duo_volume duoSys duoTheta duoFlow
    duoFlow_hasDerivAt h

/-- The Euclidean bilinear form `g(u, v) = u * v` on the tangent space of `ℝ`.

Stated through `ℝ`-typed helpers on purpose: `TangentSpace I x` is a `def`, so
its `Mul` and `AddCommGroup` instances are not the ones instance search finds for
`ℝ`, and writing the proofs directly in the class fields fails with instance
mismatches even though everything is definitionally equal. -/
noncomputable def realForm (x : ℝ) :
    TangentSpace (modelWithCornersSelf ℝ ℝ) x →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℝ) x →L[ℝ] ℝ :=
  ContinuousLinearMap.mul ℝ ℝ

theorem realForm_apply (x u v : ℝ) : realForm x u v = u * v := rfl

theorem realForm_symm (x u v : ℝ) : realForm x u v = realForm x v u := by
  rw [realForm_apply, realForm_apply, mul_comm]

theorem realForm_nondeg (x u : ℝ) (h : ∀ v : ℝ, realForm x u v = 0) : u = 0 := by
  have h1 : u * 1 = 0 := by rw [← realForm_apply]; exact h 1
  linarith

/-- The real line with the Euclidean metric. Positive definite, so this is a
Riemannian rather than a properly pseudo-Riemannian witness — the class asks only
for symmetry and non-degeneracy, and a Lorentzian example would need a
two-dimensional model. -/
noncomputable instance realMetric :
    PseudoRiemannianManifold (modelWithCornersSelf ℝ ℝ) ℝ where
  metric := realForm
  symm := realForm_symm
  nondeg := realForm_nondeg


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


/-! ## 15. A trajectory that runs into the minimum

  Open item **O20** records that nothing in this development runs a dynamics.
  Every Derivation 5 result is conditional on `thermodynamic_equilibrium` — the
  cover is *assumed* to sit at the potential minimum — and until now the only
  trajectory anywhere in the development was §7's rigid rotation
  `pairTrajectory Ω t = Ω·t`, which starts synchronised and therefore never
  converges to anything. `is_kuramoto_trajectory` was a predicate whose one
  inhabitant began at its own limit.

  This section exhibits a trajectory that does not. On two oscillators with unit
  coupling and zero natural frequency, the phase difference `Δ = θ₁ - θ₀` obeys
  the scalar equation `Δ̇ = -2 sin Δ`, which is integrable: `Δ(t) = 2 arctan(c
  e^{-2t})`. Splitting it symmetrically gives an exact solution of the full
  Kuramoto system (`pairRelax_is_trajectory`), defined on all of `ℝ`, and
  everything downstream is a statement about it:

  * it is **not** phase-locked at time zero — at `c = 1` the phases start a
    quarter turn apart (`pairRelax_not_locked_at_zero`);
  * the cosine of the phase difference tends to `1`
    (`pairRelax_tendsto_locked`), which is the value `is_phase_locked` demands;
  * the order parameter tends to `1` (`pairRelax_order_parameter_tendsto`), via
    the two-oscillator identity `r² = (1 + cos Δ)/2`;
  * and the dynamic potential tends to its **global minimum**
    (`pairRelax_potential_tendsto_min`) — the value
    `phase_locked_minimizes_potential` names.

  **What this settles and what it does not.** It settles the vacuity worry:
  the phrase "a thermodynamic phase transition into unity" now has one instance
  in Lean where a trajectory genuinely runs from a non-synchronised state into
  the minimiser, rather than being placed there by hypothesis. Combined with
  `is_kuramoto_trajectory_unique` this is the *only* trajectory through its
  initial state, so it is not one solution among many.

  It does not settle O20 by itself. `is_kuramoto_trajectory_exists` (O20(a))
  gives every system a solution on all of `ℝ`; `dynamic_potential_tendsto`
  (O20(b)) makes every trajectory's potential converge; `velocity_sq_tendsto_zero`
  (O22) makes every trajectory's velocity tend to zero, and
  `pairRelax_velocity_sq_tendsto_zero` below is that theorem fired on this
  trajectory. What none of them gives is *where* the motion stops.

  That is O20(d), and it is now proved — `kuramoto_tendsto_global_minimum` in
  `Phase4_RotatingFrame.lean` §7 — but conditionally, and by a Łojasiewicz
  estimate rather than the LaSalle principle this note used to name as the
  blocker. The general statement of O20(e) is genuinely **false**: splay and
  twisted configurations are equilibria too, so no theorem of the form "every
  trajectory reaches the phase-locked state" can be proved. The arc condition
  that makes it true is satisfied here for every `c`, since `2 arctan` lands in
  `(-π, π)`, which is why this witness converges and a general trajectory need
  not. §17 runs the general theorem on three sites, where no closed form of the
  kind this section relies on exists.
-/

section RunningDynamics

/-- `sin(2 arctan u) = 2u/(1+u²)`. -/
lemma sin_two_arctan (u : ℝ) : Real.sin (2 * Real.arctan u) = 2 * u / (1 + u ^ 2) := by
  have h1 : (0:ℝ) < 1 + u ^ 2 := by positivity
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have hs : Real.sqrt (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) = 1 + u ^ 2 :=
    Real.mul_self_sqrt h1.le
  have hne : Real.sqrt (1 + u ^ 2) ≠ 0 := by positivity
  have hsq : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt h1.le
  field_simp
  rw [hsq]

/-- The relaxing gap: `c e^{-2t}`, the tangent of half the phase difference. -/
noncomputable def relaxU (c : ℝ) (t : ℝ) : ℝ := c * Real.exp (-2 * t)

/-- Half the phase difference along the relaxing trajectory. -/
noncomputable def relaxAngle (c : ℝ) (t : ℝ) : ℝ := Real.arctan (relaxU c t)

/-- The relaxing two-oscillator trajectory: the phases approach each other. -/
noncomputable def pairRelax (c : ℝ) : ℝ → Bool → ℝ :=
  fun t i => if i then relaxAngle c t else -relaxAngle c t

lemma hasDerivAt_relaxU (c t : ℝ) : HasDerivAt (relaxU c) (-2 * relaxU c t) t := by
  have hin : HasDerivAt (fun t : ℝ => -2 * t) (-2 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
  have h : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t :=
    (Real.hasDerivAt_exp (-2 * t)).comp t hin
  have h2 := h.const_mul c
  refine h2.congr_deriv ?_
  simp [relaxU]
  ring

lemma hasDerivAt_relaxAngle (c t : ℝ) :
    HasDerivAt (relaxAngle c) (-2 * relaxU c t / (1 + relaxU c t ^ 2)) t := by
  have := (hasDerivAt_relaxU c t).arctan
  refine this.congr_deriv ?_
  field_simp

/-- **A trajectory that runs into synchrony.** The relaxing pair solves the
zero-frequency Kuramoto equations exactly. -/
theorem pairRelax_is_trajectory (c : ℝ) :
    is_kuramoto_trajectory (pairSystem 0) (pairRelax c) := by
  intro i t
  have hsin := sin_two_arctan (relaxU c t)
  cases i
  · have hval : (pairSystem 0).omega false
        + ∑ j, (pairSystem 0).A false j * Real.sin (pairRelax c t j - pairRelax c t false)
        = -(-2 * relaxU c t / (1 + relaxU c t ^ 2)) := by
      simp only [pairSystem, pairRelax, relaxAngle, Fintype.sum_bool]
      norm_num
      rw [show Real.arctan (relaxU c t) + Real.arctan (relaxU c t)
          = 2 * Real.arctan (relaxU c t) by ring, hsin]
      ring
    rw [hval]
    have hfun : (fun t : ℝ => pairRelax c t false) = fun t => -relaxAngle c t := by
      funext s; simp [pairRelax]
    rw [hfun]
    exact (hasDerivAt_relaxAngle c t).neg
  · have hval : (pairSystem 0).omega true
        + ∑ j, (pairSystem 0).A true j * Real.sin (pairRelax c t j - pairRelax c t true)
        = -2 * relaxU c t / (1 + relaxU c t ^ 2) := by
      simp only [pairSystem, pairRelax, relaxAngle, Fintype.sum_bool]
      norm_num
      rw [show -Real.arctan (relaxU c t) - Real.arctan (relaxU c t)
          = -(2 * Real.arctan (relaxU c t)) by ring, Real.sin_neg, hsin]
      ring
    rw [hval]
    have hfun : (fun t : ℝ => pairRelax c t true) = fun t => relaxAngle c t := by
      funext s; simp [pairRelax]
    rw [hfun]
    exact hasDerivAt_relaxAngle c t

/-! ### It converges, and it does not start where it ends -/

lemma relaxU_tendsto (c : ℝ) : Tendsto (relaxU c) atTop (𝓝 0) := by
  have hb : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
    have h2 : Tendsto (fun t : ℝ => (2 : ℝ) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
    have : (fun t : ℝ => -2 * t) = fun t : ℝ => -((2 : ℝ) * t) := by funext t; ring
    rw [this]
    exact tendsto_neg_atBot_iff.2 h2
  have he : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hb
  have h3 := he.const_mul c
  have heq : relaxU c = fun t : ℝ => c * Real.exp (-2 * t) := by funext t; rfl
  rw [heq]
  simpa using h3

lemma relaxAngle_tendsto (c : ℝ) : Tendsto (relaxAngle c) atTop (𝓝 0) := by
  have h := (Real.continuous_arctan.tendsto 0).comp (relaxU_tendsto c)
  rw [Real.arctan_zero] at h
  exact h

/-- The phase difference along the relaxing trajectory. -/
lemma pairRelax_gap (c t : ℝ) :
    pairRelax c t true - pairRelax c t false = 2 * relaxAngle c t := by
  simp [pairRelax]; ring

/-- **The trajectory synchronises.** The cosine of the phase difference tends to
`1` — the value `is_phase_locked` demands. -/
theorem pairRelax_tendsto_locked (c : ℝ) :
    Tendsto (fun t => Real.cos (pairRelax c t true - pairRelax c t false)) atTop (𝓝 1) := by
  have h : Tendsto (fun t => 2 * relaxAngle c t) atTop (𝓝 0) := by
    simpa using (relaxAngle_tendsto c).const_mul 2
  have h2 := (Real.continuous_cos.tendsto 0).comp h
  rw [Real.cos_zero] at h2
  have : (fun t => Real.cos (pairRelax c t true - pairRelax c t false))
      = Real.cos ∘ fun t => 2 * relaxAngle c t := by
    funext t; simp [Function.comp, pairRelax_gap]
  rw [this]
  exact h2

/-- With `c = 1` the trajectory starts at a phase difference of `π/2`: it is
*not* phase-locked at time zero, so it has somewhere to go. -/
theorem pairRelax_not_locked_at_zero : ¬ is_phase_locked (pairRelax 1 0) := by
  intro h
  have h1 := h true false
  rw [pairRelax_gap] at h1
  have hu : relaxU 1 0 = 1 := by simp [relaxU]
  rw [relaxAngle, hu, Real.arctan_one] at h1
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two] at h1
  norm_num at h1

/-! ### The potential falls to its minimum -/

/-- The dynamic potential along the relaxing trajectory, in closed form. -/
lemma pairRelax_potential (c t : ℝ) :
    kuramoto_potential_dynamic (pairSystem 0) (pairRelax c t)
      = -(1 + Real.cos (2 * relaxAngle c t)) := by
  simp only [kuramoto_potential_dynamic, pairSystem, Fintype.sum_bool, pairRelax]
  norm_num
  rw [show -relaxAngle c t - relaxAngle c t = -(2 * relaxAngle c t) by ring,
    show relaxAngle c t + relaxAngle c t = 2 * relaxAngle c t by ring, Real.cos_neg]
  ring

/-- The minimum value of the dynamic potential on this system. -/
lemma pairSystem_potential_min : kuramoto_potential_dynamic (pairSystem 0) (fun _ => 0) = -2 := by
  simp [kuramoto_potential_dynamic, pairSystem]

/-- **The potential falls to its global minimum along the trajectory.** -/
theorem pairRelax_potential_tendsto_min (c : ℝ) :
    Tendsto (fun t => kuramoto_potential_dynamic (pairSystem 0) (pairRelax c t)) atTop
      (𝓝 (kuramoto_potential_dynamic (pairSystem 0) (fun _ => 0))) := by
  rw [pairSystem_potential_min]
  have h : Tendsto (fun t => 2 * relaxAngle c t) atTop (𝓝 0) := by
    simpa using (relaxAngle_tendsto c).const_mul 2
  have h2 := (Real.continuous_cos.tendsto 0).comp h
  rw [Real.cos_zero] at h2
  have h3 : Tendsto (fun t => -(1 + Real.cos (2 * relaxAngle c t))) atTop (𝓝 (-(1 + 1))) := by
    exact (h2.const_add 1).neg
  have heq : (fun t => kuramoto_potential_dynamic (pairSystem 0) (pairRelax c t))
      = fun t => -(1 + Real.cos (2 * relaxAngle c t)) := by
    funext t; exact pairRelax_potential c t
  rw [heq]
  have : (-(1 + 1) : ℝ) = -2 := by norm_num
  rw [← this]
  exact h3

/-! ### The order parameter -/

/-- On two oscillators the squared order parameter is `(1 + cos Δ)/2`. -/
lemma pair_order_parameter (theta : Bool → ℝ) :
    order_parameter_r_sq theta = (1 + Real.cos (theta true - theta false)) / 2 := by
  simp only [order_parameter_r_sq, order_parameter_complex, Fintype.sum_bool]
  rw [Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  rw [mul_comm Complex.I _, mul_comm Complex.I _, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Real.cos_sub]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq (theta true), Real.sin_sq_add_cos_sq (theta false)]

/-- **The static order-parameter link: incoherent state.**
`order_parameter_complex` (discrete, empirical average over finitely many sites)
and `circularOrderParameter` (continuum integral against a density) agree on the
incoherent state: both are zero.

For the discrete side, opposite phases on two sites — `θ(false)=0`, `θ(true)=π` —
give `order_parameter_complex = 0`. For the continuum side, the uniform density
(von Mises at concentration zero) gives `circularOrderParameter = 0`.  This
isolates the mean-field limit (propagation of chaos) as the only remaining gap
between the two order-parameter notions. -/
theorem incoherent_orderParameters_agree :
    let theta : Bool → ℝ := fun b => if b then Real.pi else 0
    order_parameter_complex theta = 0 ∧
    circularOrderParameter (vonMisesDensity 0) = 0 :=
by
  intro theta
  constructor
  · unfold order_parameter_complex
    simp [theta, Complex.exp_zero]
    have h2 : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
      simpa [mul_comm] using Complex.exp_pi_mul_I
    simp [h2]
  · rw [circularOrderParameter_vonMises, besselRatio_zero]
    norm_num

/-- **The order parameter tends to 1 along the trajectory.** -/
theorem pairRelax_order_parameter_tendsto (c : ℝ) :
    Tendsto (fun t => order_parameter_r_sq (pairRelax c t)) atTop (𝓝 1) := by
  have heq : (fun t => order_parameter_r_sq (pairRelax c t))
      = fun t => (1 + Real.cos (pairRelax c t true - pairRelax c t false)) / 2 := by
    funext t; exact pair_order_parameter _
  rw [heq]
  have h := ((pairRelax_tendsto_locked c).const_add 1).div_const 2
  simpa using h

/-! ### The motion stops -/

/-- The velocity of the upper oscillator along the relaxing trajectory, in closed
form: it is exactly the derivative `hasDerivAt_relaxAngle` computes, which is
what makes `pairRelax` a solution in the first place. -/
lemma pairRelax_velocity (c t : ℝ) :
    kuramoto_velocity (pairSystem 0) (pairRelax c t) true
      = -2 * relaxU c t / (1 + relaxU c t ^ 2) := by
  have hsin := sin_two_arctan (relaxU c t)
  simp only [kuramoto_velocity, pairSystem, pairRelax, relaxAngle, Fintype.sum_bool]
  norm_num
  rw [show -Real.arctan (relaxU c t) - Real.arctan (relaxU c t)
      = -(2 * Real.arctan (relaxU c t)) by ring, Real.sin_neg, hsin]
  ring

/-- **The witness is not already at rest.** With `c = 1` the upper oscillator
moves at speed `1` at time zero, so the convergence below is a statement about a
trajectory that has somewhere to go. -/
theorem pairRelax_velocity_at_zero :
    kuramoto_velocity (pairSystem 0) (pairRelax 1 0) true = -1 := by
  rw [pairRelax_velocity]
  have hu : relaxU 1 0 = 1 := by simp [relaxU]
  rw [hu]; norm_num

/-- **O22 on the witness.** `velocity_sq_tendsto_zero` is a statement about an
arbitrary trajectory of an arbitrary zero-frequency system; here it fires on the
one trajectory this development writes down, whose velocity starts at `-1`
(`pairRelax_velocity_at_zero`) and is therefore genuinely decaying rather than
identically zero. -/
theorem pairRelax_velocity_sq_tendsto_zero (c : ℝ) :
    Tendsto (fun t => ∑ i, (kuramoto_velocity (pairSystem 0) (pairRelax c t) i) ^ 2)
      atTop (𝓝 0) :=
  velocity_sq_tendsto_zero (pairSystem 0) (fun _ => rfl) (pairRelax c)
    (pairRelax_is_trajectory c)

/-- **Uniqueness applied to the witness.** The relaxing trajectory is the *only*
solution through its initial state — so the convergence above is not a property
of a lucky choice among many solutions. -/
theorem pairRelax_unique (c : ℝ) (psi : ℝ → Bool → ℝ)
    (hpsi : is_kuramoto_trajectory (pairSystem 0) psi)
    (h0 : psi 0 = pairRelax c 0) : psi = pairRelax c :=
  is_kuramoto_trajectory_unique (pairSystem 0) psi (pairRelax c) hpsi
    (pairRelax_is_trajectory c) 0 h0

end RunningDynamics

/-!
## §16 — A symmetric kernel, and a one-way one that breaks the theorem

Open item **O11** asked whether `phase_locked_achieves_minimum_entropy`'s
`h_mean` hypothesis could be removed. It can, for symmetric kernels, and
`Phase8_ContinuousField` §2a proves it. This section discharges that theorem's
integrability hypotheses on a concrete substrate and then answers the question
the theorem itself cannot: whether the symmetry hypothesis that replaced
`h_mean` is doing work.

It is, and the check is a counterexample rather than a remark. `asymSys` is the
same two sites with a **one-way** coupling — `a` feels `b`, `b` does not feel
`a` — and there the phase-locked field is *strictly beaten*
(`asymSys_locked_not_minimal`): moving `b` to `−π/2` cancels `a`'s natural drift
without adding any drift at `b`, halving the entropy production. So
"phase-locking minimizes entropy production" is **false** for general kernels and
true for reciprocal ones, which is the physically intended case and the one
`ThermodynamicCover.A_symm` already imposes in Derivation 5.

Both systems live on the `Duo` substrate of §5, whose `volume` is counting
measure; `Integrable.of_finite` discharges every integrability hypothesis there,
including the one on the product measure that Fubini needs.
-/

section SymmetricKernel

/-- Counting measure on two sites is finite, which the variance bound needs. -/
instance : IsFiniteMeasure (volume : Measure Duo) := by
  constructor
  show (Measure.count : Measure Duo) Set.univ < ⊤
  rw [Measure.count_univ]; simp

/-- Entropy production on `Duo`, written out. Both integrals are sums against
counting measure, so the functional is four `sin` evaluations. -/
lemma duo_entropy (sys : StochasticNeuralField Duo) (theta : Duo → ℝ) :
    entropy_production_rate sys theta
      = (1/sys.D) * (sys.omega Duo.a + (sys.K Duo.a Duo.a * Real.sin (theta Duo.a - theta Duo.a)
          + sys.K Duo.a Duo.b * Real.sin (theta Duo.b - theta Duo.a)))^2
      + (1/sys.D) * (sys.omega Duo.b + (sys.K Duo.b Duo.a * Real.sin (theta Duo.a - theta Duo.b)
          + sys.K Duo.b Duo.b * Real.sin (theta Duo.b - theta Duo.b)))^2 := by
  unfold entropy_production_rate
  simp only [duo_volume, integral_count, duo_sum]

/-- Reciprocal coupling: every pair of sites influences the other equally. -/
noncomputable def symmSys : StochasticNeuralField Duo where
  omega := fun _ => 0
  K := fun _ _ => 1
  tau := 1
  D := 2
  h_D_pos := by norm_num
  Omega_avg := 0

theorem symmSys_symm : ∀ x y, symmSys.K x y = symmSys.K y x := fun _ _ => rfl

theorem symmSys_locked : is_dynamically_phase_locked symmSys (fun _ => 0) := by
  intro x
  show (0:ℝ) + ∫ y : Duo, (1:ℝ) * Real.sin (0 - 0) = 0
  simp

/-- **The unrestricted minimality theorem fires.** No `h_mean`: the conclusion
holds against *every* competitor field, with only integrability of its squared
drift assumed — and that is discharged here too, by finiteness. -/
theorem symmSys_minimizes :
    ∀ (t : Duo → ℝ) (_hf2 : Integrable
        (fun x => (symmSys.omega x + ∫ y : Duo, symmSys.K x y * Real.sin (t y - t x)) ^ 2)),
      entropy_production_rate symmSys (fun _ => 0) ≤ entropy_production_rate symmSys t :=
  (phase_locked_minimizes_entropy_of_symm symmSys (fun _ => 0) symmSys_symm symmSys_locked
    Integrable.of_finite (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite)).2

theorem symmSys_locked_entropy : entropy_production_rate symmSys (fun _ => 0) = 0 := by
  rw [duo_entropy]; norm_num [symmSys]

theorem symmSys_competitor_entropy : entropy_production_rate symmSys duoTheta = 1 := by
  rw [duo_entropy]
  norm_num [symmSys, duoTheta, Real.sin_pi_div_two]

/-- **The minimum is attained strictly.** `duoTheta` produces entropy `1` where
the locked field produces `0`, so `symmSys_minimizes` is not the observation that
every field is equally good. -/
theorem symmSys_gap :
    entropy_production_rate symmSys (fun _ => 0) < entropy_production_rate symmSys duoTheta := by
  rw [symmSys_locked_entropy, symmSys_competitor_entropy]; norm_num

/-- A **one-way** coupling: `a` feels `b`, `b` does not feel `a`. Physically this
is a directed synapse rather than a reciprocal field. -/
noncomputable def asymSys : StochasticNeuralField Duo where
  omega := fun _ => 1
  K := fun x y => if x = Duo.a ∧ y = Duo.b then 1 else 0
  tau := 1
  D := 2
  h_D_pos := by norm_num
  Omega_avg := 1

theorem asymSys_not_symm : ¬ ∀ x y, asymSys.K x y = asymSys.K y x := by
  intro h
  have hab := h Duo.a Duo.b
  simp [asymSys] at hab

theorem asymSys_locked : is_dynamically_phase_locked asymSys (fun _ => 0) := by
  intro x
  show (1:ℝ) + ∫ y : Duo, asymSys.K x y * Real.sin (0 - 0) = 1
  simp

/-- Phases `0` and `−π/2`. The one-way coupling subtracts exactly `a`'s natural
drift and adds nothing at `b`, which is what a reciprocal kernel cannot do. -/
noncomputable def asymTheta : Duo → ℝ
  | Duo.a => 0
  | Duo.b => -(Real.pi / 2)

theorem asymSys_locked_entropy : entropy_production_rate asymSys (fun _ => 0) = 1 := by
  rw [duo_entropy]; norm_num [asymSys]

theorem asymSys_competitor_entropy : entropy_production_rate asymSys asymTheta = 1/2 := by
  rw [duo_entropy]
  norm_num [asymSys, asymTheta, Real.sin_neg, Real.sin_pi_div_two]
  exact Or.inl (by decide)

/-- **Symmetry is necessary, not decorative.** Drop it and the theorem is false:
here a phase-locked field is strictly beaten by a competitor, so no amount of
extra work could remove `hK` from `phase_locked_minimizes_entropy_of_symm`.

This is the same kind of result as `contracting_implies_const` in §10 and
`ThermodynamicCover.phase_locked` in §13 — a proof that a hypothesis is as weak
as it can be made, rather than a hope that it is. -/
theorem asymSys_locked_not_minimal :
    entropy_production_rate asymSys asymTheta
      < entropy_production_rate asymSys (fun _ => 0) := by
  rw [asymSys_locked_entropy, asymSys_competitor_entropy]; norm_num

/-- The mechanism of the counterexample, isolated: for the one-way kernel the
total drift is *not* conserved, so `h_mean` fails and the variance bound has
nothing to stand on. Compare `total_drift_eq_of_symm`. -/
theorem asymSys_mean_drift_fails :
    (∫ x : Duo, (asymSys.omega x + ∫ y : Duo, asymSys.K x y
        * Real.sin (asymTheta y - asymTheta x)))
      ≠ asymSys.Omega_avg * (volume (Set.univ : Set Duo)).toReal := by
  have hlhs : (∫ x : Duo, (asymSys.omega x + ∫ y : Duo, asymSys.K x y
      * Real.sin (asymTheta y - asymTheta x))) = 1 := by
    simp only [duo_volume, integral_count, duo_sum]
    norm_num [asymSys, asymTheta, Real.sin_neg, Real.sin_pi_div_two]
    decide
  have hrhs : asymSys.Omega_avg * (volume (Set.univ : Set Duo)).toReal = 2 := by
    show (1:ℝ) * ((Measure.count : Measure Duo) Set.univ).toReal = 2
    rw [Measure.count_univ]
    have hcard : Fintype.card Duo = 2 := rfl
    simp [hcard]
  rw [hlhs, hrhs]; norm_num

end SymmetricKernel

/-! ## 17. A trajectory with no closed form that still reaches the minimum

  §15's `pairRelax` settles vacuity for O20 by exhibiting a trajectory that runs
  from an unsynchronised state into the potential's global minimum. It does so by
  *solving* the equation: on two oscillators the phase difference obeys a scalar
  ODE that integrates to `2 arctan(c e^{-2t})`, and every statement about it is a
  statement about that formula.

  That method does not scale, and it is the reason a general theorem was needed.
  On three sites the Kuramoto system has no closed-form solution, so nothing in
  §15's style can be repeated. This section runs the general theorem instead:
  `is_kuramoto_trajectory_exists` supplies a trajectory through an explicit
  initial configuration, and
  `kuramoto_tendsto_global_minimum` (`Phase4_RotatingFrame.lean` §7) proves it
  converges to a phase-locked configuration which is a global minimiser of the
  potential — with the trajectory itself never written down, and no formula for
  its limit.

  The initial data is `(0, 0, ½)`: two oscillators together and one displaced.
  It is genuinely unsynchronised (`trioStart_not_locked`), it satisfies the arc
  condition `|θᵢ - θⱼ| ≤ π/2`, and its excess `2(1 - cos ½)` is below the
  threshold `a/2 = ½` — the numerical content is `cos ½ > ¾`, which
  `Real.cos_bound` supplies.

  §17.1 then builds a `ThermodynamicCover` on that limit. This is what discharges
  `ThermodynamicCover.thermodynamic_equilibrium` on an instance rather than
  assuming it: the configuration the cover is required to sit at is *reached*,
  from data that does not start there.
-/

section TrioDynamics

open Filter Topology

/-- Three sites, unit coupling, no natural frequencies. -/
noncomputable def trioSys : KuramotoSystem (Fin 3) where
  omega := fun _ => 0
  A := fun _ _ => 1
  symm := fun _ _ => rfl

/-- Two oscillators together and one displaced by a half radian. -/
noncomputable def trioStart : Fin 3 → ℝ := ![0, 0, 1/2]

lemma trioSys_omega : ∀ i, trioSys.omega i = 0 := fun _ => rfl

lemma trioSys_coupling : ∀ i j, (1:ℝ) ≤ trioSys.A i j := fun _ _ => le_rfl

/-- `cos ½ > ¾`, from the quartic Taylor bound. This is the whole numerical
content of the witness. -/
lemma cos_half_gt : (3:ℝ)/4 < Real.cos (1/2) := by
  have h := Real.cos_bound (x := 1/2) (by rw [abs_of_nonneg] <;> norm_num)
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
  have h2 := abs_le.mp h
  norm_num at h2 ⊢
  linarith [h2.1]

lemma cos_half_lt_one : Real.cos (1/2) < 1 := by
  have h := Real.cos_bound (x := 1/2) (by rw [abs_of_nonneg] <;> norm_num)
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
  have h2 := abs_le.mp h
  norm_num at h2 ⊢
  linarith [h2.2]

/-- The excess of the initial configuration above the minimum: four of the nine
ordered pairs see the displacement. -/
lemma trioStart_excess :
    potentialExcess trioSys trioStart = 2 * (1 - Real.cos (1/2)) := by
  rw [potentialExcess_eq]
  simp only [trioSys, trioStart, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [show (0:ℝ) - 0 = 0 by ring, show (1:ℝ)/2 - 0 = 1/2 by ring,
    show (0:ℝ) - 1/2 = -(1/2) by ring, show (1:ℝ)/2 - 1/2 = 0 by ring]
  rw [Real.cos_neg, Real.cos_zero]
  ring

/-- The initial configuration is **not** phase-locked: it is not placed at the
limit it will reach. -/
theorem trioStart_not_locked : ¬ is_phase_locked trioStart := by
  intro h
  have := h 2 0
  simp only [trioStart, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at this
  rw [show (1:ℝ)/2 - 0 = 1/2 by ring] at this
  linarith [cos_half_lt_one, this]

lemma trioStart_small : 2 * potentialExcess trioSys trioStart < 1 := by
  rw [trioStart_excess]
  linarith [cos_half_gt]

lemma trioStart_init : ∀ i j, |trioStart i - trioStart j| ≤ Real.pi/2 := by
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [trioStart] <;>
    rw [abs_le] <;> constructor <;> norm_num <;> linarith

/-- **The general theorem, fired on a trajectory nobody can write down.**

There is a Kuramoto trajectory on three sites through the unsynchronised
configuration `(0, 0, ½)`, and it converges to a phase-locked configuration that
minimises the dynamic potential and carries order parameter `r² = 1`.

Neither the trajectory nor its limit is exhibited by a formula — the trajectory
comes from `is_kuramoto_trajectory_exists` and the limit from
`kuramoto_tendsto_global_minimum`, which builds it as `θ(0) + ∫₀^∞ θ̇`. This is
the sense in which §7 says more than §15: three-oscillator Kuramoto has no closed
form, so §15's method cannot produce this statement at any effort. -/
theorem trio_reaches_minimum :
    ∃ theta : ℝ → Fin 3 → ℝ,
      is_kuramoto_trajectory trioSys theta
      ∧ theta 0 = trioStart
      ∧ ¬ is_phase_locked (theta 0)
      ∧ ∃ thetaInf : Fin 3 → ℝ,
          (∀ i, Tendsto (fun t => theta t i) atTop (𝓝 (thetaInf i)))
          ∧ is_phase_locked thetaInf
          ∧ (∀ phi, kuramoto_potential_dynamic trioSys thetaInf
                ≤ kuramoto_potential_dynamic trioSys phi)
          ∧ order_parameter_r_sq thetaInf = 1 := by
  obtain ⟨theta, h_traj, h0⟩ := is_kuramoto_trajectory_exists trioSys 0 trioStart
  refine ⟨theta, h_traj, h0, by rw [h0]; exact trioStart_not_locked, ?_⟩
  exact kuramoto_tendsto_global_minimum trioSys trioSys_omega one_pos trioSys_coupling
    theta h_traj (by rw [h0]; exact trioStart_small) (by rw [h0]; exact trioStart_init)


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

end TrioDynamics

/-! ## 18. Prediction, memory, and what dissipation pays for

Witnesses `Phase3_PredictiveThermodynamics`. Three obligations are discharged
here and they are different in kind.

**(a) The class is inhabited, twice, on the same joint law.** `PredictiveDissipation`
carries Still, Sivak, Bell and Crooks' bound as a field, exactly as
`StructuralResonance` carries its own postulate. Two instances are built over the
same two-bit joint law and differ only in the signal's dynamics: in
`frozenSystem` the signal does not move, in `scrambledSystem` it is redrawn from
its stationary law at every step. The first dissipates nothing and is allowed to;
the second is *forced* to dissipate, and the amount is computed.

**(b) The informations are not zero, and not infinite.** A witness whose mutual
information were `0` would satisfy every bound in the file vacuously, and one
whose mutual information were `⊤` would make `dissipatedWork` say nothing. Both
are excluded here by direct computation on the two-bit law
(`memory_ne_zero`, `memory_ne_top`), and the second needs real work: absolute
continuity of the joint against the product of its marginals, established by
showing that the product charges every singleton with mass `1/4`.

**(c) The data processing inequality is fenced.** `predictiveInfo_le_mutualInfo`
holds because the evolution has the form `id ∥ₖ κ` — the system cannot write to
its environment. `writeKernel_increases_mutualInfo` exhibits a Markov kernel on
the *pair* that raises mutual information from `0` to something positive, so the
restriction on the kernel's shape is load-bearing and not decoration. This is the
same service `§16`'s one-way kernel performs for the symmetric-kernel theorems.

Finally, `still_bound_is_not_an_axiom` proves the claim the class docstring makes
in prose: the `axiom` formulation of Still's bound, quantified over all joint laws
and all signal dynamics with `dissipatedWork` a fixed field, is refuted by
`frozenSystem`'s own data read against `scrambledSystem`'s signal. -/

section PredictiveThermodynamicsWitness

open ProbabilityTheory InformationTheory

/-! ### The two-bit law

`Bool` for the system state, `Bool` for the signal. The joint law is the
perfectly correlated pair: the system's bit *is* the signal's bit. This is the
smallest law with non-zero mutual information, and everything below is computed
against it. -/

/-- The uniform law on one bit. -/
noncomputable def unifBool : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

/-- **The system remembers the signal exactly.** The joint law of `(X_t, S_t)`
puts mass `1/2` on each of the two agreeing configurations and nothing on the
two disagreeing ones. -/
noncomputable def corrJoint : Measure (Bool × Bool) :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (true, true) + Measure.dirac (false, false))

/-- The same marginals, made independent. This is the reference law mutual
information is measured against, and — in `§18.3` — a joint law in its own
right, the one a system that has forgotten the signal would carry. -/
noncomputable def indepJoint : Measure (Bool × Bool) := unifBool.prod unifBool

instance : IsProbabilityMeasure unifBool :=
  ⟨by simp [unifBool, ENNReal.inv_two_add_inv_two]⟩

instance : IsProbabilityMeasure corrJoint :=
  ⟨by simp [corrJoint, ENNReal.inv_two_add_inv_two]⟩

instance : IsProbabilityMeasure indepJoint := by unfold indepJoint; infer_instance

/-- Both marginals of the correlated law are uniform: the correlation is in the
joint alone, not in either coordinate. -/
theorem corrJoint_fst : corrJoint.fst = unifBool := by
  ext s hs
  rw [Measure.fst_apply hs]
  simp only [corrJoint, unifBool, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (measurable_fst hs)]
  rfl

theorem corrJoint_snd : corrJoint.snd = unifBool := by
  ext s hs
  rw [Measure.snd_apply hs]
  simp only [corrJoint, unifBool, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (measurable_snd hs)]
  rfl

/-- Mutual information for this law is the divergence of the correlated joint
from the independent one. -/
theorem mutualInfo_corrJoint : mutualInfo corrJoint = klDiv corrJoint indepJoint := by
  rw [mutualInfo, corrJoint_fst, corrJoint_snd, indepJoint]

/-! ### The memory is real: neither zero nor infinite -/

theorem unifBool_singleton (b : Bool) : unifBool {b} = (2 : ℝ≥0∞)⁻¹ := by
  simp only [unifBool, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton b)]
  cases b <;> simp

/-- The independent law charges every configuration with mass `1/4`. This is what
makes it a legitimate reference: nothing is invisible to it. -/
theorem indepJoint_singleton (p : Bool × Bool) : indepJoint {p} = (4 : ℝ≥0∞)⁻¹ := by
  have hs : ({p} : Set (Bool × Bool)) = ({p.1} : Set Bool) ×ˢ ({p.2} : Set Bool) := by
    ext q; simp [Prod.ext_iff]
  rw [indepJoint, hs, Measure.prod_prod, unifBool_singleton, unifBool_singleton,
    ← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

theorem corrJoint_singleton_tt : corrJoint {((true, true) : Bool × Bool)} = (2 : ℝ≥0∞)⁻¹ := by
  simp only [corrJoint, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton ((true, true) : Bool × Bool))]
  simp

/-- **The pair is genuinely dependent**: the joint charges the agreeing
configuration with `1/2` where independence would charge `1/4`. -/
theorem corrJoint_ne_indepJoint : corrJoint ≠ indepJoint := by
  intro h
  have h1 : corrJoint {((true, true) : Bool × Bool)}
      = indepJoint {((true, true) : Bool × Bool)} := by rw [h]
  rw [corrJoint_singleton_tt, indepJoint_singleton] at h1
  revert h1
  norm_num

/-- Absolute continuity, from the fact that the reference law has no null
singletons: a set the product ignores is empty. -/
theorem corrJoint_ac : corrJoint ≪ indepJoint := by
  intro s hs
  have hmem : ∀ p : Bool × Bool, p ∉ s := by
    intro p hp
    have hle : indepJoint {p} ≤ indepJoint s := measure_mono (Set.singleton_subset_iff.2 hp)
    rw [indepJoint_singleton, hs] at hle
    revert hle
    norm_num
  rw [Set.eq_empty_iff_forall_notMem.2 hmem, measure_empty]

/-- **The memory is finite**, so `PredictiveDissipation.memory_ne_top` is
dischargeable and the real number `dissipatedWork` says something. -/
theorem memory_ne_top : mutualInfo corrJoint ≠ ⊤ := by
  rw [mutualInfo_corrJoint]
  exact klDiv_ne_top corrJoint_ac Integrable.of_finite

/-- **The memory is non-zero.** Without this every bound in
`Phase3_PredictiveThermodynamics` would hold of this witness vacuously. -/
theorem memory_ne_zero : mutualInfo corrJoint ≠ 0 := by
  rw [mutualInfo_corrJoint]
  exact fun h => corrJoint_ne_indepJoint (klDiv_eq_zero_iff.1 h)

theorem memory_pos : 0 < (mutualInfo corrJoint).toReal :=
  ENNReal.toReal_pos memory_ne_zero memory_ne_top

/-! ### 18.1 A frozen signal: the memory is entirely predictive

The signal does not move, so what the system remembers about `S_t` is exactly
what it knows about `S_{t+1}`. Nonpredictive information is zero and the instance
is permitted to dissipate nothing. -/

/-- A system whose environment is static. `dissipatedWork := 0` is *allowed* here,
not assumed: `still_bound` has to be checked, and it is checked by
`predictiveInfo_id`. -/
@[instance_reducible]
noncomputable def frozenSystem : PredictiveDissipation Bool Bool Bool where
  joint := corrJoint
  joint_isProb := inferInstance
  signal := Kernel.id
  signal_isMarkov := inferInstance
  memory_ne_top := memory_ne_top
  thermalEnergy := 1
  thermalEnergy_pos := one_pos
  dissipatedWork := 0
  still_bound := by rw [predictiveInfo_id, tsub_self]; simp

/-- Every bit the frozen system holds is a predictive bit. -/
theorem frozenSystem_predictive : frozenSystem.predictive = mutualInfo corrJoint :=
  predictiveInfo_id corrJoint

theorem frozenSystem_nonpredictive : frozenSystem.nonpredictive = 0 := by
  show mutualInfo corrJoint - predictiveInfo corrJoint (Kernel.id : Kernel Bool Bool) = 0
  rw [predictiveInfo_id, tsub_self]

/-- **The zero-dissipation theorem, fired.** `predictive_eq_of_no_dissipation`
returns the equality of the two informations on this instance — and by
`memory_pos` the common value is strictly positive, so the conclusion is about a
system that actually remembers something. -/
theorem frozenSystem_all_memory_predictive :
    frozenSystem.predictive = mutualInfo corrJoint ∧ 0 < (frozenSystem.predictive).toReal :=
  ⟨frozenSystem.predictive_eq_of_no_dissipation rfl,
    by rw [frozenSystem.predictive_eq_of_no_dissipation rfl]; exact memory_pos⟩

/-! ### 18.2 A scrambled signal: the memory is entirely wasted

The signal is redrawn from the uniform law at every step, independently of its
own past. The system's memory of `S_t` therefore says nothing whatever about
`S_{t+1}`, and Still's bound charges the *whole* of it against dissipated work.
This is the regime the phrase "memory that does not predict is thermodynamic
waste" names, and here the waste is computed rather than asserted. -/

/-- A system whose environment has no memory of its own. -/
@[instance_reducible]
noncomputable def scrambledSystem : PredictiveDissipation Bool Bool Bool where
  joint := corrJoint
  joint_isProb := inferInstance
  signal := Kernel.const Bool unifBool
  signal_isMarkov := inferInstance
  memory_ne_top := memory_ne_top
  thermalEnergy := 1
  thermalEnergy_pos := one_pos
  dissipatedWork := (mutualInfo corrJoint).toReal
  still_bound := by rw [predictiveInfo_const, tsub_zero]; simp

/-- Nothing the scrambled system remembers predicts anything. -/
theorem scrambledSystem_predictive : scrambledSystem.predictive = 0 :=
  predictiveInfo_const corrJoint unifBool

theorem scrambledSystem_nonpredictive : scrambledSystem.nonpredictive = mutualInfo corrJoint :=
  nonpredictiveInfo_const corrJoint unifBool

/-- **The instance is forced to dissipate.** This is the content of the witness:
the bound is not satisfiable at zero cost once the signal stops being
predictable, and the floor is the system's entire memory. -/
theorem scrambledSystem_dissipates : 0 < scrambledSystem.dissipatedWork := memory_pos

/-- The data processing inequality is *strict* on this instance: `0 = I_pred <
I_mem`. Together with `§18.1`, where it is an equality, this shows the inequality
is not secretly one or the other. -/
theorem scrambledSystem_dpi_strict : scrambledSystem.predictive < mutualInfo corrJoint := by
  rw [scrambledSystem_predictive]
  exact pos_iff_ne_zero.2 memory_ne_zero

/-- **The Kawai–Parrondo–Van den Broeck predicate, discharged.** The forward
ensemble is the correlated law, the reversed one is the product of its marginals,
and the dissipated work is `k_B T` times the divergence between them — with
equality, so the instance saturates both postulates at once.

Read physically, the identification is the sharp case: the only distinguishable
consequence of running this system's film backwards is the correlation it holds,
so the arrow of time and the wasted memory coincide. A physical instance would
carry path ensembles with structure of their own and the inequality of
`nonpredictive_le_arrow` would be slack. -/
theorem scrambledSystem_kpv : IsKPVDissipation scrambledSystem corrJoint indepJoint := by
  show (mutualInfo corrJoint).toReal = 1 * (klDiv corrJoint indepJoint).toReal
  rw [one_mul, mutualInfo_corrJoint]

/-- The arrow-of-time bound, fired on the instance. -/
theorem scrambledSystem_arrow :
    (scrambledSystem.nonpredictive).toReal ≤ (klDiv corrJoint indepJoint).toReal :=
  nonpredictive_le_arrow scrambledSystem corrJoint indepJoint scrambledSystem_kpv

/-- The second law, read off the instance rather than assumed of it. -/
theorem scrambledSystem_second_law : 0 ≤ scrambledSystem.dissipatedWork :=
  scrambledSystem.dissipatedWork_nonneg

/-! ### 18.3 Why the kernel must have the form `id ∥ₖ κ`

`predictiveInfo_le_mutualInfo` is the data processing inequality for the Markov
chain `X_t → S_t → S_{t+1}`, and the chain is enforced by the *shape* of the
evolution: `Kernel.id ∥ₖ κ` leaves the system coordinate alone and acts on the
signal coordinate through `κ` only. Drop that shape and the theorem is false, not
merely unproved. The kernel below is the system writing its own state into the
environment, and it takes an independent pair to a perfectly correlated one. -/

/-- The system stamps its state onto the signal. A perfectly good Markov kernel
on the pair — and not of the form `id ∥ₖ κ`. -/
noncomputable def writeKernel : Kernel (Bool × Bool) (Bool × Bool) :=
  Kernel.deterministic (fun p => (p.1, p.1)) (by fun_prop)

theorem writeKernel_comp : writeKernel ∘ₘ indepJoint = corrJoint := by
  have hcomp : (fun p : Bool × Bool => (p.1, p.1))
      = (fun x : Bool => (x, x)) ∘ Prod.fst := rfl
  rw [writeKernel, Measure.deterministic_comp_eq_map, hcomp,
    ← Measure.map_map (by fun_prop) measurable_fst]
  have hfst : indepJoint.map Prod.fst = unifBool := by
    rw [indepJoint, ← Measure.fst, Measure.fst_prod]
  rw [hfst]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  simp only [corrJoint, unifBool, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ ((by fun_prop : Measurable fun x : Bool => (x, x)) hs)]
  rfl

/-- An independent pair carries no mutual information. -/
theorem mutualInfo_indepJoint : mutualInfo indepJoint = 0 := by
  rw [indepJoint, mutualInfo_prod]

/-- **The system that writes to its environment breaks the bound.** Mutual
information rises from `0` to a strictly positive value under one application of
a Markov kernel on the pair. So `predictiveInfo_le_mutualInfo` is not a fact about
Markov kernels in general, and the parallel form in `evolvedJoint` is carrying the
physical hypothesis rather than decorating it. -/
theorem writeKernel_increases_mutualInfo :
    mutualInfo indepJoint < mutualInfo (writeKernel ∘ₘ indepJoint) := by
  rw [mutualInfo_indepJoint, writeKernel_comp]
  exact pos_iff_ne_zero.2 memory_ne_zero

/-! ### 18.4 Why Still's bound is a class field and not an axiom -/

/-- **The `axiom` form of Still's bound is inconsistent**, and this is the
refutation the class docstring describes rather than a restatement of it.

`frozenSystem` fixes `dissipatedWork = 0` and `thermalEnergy = 1`. Had
`still_bound` been declared as a free-standing axiom quantified over all joint
laws and all signal dynamics, it would apply to that instance's fields with
`scrambledSystem`'s signal, and assert `1 * (mutualInfo corrJoint).toReal ≤ 0` —
which `memory_pos` refutes. Bundling the joint law and the signal dynamics as
*data of one system* is what makes the postulate a constraint on that system
instead of a false claim about every pair.

This is the same failure that made three of the development's five original
axioms provably `False` (`Axioms.lean` §5). -/
theorem still_bound_is_not_an_axiom :
    ¬ ((1 : ℝ) * (mutualInfo corrJoint
          - predictiveInfo corrJoint (Kernel.const Bool unifBool)).toReal ≤ 0) := by
  rw [predictiveInfo_const, tsub_zero, one_mul]
  exact not_le.2 memory_pos

/-! ### 18.5 The two-bit law, charged to Landauer's bill

`§18.2` computes the wasted memory of a system whose signal is unpredictable and
declares a `dissipatedWork` equal to it. That is legitimate — the class field is
an obligation and the instance meets it — but the number stands beside the
system rather than coming out of it, exactly as `K` and `D` once stood beside
the field in `Phase9_EMIdentification`.

`landauerSystem` is the same two-bit law with the number produced instead.
`PredictiveDissipation.ofLandauer` (`Phase3_LandauerBridge.lean`) takes the
one-bit eraser of `§1` — the register `fun _ => true`, whose Landauer heat
`§1`'s bath fixes at `log 2` — and returns a predictive structure whose
`dissipatedWork` *is* that heat and whose `still_bound` is derived from
`landauer_bound`. Nothing is postulated twice.

The arithmetic is the sharp case and is worth stating plainly: the register
erases one bit, `log 2` of entropy; the correlated law wastes one bit, `log 2`
of memory; and the bound is met with **equality** (`landauerSystem_tight`). A
witness in which the erased entropy exceeded the waste would show the
construction runs; this one shows it runs with nothing to spare. -/

/-- The density of the correlated law against the independent one: `2` on the
diagonal, `0` off it. The mutual information of `§18` is computed from it. -/
noncomputable def corrDensity : Bool × Bool → ℝ≥0∞ := fun p => if p.1 = p.2 then 2 else 0

lemma measurable_corrDensity : Measurable corrDensity := measurable_of_countable _

theorem corrJoint_singleton (p : Bool × Bool) :
    corrJoint {p} = if p.1 = p.2 then (2 : ℝ≥0∞)⁻¹ else 0 := by
  simp only [corrJoint, Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton p)]
  obtain ⟨a, b⟩ := p
  cases a <;> cases b <;> simp

theorem corrJoint_eq_withDensity : corrJoint = indepJoint.withDensity corrDensity := by
  refine Measure.ext_of_singleton fun p => ?_
  rw [withDensity_apply _ (measurableSet_singleton p), lintegral_singleton,
    indepJoint_singleton, corrJoint_singleton]
  by_cases h : p.1 = p.2 <;> simp [corrDensity, h]
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

lemma rnDeriv_corrJoint : corrJoint.rnDeriv indepJoint =ᵐ[indepJoint] corrDensity := by
  rw [corrJoint_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ measurable_corrDensity

lemma llr_corrJoint :
    llr corrJoint indepJoint =ᵐ[corrJoint] fun p => Real.log (corrDensity p).toReal := by
  filter_upwards [corrJoint_ac.ae_le rnDeriv_corrJoint] with p hp
  simp only [llr_def, hp]

/-- **The memory is exactly one bit.** `§18` proves the mutual information of the
correlated law is neither `0` nor `⊤`; this computes it. The Radon–Nikodym
derivative against the product law is `2` on the diagonal and `0` off it, so the
log-likelihood ratio is `log 2` wherever the law charges anything. -/
theorem klDiv_corrJoint : klDiv corrJoint indepJoint = ENNReal.ofReal (Real.log 2) := by
  rw [klDiv_of_ac_of_integrable corrJoint_ac Integrable.of_finite]
  have hint : ∫ p, llr corrJoint indepJoint p ∂corrJoint = Real.log 2 := by
    rw [integral_congr_ae llr_corrJoint, integral_fintype Integrable.of_finite]
    simp only [corrDensity, Measure.real, corrJoint_singleton, Fintype.sum_prod_type,
      Fintype.sum_bool]
    norm_num
    ring
  rw [hint]
  simp

theorem mutualInfo_corrJoint_eq : mutualInfo corrJoint = ENNReal.ofReal (Real.log 2) := by
  rw [mutualInfo_corrJoint, klDiv_corrJoint]

theorem memory_toReal : (mutualInfo corrJoint).toReal = Real.log 2 := by
  rw [mutualInfo_corrJoint_eq, ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num))]

/-- **The register of `§1`, and what it erases.** `fun _ => true` collapses two
states onto one: `log 2 − log 1` of entropy, which is one bit. -/
theorem erasedEntropy_boolEraser : erasedEntropy (fun _ : Bool => true) = Real.log 2 := by
  simp [erasedEntropy, entropy, boltzmann_entropy]

/-- The identification the bridge asks for, discharged by computation: the memory
this law wastes is exactly the entropy that register destroys. -/
theorem boolEraser_waste :
    (nonpredictiveInfo corrJoint (Kernel.const Bool unifBool)).toReal
      ≤ erasedEntropy (fun _ : Bool => true) := by
  rw [nonpredictiveInfo_const, erasedEntropy_boolEraser, memory_toReal]

/-- **The predictive structure of the one-bit eraser.** Same joint law as
`§18.1` and `§18.2`; the thermal scale and the dissipated work are now `§1`'s
temperature and `§1`'s Landauer heat, and `still_bound` is discharged by
`landauer_bound` rather than by a declaration. -/
@[instance_reducible]
noncomputable def landauerSystem : PredictiveDissipation Bool Bool Bool :=
  PredictiveDissipation.ofLandauer (sys := Bool) (fun _ => true) corrJoint
    (Kernel.const Bool unifBool) memory_ne_top boolEraser_waste

theorem landauerSystem_dissipatedWork :
    landauerSystem.dissipatedWork = heat_dissipation (fun _ : Bool => true) := rfl

theorem landauerSystem_thermalEnergy :
    landauerSystem.thermalEnergy = Thermodynamics.temperature (sys := Bool) := rfl

theorem landauerSystem_nonpredictive :
    landauerSystem.nonpredictive = mutualInfo corrJoint :=
  nonpredictiveInfo_const corrJoint unifBool

/-- The waste is real: the instance is not one of those that satisfy every bound
by holding no memory. -/
theorem landauerSystem_nonpredictive_pos : 0 < (landauerSystem.nonpredictive).toReal := by
  rw [landauerSystem_nonpredictive]; exact memory_pos

/-- **The bound is attained.** `k_B T · I_nonpred = W_diss`: the bit the register
erases is the bit the memory wastes, and Landauer's heat pays for it exactly.
Nothing is left over, so the inequality of `still_bound` cannot be strengthened
on this witness. -/
theorem landauerSystem_tight :
    landauerSystem.thermalEnergy * (landauerSystem.nonpredictive).toReal
      = landauerSystem.dissipatedWork := by
  rw [landauerSystem_nonpredictive, memory_toReal]
  show (1 : ℝ) * Real.log 2 = Real.log 2
  rw [one_mul]

/-- **The regression.** `frozenSystem` is a legitimate `PredictiveDissipation`
and it is *not* a predictive structure of the erasing register: its dissipated
work is zero where the register's Landauer heat is `log 2`, and it wastes no
memory at all. An edge asking only for `Nonempty (PredictiveDissipation _ _ _)`
is discharged by it; the edge `Chain.E34` asks for more, and this is what "more"
excludes. -/
theorem frozenSystem_not_of_eraser :
    frozenSystem.dissipatedWork ≠ heat_dissipation (fun _ : Bool => true)
      ∧ (frozenSystem.nonpredictive).toReal = 0 := by
  constructor
  · show (0 : ℝ) ≠ Real.log 2
    exact ne_of_lt (Real.log_pos (by norm_num))
  · rw [frozenSystem_nonpredictive, ENNReal.toReal_zero]

end PredictiveThermodynamicsWitness

/-! ## 19. The capacity of a finite phase space, on two bits

  `Phase1_PhaseSpaceCapacity.lean` is the answer to the standing complaint that
  the first premise "contributes vocabulary rather than content". This section
  runs its three theorems on the smallest system that can carry them, and — as
  everywhere else in this file — fences the hypotheses that are doing the work.

  What is witnessed:

  * the capacity bound is *attained*, so `log |X|` is the exact figure and not a
    slack over-estimate (`bool_uniform_entropy`);
  * it is *strict* off the uniform law, on a concrete biased bit
    (`biased_bit_below_capacity`);
  * a two-letter stream of length two already outruns a one-bit phase space
    (`bit_cannot_record_two_perturbations`), and its entropy strictly exceeds
    anything that phase space can hold (`two_bit_source_exceeds_bit_capacity`);
  * an unreachable state on a finite phase space costs heat, on §1's
    `boolStatMech` (`unreachable_state_costs_heat`);
  * and the finiteness hypothesis is not decoration: on `ℕ` the same step fails,
    because `Nat.succ` is injective and misses `0`
    (`succ_is_not_an_erasure`). That last one is the fence. Without it,
    `is_erasure_of_not_surjective` would read like a triviality about maps
    rather than a fact about *finite* phase spaces.
-/

section PhaseSpaceCapacityWitness

/-- The uniform law on a bit is the fair coin. -/
theorem bool_uniformDist_eq : uniformDist Bool = fun _ => (1 : ℝ) / 2 := by
  funext b
  simp [uniformDist]

/-- **Capacity is attained.** One bit holds exactly `log 2` nats. -/
theorem bool_uniform_entropy : shannon_entropy (uniformDist Bool) = Real.log 2 := by
  rw [shannon_entropy_uniformDist]
  norm_num

/-- A bit that is not fair: `3/4` on `false`, `1/4` on `true`. -/
noncomputable def biasedBit : Bool → ℝ := fun b => if b then 1 / 4 else 3 / 4

theorem is_prob_dist_biasedBit : is_prob_dist biasedBit := by
  refine ⟨fun b => by cases b <;> norm_num [biasedBit], ?_⟩
  simp [biasedBit]
  norm_num

/-- **The bound is strict off the uniform law**, on this instance rather than in
general: a biased bit holds strictly less than `log 2`. -/
theorem biased_bit_below_capacity : shannon_entropy biasedBit < Real.log 2 := by
  have h := shannon_entropy_lt_log_card_of_ne_uniform biasedBit is_prob_dist_biasedBit true
    (by simp [biasedBit])
  simpa using h

/-- **A one-bit phase space cannot record two binary perturbations.** Four
histories, two states. The update below is a genuine one — the perturbation is
`xor`-ed into the state, which is *reversible at each step* — so the collision is
not an artefact of a lossy update but of the phase space being smaller than the
stream. -/
theorem bit_cannot_record_two_perturbations :
    ¬ Function.Injective (fun w : Fin 2 → Bool => absorb (fun s p => xor s p) false w) := by
  apply absorb_not_injective
  simp

/-- The two histories that collide, exhibited. `absorb` on `xor` returns the
parity of the word, so `(true, false)` and `(false, true)` are indistinguishable
to the system while being different perturbation streams. -/
example :
    absorb (fun s p => xor s p) false (![true, false] : Fin 2 → Bool)
      = absorb (fun s p => xor s p) false (![false, true] : Fin 2 → Bool) := by
  decide

/-- **The source outruns the capacity, entropically.** No law on one bit reaches
the entropy of the uniform law on two-letter words of length two. -/
theorem two_bit_source_exceeds_bit_capacity (p : Bool → ℝ) (hp : is_prob_dist p) :
    shannon_entropy p < shannon_entropy (uniformDist (Fin 2 → Bool)) :=
  source_entropy_exceeds_capacity 2 (by simp) p hp

/-- **An unreachable state costs heat**, on §1's one-bit thermodynamic system.
`fun _ => false` never reaches `true`; §1's `boolStatMech` supplies the bath, and
`finite_phase_space_dissipates` supplies the rest. This is the same conclusion §1
reaches by exhibiting non-injectivity directly — the point is that the hypothesis
is now the physically checkable one. -/
theorem unreachable_state_costs_heat :
    heat_dissipation (fun _ => false : Bool → Bool) > 0 := by
  apply finite_phase_space_dissipates
  intro hsurj
  obtain ⟨b, hb⟩ := hsurj true
  exact Bool.noConfusion hb

/-- **The finiteness hypothesis is load-bearing.** `Nat.succ` misses `0` and is
injective, so on an infinite phase space "cannot reach every state" does not
imply erasure and no Landauer charge follows. `is_erasure_of_not_surjective`
therefore says something about finite phase spaces specifically, which is what
makes it a consumer of the first premise rather than a general fact about
maps. -/
theorem succ_is_not_an_erasure :
    ¬ Function.Surjective Nat.succ ∧ ¬ is_erasure Nat.succ := by
  refine ⟨fun h => ?_, fun h => h Nat.succ_injective⟩
  obtain ⟨n, hn⟩ := h 0
  exact Nat.succ_ne_zero n hn

/-- **Refreshing the incoming register is what dissipates**, exhibited on the
joint two-bit space. The record-keeping alternative is injective and appears
immediately below, so the two are visibly different maps rather than two
descriptions of one. -/
theorem absorbStep_bool_is_erasure :
    is_erasure (absorbStep (fun s p => xor s p) false) :=
  absorbStep_is_erasure _ (p₁ := true) (by simp)

/-- The map that keeps the record instead of refreshing it **is** injective, so
nothing forces it to dissipate. This is the Norton / Shenker point in one line:
losing the history is not the same as erasing it, and only the second is
charged. -/
theorem keepRecord_injective :
    Function.Injective (fun sp : Bool × Bool => (xor sp.1 sp.2, sp.2)) := by
  decide

end PhaseSpaceCapacityWitness

/-! ## 20. The continuum operator, on a substrate with no atoms

`Phase8_ContinuousField` §9 builds the drift map `K ↦ (x ↦ ∫ K(x,y) sin(θ_y − θ_x) dy)`
as a bounded operator `L²(μ⊗μ) → L²(μ)`, which is what open item **O10** asked for,
and derives the continuum gradient and descent results from it.

This section runs those on Lebesgue measure restricted to `(0,1)`. The substrate
is chosen so that the finite-substrate machinery of §7 cannot be doing the work
in disguise: `ℝ` is not finite (`unit_substrate_infinite`), so `sigmaOfKernel`,
`driftCLM` and `hasFDerivAt_sigmaOfKernel` do not typecheck here at all; and the
measure has no atoms (`NullSingletonClass`), so the substrate is not a finite set
carrying point masses either.

What is checked: the operator exists, its norm is at most `μ(α)^{1/2} = 1`
(`unit_opNorm_le_one`), and the structural-resonance descent theorem applies to
it unchanged (`unit_resonance_antitone`).

What is **not** checked here: that any particular coupling trajectory satisfies
the flow equation. `unit_resonance_antitone` takes the flow as a hypothesis, as
its finite-substrate counterpart does; no dynamics in this development produces
one. And nothing here connects this continuum field to a finite Kuramoto system
— that is the propagation-of-chaos gap, which is untouched and is recorded as
such in `tasks/todo.md`.
-/

section ContinuumOperatorWitness

/-- Lebesgue measure on the open unit interval: a finite measure with no atoms. -/
noncomputable def unitMeasure : Measure ℝ := volume.restrict (Set.Ioo 0 1)

@[simp] theorem unitMeasure_univ : unitMeasure Set.univ = 1 := by
  rw [unitMeasure, Measure.restrict_apply_univ, Real.volume_Ioo]
  norm_num

instance : IsFiniteMeasure unitMeasure := ⟨by rw [unitMeasure_univ]; exact ENNReal.one_lt_top⟩

instance : NullSingletonClass unitMeasure := by
  rw [unitMeasure]; infer_instance

theorem unitMeasure_toReal : (unitMeasure Set.univ).toReal = 1 := by
  rw [unitMeasure_univ]; norm_num

/-- **The operator norm bound on a genuine continuum.** -/
theorem unit_opNorm_le_one {theta : ℝ → ℝ} (h : Measurable theta) :
    ‖continuumDriftCLM unitMeasure h‖ ≤ 1 := by
  have := opNorm_kernelCLM_le (μ := unitMeasure)
    (stronglyMeasurable_sinKernel h) (abs_sinKernel_le_one theta)
  rwa [unitMeasure_toReal, Real.sqrt_one] at this

/-- The substrate is not finite, so nothing in §7 applies to it. -/
theorem unit_substrate_infinite : ¬ Finite ℝ := by
  intro h
  exact absurd (Set.toFinite (Set.univ : Set ℝ)) (Set.infinite_univ (α := ℝ))

/-- The descent theorem, on this substrate. -/
theorem unit_resonance_antitone {theta : ℝ → ℝ} (h : Measurable theta) (D : ℝ)
    (omega : Lp ℝ 2 unitMeasure) (K_t : ℝ → Lp ℝ 2 (unitMeasure.prod unitMeasure))
    {c : ℝ} (hc : 0 < c)
    (hflow : ∀ t, HasDerivAt K_t (- c • gradSigmaContinuum unitMeasure h D omega (K_t t)) t) :
    Antitone (fun t => sigmaContinuum unitMeasure h D omega (K_t t)) :=
  structural_resonance_decreases_sigmaContinuum h D omega K_t hc hflow

end ContinuumOperatorWitness

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

end Examples
end PhysicsOfConsciousness
