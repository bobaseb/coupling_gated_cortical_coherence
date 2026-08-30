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
    ✓ `LocalSectionSynchronization` / `ThermodynamicCover` — two overlapping
      patches on a three-site substrate, with sections of the sheafified
      probability presheaf built from a phase-dependent invariant measure (§4).

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
  `GlobalSection`. It first pierces the sheafification: `massEquiv` proves the global
  sections of the probability sheaf on the three-site cortex *are* the finite measures
  on it, read as densities against counting measure. The metric is then the
  uniform distance between their densities, complete, and the self-prediction map
  contracts by exactly one half (`relax_dist`) without being constant
  (`relax_not_const`), with a unique fixed point (`relax_fixed_unique`). The earlier
  0/1 metric is kept as `gsDiscreteMetric`, and `contracting_implies_const` records
  why it was empty. What is still not established is that any field dynamics produces
  this particular map or this particular contraction constant.

  Every declaration in this file depends only on `propext`, `Classical.choice`
  and `Quot.sound`.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_KLBound
import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Phase6_ReflexiveTopology
import PhysicsOfConsciousness.Phase8_ContinuousField
import PhysicsOfConsciousness.Phase2_MeshConvergence
import PhysicsOfConsciousness.Phase4_RotatingFrame
import PhysicsOfConsciousness.Phase7_Rigidity

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal

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
    `phase_invariant_periodic` for trivial reasons and would witness nothing. -/
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

/-- 2π-periodicity, which is what `phase_invariant_periodic` demands. -/
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
    invariant measure. `sync_to_section_eq` then holds by `rfl` — the local
    sections *are* restrictions, which is the modelling assumption the field
    records. -/
noncomputable instance cortexSync : LocalSectionSynchronization Cortex where
  I := Bool
  cover := patch
  is_cover := patch_cover
  phase := fun _ => 0
  sync_to_section := fun i =>
    (probabilityPresheaf Cortex).map (homOfLE (le_top : patch i ≤ ⊤)).op (globalSect 0)
  phase_invariant_measure := globalSect
  phase_invariant_periodic := fun _ _ h => by
    unfold globalSect
    rw [phaseMeasure_periodic h]
  sync_to_section_eq := fun _ => rfl

/-- Uniform unit coupling between the two patches. The configuration `phase = 0`
    is a global minimum of the Kuramoto potential by
    `phase_locked_minimizes_potential`, so `thermodynamic_equilibrium` is
    discharged rather than assumed here. -/
noncomputable instance cortexCover : ThermodynamicCover Cortex where
  toLocalSectionSynchronization := cortexSync
  I_fintype := inferInstanceAs (Fintype Bool)
  I_decidable := inferInstanceAs (DecidableEq Bool)
  A := fun _ _ => 1
  A_symm := fun _ _ => rfl
  A_pos := fun _ _ => one_pos
  thermodynamic_equilibrium := fun theta =>
    phase_locked_minimizes_potential (V := Bool)
      ⟨fun _ => 0, fun _ _ => 1, fun _ _ => rfl⟩ (fun _ _ => one_pos) theta

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
  exactly what the everywhere-empty triangulation would violate.

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

/-- A nonzero weight forces an actual face of the complex: on the grid, `face_of_weight_ne_zero`
says the coupling graph is the path graph the triangulation describes and nothing more. -/
example (N : ℕ) (hN : 0 < N) (u v : Fin (N + 1))
    (h : DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor u v ≠ 0) :
    ({u, v} : Finset (Fin (N + 1))) ∈ (gridTriangulation N).complex.faces :=
  DiscreteThermodynamics.face_of_weight_ne_zero (gridThermo N hN) unitTensor h


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
*assumed* to be a nonempty complete metric space, and `predict` is *assumed* to be a
`1/2`-contraction. `GlobalSection` is defined as the sections over `⊤` of a
sheafification — a subtype of families of germs — so nothing about it is a measure until
that layer is pierced, and an earlier pass discharged the metric hypothesis with the 0/1
metric. That witness was honest but empty: `contracting_implies_const` (kept below) proves
that under the 0/1 metric *every* `ContractingWith K` map with `K < 1` is constant, so on
that model the Self was the constant section.

This section replaces it. The work is in three stages.

* **The germ–measure dictionary.** On this discrete substrate every point has a smallest
  open neighbourhood, so "mass carried at `x`" is a well-defined map out of the stalk at
  `x` (`stalkMass`, built as `colimit.desc` of `massCocone`; the cocone law is exactly
  that restriction preserves the mass at a point). Reading a global section's germ at each
  site gives `density : GlobalSection Cortex → (Site → ℝ≥0)`, and `massEquiv` proves this a
  **bijection**: `density` is injective because a germ on a discrete space is determined by its
  restriction to the point (`stalkMass_injective`), and surjective because any prescribed
  density is realized by a finite measure (`massMeasure`). Global sections of the
  probability sheaf on `Cortex` *are* the finite measures on it, read as densities against
  counting measure. Nothing in Mathlib supplied this: `TopCat.Presheaf.sheafify` has no
  adjunction and no `isIso_toSheafify`, so the inverse had to be constructed.
* **The metric.** `gsMetric` transports the metric of `Site → ℝ≥0` along `density`: the
  distance between two sections is the largest difference of the masses their measures put
  on a site: the uniform distance between their densities. (On a finite substrate that is
  equivalent to the total-variation distance of the measures, within a factor of the number
  of sites, but it is not equal to it — total variation sums the differences where this
  takes their maximum. Nothing below uses the comparison.) It is complete
  (`gsComplete`, via surjectivity of `density`, not via "Cauchy sequences are eventually
  constant"), and `exists_dist_lt_one` exhibits distinct sections at distance `1/2`, which
  is exactly the hypothesis `contracting_implies_const` needs and no longer has.
* **The Self.** `relax` is the self-prediction map "average the current field with the
  baseline": a genuine dissipative relaxation, not a constant. `relax_dist` proves it
  contracts distances by *exactly* one half, `relax_not_const` proves it is not constant,
  `relax_fixed` names its fixed point and `relax_fixed_unique` proves that fixed point is
  the only one — Banach uniqueness re-derived by hand on the witness.

**What this still does not establish.** `relax` is a modelling choice: nothing in the
development derives it from field dynamics, and the contraction constant `1/2` is built
into its definition rather than read off an entropy production rate. The Lévy–Prokhorov
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

/-- The **density** of a global section: the mass its germ carries at each site. -/
noncomputable def density (s : GlobalSection (X := Cortex)) : Site → ℝ≥0 :=
  fun x => stalkMass x (s.1 ⟨x, memTop x⟩)

/-- The density of a section glued from an honest global measure is that measure's
density. This is the bridge between the sheafified world and the measure world. -/
lemma Phi_sheafify (μ : FiniteMeasure ↥(⊤ : Opens ↥Cortex)) (x : Site) :
    density ((TopCat.Presheaf.toSheafify Fpre).app (op ⊤) μ) x
      = μ {(⟨x, memTop x⟩ : ↥(⊤ : Opens ↥Cortex))} :=
  stalkMass_germ ⊤ x (memTop x) μ

lemma Phi_injective : Function.Injective density := by
  intro s t h
  apply Subtype.ext
  funext y
  exact stalkMass_injective y.1 (congrFun h y.1)

instance : Nonempty Site := ⟨Site.mid⟩

instance : MeasurableSingletonClass Site := ⟨fun x => (isOpen_discrete {x}).measurableSet⟩

noncomputable instance topFintype : Fintype ↥(⊤ : Opens ↥Cortex) := Fintype.ofFinite _

instance topSingleton : MeasurableSingletonClass ↥(⊤ : Opens ↥Cortex) :=
  ⟨fun z => by
    have h : MeasurableSet ((Subtype.val : ↥(⊤ : Opens ↥Cortex) → Site) ⁻¹' {z.1}) :=
      measurable_subtype_coe (measurableSet_singleton z.1)
    have himg : (Subtype.val : ↥(⊤ : Opens ↥Cortex) → Site) ⁻¹' {z.1} = {z} := by
      ext b
      exact ⟨fun hb => Subtype.ext hb, fun hb => congrArg Subtype.val hb⟩
    rwa [himg] at h⟩

/-- The unit point mass at a site, as a finite measure on the whole substrate. -/
noncomputable def diracFM (y : ↥(⊤ : Opens ↥Cortex)) : FiniteMeasure ↥(⊤ : Opens ↥Cortex) :=
  ⟨Measure.dirac y, inferInstance⟩

/-- The finite measure on the whole substrate with prescribed mass at each site. -/
noncomputable def massMeasure (w : Site → ℝ≥0) : FiniteMeasure ↥(⊤ : Opens ↥Cortex) :=
  ∑ y : ↥(⊤ : Opens ↥Cortex), w y.1 • diracFM y

lemma fm_sum_apply {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} (S : Finset ι)
    (f : ι → FiniteMeasure Ω) (s : Set Ω) : (∑ i ∈ S, f i) s = ∑ i ∈ S, (f i) s := by
  classical
  induction S using Finset.induction with
  | empty => simp [FiniteMeasure.coeFn_def]
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, FiniteMeasure.coeFn_add]
      rfl

lemma diracFM_apply (y z : ↥(⊤ : Opens ↥Cortex)) :
    diracFM y {z} = if y = z then 1 else 0 := by
  rw [FiniteMeasure.coeFn_def]
  show ((Measure.dirac y) {z}).toNNReal = _
  rw [Measure.dirac_apply' _ (measurableSet_singleton z)]
  by_cases h : y = z <;> simp [h, Set.indicator]

lemma massMeasure_apply (w : Site → ℝ≥0) (x : Site) :
    massAt ⊤ x (memTop x) (massMeasure w) = w x := by
  show (massMeasure w) {(⟨x, memTop x⟩ : ↥(⊤ : Opens ↥Cortex))} = w x
  rw [massMeasure, fm_sum_apply,
    Finset.sum_eq_single (⟨x, memTop x⟩ : ↥(⊤ : Opens ↥Cortex))]
  · rw [FiniteMeasure.smul_apply, diracFM_apply]
    simp
  · intro b _ hb
    rw [FiniteMeasure.smul_apply, diracFM_apply]
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The global section with prescribed mass at each site. -/
noncomputable def sectionOfMass (w : Site → ℝ≥0) : GlobalSection (X := Cortex) :=
  (TopCat.Presheaf.toSheafify Fpre).app (op ⊤) (massMeasure w)

@[simp] lemma Phi_sectionOfMass (w : Site → ℝ≥0) : density (sectionOfMass w) = w := by
  funext x
  exact (Phi_sheafify (massMeasure w) x).trans (massMeasure_apply w x)

lemma Phi_surjective : Function.Surjective density :=
  fun w => ⟨sectionOfMass w, Phi_sectionOfMass w⟩

/-- **Global sections are measures.** On the three-site substrate the sections of the
sheafified probability presheaf over `⊤` correspond exactly to the finite measures on it,
read off as densities against counting measure. -/
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

/-- **The self-prediction map.** The field's model of its next state is the average of its
current state and the baseline: a dissipative relaxation. It is a function of the section
it is applied to — unlike the constant map the 0/1 metric forced. -/
noncomputable def relax (s : GlobalSection (X := Cortex)) : GlobalSection (X := Cortex) :=
  sectionOfMass (fun x => (density s x + density cortexState x) / 2)

@[simp] lemma Phi_relax (s : GlobalSection (X := Cortex)) :
    density (relax s) = fun x => (density s x + density cortexState x) / 2 :=
  Phi_sectionOfMass _

lemma Phi_relax_apply (s : GlobalSection (X := Cortex)) (x : Site) :
    density (relax s) x = (density s x + density cortexState x) / 2 := by
  rw [Phi_relax]

lemma nnreal_dist_avg (a b c : ℝ≥0) : dist ((a + c)/2) ((b + c)/2) = dist a b / 2 := by
  rw [NNReal.dist_eq, NNReal.dist_eq]
  push_cast
  rw [show ((a:ℝ) + c)/2 - ((b:ℝ) + c)/2 = ((a:ℝ) - b)/2 by ring, abs_div]
  norm_num

lemma relax_lipschitz : LipschitzWith (1/2) relax := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [gs_dist_eq, Phi_relax, Phi_relax]
  push_cast
  have hb : (0:ℝ) ≤ 1/2 * dist s t := by positivity
  rw [dist_pi_le_iff hb]
  intro x
  rw [nnreal_dist_avg]
  have h1 : dist (density s x) (density t x) ≤ dist s t := by
    rw [gs_dist_eq]; exact dist_le_pi_dist _ _ x
  linarith

theorem relax_contracting : ContractingWith (1/2) relax :=
  ⟨by norm_num, relax_lipschitz⟩

/-- The contraction factor is exactly one half, not merely at most one half: the map
genuinely moves sections and genuinely damps the distance between them. -/
theorem relax_dist (s t : GlobalSection (X := Cortex)) :
    dist (relax s) (relax t) = dist s t / 2 := by
  refine le_antisymm ?_ ?_
  · have := relax_lipschitz.dist_le_mul s t
    push_cast at this
    linarith
  · have key : dist s t ≤ 2 * dist (relax s) (relax t) := by
      have hnn : (0:ℝ) ≤ 2 * dist (relax s) (relax t) := by
        have := dist_nonneg (x := relax s) (y := relax t)
        linarith
      rw [gs_dist_eq, dist_pi_le_iff hnn]
      intro x
      have h2 : dist (density s x) (density t x) = 2 * dist (density (relax s) x) (density (relax t) x) := by
        rw [Phi_relax_apply, Phi_relax_apply, nnreal_dist_avg]
        ring
      rw [h2]
      have := dist_le_pi_dist (density (relax s)) (density (relax t)) x
      rw [← gs_dist_eq] at this
      linarith
    linarith

/-- **The map is not constant** — the exact failure of `contracting_implies_const` on this
metric. The silent field and the baseline have different predictions. -/
theorem relax_not_const : relax cortexSilent ≠ relax cortexState := by
  intro h
  have h' : density (relax cortexSilent) Site.mid = density (relax cortexState) Site.mid := by rw [h]
  rw [Phi_relax_apply, Phi_relax_apply, Phi_cortexSilent, Phi_cortexState] at h'
  norm_num at h'

theorem relax_fixed : relax cortexState = cortexState := by
  apply Phi_injective
  rw [Phi_relax]
  funext x
  apply NNReal.coe_injective
  push_cast
  ring

/-- The fixed point is unique, proved directly rather than quoted from Banach: a section
that predicts itself has the baseline's density. -/
theorem relax_fixed_unique (s : GlobalSection (X := Cortex)) (h : relax s = s) :
    s = cortexState := by
  apply Phi_injective
  funext x
  have hx : (density s x + density cortexState x) / 2 = density s x := by
    have h' : density (relax s) x = density s x := by rw [h]
    rw [Phi_relax_apply] at h'
    exact h'
  apply NNReal.coe_injective
  have := congrArg NNReal.toReal hx
  push_cast at this
  linarith

/-- The avatar region: the shared site `mid`, the one point both patches of §4 see. -/
def avatarPatch : Opens ↥Cortex := ⟨{Site.mid}, isOpen_discrete _⟩

noncomputable def cortexPredict : PredictiveModel Cortex := ⟨relax⟩

/-- A reflexive boundary on the three-site cortex. `auto_resonance` is the presheaf
restriction to the avatar region, so the avatar's state does track the global field —
which the class itself never requires. -/
noncomputable def cortexReflexive : ReflexiveBoundary Cortex where
  avatar_region := avatarPatch
  auto_resonance := fun s =>
    (probabilityPresheaf Cortex).map (homOfLE (le_top : avatarPatch ≤ ⊤)).op s
  predictive_model := cortexPredict

theorem cortexPredict_contracting :
    ContractingWith (1/2) cortexReflexive.predictive_model.predict :=
  relax_contracting

/-- Derivation 6, applied to the witness: the hypotheses of
`reflexive_topology_implies_self` hold on a substrate where the metric is the
uniform distance between the glued measures' densities and the contraction is not
constant. -/
theorem cortexHasSelf : ∃ s : GlobalSection (X := Cortex),
    cortexReflexive.predictive_model.predict s = s :=
  reflexive_topology_implies_self cortexReflexive cortexPredict_contracting

/-- The fixed point named — and, by `relax_fixed_unique`, the only one. The Self this
witness produces is the attractor of a non-constant dissipative map, not the value of a
constant one. -/
theorem cortexFixedPoint : cortexReflexive.predictive_model.predict cortexState = cortexState :=
  relax_fixed

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


end Examples
end PhysicsOfConsciousness
