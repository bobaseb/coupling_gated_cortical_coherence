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
    ✓ `StructuralResonance`  — a perfectly-resonant system (KL = 0).
    ✓ `ActionPrinciples`     — a scalar field on a one-point spacetime.
    ✓ `LocalSectionSynchronization` / `ThermodynamicCover` — two overlapping
      patches on a three-site substrate, with sections of the sheafified
      probability presheaf built from a phase-dependent invariant measure (§4).

  §5 additionally exercises the Phase 8 gradient-flow link on a two-site
  substrate: counting measure, a non-zero gradient, and an explicit non-constant
  flow along which entropy production decays as `e^{-2t}`.

  Every declaration in this file depends only on `propext`, `Classical.choice`
  and `Quot.sound`.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_KLBound
import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Phase8_ContinuousField

open MeasureTheory CategoryTheory TopologicalSpace Opposite

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

/-! ## 2. A perfectly resonant system -/

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

end Examples
end PhysicsOfConsciousness
