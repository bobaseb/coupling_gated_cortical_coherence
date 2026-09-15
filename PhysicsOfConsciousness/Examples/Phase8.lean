/-
  Examples/Phase8.lean — the continuum field: gradient flow, threshold, operator

  §5 exercises the Phase 8 link on a two-site substrate: counting measure, a
  non-zero gradient, and an explicit non-constant flow along which entropy
  production decays as `e^{-2t}`. §9 is the fencing counterexample for the
  threshold — a system a factor of two below `K_c = 2D` whose unnormalized
  double integral clears the bar, which is why the criterion is about coupling
  and not about size. §12 records the three structures that still have no
  instance and why. §20 supplies an atomless witness for the continuum operator.
  §21 runs the stationary Fokker–Planck equation and both stability results on
  named numbers.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase8_ContinuousField
import PhysicsOfConsciousness.Phase8_CoherentStability

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

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

/-! ## 21. The stationary equation and its two branches, on named numbers

`Phase8_FokkerPlanck.lean` and the modules above it prove their results for
every positive diffusion and concentration. This section fixes numbers, so that
the predicates are inhabited by something a reader can evaluate, and checks the
two ways they could be hollow: the coherent stationary density could be the
uniform one in disguise, and the stability estimate could hold because its rate
is zero. Neither is the case.

The incoherent modes are exercised at `K = 3`, `D = 1` — the coupling and
diffusion of the cortex witness that `Chain.lean` carries — where the first
harmonic grows, and at `K = 1`, where no mode does.
-/

section StationaryWitness

open PhysicsOfConsciousness.FokkerPlanck

/-- The coherent stationary state at diffusion `1` and concentration `1`: the
density is stationary for the mean field it generates itself. -/
theorem unitBranch_stationary :
    IsStationary 1 (meanDrift (branchCoupling 1 1) (vonMisesDensity 1)) (vonMisesDensity 1) :=
  branch_stationary one_pos one_pos

/-- The coupling that parametrization selects is above threshold, so this is a
point of the coherent branch and not a subcritical state. -/
theorem unitBranch_supercritical : critical_coupling 1 < branchCoupling 1 1 := by
  rw [critical_coupling]
  exact branchCoupling_supercritical one_pos one_pos

/-- **Not the uniform state.** The witness would be empty of content if the
stationary density it exhibits were constant; this one takes different values at
`0` and at `π`. -/
theorem unitBranch_not_uniform : vonMisesDensity 1 0 ≠ vonMisesDensity 1 Real.pi := by
  intro h
  rw [vonMisesDensity, vonMisesDensity, vonMisesWeight, vonMisesWeight, Real.cos_zero,
    Real.cos_pi, div_left_inj' (vonMisesZ_pos 1).ne'] at h
  have h1 := Real.exp_eq_exp.mp h
  norm_num at h1

/-- **The gap is not zero.** `coherent_linear_stability` would be vacuous with a
rate of `0`; here the rate is a positive real. -/
theorem unitBranch_rate_pos : 0 < linearStabilityRate 1 1 :=
  linearStabilityRate_pos one_pos one_pos

/-- The separation, on this state: the stationary current dissipates nothing
while the phase-averaged squared drift is positive. Both are functionals on
phase space, and neither is `sigmaContinuum` on substrate sites. -/
theorem unitBranch_separation :
    currentDissipation 1 (meanDrift (branchCoupling 1 1) (vonMisesDensity 1))
      (vonMisesDensity 1) = 0 ∧
    0 < average 1 (((-1 * 1 : ℝ) • circleSin) * ((-1 * 1 : ℝ) • circleSin)) / 1 :=
  stationary_current_separation one_pos one_pos

/-- At the cortex witness's coupling the incoherent state has a growing mode. -/
theorem incoherent_unstable_three_one : ∃ n : ℕ, 0 < n ∧ 0 < incoherentRate 1 3 n :=
  (incoherent_instability_iff one_pos 3).mpr (by norm_num)

/-- Below threshold none of them grows, so the criterion is not trivially
satisfied. -/
theorem incoherent_stable_one_one : ¬ ∃ n : ℕ, 0 < n ∧ 0 < incoherentRate 1 1 n := by
  intro h
  have := (incoherent_instability_iff one_pos 1).mp h
  linarith

end StationaryWitness

end Examples
end PhysicsOfConsciousness
