import Mathlib

/-!
# Phase 8 — Continuous Field

## Structure of this file

1. A concrete half (`entropy_production_rate`, `phase_locked_achieves_minimum_entropy`)
   defining the entropy production functional σ of a stochastic neural field
   over a measure space `M`, and proving a *conditional* minimality result — see
   the `h_mean` caveat on that theorem.
2. An abstract half (`is_coupling_gradient_flow`,
   `gradient_flow_implies_entropy_decrease`, `continuous_structural_resonance`,
   `structural_resonance_implies_gradient_descent`) proving that a gradient flow
   on *any* Fréchet-differentiable functional `S` over *any* inner-product space
   `E` is monotonically non-increasing.
3. §7, which **connects the two**: on a finite substrate it computes the Fréchet
   derivative of σ with respect to the coupling kernel in closed form
   (`hasFDerivAt_sigmaOfKernel`), identifies the differentiated functional with
   `entropy_production_rate` itself (`sigmaOfKernel_eq_entropy_production_rate`),
   and transfers the descent results to σ
   (`structural_resonance_decreases_entropy_production`).

## Scope

The link in §7 is proved for a **finite** substrate whose `volume` is counting
measure; the continuum case would need differentiation under the integral sign
with respect to the kernel, which is not developed here. Throughout §7 the phase
field is held fixed: this is plasticity of the coupling at frozen phases, not
joint (θ, K) dynamics. And `phase_locked_achieves_minimum_entropy` remains
conditional on `h_mean` — see its own caveat.
-/

open Set MeasureTheory Topology

namespace PhysicsOfConsciousness

-- 1. Continuous Neural Field
variable {M : Type*} [MeasureSpace M] [TopologicalSpace M]

structure ContinuousNeuralField (M : Type*) [MeasureSpace M] [TopologicalSpace M] where
  omega : M → ℝ
  K : M → M → ℝ
  tau : ℝ

def is_continuous_kuramoto_trajectory (sys : ContinuousNeuralField M) (theta : ℝ → M → ℝ) : Prop :=
  ∀ (x : M) (t : ℝ),
    HasDerivAt (fun t => theta t x)
      (sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta t y - theta t x)) t

-- 2. Stochastic Thermodynamics & Entropy Production
structure StochasticNeuralField (M : Type*) [MeasureSpace M] [TopologicalSpace M]
  extends ContinuousNeuralField M where
  D : ℝ
  h_D_pos : D > 0
  Omega_avg : ℝ

noncomputable def entropy_production_rate (sys : StochasticNeuralField M) (theta : M → ℝ) : ℝ :=
  ∫ _x : M, (1 / sys.D) * (sys.omega _x + ∫ y : M, sys.K _x y * Real.sin (theta y - theta _x))^2

def is_dynamically_phase_locked (sys : StochasticNeuralField M) (theta : M → ℝ) : Prop :=
  ∀ x : M, sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta y - theta x) = sys.Omega_avg

/-
  Jensen-style lower bound for squared integrals (requires finite measure).
  Proves: if ∫f dμ = c·μ(M), then c²·μ(M) ≤ ∫f² dμ.
  Proof: 0 ≤ ∫(f - c)² = ∫f² - 2c·∫f + c²·μ(M); substitute ∫f = c·μ.
-/
omit [TopologicalSpace M] in
private lemma sq_integral_le_integral_sq [IsFiniteMeasure (volume : Measure M)]
    (f : M → ℝ) (c : ℝ)
    (hf : Integrable f) (hf2 : Integrable (fun x => f x ^ 2))
    (h_mean : ∫ x : M, f x = c * (volume (Set.univ : Set M)).toReal) :
    c ^ 2 * (volume (Set.univ : Set M)).toReal ≤ ∫ x : M, f x ^ 2 := by
  -- Core variance decomposition: 0 ≤ ∫(f - c)²
  have h0 : (0 : ℝ) ≤ ∫ x : M, (f x - c) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  -- Pointwise equality
  have heq : (fun x : M => (f x - c) ^ 2) = (fun x : M => (f x ^ 2 - 2 * c * f x) + c ^ 2) := by
    ext x; ring
  -- Integrability of component functions
  have hfc   : Integrable (fun x : M => 2 * c * f x) := hf.const_mul (2 * c)
  have hf2mc : Integrable (fun x : M => f x ^ 2 - 2 * c * f x) := hf2.sub hfc
  have hconst: Integrable (fun _ : M => c ^ 2) := integrable_const (c ^ 2)
  -- Expand: ∫(f-c)² = ∫f² - 2c·∫f + c²·μ
  have h_expand : ∫ x : M, (f x - c) ^ 2 =
      (∫ x : M, f x ^ 2) - 2 * c * (∫ x : M, f x) + c ^ 2 * (volume (Set.univ : Set M)).toReal := by
    rw [heq, integral_add hf2mc hconst, integral_sub hf2 hfc, integral_const_mul, integral_const]
    simp only [smul_eq_mul]
    rw [MeasureTheory.measureReal_def]
    ring
  -- Substitute h_mean and conclude
  rw [h_mean] at h_expand
  linarith

/--
**Phase-locked state achieves minimum entropy production.**

`StochasticNeuralField.lower_bound` has been removed; minimality is now proved
from the variance bound `sq_integral_le_integral_sq` (requires `[IsFiniteMeasure volume]`).

**Caveat on `h_mean`.** The hypothesis quantifies over *every* competitor field
`theta_other` and requires each to have the same spatial mean drift
`Omega_avg`. This is a strong restriction: it confines the comparison class to
configurations that already share the phase-locked state's first moment, and
minimality then follows from Jensen/variance alone. It is therefore not a proof
that phase-locking minimizes entropy production among *all* fields — only among
those with matching mean drift. Removing this hypothesis would require modelling
how `Omega_avg` itself varies with `theta_other`, which is not done here.
-/
theorem phase_locked_achieves_minimum_entropy [IsFiniteMeasure (volume : Measure M)]
  (sys : StochasticNeuralField M) (theta : M → ℝ)
  (h_lock : is_dynamically_phase_locked sys theta)
  (h_mean : ∀ (theta_other : M → ℝ),
    ∫ x : M, (sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta_other y - theta_other x)) =
    sys.Omega_avg * (volume (Set.univ : Set M)).toReal) :
  entropy_production_rate sys theta = (∫ _x : M, (1 / sys.D) * sys.Omega_avg^2) ∧
  ∀ (theta_other : M → ℝ)
    (_hf : Integrable (fun x => sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta_other y - theta_other x)))
    (_hf2 : Integrable (fun x => (sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta_other y - theta_other x))^2)),
    entropy_production_rate sys theta ≤ entropy_production_rate sys theta_other := by
  have h_drift_eq : ∀ x : M,
      (1 / sys.D) * (sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta y - theta x))^2 =
      (1 / sys.D) * sys.Omega_avg^2 := fun x => by rw [h_lock x]
  have h_integrand_eq :
      (fun x : M => (1 / sys.D) * (sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta y - theta x))^2) =
      fun _ => (1 / sys.D) * sys.Omega_avg^2 := funext h_drift_eq
  constructor
  · -- Equality: integrand is constant under phase-locking.
    unfold entropy_production_rate; rw [h_integrand_eq]
  · -- Minimality: use Jensen bound.
    intro theta_other _hf _hf2
    unfold entropy_production_rate
    rw [h_integrand_eq]
    set f_other := fun x : M =>
      sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta_other y - theta_other x)
    -- Jensen: Ω²·μ(M) ≤ ∫ f_other²
    have h_lb := sq_integral_le_integral_sq f_other sys.Omega_avg _hf _hf2 (h_mean theta_other)
    -- Rewrite LHS: ∫(1/D)·Ω² = (1/D)·Ω²·μ(M)
    have h_lhs : ∫ _x : M, (1 / sys.D) * sys.Omega_avg ^ 2 =
        (1 / sys.D) * sys.Omega_avg ^ 2 * (volume (Set.univ : Set M)).toReal := by
      rw [integral_const]
      simp only [smul_eq_mul]
      rw [MeasureTheory.measureReal_def]
      ring
    -- Rewrite RHS: ∫(1/D)·f² = (1/D)·∫f²
    have h_rhs : ∫ x : M, (1 / sys.D) * f_other x ^ 2 =
        (1 / sys.D) * ∫ x : M, f_other x ^ 2 := by
      rw [integral_const_mul]
    rw [h_lhs, h_rhs]
    have h_inv_pos : (0 : ℝ) < 1 / sys.D := div_pos one_pos sys.h_D_pos
    nlinarith [h_lb, (volume (Set.univ : Set M)).toReal_nonneg]

-- 3. Topology Deformation
structure PlasticNeuralField (M : Type*) [MeasureSpace M] [TopologicalSpace M] 
  extends StochasticNeuralField M where
  K_t : ℝ → M → M → ℝ
  h_K_init : K_t 0 = toStochasticNeuralField.K

noncomputable def dynamic_entropy_production (sys : PlasticNeuralField M) (theta : ℝ → M → ℝ) (t : ℝ) : ℝ :=
  ∫ x : M, (1 / sys.D) * (sys.omega x + ∫ y : M, sys.K_t t x y * Real.sin (theta t y - theta t x))^2

def is_gradient_descent (sys : PlasticNeuralField M) (theta : ℝ → M → ℝ) : Prop :=
  ∀ t1 t2, t1 ≤ t2 → dynamic_entropy_production sys theta t2 ≤ dynamic_entropy_production sys theta t1

-- 4. Critical Coupling Thresholds
/--
Critical coupling threshold for the Kuramoto phase transition.
When the mean-field coupling strength exceeds this value, K > K_c = 2D,
the oscillators undergo a synchronization phase transition.

Numerically validated against `simulations/kuramoto.py` (see that script's
`simulate_kuramoto` function, which sweeps K and measures the order parameter r
against the theoretical threshold K_c = 2D).

**Scope.** The threshold's content is the bifurcation of the self-consistency
equation `r = I₁(Kr/D) / I₀(Kr/D)` for the noisy mean-field Kuramoto model, and
that bifurcation *is* formalized, in `Phase8_SelfConsistency.lean`: below `2 * D`
the incoherent state is the only non-negative solution
(`subcritical_fixed_point_eq_zero'`), above it a solution with `0 < r ≤ 1` exists
(`supercritical_fixed_point_exists`); `critical_coupling_is_threshold` packages
the two. `exhibits_phase_transition_coherent` there applies this to any substrate
satisfying `exhibits_phase_transition` below.

What remains assumed is the *von Mises stationary density* those theorems take as
input — deriving it from the underlying SDE needs the Fokker–Planck operator and
stationary-measure theory for SPDEs, which Mathlib does not have. And nothing
here connects the threshold to `is_continuous_kuramoto_trajectory`,
`entropy_production_rate` or `order_parameter_r_sq`: the results are about the
self-consistency equation, not about a trajectory.
-/
noncomputable def critical_coupling (D : ℝ) : ℝ := 2 * D

/--
The mean-field coupling strength of a substrate: the kernel averaged over both
of its arguments.

This is the quantity the threshold `K_c = 2D` is about. The averaging is against
`volume`, so it is a *strength* only when `volume` is a probability measure —
see `exhibits_phase_transition`, which requires exactly that.
-/
noncomputable def mean_field_coupling (sys : StochasticNeuralField M) : ℝ :=
  ∫ x : M, ∫ y : M, sys.K x y

/--
The substrate is above the synchronization threshold.

**The probability-measure hypothesis is not decoration.** `mean_field_coupling`
integrates the kernel against `volume` twice, so on a substrate of total mass
`m` a constant kernel `K` contributes `K · m²`. Comparing that against `2D`
would make the predicate depend on the substrate's size rather than on how
strongly it is coupled, and would be satisfiable for *any* kernel by inflating
`m`. Requiring `volume` to be a probability measure fixes the normalization in
which the mean-field derivation of `K_c = 2D` is carried out: a constant kernel
then has `mean_field_coupling = K` exactly (`mean_field_coupling_const`).
-/
def exhibits_phase_transition [IsProbabilityMeasure (volume : Measure M)]
    (sys : StochasticNeuralField M) : Prop :=
  mean_field_coupling sys > critical_coupling sys.D

/-- On a probability substrate a constant kernel has mean-field strength equal
to that constant — the normalization in which `K_c = 2D` is stated. -/
@[simp] theorem mean_field_coupling_const [IsProbabilityMeasure (volume : Measure M)]
    (sys : StochasticNeuralField M) (c : ℝ) (hK : sys.K = fun _ _ => c) :
    mean_field_coupling sys = c := by
  simp [mean_field_coupling, hK]

/-- For a constant kernel the predicate says exactly what the physics says:
the coupling constant exceeds twice the noise strength. -/
theorem exhibits_phase_transition_const_iff [IsProbabilityMeasure (volume : Measure M)]
    (sys : StochasticNeuralField M) (c : ℝ) (hK : sys.K = fun _ _ => c) :
    exhibits_phase_transition sys ↔ c > 2 * sys.D := by
  rw [exhibits_phase_transition, mean_field_coupling_const sys c hK, critical_coupling]

-- 5. Empirical Grounding
noncomputable def cortical_temperature_kelvin : ℝ := 310.15
noncomputable def boltzmann_constant : ℝ := 1.380649e-23
noncomputable def macroscopic_noise_D : ℝ := cortical_temperature_kelvin * boltzmann_constant

noncomputable def ephaptic_critical_coupling : ℝ := critical_coupling macroscopic_noise_D

-- 6. Gradient Descent Mechanism
-- Replace tautological definitions with meaningful dynamic bounds.
-- Structural resonance occurs when the time evolution of the coupling matrix K_t
-- aligns with the negative gradient of the entropy production. 
-- We model the space of coupling matrices abstractly as an inner product space E.

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
A trajectory `K_t` follows the gradient flow of a functional `S` with gradient `gradS`
if its velocity is the negative gradient of `S`.
-/
def is_coupling_gradient_flow (K_t : ℝ → E) (S : E → ℝ) (gradS : E → E) : Prop :=
  (∀ K, HasFDerivAt S (innerSL ℝ (gradS K)) K) ∧
  (∀ t, HasDerivAt K_t (- gradS (K_t t)) t)

theorem gradient_flow_implies_entropy_decrease (K_t : ℝ → E) (S : E → ℝ) (gradS : E → E)
  (h_flow : is_coupling_gradient_flow K_t S gradS) :
  Antitone (fun t => S (K_t t)) := by
  apply antitone_of_hasDerivAt_nonpos (f' := fun t => - (norm (gradS (K_t t)) ^ 2))
  · intro t
    have h_comp := HasFDerivAt.comp_hasDerivAt t (h_flow.1 (K_t t)) (h_flow.2 t)
    have h_eq : (innerSL ℝ (gradS (K_t t))) (- gradS (K_t t)) = - (norm (gradS (K_t t)) ^ 2) := by
      simp [inner_neg_right]
    rw [h_eq] at h_comp
    exact h_comp
  · intro t
    exact neg_nonpos.mpr (sq_nonneg _)

/--
Continuous structural resonance is the physical regime where coupling dynamics
evolve proportionately to the negative gradient of the entropy production landscape.
We introduce a physical relaxation rate `c > 0`.
-/
def continuous_structural_resonance (K_t : ℝ → E) (S : E → ℝ) (gradS : E → E) (c : ℝ) : Prop :=
  (∀ K, HasFDerivAt S (innerSL ℝ (gradS K)) K) ∧
  (∀ t, HasDerivAt K_t (- c • gradS (K_t t)) t) ∧
  (c > 0)

theorem structural_resonance_implies_gradient_descent (K_t : ℝ → E) (S : E → ℝ) (gradS : E → E) (c : ℝ)
  (h_res : continuous_structural_resonance K_t S gradS c) : 
  Antitone (fun t => S (K_t t)) := by
  apply antitone_of_hasDerivAt_nonpos (f' := fun t => - c * norm (gradS (K_t t)) ^ 2)
  · intro t
    have h_comp := HasFDerivAt.comp_hasDerivAt t (h_res.1 (K_t t)) (h_res.2.1 t)
    have h_eq : (innerSL ℝ (gradS (K_t t))) (- c • gradS (K_t t)) = - c * norm (gradS (K_t t)) ^ 2 := by
      simp [innerSL, inner_neg_right, inner_smul_right]
    rw [h_eq] at h_comp
    exact h_comp
  · intro t
    have hc : c > 0 := h_res.2.2
    have h_sq_nonneg : 0 ≤ (norm (gradS (K_t t))) ^ 2 := sq_nonneg _
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) h_sq_nonneg

/-!
## 7. Linking the two halves: σ as a functional of the coupling kernel

Sections 2 and 6 above were, until now, unconnected: σ (`entropy_production_rate`)
was a functional of the *phase field* over a measure space, while the descent
theorems were about an arbitrary Fréchet-differentiable `S` on an arbitrary
inner-product space, with the gradient supplied as data. Nothing said that σ
*has* a gradient, so the manuscript's claim that structural resonance drives σ
downhill rested on an informal identification.

This section supplies the missing derivation, on a **finite substrate**. Fix the
phase field `theta` and read σ as a function of the coupling kernel `K`. On a
finite `M` the kernels form the finite-dimensional real inner-product space
`CouplingSpace M = EuclideanSpace ℝ (M × M)`, σ becomes a quadratic functional
of `K`, and its Fréchet derivative can be computed in closed form:

  ∂σ/∂K(a,b) = (2/D) · drift(a) · sin(θ_b − θ_a).

`hasFDerivAt_sigmaOfKernel` proves exactly that, and
`sigmaOfKernel_eq_entropy_production_rate` identifies the functional being
differentiated with `entropy_production_rate` itself, whenever `volume` is
counting measure. The abstract descent theorems then transfer:
`entropy_production_antitone_of_gradient_flow` and
`structural_resonance_decreases_entropy_production` are statements about σ, not
about an abstract `S`.

**Scope.** The link is established for finite substrates only. Extending it to a
continuum `M` requires differentiating under the integral sign with respect to
the kernel — Gateaux-to-Fréchet upgrading for the operator `K ↦ ∫ K x y sin(…)`
— which is not developed here. The phase field is held fixed throughout: this is
plasticity of the coupling at frozen phases, not joint (θ, K) dynamics.
-/

section FiniteCoupling

variable {M : Type*} [Fintype M] [MeasureSpace M] [TopologicalSpace M]

/-- Coupling kernels on a finite substrate, as a real inner-product space. -/
abbrev CouplingSpace (M : Type*) [Fintype M] := EuclideanSpace ℝ (M × M)

private lemma inner_euclid {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℝ ι) :
    (inner ℝ u v : ℝ) = ∑ i, u i * v i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [RCLike.inner_apply, mul_comm]

/-- The drift at site `x`: natural frequency plus the coupling-weighted phase
    mismatch. This is the quantity σ integrates the square of. -/
noncomputable def drift (sys : StochasticNeuralField M) (theta : M → ℝ)
    (K : CouplingSpace M) (x : M) : ℝ :=
  sys.omega x + ∑ y : M, K (x, y) * Real.sin (theta y - theta x)

/-- Entropy production, read as a functional of the coupling kernel at fixed
    phase field. Identified with `entropy_production_rate` in
    `sigmaOfKernel_eq_entropy_production_rate`. -/
noncomputable def sigmaOfKernel (sys : StochasticNeuralField M) (theta : M → ℝ)
    (K : CouplingSpace M) : ℝ :=
  ∑ x : M, (1 / sys.D) * (drift sys theta K x)^2

/-- Row `x` of the phase-mismatch matrix, as a vector of `CouplingSpace M`.
    Pairing against it extracts the coupling contribution to the drift at `x`. -/
noncomputable def sensRow [DecidableEq M] (theta : M → ℝ) (x : M) : CouplingSpace M :=
  WithLp.toLp 2 (fun p : M × M => if p.1 = x then Real.sin (theta p.2 - theta x) else 0)

omit [MeasureSpace M] [TopologicalSpace M] in
lemma inner_sensRow [DecidableEq M] (theta : M → ℝ) (x : M) (K : CouplingSpace M) :
    (inner ℝ (sensRow theta x) K : ℝ) = ∑ y : M, K (x, y) * Real.sin (theta y - theta x) := by
  rw [inner_euclid, Fintype.sum_prod_type, Finset.sum_eq_single x]
  · exact Finset.sum_congr rfl fun y _ => by simp [sensRow, mul_comm]
  · intro b _ hb
    exact Finset.sum_eq_zero fun y _ => by simp [sensRow, hb]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- The drift is affine in the kernel: constant `omega x` plus a continuous
    linear functional. This is what makes σ a quadratic functional. -/
lemma drift_eq_inner [DecidableEq M] (sys : StochasticNeuralField M) (theta : M → ℝ)
    (K : CouplingSpace M) (x : M) :
    drift sys theta K x = sys.omega x + (inner ℝ (sensRow theta x) K : ℝ) := by
  rw [inner_sensRow]; rfl

/-- The gradient of σ with respect to the coupling kernel, in closed form:
    `∂σ/∂K(a,b) = (2/D) · drift(a) · sin(θ_b − θ_a)`. -/
noncomputable def gradSigma [DecidableEq M] (sys : StochasticNeuralField M) (theta : M → ℝ)
    (K : CouplingSpace M) : CouplingSpace M :=
  WithLp.toLp 2 (fun p : M × M =>
    (2 / sys.D) * drift sys theta K p.1 * Real.sin (theta p.2 - theta p.1))

/-- **σ is Fréchet differentiable in the coupling kernel, with gradient
    `gradSigma`.** This is the fact the abstract half of the file assumed as
    data (`is_coupling_gradient_flow`'s first conjunct); here it is derived. -/
theorem hasFDerivAt_sigmaOfKernel [DecidableEq M] (sys : StochasticNeuralField M)
    (theta : M → ℝ) (K : CouplingSpace M) :
    HasFDerivAt (sigmaOfKernel sys theta) (innerSL ℝ (gradSigma sys theta K)) K := by
  have hdrift : ∀ x : M, HasFDerivAt (fun K' : CouplingSpace M => drift sys theta K' x)
      (innerSL ℝ (sensRow theta x)) K := by
    intro x
    have h : (fun K' : CouplingSpace M => drift sys theta K' x)
        = fun K' => sys.omega x + (innerSL ℝ (sensRow theta x)) K' := by
      funext K'; rw [drift_eq_inner]; rfl
    rw [h]
    exact ((innerSL ℝ (sensRow theta x)).hasFDerivAt).const_add _
  have hterm : ∀ x : M, HasFDerivAt
      (fun K' : CouplingSpace M => (1 / sys.D) * (drift sys theta K' x) ^ 2)
      ((1 / sys.D) • ((2 • (drift sys theta K x) ^ (2 - 1)) • innerSL ℝ (sensRow theta x))) K :=
    fun x => ((hdrift x).pow 2).const_mul (1 / sys.D)
  have hsum := HasFDerivAt.fun_sum (fun x (_ : x ∈ Finset.univ) => hterm x)
  have heq : (∑ x : M, (1 / sys.D) • ((2 • (drift sys theta K x) ^ (2 - 1))
        • innerSL ℝ (sensRow theta x)))
      = innerSL ℝ (gradSigma sys theta K) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sum_apply, smul_apply, smul_eq_mul, coe_innerSL_apply, nsmul_eq_mul,
      Nat.cast_ofNat]
    rw [inner_euclid, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [inner_sensRow, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [gradSigma, WithLp.ofLp_toLp]
    ring
  exact heq ▸ hsum

/-- Replace a field's coupling kernel with `K`. -/
def StochasticNeuralField.withKernel (sys : StochasticNeuralField M) (K : CouplingSpace M) :
    StochasticNeuralField M :=
  { sys with
    toContinuousNeuralField :=
      { sys.toContinuousNeuralField with K := fun x y => K (x, y) } }

/-- **The bridge.** On a finite substrate carrying counting measure, the
    functional differentiated above *is* `entropy_production_rate`. Without this
    lemma the descent results would still be about a re-definition of σ rather
    than about σ. -/
theorem sigmaOfKernel_eq_entropy_production_rate [MeasurableSingletonClass M]
    (hvol : (volume : Measure M) = Measure.count)
    (sys : StochasticNeuralField M) (theta : M → ℝ) (K : CouplingSpace M) :
    sigmaOfKernel sys theta K = entropy_production_rate (sys.withKernel K) theta := by
  unfold sigmaOfKernel entropy_production_rate drift
  simp only [hvol, integral_count]
  rfl

/-- σ is bounded below by 0, so the monotone descent below cannot run away. -/
theorem sigmaOfKernel_nonneg (sys : StochasticNeuralField M) (theta : M → ℝ)
    (K : CouplingSpace M) : 0 ≤ sigmaOfKernel sys theta K := by
  refine Finset.sum_nonneg fun x _ => ?_
  have : (0 : ℝ) < 1 / sys.D := div_pos one_pos sys.h_D_pos
  positivity

/-- A kernel trajectory moving against `gradSigma` is a gradient flow in the
    sense of §6 — the differentiability obligation is now discharged, not
    hypothesised. -/
theorem is_coupling_gradient_flow_sigmaOfKernel [DecidableEq M]
    (sys : StochasticNeuralField M) (theta : M → ℝ) (K_t : ℝ → CouplingSpace M)
    (h : ∀ t, HasDerivAt K_t (- gradSigma sys theta (K_t t)) t) :
    is_coupling_gradient_flow K_t (sigmaOfKernel sys theta) (gradSigma sys theta) :=
  ⟨hasFDerivAt_sigmaOfKernel sys theta, h⟩

/-- **Link, stated on the concrete functional.** Entropy production decreases
    monotonically along the gradient flow of the coupling kernel. -/
theorem entropy_production_antitone_of_gradient_flow [DecidableEq M] [MeasurableSingletonClass M]
    (hvol : (volume : Measure M) = Measure.count)
    (sys : StochasticNeuralField M) (theta : M → ℝ) (K_t : ℝ → CouplingSpace M)
    (h : ∀ t, HasDerivAt K_t (- gradSigma sys theta (K_t t)) t) :
    Antitone (fun t => entropy_production_rate (sys.withKernel (K_t t)) theta) := by
  have hA := gradient_flow_implies_entropy_decrease K_t (sigmaOfKernel sys theta)
    (gradSigma sys theta) (is_coupling_gradient_flow_sigmaOfKernel sys theta K_t h)
  intro a b hab
  dsimp only
  rw [← sigmaOfKernel_eq_entropy_production_rate hvol,
    ← sigmaOfKernel_eq_entropy_production_rate hvol]
  exact hA hab

/-- **Structural resonance drives entropy production down.** The manuscript's
    Derivation 3 claim, now a theorem about `entropy_production_rate` rather
    than about an abstract functional: if the coupling relaxes down the σ
    gradient at any positive rate `c`, σ is non-increasing in time. -/
theorem structural_resonance_decreases_entropy_production [DecidableEq M]
    [MeasurableSingletonClass M]
    (hvol : (volume : Measure M) = Measure.count)
    (sys : StochasticNeuralField M) (theta : M → ℝ) (K_t : ℝ → CouplingSpace M) (c : ℝ)
    (hc : c > 0) (h : ∀ t, HasDerivAt K_t (- c • gradSigma sys theta (K_t t)) t) :
    Antitone (fun t => entropy_production_rate (sys.withKernel (K_t t)) theta) := by
  have hres : continuous_structural_resonance K_t (sigmaOfKernel sys theta)
      (gradSigma sys theta) c := ⟨hasFDerivAt_sigmaOfKernel sys theta, h, hc⟩
  have hA := structural_resonance_implies_gradient_descent K_t (sigmaOfKernel sys theta)
    (gradSigma sys theta) c hres
  intro a b hab
  dsimp only
  rw [← sigmaOfKernel_eq_entropy_production_rate hvol,
    ← sigmaOfKernel_eq_entropy_production_rate hvol]
  exact hA hab

end FiniteCoupling

end PhysicsOfConsciousness
