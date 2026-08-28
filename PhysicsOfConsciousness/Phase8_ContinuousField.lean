import Mathlib

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
When the spatial coupling strength exceeds this value, K > K_c = 2D,
the oscillators undergo a synchronization phase transition.

Numerically validated against `simulations/kuramoto.py` (see that script's
`simulate_kuramoto` function, which sweeps K and measures the order parameter r
against the theoretical threshold K_c = 2D).
-/
noncomputable def critical_coupling (D : ℝ) : ℝ := 2 * D

def exhibits_phase_transition (sys : StochasticNeuralField M) : Prop :=
  (∫ x : M, ∫ y : M, sys.K x y) > critical_coupling sys.D

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

end PhysicsOfConsciousness
