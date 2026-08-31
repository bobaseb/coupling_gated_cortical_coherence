import Mathlib

/-!
# Phase 8 — Continuous Field

## Structure of this file

1. A concrete half (`entropy_production_rate`, `phase_locked_achieves_minimum_entropy`)
   defining the entropy production functional σ of a stochastic neural field
   over a measure space `M`, and proving a *conditional* minimality result — see
   the `h_mean` caveat on that theorem — since discharged for symmetric kernels
   in §2a, which is the case Derivation 5 and Derivation 7 both work in.
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
4. §8, which factors §7's computation through an abstract lemma
   (`hasFDerivAt_quadratic_of_affine`) and thereby narrows what the continuum
   case still needs to a single bounded operator.

## Scope

The link in §7 is proved for a **finite** substrate whose `volume` is counting
measure. §8 shows what that restriction costs and corrects the estimate this
header used to carry: σ is a quadratic functional of an affine image of the
kernel, so its differentiability needs no limiting argument at all, and the
continuum case is blocked only on exhibiting the drift map as a bounded operator
between `Lp` spaces — a Cauchy–Schwarz estimate, not differentiation under the
integral sign. Throughout §7 the phase
field is held fixed: this is plasticity of the coupling at frozen phases, not
joint (θ, K) dynamics. `phase_locked_achieves_minimum_entropy` remains
conditional on `h_mean`; §2a discharges that condition whenever the kernel is
symmetric, so the unrestricted minimality statement is
`phase_locked_minimizes_entropy_of_symm`.
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
`Omega_avg`. Read on its own this is a strong restriction: it confines the
comparison class to configurations that already share the phase-locked state's
first moment, and minimality then follows from Jensen/variance alone.

**It is, however, free for a symmetric kernel**, which is the case the framework
uses. `mean_drift_of_symm` (§2a below) proves `h_mean` from `h_lock` and
`K x y = K y x`, and `phase_locked_minimizes_entropy_of_symm` is the resulting
unrestricted statement. This theorem is kept in its general form because the
symmetric result is derived from it and because it is the sharper statement about
what the variance bound alone gives: nothing about symmetry enters here.
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

/-!
### 2a. Removing the comparison-class restriction: symmetric kernels

The `h_mean` caveat above was recorded as open item **O11**, on the reading that
removing it "would require modelling how `Omega_avg` varies with the competitor
field". That estimate was wrong, and in the direction that matters: for a
**symmetric** kernel the hypothesis is not a restriction at all but a theorem,
so on the class of kernels the framework actually uses the minimality result
quantifies over every competitor.

The reason is one line of antisymmetry. The coupling integrand
`K x y · sin(θ y − θ x)` picks up a sign under swapping its two sites when `K`
is symmetric, because `sin` is odd; Fubini then identifies the double integral
with its own negative, so the total coupling contribution vanishes
(`coupling_integral_eq_zero`). Hence the *total* drift `∫ (ω + coupling)` equals
`∫ ω` for **every** phase field (`total_drift_eq_of_symm`) — the coupling moves
drift between sites but cannot create or destroy it. Evaluating that invariant at
the phase-locked field, where the drift is the constant `Omega_avg`, pins the
common value, which is exactly `h_mean` (`mean_drift_of_symm`).

Symmetry is imposed as a **hypothesis**, not as a field of `ContinuousNeuralField`,
per rule §3 of `PhysicsOfConsciousness/AGENTS.md`: the results quantify over
instances. It is the same condition `ThermodynamicCover.A_symm` already carries in
Derivation 5, and it is the physical one — a reciprocal ephaptic coupling, in which
the influence of site `x` on `y` equals that of `y` on `x`.

**What this does not establish.** The integrability side conditions are
hypotheses, discharged on the finite witness in `Examples.lean` §16 and not in
general. And the result is still about a *comparison*: the phase-locked field has
the least entropy production of any field, but no dynamics is shown to reach it —
that is **O20**, and it is unaffected by this.
-/

omit [TopologicalSpace M] in
/-- **The total coupling contribution vanishes for a symmetric kernel.** The
integrand is antisymmetric under swapping sites, since `K x y = K y x` while
`sin (θ y − θ x) = −sin (θ x − θ y)`; Fubini then makes the double integral equal
to its own negative.

The integrability hypothesis is on the product measure and is what Fubini needs;
it is not implied by integrability of the iterated integrals. -/
lemma coupling_integral_eq_zero [SFinite (volume : Measure M)]
    (K : M → M → ℝ) (hK : ∀ x y, K x y = K y x) (theta : M → ℝ)
    (hint : Integrable (Function.uncurry fun x y => K x y * Real.sin (theta y - theta x))
      ((volume : Measure M).prod volume)) :
    ∫ x : M, ∫ y : M, K x y * Real.sin (theta y - theta x) = 0 := by
  set F : M → M → ℝ := fun x y => K x y * Real.sin (theta y - theta x) with hF
  have hanti : ∀ x y, F x y = -F y x := by
    intro x y
    have h : theta x - theta y = -(theta y - theta x) := by ring
    simp only [hF, hK x y, h, Real.sin_neg]; ring
  have h1 : ∫ x : M, ∫ y : M, F x y = ∫ y : M, ∫ x : M, F x y := integral_integral_swap hint
  have h2 : ∀ y : M, ∫ x : M, F x y = -∫ x : M, F y x := by
    intro y; rw [← integral_neg]; congr 1; funext x; exact hanti x y
  have h3 : ∫ y : M, ∫ x : M, F x y = -∫ y : M, ∫ x : M, F y x := by
    rw [← integral_neg]; congr 1; funext y; exact h2 y
  -- `∫ y, ∫ x, F y x` is `∫ x, ∫ y, F x y` up to renaming the bound variables.
  have h4 : (∫ x : M, ∫ y : M, F x y) = -(∫ x : M, ∫ y : M, F x y) := h1.trans h3
  linarith

/-- **The total drift is a conserved quantity of the phase field.** For a
symmetric kernel, `∫ (ω + coupling)` equals `∫ ω` whatever the phases are: the
coupling redistributes drift between sites without changing its total. This is
the invariant that makes `h_mean` free. -/
theorem total_drift_eq_of_symm [SFinite (volume : Measure M)]
    (sys : StochasticNeuralField M) (hK : ∀ x y, sys.K x y = sys.K y x)
    (hom : Integrable sys.omega) (theta : M → ℝ)
    (hcoup : Integrable (fun x => ∫ y : M, sys.K x y * Real.sin (theta y - theta x)))
    (hprod : Integrable (Function.uncurry fun x y => sys.K x y * Real.sin (theta y - theta x))
      ((volume : Measure M).prod volume)) :
    ∫ x : M, (sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta y - theta x))
      = ∫ x : M, sys.omega x := by
  rw [integral_add hom hcoup, coupling_integral_eq_zero sys.K hK theta hprod, add_zero]

/-- **`h_mean` is a theorem, not a restriction, when the kernel is symmetric.**

Every phase field has the same total drift (`total_drift_eq_of_symm`); the
phase-locked field fixes that total at `Omega_avg · μ(M)`, since its drift is
constant. So every competitor meets the mean-matching condition automatically. -/
theorem mean_drift_of_symm [IsFiniteMeasure (volume : Measure M)]
    (sys : StochasticNeuralField M) (theta : M → ℝ)
    (hK : ∀ x y, sys.K x y = sys.K y x)
    (h_lock : is_dynamically_phase_locked sys theta)
    (hom : Integrable sys.omega)
    (hcoup : ∀ t : M → ℝ, Integrable (fun x => ∫ y : M, sys.K x y * Real.sin (t y - t x)))
    (hprod : ∀ t : M → ℝ,
      Integrable (Function.uncurry fun x y => sys.K x y * Real.sin (t y - t x))
        ((volume : Measure M).prod volume)) :
    ∀ t : M → ℝ, ∫ x : M, (sys.omega x + ∫ y : M, sys.K x y * Real.sin (t y - t x))
      = sys.Omega_avg * (volume (Set.univ : Set M)).toReal := by
  have key : ∫ x : M, sys.omega x = sys.Omega_avg * (volume (Set.univ : Set M)).toReal := by
    have h1 := total_drift_eq_of_symm sys hK hom theta (hcoup theta) (hprod theta)
    have h2 : ∫ x : M, (sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta y - theta x))
        = sys.Omega_avg * (volume (Set.univ : Set M)).toReal := by
      have hc : (fun x : M => sys.omega x + ∫ y : M, sys.K x y * Real.sin (theta y - theta x))
          = fun _ => sys.Omega_avg := funext h_lock
      rw [hc, integral_const]
      simp only [smul_eq_mul]
      rw [MeasureTheory.measureReal_def]; ring
    rw [← h1, h2]
  intro t
  rw [total_drift_eq_of_symm sys hK hom t (hcoup t) (hprod t), key]

/-- **Phase-locking minimizes entropy production among *all* competitor fields**,
for a symmetric kernel. This is `phase_locked_achieves_minimum_entropy` with its
comparison-class restriction discharged rather than assumed (open item **O11**),
and it is the form the manuscript's Derivation 7 claim needs.

The integrability of the drift itself is discharged too, from `hom` and `hcoup`;
only integrability of its *square*, which the variance bound genuinely needs,
survives as a hypothesis on the competitor. -/
theorem phase_locked_minimizes_entropy_of_symm [IsFiniteMeasure (volume : Measure M)]
    (sys : StochasticNeuralField M) (theta : M → ℝ)
    (hK : ∀ x y, sys.K x y = sys.K y x)
    (h_lock : is_dynamically_phase_locked sys theta)
    (hom : Integrable sys.omega)
    (hcoup : ∀ t : M → ℝ, Integrable (fun x => ∫ y : M, sys.K x y * Real.sin (t y - t x)))
    (hprod : ∀ t : M → ℝ,
      Integrable (Function.uncurry fun x y => sys.K x y * Real.sin (t y - t x))
        ((volume : Measure M).prod volume)) :
    entropy_production_rate sys theta = (∫ _x : M, (1 / sys.D) * sys.Omega_avg ^ 2) ∧
    ∀ (t : M → ℝ) (_hf2 : Integrable
        (fun x => (sys.omega x + ∫ y : M, sys.K x y * Real.sin (t y - t x)) ^ 2)),
      entropy_production_rate sys theta ≤ entropy_production_rate sys t := by
  obtain ⟨heq, hmin⟩ := phase_locked_achieves_minimum_entropy sys theta h_lock
    (mean_drift_of_symm sys theta hK h_lock hom hcoup hprod)
  exact ⟨heq, fun t hf2 => hmin t (hom.add (hcoup t)) hf2⟩

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
and is unique (`supercritical_fixed_point_existsUnique`), and it increases
strictly with the coupling (`coherent_branch_strictMono`);
`critical_coupling_is_threshold_unique` packages the two regimes.
`exhibits_phase_transition_unique_coherent` there applies this to any substrate
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

/-!
## 8. What the finite restriction in §7 actually costs

Open item **O10** recorded the obstacle to extending §7 beyond finite substrates
as "differentiation under the integral sign with respect to the kernel", to be
attacked with `hasDerivAt_integral_of_dominated_loc_of_deriv_le` and a domination
argument. That diagnosis is wrong, and this section says why, because the
correction shrinks the item rather than growing it.

σ is not a general functional that happens to be given by an integral. It is a
**quadratic functional of an affine image**: the drift depends on the kernel
affinely — a fixed `ω` plus a linear operator applied to `K` — and σ is a
constant times the squared norm of that drift. Squared norm is Fréchet
differentiable on any real inner-product space, and an affine map is its own
derivative, so the composite is differentiable by the chain rule with no
limiting argument anywhere. `hasFDerivAt_quadratic_of_affine` is that statement,
in three lines and with no measure theory in sight.

The finite case is the instance where the operator is a matrix.
`driftCLM` packages §7's coupling sum as a continuous linear map,
`sigmaOfKernel_eq_norm_sq` identifies σ with `c‖A K + ω‖²`, and
`hasFDerivAt_sigmaOfKernel_of_operator` re-derives §7's gradient from the
abstract lemma — so the closed-form computation in `hasFDerivAt_sigmaOfKernel`
is a *convenience*, not the content.

**What this leaves.** Extending §7 to a continuum needs exactly one thing: the
continuum drift map `K ↦ (x ↦ ∫ K(x,y) sin(θ_y − θ_x) dy)` as a bounded operator
`L²(μ⊗μ) → L²(μ)`. That is a Cauchy–Schwarz estimate — the kernel of the
integral is bounded by `1`, so on a finite measure space the operator norm is at
most `μ(M)^{1/2}` — and not a theorem about differentiating anything.

**§9 builds it** (`kernelCLM`, `continuumDriftCLM`). One step this diagnosis did
*not* see is also needed and is in §9: the descent theorems want the derivative as
a gradient *vector*, not as an arbitrary bounded functional, which needs the
adjoint. So the corrected scope recorded here was right that the obstruction was
not analytic, and incomplete about what "given the operator, the derivative
follows" actually reaches.
-/

/-- **A quadratic functional of an affine image is Fréchet differentiable.**
`c‖A K + w‖²` has derivative `c · 2⟪A K + w, A ·⟫`, for any continuous linear
`A` between real inner-product spaces.

This is the whole analytic content of §7. Nothing here is finite-dimensional and
nothing is an integral: given the operator, the derivative follows. -/
theorem hasFDerivAt_quadratic_of_affine {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : H →L[ℝ] E) (w : E) (c : ℝ) (K : H) :
    HasFDerivAt (fun K' : H => c * ‖A K' + w‖ ^ 2)
      (c • (2 • (innerSL ℝ (A K + w)).comp A)) K :=
  (((A.hasFDerivAt).add_const w).norm_sq).const_mul c

section OperatorForm

variable {M : Type*} [Fintype M] [MeasureSpace M] [TopologicalSpace M] [DecidableEq M]

private lemma inner_euclid' {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℝ ι) :
    (inner ℝ u v : ℝ) = ∑ i, u i * v i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [RCLike.inner_apply, mul_comm]

/-- §7's coupling sum, as a linear map of the kernel. This is the operator whose
continuum analogue is all that O10 still needs. -/
noncomputable def driftLin (theta : M → ℝ) : CouplingSpace M →ₗ[ℝ] EuclideanSpace ℝ M where
  toFun K := WithLp.toLp 2 (fun x => ∑ y : M, K (x, y) * Real.sin (theta y - theta x))
  map_add' K L := by ext x; simp [Finset.sum_add_distrib, add_mul]
  map_smul' c K := by ext x; simp [Finset.mul_sum, mul_assoc]

/-- Continuity is free in finite dimension; in the continuum it is the
Cauchy–Schwarz estimate described in the section header. -/
noncomputable def driftCLM (theta : M → ℝ) : CouplingSpace M →L[ℝ] EuclideanSpace ℝ M :=
  LinearMap.toContinuousLinearMap (driftLin theta)

/-- The natural frequencies, as the affine offset. -/
noncomputable def omegaVec (sys : StochasticNeuralField M) : EuclideanSpace ℝ M :=
  WithLp.toLp 2 sys.omega

omit [DecidableEq M] in
lemma driftCLM_apply (sys : StochasticNeuralField M) (theta : M → ℝ)
    (K : CouplingSpace M) (x : M) :
    (driftCLM theta K + omegaVec sys) x = drift sys theta K x := by
  show (∑ y : M, K (x, y) * Real.sin (theta y - theta x)) + sys.omega x = _
  rw [drift]; ring

omit [DecidableEq M] in
/-- **σ is `c‖A K + ω‖²`.** The identification that makes the abstract lemma
apply. -/
lemma sigmaOfKernel_eq_norm_sq (sys : StochasticNeuralField M) (theta : M → ℝ)
    (K : CouplingSpace M) :
    sigmaOfKernel sys theta K = (1 / sys.D) * ‖driftCLM theta K + omegaVec sys‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_euclid']
  rw [sigmaOfKernel, ← Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  rw [driftCLM_apply]; ring

omit [DecidableEq M] in
/-- **§7's gradient, re-derived from the abstract lemma.** The point is not a new
result — `hasFDerivAt_sigmaOfKernel` already proves this, in the closed form the
manuscript quotes — but that the closed form is inessential. Everything §7 needs
follows from the operator, so the continuum case is blocked only on producing
one. -/
theorem hasFDerivAt_sigmaOfKernel_of_operator (sys : StochasticNeuralField M)
    (theta : M → ℝ) (K : CouplingSpace M) :
    HasFDerivAt (sigmaOfKernel sys theta)
      ((1 / sys.D) • (2 • (innerSL ℝ (driftCLM theta K + omegaVec sys)).comp (driftCLM theta)))
      K := by
  have hfun : sigmaOfKernel sys theta
      = fun K' => (1 / sys.D) * ‖driftCLM theta K' + omegaVec sys‖ ^ 2 :=
    funext fun K' => sigmaOfKernel_eq_norm_sq sys theta K'
  rw [hfun]
  exact hasFDerivAt_quadratic_of_affine _ _ _ _

end OperatorForm

/-!
## 9. The continuum operator, and what it closes

§8 narrowed the continuum case to one missing object: the drift map
`K ↦ (x ↦ ∫ K(x,y) sin(θ_y − θ_x) dy)` as a bounded operator
`L²(μ⊗μ) → L²(μ)`. Open item **O10** recorded that as `Lp` bookkeeping rather
than analysis. This section builds it and takes the consequences.

The estimate is the one §8 predicted and nothing more. For a kernel factor `s`
bounded by `1` on a finite measure space,

  `|∫ K(x,y) s(x,y) dy| ≤ ∫ |K(x,y)| dy ≤ μ(α)^{1/2} (∫ |K(x,y)|² dy)^{1/2}`

by Cauchy–Schwarz in the second variable, and squaring and integrating in `x`
gives `‖T K‖_{L²(μ)} ≤ μ(α)^{1/2} ‖K‖_{L²(μ⊗μ)}` by Tonelli. `kernelCLM` is the
resulting operator; `continuumDriftCLM` is the instance with
`s(x,y) = sin(θ_y − θ_x)`.

**What the operator buys, and why it is more than §8 claimed.** §8 said that
given the operator, differentiability of σ follows from
`hasFDerivAt_quadratic_of_affine`. That is true but not sufficient to reach the
descent theorems, because `is_coupling_gradient_flow` wants the derivative in
the form `innerSL ℝ (grad K)` — a gradient *vector*, not an arbitrary functional.
Producing one needs the adjoint, which exists because `L²` is complete.
`hasFDerivAt_quadratic_grad` is that step, stated for an arbitrary bounded
operator between real Hilbert spaces, and it makes the finite and continuum
cases the same theorem. The continuum gradient is

  `grad σ (K) = (2/D) · A* (A K + ω)`,

and `structural_resonance_decreases_sigmaContinuum` is §7's descent result with
no finiteness hypothesis anywhere in it.

**What this does not establish.** The functional differentiated here is σ as a
function of the *coupling kernel at a fixed phase field*, exactly as in §7; this
is plasticity at frozen phases, not joint `(θ, K)` dynamics, and the continuum
version inherits that restriction unchanged. Nothing here connects the
continuum field to the finite Kuramoto system — that is the propagation-of-chaos
gap, which is untouched. And `σ` is identified with the integral
`entropy_production_rate` computes (`sigmaContinuum_eq_integral`), not with a
measured quantity.
-/

section ContinuumOperator

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- **Cauchy–Schwarz against the constant function.** `(∫|f|)² ≤ μ(α) ∫f²`,
proved from `0 ≤ ∫ (μ(α)|f| − ∫|f|)²` rather than by invoking Hölder, so the
only inputs are integrability of `f` and of `f²`. -/
private lemma sq_integral_abs_le {f : α → ℝ} (h1 : Integrable f μ)
    (h2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, |f x| ∂μ) ^ 2 ≤ (μ Set.univ).toReal * ∫ x, f x ^ 2 ∂μ := by
  by_cases hμ : μ = 0
  · subst hμ; simp
  have hVpos : 0 < (μ Set.univ).toReal :=
    ENNReal.toReal_pos (fun h => hμ (Measure.measure_univ_eq_zero.mp h)) (measure_ne_top μ _)
  set V : ℝ := (μ Set.univ).toReal with hVdef
  set A : ℝ := ∫ x, |f x| ∂μ with hAdef
  set B : ℝ := ∫ x, f x ^ 2 ∂μ with hBdef
  have habs : Integrable (fun x => |f x|) μ := h1.abs
  have hint1 : Integrable (fun x => V ^ 2 * f x ^ 2) μ := h2.const_mul _
  have hint2 : Integrable (fun x => (2 * V * A) * |f x|) μ := habs.const_mul _
  have hfun : (fun x => (V * |f x| - A) ^ 2)
      = fun x => (V ^ 2 * f x ^ 2 - (2 * V * A) * |f x|) + A ^ 2 := by
    funext x
    rw [show (V * |f x| - A) ^ 2 = V ^ 2 * |f x| ^ 2 - (2 * V * A) * |f x| + A ^ 2 by ring,
      sq_abs]
  have e1 : ∫ x, ((V ^ 2 * f x ^ 2 - (2 * V * A) * |f x|) + A ^ 2) ∂μ
      = (∫ x, (V ^ 2 * f x ^ 2 - (2 * V * A) * |f x|) ∂μ) + ∫ _x : α, A ^ 2 ∂μ :=
    integral_add (hint1.sub hint2) (integrable_const _)
  have e2 : ∫ x, (V ^ 2 * f x ^ 2 - (2 * V * A) * |f x|) ∂μ
      = (∫ x, V ^ 2 * f x ^ 2 ∂μ) - ∫ x, (2 * V * A) * |f x| ∂μ :=
    integral_sub hint1 hint2
  have hnn : (0:ℝ) ≤ ∫ x, (V * |f x| - A) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  rw [hfun, e1, e2, integral_const_mul, integral_const_mul, integral_const, smul_eq_mul,
    measureReal_def, ← hVdef] at hnn
  nlinarith [hnn, hVpos]

/-- One row of an integral operator: the kernel `K` contracted against a bounded
factor `s` in the second variable. -/
noncomputable def kernelApply (μ : Measure α) (s K : α × α → ℝ) (x : α) : ℝ :=
  ∫ y, K (x, y) * s (x, y) ∂μ

variable {s : α × α → ℝ}

omit [IsFiniteMeasure μ] in
private lemma slice_mul_integrable (hs : StronglyMeasurable s) (hs1 : ∀ p, |s p| ≤ 1)
    {g : α × α → ℝ} {x : α} (hx : Integrable (fun y => g (x, y)) μ) :
    Integrable (fun y => g (x, y) * s (x, y)) μ := by
  have hsx : StronglyMeasurable (fun y => s (x, y)) :=
    hs.comp_measurable measurable_prodMk_left
  refine Integrable.mono' hx.abs (hx.aestronglyMeasurable.mul hsx.aestronglyMeasurable) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [abs_nonneg (g (x, y)), hs1 (x, y), abs_nonneg (s (x, y))]

private lemma kernelApply_sq_le_ae (hs : StronglyMeasurable s) (hs1 : ∀ p, |s p| ≤ 1)
    {K : α × α → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, kernelApply μ s K x ^ 2 ≤ (μ Set.univ).toReal * ∫ y, K (x, y) ^ 2 ∂μ := by
  have hKint : Integrable K (μ.prod μ) := hK.integrable one_le_two
  have hKsq : Integrable (fun p => K p ^ 2) (μ.prod μ) := hK.integrable_sq
  filter_upwards [hKint.prod_right_ae, hKsq.prod_right_ae] with x hx1 hx2
  have hmul : Integrable (fun y => K (x, y) * s (x, y)) μ :=
    slice_mul_integrable hs hs1 hx1
  have habs : |kernelApply μ s K x| ≤ ∫ y, |K (x, y)| ∂μ := by
    calc |∫ y, K (x, y) * s (x, y) ∂μ| ≤ ∫ y, |K (x, y) * s (x, y)| ∂μ := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (μ := μ) (f := fun y => K (x, y) * s (x, y))
      _ ≤ ∫ y, |K (x, y)| ∂μ := by
          refine integral_mono hmul.abs hx1.abs fun y => ?_
          rw [abs_mul]
          nlinarith [abs_nonneg (K (x, y)), hs1 (x, y), abs_nonneg (s (x, y))]
  calc kernelApply μ s K x ^ 2 = |kernelApply μ s K x| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ y, |K (x, y)| ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ (μ Set.univ).toReal * ∫ y, K (x, y) ^ 2 ∂μ := sq_integral_abs_le hx1 hx2

/-- The contracted kernel is in `L²(μ)` whenever the kernel is in `L²(μ⊗μ)`. -/
theorem memLp_kernelApply (hs : StronglyMeasurable s) (hs1 : ∀ p, |s p| ≤ 1)
    {K : α × α → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    MemLp (kernelApply μ s K) 2 μ := by
  have hmeas : AEStronglyMeasurable (kernelApply μ s K) μ :=
    (hK.1.mul hs.aestronglyMeasurable).integral_prod_right'
  refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
  refine Integrable.mono' ((hK.integrable_sq.integral_prod_left).const_mul
    (μ Set.univ).toReal) (hmeas.pow 2) ?_
  filter_upwards [kernelApply_sq_le_ae hs hs1 hK] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hx

/-- **The Cauchy–Schwarz estimate of §8, proved.**
`‖T K‖²_{L²(μ)} ≤ μ(α) · ‖K‖²_{L²(μ⊗μ)}`. -/
theorem integral_sq_kernelApply_le (hs : StronglyMeasurable s) (hs1 : ∀ p, |s p| ≤ 1)
    {K : α × α → ℝ} (hK : MemLp K 2 (μ.prod μ)) :
    ∫ x, kernelApply μ s K x ^ 2 ∂μ
      ≤ (μ Set.univ).toReal * ∫ p, K p ^ 2 ∂(μ.prod μ) := by
  have hKsq : Integrable (fun p => K p ^ 2) (μ.prod μ) := hK.integrable_sq
  calc ∫ x, kernelApply μ s K x ^ 2 ∂μ
      ≤ ∫ x, (μ Set.univ).toReal * ∫ y, K (x, y) ^ 2 ∂μ ∂μ :=
        integral_mono_ae (memLp_kernelApply hs hs1 hK).integrable_sq
          ((hKsq.integral_prod_left).const_mul _) (kernelApply_sq_le_ae hs hs1 hK)
    _ = (μ Set.univ).toReal * ∫ p, K p ^ 2 ∂(μ.prod μ) := by
        rw [integral_const_mul, integral_integral hKsq]

omit [IsFiniteMeasure μ] in
/-- `‖g‖² = ∫ g²` in a real `L²`. -/
lemma Lp2_norm_sq (g : Lp ℝ 2 μ) : ‖g‖ ^ 2 = ∫ a, (g a) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [sq]

/-- The integral operator, as a linear map on `L²`. -/
noncomputable def kernelLin (μ : Measure α) [IsFiniteMeasure μ] {s : α × α → ℝ}
    (hs : StronglyMeasurable s) (hs1 : ∀ p, |s p| ≤ 1) :
    Lp ℝ 2 (μ.prod μ) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun K := (memLp_kernelApply hs hs1 (Lp.memLp K)).toLp _
  map_add' K L := by
    refine Eq.trans (MemLp.toLp_congr _ ((memLp_kernelApply hs hs1 (Lp.memLp K)).add
      (memLp_kernelApply hs hs1 (Lp.memLp L))) ?_) (MemLp.toLp_add _ _)
    have hslice := Measure.ae_ae_of_ae_prod (Lp.coeFn_add K L)
    have hKi := ((Lp.memLp K).integrable one_le_two).prod_right_ae
    have hLi := ((Lp.memLp L).integrable one_le_two).prod_right_ae
    filter_upwards [hslice, hKi, hLi] with x hx hKx hLx
    show ∫ y, (K + L : Lp ℝ 2 (μ.prod μ)) (x, y) * s (x, y) ∂μ
        = kernelApply μ s (⇑K) x + kernelApply μ s (⇑L) x
    rw [show (∫ y, (K + L : Lp ℝ 2 (μ.prod μ)) (x, y) * s (x, y) ∂μ)
        = ∫ y, (K (x, y) * s (x, y) + L (x, y) * s (x, y)) ∂μ from
      integral_congr_ae (by
        filter_upwards [hx] with y hy
        rw [hy]
        show (⇑K (x, y) + ⇑L (x, y)) * s (x, y) = _
        ring),
      integral_add (slice_mul_integrable hs hs1 hKx) (slice_mul_integrable hs hs1 hLx)]
    rfl
  map_smul' c K := by
    refine Eq.trans (MemLp.toLp_congr _ ((memLp_kernelApply hs hs1 (Lp.memLp K)).const_smul c) ?_)
      (MemLp.toLp_const_smul c _)
    have hslice := Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c K)
    have hKi := ((Lp.memLp K).integrable one_le_two).prod_right_ae
    filter_upwards [hslice, hKi] with x hx hKx
    show ∫ y, (c • K : Lp ℝ 2 (μ.prod μ)) (x, y) * s (x, y) ∂μ
        = (c • kernelApply μ s (⇑K)) x
    rw [show (∫ y, (c • K : Lp ℝ 2 (μ.prod μ)) (x, y) * s (x, y) ∂μ)
        = ∫ y, c * (K (x, y) * s (x, y)) ∂μ from
      integral_congr_ae (by
        filter_upwards [hx] with y hy
        rw [hy]
        show (c • ⇑K) (x, y) * s (x, y) = _
        show c * ⇑K (x, y) * s (x, y) = _
        ring),
      integral_const_mul]
    rfl

/-- **The bounded operator open item O10 asked for**, with operator norm at most
`μ(α)^{1/2}`. Nothing about it is specific to the Kuramoto coupling: the only
hypothesis on the contracted factor is that it is bounded by `1`. -/
noncomputable def kernelCLM (μ : Measure α) [IsFiniteMeasure μ] {s : α × α → ℝ}
    (hs : StronglyMeasurable s) (hs1 : ∀ p, |s p| ≤ 1) :
    Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous (kernelLin μ hs hs1) (Real.sqrt (μ Set.univ).toReal) (by
    intro K
    have hV : (0:ℝ) ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
    have hcoe : ∫ x, ((kernelLin μ hs hs1 K) x) ^ 2 ∂μ
        = ∫ x, kernelApply μ s (⇑K) x ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      have hae : ⇑(kernelLin μ hs hs1 K) =ᵐ[μ] kernelApply μ s (⇑K) :=
        MemLp.coeFn_toLp (memLp_kernelApply hs hs1 (Lp.memLp K))
      filter_upwards [hae] with x hx
      rw [hx]
    have hsq : ‖kernelLin μ hs hs1 K‖ ^ 2 ≤ (Real.sqrt (μ Set.univ).toReal * ‖K‖) ^ 2 := by
      rw [Lp2_norm_sq, hcoe, mul_pow, Real.sq_sqrt hV, Lp2_norm_sq]
      exact integral_sq_kernelApply_le hs hs1 (Lp.memLp K)
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h1)

/-- The operator computes the integral it is supposed to, almost everywhere. -/
lemma kernelCLM_apply (hs : StronglyMeasurable s) (hs1 : ∀ p, |s p| ≤ 1)
    (K : Lp ℝ 2 (μ.prod μ)) :
    ⇑(kernelCLM μ hs hs1 K) =ᵐ[μ] fun x => ∫ y, K (x, y) * s (x, y) ∂μ :=
  MemLp.coeFn_toLp (memLp_kernelApply hs hs1 (Lp.memLp K))

/-- The operator-norm bound, stated on the operator rather than pointwise. -/
lemma opNorm_kernelCLM_le (hs : StronglyMeasurable s) (hs1 : ∀ p, |s p| ≤ 1) :
    ‖kernelCLM μ hs hs1‖ ≤ Real.sqrt (μ Set.univ).toReal :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

end ContinuumOperator

section ContinuumDrift

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {theta : α → ℝ}

/-- The Kuramoto coupling factor, as a function on the product. -/
noncomputable def sinKernel (theta : α → ℝ) : α × α → ℝ :=
  fun p => Real.sin (theta p.2 - theta p.1)

lemma stronglyMeasurable_sinKernel (h : Measurable theta) :
    StronglyMeasurable (sinKernel theta) :=
  (Real.continuous_sin.measurable.comp
    ((h.comp measurable_snd).sub (h.comp measurable_fst))).stronglyMeasurable

omit [MeasurableSpace α] in
lemma abs_sinKernel_le_one (theta : α → ℝ) (p : α × α) : |sinKernel theta p| ≤ 1 :=
  abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- **The continuum drift map.** `K ↦ (x ↦ ∫ K(x,y) sin(θ_y − θ_x) dy)`, bounded
from `L²(μ⊗μ)` to `L²(μ)`. This is the object §8 said the continuum case was
blocked on. -/
noncomputable def continuumDriftCLM (μ : Measure α) [IsFiniteMeasure μ]
    {theta : α → ℝ} (h : Measurable theta) :
    Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 μ :=
  kernelCLM μ (stronglyMeasurable_sinKernel h) (abs_sinKernel_le_one theta)

lemma continuumDriftCLM_apply (h : Measurable theta) (K : Lp ℝ 2 (μ.prod μ)) :
    ⇑(continuumDriftCLM μ h K)
      =ᵐ[μ] fun x => ∫ y, K (x, y) * Real.sin (theta y - theta x) ∂μ :=
  kernelCLM_apply _ _ K

end ContinuumDrift

section QuadraticGradient

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Precomposition with `A` is the same as taking the inner product against
`A* v`. This is the only place the adjoint is used, and it is what turns §8's
derivative into a gradient vector. -/
lemma innerSL_comp_eq_adjoint (A : H →L[ℝ] F) (v : F) :
    (innerSL ℝ v).comp A = innerSL ℝ ((ContinuousLinearMap.adjoint A) v) := by
  ext h
  simp [ContinuousLinearMap.adjoint_inner_left]

/-- **§8's lemma, with the derivative as a gradient.** `c‖A K + w‖²` has
gradient `2c · A*(A K + w)`.

`hasFDerivAt_quadratic_of_affine` gives the derivative as a functional; the
descent theorems of §2 want a vector, because `is_coupling_gradient_flow` is
stated as `HasFDerivAt S (innerSL ℝ (gradS K)) K`. Completeness is what supplies
one, and `L²` is complete, so the finite and continuum cases are now literally
the same theorem. -/
theorem hasFDerivAt_quadratic_grad (A : H →L[ℝ] F) (w : F) (c : ℝ) (K : H) :
    HasFDerivAt (fun K' : H => c * ‖A K' + w‖ ^ 2)
      (innerSL ℝ ((2 * c) • (ContinuousLinearMap.adjoint A) (A K + w))) K := by
  have h := hasFDerivAt_quadratic_of_affine A w c K
  convert h using 1
  ext u
  simp [innerSL_comp_eq_adjoint]
  ring

end QuadraticGradient

section ContinuumSigma

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {theta : α → ℝ}

/-- **Entropy production in the continuum, as a functional of the coupling
kernel at a fixed phase field.** The continuum analogue of `sigmaOfKernel`;
`sigmaContinuum_eq_integral` identifies it with the integral
`entropy_production_rate` computes. -/
noncomputable def sigmaContinuum (μ : Measure α) [IsFiniteMeasure μ]
    {theta : α → ℝ} (h : Measurable theta) (D : ℝ) (omega : Lp ℝ 2 μ)
    (K : Lp ℝ 2 (μ.prod μ)) : ℝ :=
  (1 / D) * ‖continuumDriftCLM μ h K + omega‖ ^ 2

/-- The gradient of `sigmaContinuum`, through the adjoint of the drift map. -/
noncomputable def gradSigmaContinuum (μ : Measure α) [IsFiniteMeasure μ]
    {theta : α → ℝ} (h : Measurable theta) (D : ℝ) (omega : Lp ℝ 2 μ)
    (K : Lp ℝ 2 (μ.prod μ)) : Lp ℝ 2 (μ.prod μ) :=
  (2 * (1 / D)) •
    (ContinuousLinearMap.adjoint (continuumDriftCLM μ h)) (continuumDriftCLM μ h K + omega)

/-- **σ is Fréchet differentiable in the coupling kernel on a continuum**, with
gradient `gradSigmaContinuum`. The continuum analogue of
`hasFDerivAt_sigmaOfKernel`, and it needs no closed form: the operator plus
`hasFDerivAt_quadratic_grad` is the whole proof. -/
theorem hasFDerivAt_sigmaContinuum (h : Measurable theta) (D : ℝ) (omega : Lp ℝ 2 μ)
    (K : Lp ℝ 2 (μ.prod μ)) :
    HasFDerivAt (sigmaContinuum μ h D omega)
      (innerSL ℝ (gradSigmaContinuum μ h D omega K)) K :=
  hasFDerivAt_quadratic_grad (continuumDriftCLM μ h) omega (1 / D) K

/-- **σ is what `entropy_production_rate` integrates.** With `sys.omega := ⇑ω`,
`sys.K := Function.curry ⇑K` and `sys.D := D`, the right-hand side is literally
the body of `entropy_production_rate`. Stated as an integral rather than by
building a `StochasticNeuralField`, because that structure carries a topology
and an `Omega_avg` that play no part here. -/
theorem sigmaContinuum_eq_integral (h : Measurable theta) (D : ℝ) (omega : Lp ℝ 2 μ)
    (K : Lp ℝ 2 (μ.prod μ)) :
    sigmaContinuum μ h D omega K
      = ∫ x, (1 / D) * (omega x + ∫ y, K (x, y) * Real.sin (theta y - theta x) ∂μ) ^ 2 ∂μ := by
  rw [sigmaContinuum, Lp2_norm_sq, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (continuumDriftCLM μ h K) omega,
    continuumDriftCLM_apply h K] with x hx hdrift
  rw [hx]
  show (1 / D) * (⇑(continuumDriftCLM μ h K) x + omega x) ^ 2 = _
  rw [hdrift, add_comm]

/-- Non-negativity, for a positive diffusion constant. -/
theorem sigmaContinuum_nonneg (h : Measurable theta) {D : ℝ} (hD : 0 < D)
    (omega : Lp ℝ 2 μ) (K : Lp ℝ 2 (μ.prod μ)) :
    0 ≤ sigmaContinuum μ h D omega K :=
  mul_nonneg (by positivity) (sq_nonneg _)

/-- **The continuum gradient flow decreases σ.** §7's
`gradient_flow_decreases_entropy_production` with the finiteness hypothesis
removed. -/
theorem gradient_flow_decreases_sigmaContinuum (h : Measurable theta) (D : ℝ)
    (omega : Lp ℝ 2 μ) (K_t : ℝ → Lp ℝ 2 (μ.prod μ))
    (hflow : ∀ t, HasDerivAt K_t (- gradSigmaContinuum μ h D omega (K_t t)) t) :
    Antitone (fun t => sigmaContinuum μ h D omega (K_t t)) :=
  gradient_flow_implies_entropy_decrease K_t (sigmaContinuum μ h D omega)
    (gradSigmaContinuum μ h D omega)
    ⟨hasFDerivAt_sigmaContinuum h D omega, hflow⟩

/-- **The continuum structural-resonance result.** The statement
`structural_resonance_decreases_entropy_production` makes on a finite substrate,
now with no finiteness anywhere in it — only that the substrate carries a finite
measure and the phase field is measurable. -/
theorem structural_resonance_decreases_sigmaContinuum (h : Measurable theta) (D : ℝ)
    (omega : Lp ℝ 2 μ) (K_t : ℝ → Lp ℝ 2 (μ.prod μ)) {c : ℝ} (hc : 0 < c)
    (hflow : ∀ t, HasDerivAt K_t (- c • gradSigmaContinuum μ h D omega (K_t t)) t) :
    Antitone (fun t => sigmaContinuum μ h D omega (K_t t)) :=
  structural_resonance_implies_gradient_descent K_t (sigmaContinuum μ h D omega)
    (gradSigmaContinuum μ h D omega) c
    ⟨hasFDerivAt_sigmaContinuum h D omega, hflow, hc⟩

end ContinuumSigma

end PhysicsOfConsciousness
