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
most `μ(M)^{1/2}` — and not a theorem about differentiating anything. We have not
built it, because it needs the `Lp` API and the construction of a continuous
linear map between two `Lp` spaces, which is bookkeeping we have not done. But
the item is "construct one bounded operator", not "differentiate under the
integral sign", and the difference is worth recording: the second is an analytic
obstruction and the first is not.
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

end PhysicsOfConsciousness
