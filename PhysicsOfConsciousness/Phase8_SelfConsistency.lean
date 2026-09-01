import Mathlib
import PhysicsOfConsciousness.Phase8_ContinuousField

/-!
# Phase 8 — The mean-field self-consistency equation

`Phase8_ContinuousField.lean` defines `critical_coupling D = 2 * D` and the
predicate `exhibits_phase_transition`, but proves nothing about the *value*
`2 * D`: it is a stipulation, justified in the literature by an argument this
file begins to formalize.

## The argument being formalized

For the noisy mean-field Kuramoto model with identical natural frequencies, the
stationary density of the Fokker–Planck equation at order parameter `r` is the
von Mises density `ρ(θ) ∝ exp((K r / D) cos θ)`. Self-consistency of the order
parameter — `r` must equal the mean of `cos θ` under the density it induces —
gives the fixed-point equation

    r = R(K, r) := (∫_{-π}^{π} cos θ · e^{(Kr/D) cos θ} dθ)
                 / (∫_{-π}^{π}       e^{(Kr/D) cos θ} dθ)

whose right-hand side is the Bessel ratio `I₁(Kr/D) / I₀(Kr/D)`. Mathlib has no
`Real.besselI`, so `besselRatio` below is that ratio *as a ratio of integrals*,
which is all the argument needs.

## What is proved here

* `vonMisesM_eq_mul_vonMisesS` — the integration-by-parts identity
  `∫ cos θ · e^{a cos θ} = a ∫ sin²θ · e^{a cos θ}`, from which everything else
  follows. Taking `u = sin`, `v = -e^{a cos}` the boundary term vanishes by
  periodicity, so the identity is exact with no remainder.
* `vonMisesC2_nonneg` — `I₂(a) ≥ 0`, proved elementarily by folding `[-π, π]`
  onto `[0, π/4]`; see §5. Equivalently (`vonMisesS_le_half_vonMisesZ`) the mean
  of `sin²` under the von Mises weight is at most `1/2`.
* `besselRatio_le_half_self` — `R(a) ≤ a/2` for `a ≥ 0`. The factor `1/2` is
  exactly what puts the threshold at `2D` rather than `D`.
* `subcritical_fixed_point_eq_zero'` — **for `K < critical_coupling D = 2D`, the
  only non-negative solution of `r = R(K, r)` is `r = 0`.** This is the first
  theorem in the development in which `critical_coupling` occurs at all.
* `selfConsistency_zero` — `r = 0` *is* a solution, for every `K` and `D`. The
  theorem above is therefore a uniqueness statement about a fixed point that
  exists, not a vacuous one.
* `supercritical_fixed_point_exists` — **for `K > critical_coupling D = 2D`,
  there is an `r` with `0 < r ≤ 1` solving `r = R(K, r)`.** The converse half,
  proved in §6 from continuity of the mean `E_a[sin²θ]` at `a = 0` together with
  the intermediate value theorem; no series expansion is involved.
* `fixed_point_eq_zero_of_le_critical` — **for `K ≤ 2D`, threshold included, the
  only non-negative solution is `r = 0`.** The strict form
  `besselRatio_lt_half_self` (`R(a) < a/2` for `a > 0`, from `I₂(a) > 0`) is what
  settles the threshold case that the non-strict bound could not.
* `coherent_iff_sRatio_eq` — for `r ≠ 0`, solving `r = R(K, r)` is the same as
  `E(K r / D) = D/K`. The coherent branch is a level set of the single function
  `E(a) = E_a[sin²θ]`, which is what makes the remaining questions precise.
* `coherent_branch_continuous_at_threshold` — **no jump.** For every `ε > 0`
  there is a `δ > 0` such that on `(2D, 2D + δ)` *every* coherent solution has
  `r < ε`. The branch emerges from zero, which is what "supercritical
  bifurcation" means technically. Quantified over all solutions, so it does not
  presuppose uniqueness.
* `vonMisesSRatio_strictAntiOn` — **`E` is strictly decreasing on `[0, ∞)`**,
  hence injective, hence the coherent branch is a single point: §7. The proof
  folds `[-π, π]` onto `[0, π/2]` as in §5 and then runs a one-dimensional
  crossing argument, so no derivative of `E` and no double integral appears.
* `besselRatio_strictMono` — **`R` is strictly increasing on `ℝ`**, the same
  crossing argument with no fold needed. This is the monotonicity of `R` that
  this header used to list as unproved.
* `supercritical_fixed_point_existsUnique`, `supercritical_solution_set` — above
  threshold there is **exactly one** coherent solution, so the non-negative
  solution set is `{0}` at or below `2D` and `{0, r}` above it.
* `coherent_branch_strictMono` — **the coherent order parameter increases
  strictly with the coupling.** Both halves of §7 are needed: `E` decreasing
  moves the concentration, `R` increasing moves the order parameter with it.
* `critical_coupling_is_threshold` — the three parts packaged: at or below `2D`
  the incoherent state is the only solution, above it a coherent one exists, and
  the branch emerges continuously. `critical_coupling_is_threshold_unique`
  sharpens the middle part to `∃!`.
* `exhibits_phase_transition_coherent` — a substrate satisfying
  `exhibits_phase_transition` of `Phase8_ContinuousField.lean` admits a positive
  stationary order parameter. This is what stops `critical_coupling` from being
  an inert stipulation: exceeding it now *implies* something.
* `circularOrderParameter_vonMises` and `fixedPoint_iff_selfReproducing` — §8.
  `selfConsistency` is *named* for a self-consistency condition, but as a
  definition it is just `besselRatio (K * r / D)` and could be any function of
  `r`. These identify it: `vonMisesDensity` is the actual probability density,
  `circularOrderParameter` is the continuum analogue of `Phase4`'s
  `order_parameter_complex`, and a fixed point of `selfConsistency` is exactly a
  density whose own order parameter is the `r` that generated it.

`subcritical_fixed_point_eq_zero` and `besselRatio_le_self` are the crude
versions of the last two, obtained from the pointwise bound `sin² ≤ 1` alone.
They are kept because they isolate where the factor of two comes from: the
entire difference between a threshold at `D` and the physical one at `2D` is the
sharpening of `sin² ≤ 1` to its *mean* value under the von Mises weight.

## What is NOT proved here

**Dynamical selection.** `supercritical_fixed_point_existsUnique` says the
coherent solution of the *equation* is unique; it does not say a trajectory
converges to it, or that it is stable. Nothing in this file mentions a
trajectory at all, so "the selected branch" is not a statement this file can
make — that is the dynamics, and it lives in `Phase4_RotatingFrame.lean`.

*Three gaps this section used to record are now closed.* `K = 2D` is covered
(`fixed_point_eq_zero_of_le_critical`, and it falls on the incoherent side), a
discontinuous jump at threshold is excluded
(`coherent_branch_continuous_at_threshold`) without needing uniqueness, and
uniqueness itself is §7. The route recorded here as the one uniqueness would
need — differentiate the exponential family, then show
`Cov_a(cos²θ, cos θ) > 0` — is *not* the route taken, and it was the harder one:
that covariance is not sign-definite pointwise. §7 folds first, which is the
same symmetrisation performed once at the start, and then compares at a single
crossing point rather than integrating over a square.

**Derivatives and rates.** Nothing in *this* file differentiates anything: `E`
and `R` are shown strictly monotone, not differentiable, and no rate is proved
here. The threshold theorems run on the bounds of §5 and §6, which are proved
independently of §7.

The second-order behaviour of `E` is available downstream, in
`Phase8_CriticalExponent`, which differentiates the von Mises moments under the
integral and proves `E(a) = 1/2 - a²/16 + o(a²)`
(`vonMisesSRatio_second_order`) and, from it, the mean-field critical exponent
`β = 1/2`. The remainder there is `o(a²)` rather than `O(a⁴)`; the stronger
form would need a fourth derivative and no result requires it. `R(a) → 1` and
concavity of `R` remain unformalized, and nothing needs them either.

**The ansatz.** Nothing here derives the von Mises stationary density from the
SDE `dθ = (ω + K·mean-field) dt + √(2D) dW`. That needs the Fokker–Planck
operator, existence and uniqueness of its stationary solution, and a spectral
stability argument, none of which Mathlib has. The density is an input to this
file, not an output of it.

**The dynamics.** §7 connects `selfConsistency` to the order parameter *of a
density*. It does not connect it to a *trajectory*: nothing here mentions
`is_continuous_kuramoto_trajectory` or `entropy_production_rate`, and
`circularOrderParameter` is not linked to `Phase4`'s `order_parameter_complex`
— the latter is the empirical average `(1/N) ∑ e^{iθⱼ}` over a finite system,
the former an integral against a density, and closing that gap is the mean-field
limit (propagation of chaos), not a lemma. Table 1 of the manuscript accordingly
reads "Theorem (partial)" for this row rather than "Theorem".
-/

open Real MeasureTheory intervalIntegral Set

namespace PhysicsOfConsciousness

/-! ## 1. The von Mises weight and its moments -/

/-- The unnormalized von Mises weight `e^{a cos θ}` at concentration `a`. -/
noncomputable def vonMisesWeight (a θ : ℝ) : ℝ := Real.exp (a * Real.cos θ)

/-- The partition function `Z(a) = ∫_{-π}^{π} e^{a cos θ} dθ`, i.e. `2π I₀(a)`. -/
noncomputable def vonMisesZ (a : ℝ) : ℝ := ∫ θ in (-π)..π, vonMisesWeight a θ

/-- The first moment `M(a) = ∫_{-π}^{π} cos θ · e^{a cos θ} dθ`, i.e. `2π I₁(a)`. -/
noncomputable def vonMisesM (a : ℝ) : ℝ := ∫ θ in (-π)..π, Real.cos θ * vonMisesWeight a θ

/-- The second quantity the identity produces:
`S(a) = ∫_{-π}^{π} sin²θ · e^{a cos θ} dθ`. -/
noncomputable def vonMisesS (a : ℝ) : ℝ := ∫ θ in (-π)..π, Real.sin θ ^ 2 * vonMisesWeight a θ

lemma continuous_vonMisesWeight (a : ℝ) : Continuous (vonMisesWeight a) := by
  unfold vonMisesWeight; fun_prop

lemma vonMisesWeight_pos (a θ : ℝ) : 0 < vonMisesWeight a θ := Real.exp_pos _

lemma intervalIntegrable_vonMisesWeight (a c d : ℝ) :
    IntervalIntegrable (vonMisesWeight a) volume c d :=
  (continuous_vonMisesWeight a).intervalIntegrable c d

lemma intervalIntegrable_cos_mul (a c d : ℝ) :
    IntervalIntegrable (fun θ => Real.cos θ * vonMisesWeight a θ) volume c d :=
  (Real.continuous_cos.mul (continuous_vonMisesWeight a)).intervalIntegrable c d

lemma intervalIntegrable_sin_sq_mul (a c d : ℝ) :
    IntervalIntegrable (fun θ => Real.sin θ ^ 2 * vonMisesWeight a θ) volume c d :=
  ((Real.continuous_sin.pow 2).mul (continuous_vonMisesWeight a)).intervalIntegrable c d

/-- The partition function is strictly positive: it integrates a positive
continuous function over a nondegenerate interval. -/
theorem vonMisesZ_pos (a : ℝ) : 0 < vonMisesZ a := by
  refine intervalIntegral_pos_of_pos_on (intervalIntegrable_vonMisesWeight a _ _)
    (fun θ _ => vonMisesWeight_pos a θ) ?_
  linarith [Real.pi_pos]

/-! ## 2. The integration-by-parts identity

`∫ cos θ · e^{a cos θ} dθ = a ∫ sin²θ · e^{a cos θ} dθ` on `[-π, π]`.

Take `u = sin` and `v = -e^{a cos}`, so that `u' = cos` and
`v' = a · sin · e^{a cos}`. The boundary term `u(π)v(π) - u(-π)v(-π)` vanishes
because `sin (±π) = 0`, which is why the identity has no remainder. -/

theorem vonMisesM_eq_mul_vonMisesS (a : ℝ) : vonMisesM a = a * vonMisesS a := by
  have hv : ∀ x : ℝ, HasDerivAt (fun θ => -Real.exp (a * Real.cos θ))
      (a * Real.sin x * Real.exp (a * Real.cos x)) x := by
    intro x
    have h1 : HasDerivAt (fun θ => a * Real.cos θ) (a * -Real.sin x) x :=
      (Real.hasDerivAt_cos x).const_mul a
    have h2 := h1.exp
    have hderiv : a * Real.sin x * Real.exp (a * Real.cos x)
        = -(Real.exp (a * Real.cos x) * (a * -Real.sin x)) := by ring
    rw [hderiv]
    exact h2.neg
  have key := intervalIntegral.integral_deriv_mul_eq_sub (a := -π) (b := π)
    (u := Real.sin) (u' := Real.cos)
    (v := fun θ => -Real.exp (a * Real.cos θ))
    (v' := fun θ => a * Real.sin θ * Real.exp (a * Real.cos θ))
    (fun x _ => Real.hasDerivAt_sin x) (fun x _ => hv x)
    (Real.continuous_cos.intervalIntegrable _ _)
    (((continuous_const.mul Real.continuous_sin).mul
      (continuous_vonMisesWeight a)).intervalIntegrable _ _)
  -- The boundary term vanishes: `sin (±π) = 0`.
  have hbdry : Real.sin π * -Real.exp (a * Real.cos π) -
      Real.sin (-π) * -Real.exp (a * Real.cos (-π)) = 0 := by
    simp
  rw [hbdry] at key
  -- Rearrange the integrand into `a · sin²·e^{a cos} - cos·e^{a cos}`.
  have hfun : (fun x => Real.cos x * -Real.exp (a * Real.cos x) +
        Real.sin x * (a * Real.sin x * Real.exp (a * Real.cos x)))
      = fun x => a * (Real.sin x ^ 2 * vonMisesWeight a x) -
        Real.cos x * vonMisesWeight a x := by
    funext x
    unfold vonMisesWeight
    ring
  rw [hfun, intervalIntegral.integral_sub
      (((intervalIntegrable_sin_sq_mul a _ _).const_mul a))
      (intervalIntegrable_cos_mul a _ _),
    intervalIntegral.integral_const_mul] at key
  unfold vonMisesM vonMisesS
  linarith [key]

/-! ## 3. The Bessel ratio, and the bound that costs a factor of two -/

/-- `I₁(a) / I₀(a)`, expressed as a ratio of integrals because Mathlib has no
modified Bessel functions. -/
noncomputable def besselRatio (a : ℝ) : ℝ := vonMisesM a / vonMisesZ a

@[simp] theorem besselRatio_zero : besselRatio 0 = 0 := by
  rw [besselRatio, vonMisesM_eq_mul_vonMisesS]
  simp

theorem vonMisesS_nonneg (a : ℝ) : 0 ≤ vonMisesS a := by
  refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => ?_)
  exact mul_nonneg (sq_nonneg _) (vonMisesWeight_pos a θ).le

/-- The crude bound: `sin²θ ≤ 1` pointwise. Sharpened to `Z/2` in §5. -/
theorem vonMisesS_le_vonMisesZ (a : ℝ) : vonMisesS a ≤ vonMisesZ a := by
  refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (intervalIntegrable_sin_sq_mul a _ _) (intervalIntegrable_vonMisesWeight a _ _)
    (fun θ _ => ?_)
  have h1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  nlinarith [vonMisesWeight_pos a θ]

/-- `R(a) ≤ a` for `a ≥ 0`. The physical threshold needs `R(a) ≤ a/2`; see §5. -/
theorem besselRatio_le_self {a : ℝ} (ha : 0 ≤ a) : besselRatio a ≤ a := by
  rw [besselRatio, vonMisesM_eq_mul_vonMisesS, div_le_iff₀ (vonMisesZ_pos a)]
  nlinarith [vonMisesS_le_vonMisesZ a, vonMisesS_nonneg a, vonMisesZ_pos a]

theorem besselRatio_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ besselRatio a := by
  rw [besselRatio, vonMisesM_eq_mul_vonMisesS]
  exact div_nonneg (mul_nonneg ha (vonMisesS_nonneg a)) (vonMisesZ_pos a).le

/-! ## 4. The self-consistency equation -/

/-- The self-consistency map `r ↦ R(K, r)` of the noisy mean-field Kuramoto
model: the mean of `cos θ` under the von Mises density of concentration
`K r / D`. A stationary order parameter is a fixed point of this map. -/
noncomputable def selfConsistency (K D r : ℝ) : ℝ := besselRatio (K * r / D)

/-- The incoherent state is always stationary. Without this the uniqueness
theorems below would be about an empty set of solutions. -/
@[simp] theorem selfConsistency_zero (K D : ℝ) : selfConsistency K D 0 = 0 := by
  simp [selfConsistency]

/-- **Subcritical uniqueness, crude threshold.** For `K < D` the incoherent
state is the only non-negative solution of the self-consistency equation.

This is a factor of two away from the physical threshold `K < 2 * D`; the whole
of the difference is the pointwise bound `sin² ≤ 1` used in
`vonMisesS_le_vonMisesZ`. See `subcritical_fixed_point_eq_zero'` for the sharp
form. -/
theorem subcritical_fixed_point_eq_zero {K D r : ℝ} (hD : 0 < D) (hK : 0 ≤ K)
    (hKD : K < D) (hr : 0 ≤ r) (hfix : r = selfConsistency K D r) : r = 0 := by
  rcases eq_or_lt_of_le hr with h | hpos
  · exact h.symm
  have ha : 0 ≤ K * r / D := by positivity
  have h1 : selfConsistency K D r ≤ K * r / D := besselRatio_le_self ha
  have h2 : K * r / D < r := by
    rw [div_lt_iff₀ hD]
    nlinarith
  linarith [hfix ▸ h1]

/-! ## 5. The sharp bound: `∫ sin²θ · e^{a cos θ} ≤ (1/2) ∫ e^{a cos θ}`

Equivalently `∫ cos 2θ · e^{a cos θ} dθ ≥ 0`, i.e. `I₂(a) ≥ 0`. The proof is
elementary — no Bessel series — and folds `[-π, π]` down to `[0, π/4]` in three
steps:

1. the integrand is even, so `∫_{-π}^{π} = 2∫_0^{π}`;
2. `θ ↦ π - θ` maps `[0, π/2]` onto `[π/2, π]` and sends the integrand to
   `cos 2θ · e^{-a cos θ}`, so `∫_0^{π}` becomes `∫_0^{π/2}` of
   `cos 2θ · (e^{a cos θ} + e^{-a cos θ})`;
3. `θ ↦ π/2 - θ` maps `[0, π/4]` onto `[π/4, π/2]` and flips the sign of
   `cos 2θ` while turning `cos θ` into `sin θ`, so `∫_0^{π/2}` becomes
   `∫_0^{π/4}` of `cos 2θ · (2 cosh(a cos θ) - 2 cosh(a sin θ))`.

On `(0, π/4)` both factors are non-negative: `cos 2θ ≥ 0`, and
`0 ≤ sin θ ≤ cos θ` with `cosh` increasing in `|·|`. That is the whole argument.
-/

/-- The second moment `C₂(a) = ∫_{-π}^{π} cos 2θ · e^{a cos θ} dθ`, i.e.
`2π I₂(a)`. -/
noncomputable def vonMisesC2 (a : ℝ) : ℝ :=
  ∫ θ in (-π)..π, Real.cos (2 * θ) * vonMisesWeight a θ

/-- The integrand after the first fold: `[0, π/2]` carries both halves of
`[0, π]`. -/
noncomputable def foldA (a x : ℝ) : ℝ :=
  Real.cos (2 * x) * (Real.exp (a * Real.cos x) + Real.exp (-(a * Real.cos x)))

/-- The integrand after the second fold: `[0, π/4]` carries all of `[-π, π]`,
and here positivity is visible pointwise. -/
noncomputable def foldB (a x : ℝ) : ℝ :=
  Real.cos (2 * x) *
    ((Real.exp (a * Real.cos x) + Real.exp (-(a * Real.cos x)))
      - (Real.exp (a * Real.sin x) + Real.exp (-(a * Real.sin x))))

lemma intervalIntegrable_cos_two_mul (a c d : ℝ) :
    IntervalIntegrable (fun θ => Real.cos (2 * θ) * vonMisesWeight a θ) volume c d := by
  refine Continuous.intervalIntegrable ?_ c d
  unfold vonMisesWeight; fun_prop

lemma intervalIntegrable_foldA (a c d : ℝ) :
    IntervalIntegrable (foldA a) volume c d := by
  refine Continuous.intervalIntegrable ?_ c d
  unfold foldA; fun_prop

lemma intervalIntegrable_foldB (a c d : ℝ) :
    IntervalIntegrable (foldB a) volume c d := by
  refine Continuous.intervalIntegrable ?_ c d
  unfold foldB; fun_prop

/-- `sin²θ = 1/2 - cos 2θ/2`, integrated. -/
theorem vonMisesS_eq (a : ℝ) : vonMisesS a = vonMisesZ a / 2 - vonMisesC2 a / 2 := by
  have h : ∀ θ : ℝ, Real.sin θ ^ 2 * vonMisesWeight a θ
      = vonMisesWeight a θ / 2 - Real.cos (2 * θ) * vonMisesWeight a θ / 2 := by
    intro θ
    rw [Real.sin_sq_eq_half_sub]
    ring
  unfold vonMisesS vonMisesZ vonMisesC2
  rw [intervalIntegral.integral_congr (fun θ _ => h θ),
    intervalIntegral.integral_sub
      ((intervalIntegrable_vonMisesWeight a _ _).div_const 2)
      ((intervalIntegrable_cos_two_mul a _ _).div_const 2),
    intervalIntegral.integral_div, intervalIntegral.integral_div]

/-! ### Fold 1 — evenness -/

lemma c2_integrand_neg (a x : ℝ) :
    Real.cos (2 * -x) * vonMisesWeight a (-x) = Real.cos (2 * x) * vonMisesWeight a x := by
  simp [vonMisesWeight, mul_neg, Real.cos_neg]

theorem vonMisesC2_eq_two_mul (a : ℝ) :
    vonMisesC2 a = 2 * ∫ θ in (0:ℝ)..π, Real.cos (2 * θ) * vonMisesWeight a θ := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := -π) (b := (0:ℝ)) (c := π)
    (intervalIntegrable_cos_two_mul a _ _) (intervalIntegrable_cos_two_mul a _ _)
  have hneg := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := π)
    (f := fun θ => Real.cos (2 * θ) * vonMisesWeight a θ)
  simp only [c2_integrand_neg, neg_zero] at hneg
  unfold vonMisesC2
  linarith [hadd, hneg]

/-! ### Fold 2 — `θ ↦ π - θ` -/

lemma c2_integrand_pi_sub (a x : ℝ) :
    Real.cos (2 * (π - x)) * vonMisesWeight a (π - x)
      = Real.cos (2 * x) * Real.exp (-(a * Real.cos x)) := by
  have h : 2 * (π - x) = 2 * π - 2 * x := by ring
  rw [h, Real.cos_two_pi_sub, vonMisesWeight, Real.cos_pi_sub, mul_neg]

theorem integral_c2_eq_foldA (a : ℝ) :
    (∫ θ in (0:ℝ)..π, Real.cos (2 * θ) * vonMisesWeight a θ)
      = ∫ x in (0:ℝ)..(π/2), foldA a x := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := π/2) (c := π)
    (intervalIntegrable_cos_two_mul a _ _) (intervalIntegrable_cos_two_mul a _ _)
  have hsub := intervalIntegral.integral_comp_sub_left
    (a := (0:ℝ)) (b := π/2) (f := fun θ => Real.cos (2 * θ) * vonMisesWeight a θ) π
  simp only [c2_integrand_pi_sub] at hsub
  have e1 : π - π/2 = π/2 := by ring
  have e2 : π - (0:ℝ) = π := by ring
  rw [e1, e2] at hsub
  have hsplit : (∫ x in (0:ℝ)..(π/2), foldA a x)
      = (∫ θ in (0:ℝ)..(π/2), Real.cos (2 * θ) * vonMisesWeight a θ)
        + ∫ x in (0:ℝ)..(π/2), Real.cos (2 * x) * Real.exp (-(a * Real.cos x)) := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_cos_two_mul a _ _)
      (by refine Continuous.intervalIntegrable ?_ _ _; fun_prop)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    unfold foldA vonMisesWeight
    ring
  rw [hsplit, hsub, hadd]

/-! ### Fold 3 — `θ ↦ π/2 - θ` -/

lemma foldA_pi_div_two_sub (a x : ℝ) :
    foldA a (π/2 - x)
      = -(Real.cos (2 * x) *
          (Real.exp (a * Real.sin x) + Real.exp (-(a * Real.sin x)))) := by
  have h : 2 * (π/2 - x) = π - 2 * x := by ring
  rw [foldA, h, Real.cos_pi_sub, Real.cos_pi_div_two_sub]
  ring

theorem integral_foldA_eq_foldB (a : ℝ) :
    (∫ x in (0:ℝ)..(π/2), foldA a x) = ∫ x in (0:ℝ)..(π/4), foldB a x := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := π/4) (c := π/2)
    (intervalIntegrable_foldA a _ _) (intervalIntegrable_foldA a _ _)
  have hsub := intervalIntegral.integral_comp_sub_left
    (a := (0:ℝ)) (b := π/4) (f := foldA a) (π/2)
  simp only [foldA_pi_div_two_sub] at hsub
  have e1 : π/2 - π/4 = π/4 := by ring
  have e2 : π/2 - (0:ℝ) = π/2 := by ring
  rw [e1, e2] at hsub
  have hsplit : (∫ x in (0:ℝ)..(π/4), foldB a x)
      = (∫ x in (0:ℝ)..(π/4), foldA a x)
        + ∫ x in (0:ℝ)..(π/4), -(Real.cos (2 * x) *
            (Real.exp (a * Real.sin x) + Real.exp (-(a * Real.sin x)))) := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_foldA a _ _)
      (by refine Continuous.intervalIntegrable ?_ _ _; fun_prop)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    unfold foldB foldA
    ring
  rw [hsplit, hsub, hadd]

/-! ### Pointwise positivity on `[0, π/4]` -/

lemma sin_le_cos_of_mem {x : ℝ} (hx : x ∈ Icc (0:ℝ) (π/4)) : Real.sin x ≤ Real.cos x := by
  obtain ⟨hx0, hx4⟩ := hx
  have hpi := Real.pi_pos
  have h : Real.sin x ≤ Real.sin (π/2 - x) := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  rwa [Real.sin_pi_div_two_sub] at h

/-- The strict form, on the half-open interval. `sin` and `cos` meet only at
`π/4`, which is why the strictness below survives integration. -/
lemma sin_lt_cos_of_mem {x : ℝ} (hx : x ∈ Ico (0:ℝ) (π/4)) : Real.sin x < Real.cos x := by
  obtain ⟨hx0, hx4⟩ := hx
  have hpi := Real.pi_pos
  have h : Real.sin x < Real.sin (π/2 - x) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  rwa [Real.sin_pi_div_two_sub] at h

lemma foldB_nonneg {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc (0:ℝ) (π/4)) : 0 ≤ foldB a x := by
  obtain ⟨hx0, hx4⟩ := hx
  have hpi := Real.pi_pos
  have hcos2 : 0 ≤ Real.cos (2 * x) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith)
  have hsc : Real.sin x ≤ Real.cos x := sin_le_cos_of_mem ⟨hx0, hx4⟩
  -- `cosh` is increasing in `|·|`, and `|a sin x| ≤ |a cos x|`.
  have habs : |a * Real.sin x| ≤ |a * Real.cos x| := by
    rw [abs_of_nonneg (mul_nonneg ha hsin0),
      abs_of_nonneg (mul_nonneg ha (by linarith))]
    exact mul_le_mul_of_nonneg_left hsc ha
  have hcosh : Real.cosh (a * Real.sin x) ≤ Real.cosh (a * Real.cos x) :=
    Real.cosh_le_cosh.mpr habs
  have hbracket : 0 ≤ (Real.exp (a * Real.cos x) + Real.exp (-(a * Real.cos x)))
      - (Real.exp (a * Real.sin x) + Real.exp (-(a * Real.sin x))) := by
    have h1 := Real.cosh_eq (a * Real.cos x)
    have h2 := Real.cosh_eq (a * Real.sin x)
    linarith [hcosh, h1, h2]
  exact mul_nonneg hcos2 hbracket

/-- **The strict form.** On the open interval both factors are strictly
positive: `cos 2x > 0` for `x ∈ (0, π/4)`, and `cosh` is *strictly* increasing in
`|·|`, so `a sin x < a cos x` separates the two hyperbolic cosines. -/
lemma foldB_pos {a x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo (0:ℝ) (π/4)) : 0 < foldB a x := by
  obtain ⟨hx0, hx4⟩ := hx
  have hpi := Real.pi_pos
  have hcos2 : 0 < Real.cos (2 * x) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hx0) (by linarith)
  have hsc : Real.sin x < Real.cos x := sin_lt_cos_of_mem ⟨le_of_lt hx0, hx4⟩
  have habs : |a * Real.sin x| < |a * Real.cos x| := by
    rw [abs_of_nonneg (mul_nonneg ha.le hsin0),
      abs_of_nonneg (mul_nonneg ha.le (by linarith))]
    exact mul_lt_mul_of_pos_left hsc ha
  have hcosh : Real.cosh (a * Real.sin x) < Real.cosh (a * Real.cos x) :=
    Real.cosh_lt_cosh.mpr habs
  have hbracket : 0 < (Real.exp (a * Real.cos x) + Real.exp (-(a * Real.cos x)))
      - (Real.exp (a * Real.sin x) + Real.exp (-(a * Real.sin x))) := by
    have h1 := Real.cosh_eq (a * Real.cos x)
    have h2 := Real.cosh_eq (a * Real.sin x)
    linarith [hcosh, h1, h2]
  exact mul_pos hcos2 hbracket

/-- **`I₂(a) ≥ 0`.** The second moment of the von Mises weight is non-negative
for every non-negative concentration. -/
theorem vonMisesC2_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ vonMisesC2 a := by
  have hpi := Real.pi_pos
  rw [vonMisesC2_eq_two_mul, integral_c2_eq_foldA, integral_foldA_eq_foldB]
  have : 0 ≤ ∫ x in (0:ℝ)..(π/4), foldB a x :=
    intervalIntegral.integral_nonneg (by linarith) (fun x hx => foldB_nonneg ha hx)
  linarith

/-- **`I₂(a) > 0` for `a > 0`.** The strict form of `vonMisesC2_nonneg`, and the
only new analytic input this pass needs: `foldB` is continuous, non-negative on
`[0, π/4]` and strictly positive on its interior, so
`intervalIntegral_pos_of_pos_on` upgrades the integral. Everything below is
algebra on top of it. -/
theorem vonMisesC2_pos {a : ℝ} (ha : 0 < a) : 0 < vonMisesC2 a := by
  have hpi := Real.pi_pos
  rw [vonMisesC2_eq_two_mul, integral_c2_eq_foldA, integral_foldA_eq_foldB]
  have h : 0 < ∫ x in (0:ℝ)..(π/4), foldB a x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_foldB a _ _)
      (fun x hx => foldB_pos ha hx) (by linarith)
  linarith

/-- **The sharp bound.** Under the von Mises weight the mean of `sin²` is at
most `1/2` — the pointwise bound `sin² ≤ 1` of `vonMisesS_le_vonMisesZ` loses
exactly a factor of two, and this recovers it. -/
theorem vonMisesS_le_half_vonMisesZ {a : ℝ} (ha : 0 ≤ a) :
    vonMisesS a ≤ vonMisesZ a / 2 := by
  rw [vonMisesS_eq]
  linarith [vonMisesC2_nonneg ha]

/-- **The strict sharp bound.** For a *positive* concentration the mean of `sin²`
is strictly below `1/2`. Equality holds only at `a = 0`, where the weight is
constant — which is exactly why `K = 2D` turns out to sit on the incoherent side
of the threshold rather than on the boundary between the two. -/
theorem vonMisesS_lt_half_vonMisesZ {a : ℝ} (ha : 0 < a) :
    vonMisesS a < vonMisesZ a / 2 := by
  rw [vonMisesS_eq]
  linarith [vonMisesC2_pos ha]

/-- `R(a) ≤ a/2` — the slope of the Bessel ratio at the origin, as an upper
bound for all `a ≥ 0`. This is what puts the threshold at `2D` rather than
`D`. -/
theorem besselRatio_le_half_self {a : ℝ} (ha : 0 ≤ a) : besselRatio a ≤ a / 2 := by
  rw [besselRatio, vonMisesM_eq_mul_vonMisesS, div_le_iff₀ (vonMisesZ_pos a)]
  nlinarith [mul_le_mul_of_nonneg_left (vonMisesS_le_half_vonMisesZ ha) ha,
    vonMisesS_nonneg a, vonMisesZ_pos a]

/-- **`R(a) < a/2` for `a > 0`.** The self-consistency map is *strictly* below
the line of slope `1/2` everywhere except at the origin. This is what closes the
threshold case: at `K = 2D` the line `r ↦ K r /(2D) = r` is exactly the diagonal,
and a strict inequality leaves no room for a second crossing. -/
theorem besselRatio_lt_half_self {a : ℝ} (ha : 0 < a) : besselRatio a < a / 2 := by
  rw [besselRatio, vonMisesM_eq_mul_vonMisesS, div_lt_iff₀ (vonMisesZ_pos a)]
  nlinarith [mul_lt_mul_of_pos_left (vonMisesS_lt_half_vonMisesZ ha) ha,
    vonMisesS_nonneg a, vonMisesZ_pos a]

/-- **Subcritical uniqueness at the physical threshold.** For `K < 2D` the
incoherent state `r = 0` is the only non-negative solution of the
self-consistency equation `r = R(K, r)`.

This is the sharp form of `subcritical_fixed_point_eq_zero`, and half of the
sense in which `critical_coupling D = 2 * D` of `Phase8_ContinuousField.lean` is
the right number: below it, no coherent stationary order parameter exists. The
converse — that a positive solution does branch off for `K > 2D` — is
`supercritical_fixed_point_exists` in §6; the two are packaged as
`critical_coupling_is_threshold`. -/
theorem subcritical_fixed_point_eq_zero' {K D r : ℝ} (hD : 0 < D) (hK : 0 ≤ K)
    (hKD : K < critical_coupling D) (hr : 0 ≤ r)
    (hfix : r = selfConsistency K D r) : r = 0 := by
  rw [critical_coupling] at hKD
  rcases eq_or_lt_of_le hr with h | hpos
  · exact h.symm
  have ha : 0 ≤ K * r / D := by positivity
  have h1 : selfConsistency K D r ≤ K * r / D / 2 := besselRatio_le_half_self ha
  have h2 : K * r / D / 2 < r := by
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2), div_lt_iff₀ hD]
    nlinarith
  linarith [hfix ▸ h1]


/-- **The threshold case, and the sharp subcritical statement in one.** For
every `K ≤ 2D` — the strict inequality of `subcritical_fixed_point_eq_zero'`
*and* the threshold itself — the incoherent state `r = 0` is the only
non-negative solution.

`K = 2D` was previously covered by neither half of `critical_coupling_is_threshold`,
and it is the case where the naive picture would put a second fixed point: the
self-consistency map has slope exactly `1/2` at the origin there, so it is
tangent to the diagonal after the rescaling. `besselRatio_lt_half_self` settles
it — the tangency is one-sided, the map falls strictly below the diagonal for
every `r > 0`, and nothing crosses. So the bifurcation happens strictly *after*
`K = 2D`, not at it.

**What this does not establish.** Nothing about uniqueness *above* threshold;
see `coherent_branch_continuous_at_threshold` for what is known there, and the
`vonMisesSRatio` note on it for what uniqueness would take. The von Mises
density remains an input throughout. -/
theorem fixed_point_eq_zero_of_le_critical {K D r : ℝ} (hD : 0 < D) (hK : 0 ≤ K)
    (hKD : K ≤ critical_coupling D) (hr : 0 ≤ r)
    (hfix : r = selfConsistency K D r) : r = 0 := by
  rw [critical_coupling] at hKD
  rcases eq_or_lt_of_le hr with h | hpos
  · exact h.symm
  rcases eq_or_lt_of_le hK with hk0 | hkpos
  · rw [selfConsistency, ← hk0] at hfix
    simpa using hfix
  have hapos : 0 < K * r / D := by positivity
  have h1 : selfConsistency K D r < K * r / D / 2 := besselRatio_lt_half_self hapos
  have h2 : K * r / D / 2 ≤ r := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), div_le_iff₀ hD]
    nlinarith
  linarith [hfix ▸ h1]

/-! ## 6. The supercritical direction

Below threshold the bound `R(a) ≤ a/2` of §5 was enough, because it is global.
Above threshold a *lower* bound is needed, and only near the origin. The
anticipated route was a second-order expansion of the Bessel ratio; none is
required. Writing `R(a) = a · E(a)` with

    E(a) := S(a) / Z(a) = E_a[sin²θ]

the integration-by-parts identity of §2 already exposes the slope as a single
factor, and `E` is continuous with `E(0) = 1/2` — the latter because the weight
is constant at `a = 0`, so `E(0)` is the mean of `sin²` against Lebesgue measure
on `[-π, π]`. Continuity is `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
applied to the jointly continuous integrand; no dominated-convergence argument
is written by hand.

Given `K > 2D`, the number `D/K` is strictly below `1/2`, so `E(a) > D/K` on a
neighbourhood of `0`. For `r` in the corresponding neighbourhood the map
overshoots, `R(K, r) > r`. At the other end `R ≤ 1` always, since `cos θ ≤ 1`,
so the map undershoots at `r = 1`. The intermediate value theorem closes the
gap.

Note what this does *not* use: `R` is never shown monotone, and the fixed point
is not produced by iteration. -/

/-- The partition function is continuous in the concentration. -/
theorem continuous_vonMisesZ : Continuous vonMisesZ := by
  unfold vonMisesZ
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by unfold vonMisesWeight; fun_prop) _ _

/-- The first moment is continuous in the concentration. -/
theorem continuous_vonMisesM : Continuous vonMisesM := by
  unfold vonMisesM
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by unfold vonMisesWeight; fun_prop) _ _

/-- The `sin²` moment is continuous in the concentration. -/
theorem continuous_vonMisesS : Continuous vonMisesS := by
  unfold vonMisesS
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by unfold vonMisesWeight; fun_prop) _ _

@[simp] theorem vonMisesZ_zero : vonMisesZ 0 = 2 * π := by
  unfold vonMisesZ vonMisesWeight
  simp
  ring

@[simp] theorem vonMisesC2_zero : vonMisesC2 0 = 0 := by
  unfold vonMisesC2 vonMisesWeight
  simp

@[simp] theorem vonMisesS_zero : vonMisesS 0 = π := by
  rw [vonMisesS_eq, vonMisesZ_zero, vonMisesC2_zero]
  ring

/-- `E(a) = E_a[sin²θ]`, the mean of `sin²` under the von Mises weight. The
whole of §5 is the statement `vonMisesSRatio a ≤ 1/2`; the whole of this section
is that it is *close to* `1/2` near the origin. -/
noncomputable def vonMisesSRatio (a : ℝ) : ℝ := vonMisesS a / vonMisesZ a

theorem continuous_vonMisesSRatio : Continuous vonMisesSRatio :=
  continuous_vonMisesS.div continuous_vonMisesZ (fun a => (vonMisesZ_pos a).ne')

/-- At zero concentration the weight is constant, so `E(0)` is the mean of
`sin²` against Lebesgue measure on `[-π, π]`. -/
@[simp] theorem vonMisesSRatio_zero : vonMisesSRatio 0 = 1 / 2 := by
  rw [vonMisesSRatio, vonMisesS_zero, vonMisesZ_zero]
  field_simp

/-- `R(a) = a · E(a)` — the integration-by-parts identity of §2, with the slope
factored out. Both bounds on `R` in this file go through this form. -/
theorem besselRatio_eq_mul (a : ℝ) : besselRatio a = a * vonMisesSRatio a := by
  rw [besselRatio, vonMisesM_eq_mul_vonMisesS, vonMisesSRatio, mul_div_assoc]

/-- The strict form of §5's bound, in the `E`-notation this section uses:
`E(a) < 1/2` for every `a > 0`, with equality only at the origin. -/
theorem vonMisesSRatio_lt_half {a : ℝ} (ha : 0 < a) : vonMisesSRatio a < 1 / 2 := by
  rw [vonMisesSRatio, div_lt_iff₀ (vonMisesZ_pos a)]
  linarith [vonMisesS_lt_half_vonMisesZ ha]

theorem continuous_besselRatio : Continuous besselRatio :=
  continuous_vonMisesM.div continuous_vonMisesZ (fun a => (vonMisesZ_pos a).ne')

theorem continuous_selfConsistency (K D : ℝ) : Continuous (selfConsistency K D) := by
  unfold selfConsistency
  exact continuous_besselRatio.comp (by fun_prop)

theorem vonMisesM_le_vonMisesZ (a : ℝ) : vonMisesM a ≤ vonMisesZ a := by
  refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (intervalIntegrable_cos_mul a _ _) (intervalIntegrable_vonMisesWeight a _ _)
    (fun θ _ => ?_)
  nlinarith [Real.cos_le_one θ, vonMisesWeight_pos a θ]

/-- `R(a) ≤ 1`: the order parameter is a mean of `cos θ`. This is what makes the
self-consistency map undershoot at `r = 1`, and is the only bound used at the
upper end of the interval. -/
theorem besselRatio_le_one (a : ℝ) : besselRatio a ≤ 1 := by
  rw [besselRatio, div_le_one (vonMisesZ_pos a)]
  exact vonMisesM_le_vonMisesZ a

/-- **Supercritical existence.** For `K > critical_coupling D = 2D` the
self-consistency equation `r = R(K, r)` has a solution with `0 < r ≤ 1`: a
coherent stationary order parameter.

Together with `subcritical_fixed_point_eq_zero'` this is the content of
`K_c = 2D` at the level of the self-consistency equation. See
`critical_coupling_is_threshold`.

**What it does not establish.** Existence, not uniqueness — but all three gaps
this doc-string used to record are now closed elsewhere in the file:
`fixed_point_eq_zero_of_le_critical` covers `K = 2D`,
`coherent_branch_continuous_at_threshold` rules out a discontinuous jump at
threshold, and §7's `supercritical_fixed_point_existsUnique` upgrades this
statement to `∃!`. What remains is dynamical selection, which is not a statement
about this equation at all: there is no dynamics in this file. And the von Mises
density remains an input — see the file header. -/
theorem supercritical_fixed_point_exists {K D : ℝ} (hD : 0 < D)
    (hKD : critical_coupling D < K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency K D r := by
  rw [critical_coupling] at hKD
  have hK : 0 < K := by linarith
  -- `D/K < 1/2 = E(0)`, so `E > D/K` on a ball around the origin.
  have hc : D / K < 1 / 2 := by rw [div_lt_iff₀ hK]; linarith
  have hcont : ContinuousAt vonMisesSRatio 0 := continuous_vonMisesSRatio.continuousAt
  have hev : ∀ᶠ a in nhds (0:ℝ), D / K < vonMisesSRatio a :=
    hcont.eventually (lt_mem_nhds (by rw [vonMisesSRatio_zero]; exact hc))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  -- a point of the interval whose concentration lands inside that ball
  set r₀ : ℝ := min (1/2) (ε * D / (2 * K)) with hr₀def
  have hr₀pos : 0 < r₀ := lt_min (by norm_num) (by positivity)
  have hr₀le : r₀ ≤ 1/2 := min_le_left _ _
  have ha₀ : K * r₀ / D < ε := by
    have h1 : r₀ ≤ ε * D / (2 * K) := min_le_right _ _
    rw [div_lt_iff₀ hD]
    calc K * r₀ ≤ K * (ε * D / (2 * K)) := by nlinarith
      _ = ε * D / 2 := by field_simp
      _ < ε * D := by nlinarith
  have ha₀pos : 0 < K * r₀ / D := by positivity
  -- at `r₀` the map overshoots
  have hlow : r₀ < selfConsistency K D r₀ := by
    have hE : D / K < vonMisesSRatio (K * r₀ / D) := by
      refine hball ?_
      rw [Real.dist_eq, sub_zero, abs_of_pos ha₀pos]
      exact ha₀
    have hsplit : selfConsistency K D r₀
        = (K * r₀ / D) * vonMisesSRatio (K * r₀ / D) := by
      rw [selfConsistency, besselRatio_eq_mul]
    rw [hsplit]
    have hkey : (K * r₀ / D) * (D / K) < (K * r₀ / D) * vonMisesSRatio (K * r₀ / D) :=
      mul_lt_mul_of_pos_left hE ha₀pos
    have hid : (K * r₀ / D) * (D / K) = r₀ := by field_simp
    linarith [hid ▸ hkey]
  -- at `r = 1` it undershoots
  have hhigh : selfConsistency K D 1 ≤ 1 := by
    rw [selfConsistency]; exact besselRatio_le_one _
  -- intermediate value theorem on `[r₀, 1]`
  set f : ℝ → ℝ := fun r => selfConsistency K D r - r with hfdef
  have hfc : ContinuousOn f (Set.Icc r₀ 1) :=
    ((continuous_selfConsistency K D).sub continuous_id).continuousOn
  have hmem : (0:ℝ) ∈ Set.Icc (f 1) (f r₀) := by
    constructor
    · simp only [hfdef]; linarith
    · simp only [hfdef]; linarith
  obtain ⟨r, hrmem, hr⟩ :=
    intermediate_value_Icc' (by linarith : r₀ ≤ (1:ℝ)) hfc hmem
  refine ⟨r, lt_of_lt_of_le hr₀pos hrmem.1, hrmem.2, ?_⟩
  simp only [hfdef] at hr
  linarith

/-! ### The coherent branch as a level set

`supercritical_fixed_point_exists` produces *a* positive solution and says
nothing about which. The reformulation below is what makes the remaining
questions precise, and it is pure algebra: since `R(a) = a · E(a)`, a *non-zero*
`r` solves `r = R(K r / D)` exactly when `E(K r / D) = D/K`. The coherent branch
is therefore the level set of a single function `E` at height `D/K`, and the
three things O8 asked for become three statements about `E`:

* **uniqueness** ⟺ `E` is injective on `(0, ∞)`. Proved in §7, and by the
  stronger statement that `E` is strictly decreasing on `[0, ∞)`.
* **no jump at threshold** — proved below, and it does *not* need uniqueness:
  it follows from `E < 1/2` strictly plus a compactness argument.
* **the threshold itself** — `fixed_point_eq_zero_of_le_critical`, above. -/

/-- **The coherent branch is a level set of `E`.** For `r ≠ 0`, solving the
self-consistency equation is the same as sitting at concentration `K r / D`
where the mean of `sin²` equals `D/K`.

This is the reformulation the rest of this section runs on. It is an equivalence,
so nothing is lost: every statement about coherent solutions can be made about
the level sets of `E`, and vice versa. -/
theorem coherent_iff_sRatio_eq {K D r : ℝ} (hD : 0 < D) (hK : 0 < K) (hr : r ≠ 0) :
    r = selfConsistency K D r ↔ vonMisesSRatio (K * r / D) = D / K := by
  set E := vonMisesSRatio (K * r / D) with hEdef
  rw [selfConsistency, besselRatio_eq_mul, ← hEdef, eq_div_iff hK.ne',
    show K * r / D * E = r * (K * E / D) by ring]
  constructor
  · intro h
    have h1 : r * 1 = r * (K * E / D) := by rw [mul_one]; exact h
    have h2 : (1 : ℝ) = K * E / D := mul_left_cancel₀ hr h1
    rw [eq_comm, div_eq_one_iff_eq hD.ne'] at h2
    linarith [h2, mul_comm K E]
  · intro h
    have h3 : K * E / D = 1 := by
      rw [div_eq_one_iff_eq hD.ne']
      linarith [h, mul_comm K E]
    rw [h3, mul_one]

/-- **`E` is uniformly below `1/2` away from the origin.** For any `a₀ > 0`
there is a gap `c > 0` with `E(a) ≤ 1/2 - c` for all `a ≥ a₀`.

Two regimes, and neither needs monotonicity of `E`. On the compact `[a₀, A]` the
extreme value theorem gives a maximum, which `vonMisesSRatio_lt_half` puts
strictly below `1/2`. Beyond `A ≥ 4` the crude bound `E(a) = R(a)/a ≤ 1/a`
suffices, since `R ≤ 1`. -/
theorem exists_sRatio_gap {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ ∀ a : ℝ, a₀ ≤ a → vonMisesSRatio a ≤ 1 / 2 - c := by
  set A : ℝ := max a₀ 4 with hAdef
  have hA4 : (4:ℝ) ≤ A := le_max_right _ _
  have hne : (Icc a₀ A).Nonempty := ⟨a₀, ⟨le_refl _, le_max_left _ _⟩⟩
  obtain ⟨x, hx, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn hne continuous_vonMisesSRatio.continuousOn
  have hxpos : 0 < x := lt_of_lt_of_le ha₀ hx.1
  have hm : vonMisesSRatio x < 1 / 2 := vonMisesSRatio_lt_half hxpos
  refine ⟨min (1 / 2 - vonMisesSRatio x) (1 / 4), lt_min (by linarith) (by norm_num),
    min_le_right _ _, ?_⟩
  intro a ha
  rcases le_or_gt a A with hle | hlt
  · have hax : vonMisesSRatio a ≤ vonMisesSRatio x := hmax ⟨ha, hle⟩
    have hc : min (1 / 2 - vonMisesSRatio x) (1 / 4) ≤ 1 / 2 - vonMisesSRatio x :=
      min_le_left _ _
    linarith
  · have hapos : 0 < a := by linarith
    have h1 : vonMisesSRatio a ≤ 1 / a := by
      have hb := besselRatio_le_one a
      rw [besselRatio_eq_mul] at hb
      rw [le_div_iff₀ hapos]
      linarith
    have h2 : 1 / a ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hc : min (1 / 2 - vonMisesSRatio x) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    linarith

/-- **The bifurcation is continuous at threshold: no jump.** For every `ε > 0`
there is a `δ > 0` such that for couplings in `(2D, 2D + δ)` *every* coherent
solution satisfies `r < ε`. The coherent branch emerges from `r = 0`; it does
not appear at a finite distance from the incoherent state.

This is the property that makes the transition supercritical in the technical
sense, and it is the second of the three gaps the doc-string of
`supercritical_fixed_point_exists` records. Note the quantifier: it is over
*every* solution, so it does not presuppose that the solution is unique — which
is why it can be proved without the monotonicity of `E` that uniqueness needs.

**Uniqueness, which this used to record as open, is proved in §7**
(`vonMisesSRatio_strictAntiOn`), and by an argument that avoids the derivative
`E'(a) = -Cov_a(cos²θ, cos θ)` this doc-string used to propose: see the §7 header
for why folding first and then crossing once replaces differentiating under the
integral sign. With uniqueness available, this theorem's quantifier over *all*
solutions is no longer the point it was — but the proof is kept as it stands,
since it does not depend on §7 and so records that the no-jump property is the
weaker fact. -/
theorem coherent_branch_continuous_at_threshold {D : ℝ} (hD : 0 < D) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ K r : ℝ, critical_coupling D < K → K < critical_coupling D + δ →
      0 < r → r = selfConsistency K D r → r < ε := by
  obtain ⟨c, hc0, hc4, hgap⟩ := exists_sRatio_gap (a₀ := 2 * ε) (by linarith)
  have hhalf : 0 < 1 / 2 - c := by linarith
  refine ⟨D / (1 / 2 - c) - 2 * D, ?_, ?_⟩
  · have h : 2 * D < D / (1 / 2 - c) := by
      rw [lt_div_iff₀ hhalf]; nlinarith
    linarith
  · intro K r hKlow hKhigh hrpos hfix
    rw [critical_coupling] at hKlow hKhigh
    have hK : 0 < K := by linarith
    by_contra hcon
    have hre : ε ≤ r := not_lt.mp hcon
    have ha : 2 * ε ≤ K * r / D := by
      rw [le_div_iff₀ hD]; nlinarith
    have hE : vonMisesSRatio (K * r / D) = D / K :=
      (coherent_iff_sRatio_eq hD hK (ne_of_gt hrpos)).mp hfix
    have h1 : D / K ≤ 1 / 2 - c := hE ▸ hgap _ ha
    have h2 : D / (1 / 2 - c) ≤ K := by
      rw [div_le_iff₀ hhalf]
      rw [div_le_iff₀ hK] at h1
      linarith
    linarith

/-- **`K_c = 2D` for the self-consistency equation**, now all three parts in one
statement: at or below the threshold the incoherent state is the only
non-negative solution, strictly above it a coherent one exists, and the coherent
branch emerges continuously from zero rather than jumping.

The threshold `K = critical_coupling D` itself used to be covered by neither
half; `fixed_point_eq_zero_of_le_critical` now puts it on the incoherent side,
so the two regimes together exhaust `K ≥ 0` with no gap. The von Mises ansatz is
assumed throughout; see the file header.

**Sharpened in §7.** `critical_coupling_is_threshold_unique` replaces the middle
component's `∃` by `∃!`, and `supercritical_solution_set` describes the
non-negative solution set outright: `{0}` at or below threshold, `{0, r}` above
it. This packaging is kept because nothing in it depends on §7. -/
theorem critical_coupling_is_threshold {K D : ℝ} (hD : 0 < D) (hK : 0 ≤ K) :
    (K ≤ critical_coupling D →
      ∀ r : ℝ, 0 ≤ r → r = selfConsistency K D r → r = 0)
    ∧ (critical_coupling D < K →
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency K D r)
    ∧ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ K' r : ℝ,
        critical_coupling D < K' → K' < critical_coupling D + δ →
        0 < r → r = selfConsistency K' D r → r < ε) :=
  ⟨fun h r hr hfix => fixed_point_eq_zero_of_le_critical (r := r) hD hK h hr hfix,
    fun h => supercritical_fixed_point_exists hD h,
    fun _ hε => coherent_branch_continuous_at_threshold hD hε⟩

section PhaseTransition

variable {M : Type*} [MeasureSpace M] [TopologicalSpace M]

/-- **The predicate is no longer inert.** A substrate satisfying
`exhibits_phase_transition` — its mean-field coupling exceeds
`critical_coupling` — admits a positive stationary order parameter.

Before this, `critical_coupling` was a named real number that nothing was proved
about, and `exhibits_phase_transition` compared against it; satisfying the
predicate implied nothing. It now implies the existence of a coherent solution
of the self-consistency equation.

**Scope, unchanged from the rest of the file.** That solution is a fixed point
of `selfConsistency`, which rests on the von Mises stationary density. It is not
a statement about `is_continuous_kuramoto_trajectory` or `order_parameter_r_sq`,
so the link from the predicate to the *dynamics* is still missing. -/
theorem exhibits_phase_transition_coherent [IsProbabilityMeasure (volume : Measure M)]
    (sys : StochasticNeuralField M) (h : exhibits_phase_transition sys) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency (mean_field_coupling sys) sys.D r :=
  supercritical_fixed_point_exists sys.h_D_pos h

end PhaseTransition

/-! ## 7. Uniqueness of the coherent branch

`coherent_iff_sRatio_eq` reduced uniqueness to the injectivity of
`E(a) = E_a[sin²θ]` on `(0, ∞)`. This section proves the stronger statement that
`E` is **strictly decreasing** on `[0, ∞)`, and — by the same argument in a
simpler form — that the Bessel ratio `R` is **strictly increasing** on all of
`ℝ`, which is the monotonicity the header of this file used to list as unproved.

## Why the recorded obstacle is not one

The gap was recorded as needing `E'(a) = -Cov_a(cos²θ, cos θ) < 0`: an
identity that costs differentiation under the integral sign, and whose
right-hand side is *not* sign-definite pointwise — symmetrising with an
independent copy gives `½ E[(X - X')²(X + X')]` with `X = cos θ`, whose integrand
changes sign with `X + X'`. Nothing below differentiates anything, and no
covariance appears. Two moves replace the derivative:

1. **Fold before comparing.** The statement is the two-point inequality
   `C₂(a)·Z(b) < C₂(b)·Z(a)` for `a < b` (`vonMisesS_eq` turns it into
   `E(b) < E(a)`), and folds 1 and 2 of §5 already carry `[-π, π]` onto
   `[0, π/2]`, replacing `e^{a cos x}` by `W(a,x) = 2 cosh(a cos x)` and letting
   `cos x` run over `[0, 1]` instead of `[-1, 1]`. That fold *is* the
   symmetrisation `X ↦ -X` that the covariance form needed the tilt to perform,
   done once at the start; after it, both `cos 2x - cos 2y` and
   `W(b,x)·W(a,y) - W(a,x)·W(b,y)` are governed by `cos x` against `cos y` alone
   and have the same sign. This is `crossIntegrand_nonneg`.
2. **Integrate once, not twice.** With the two factors monovarying, the classical
   Chebyshev-association argument would still integrate over a square. It is
   avoided by a crossing point: let `α` be the mean of `cos 2x` under `W(a, ·)`
   and let `x₀` be a point of `[0, π/2]` where `cos 2x₀ = α` (intermediate value
   theorem). The pointwise inequality at `y = x₀` then integrates to
   `W(a,x₀)·(∫ cos 2x·W(b,x) - α ∫ W(b,x)) ≥ 0`, because the `W(b,x₀)` term
   carries `∫ cos 2x·W(a,x) - α ∫ W(a,x)`, which is `0` by the choice of `α`.
   No product measure and no Fubini.

The analytic input is one line of hyperbolic algebra:
`2 cosh X cosh Y = cosh(X+Y) + cosh(X-Y)` together with `cosh` increasing in
`|·|` gives `cosh(ap)·cosh(bq) ≤ cosh(bp)·cosh(aq)` for `0 ≤ a ≤ b` and
`0 ≤ q ≤ p` (`cosh_mul_cosh_cross`), i.e. `t ↦ cosh(bt)/cosh(at)` is increasing
on `[0, ∞)`.

For `R` the fold is not needed at all: `R(a) = E_a[cos θ]` is the mean of the
very variable the exponential family is tilted by, so
`(cos x - cos y)·(e^{b cos x + a cos y} - e^{a cos x + b cos y}) ≥ 0` holds on all
of `[-π, π]²` and the crossing argument runs directly on `[-π, π]`.

**What this section does not establish.** `E` and `R` are not shown
differentiable, and no rate is proved — only strict order. Uniqueness is of the
solution of the *self-consistency equation*, which rests on the von Mises
stationary density; it says nothing about which state a trajectory selects, or
about stability. That is the dynamics, and it is not in this file. -/

/-- The folded weight `W(a, x) = e^{a cos x} + e^{-a cos x} = 2 cosh(a cos x)`,
the image of the von Mises weight under folds 1 and 2 of §5. It is `foldA`
without the `cos 2x` factor, so `foldA a x = cos (2x) · W(a, x)` definitionally. -/
noncomputable def foldW (a x : ℝ) : ℝ :=
  Real.exp (a * Real.cos x) + Real.exp (-(a * Real.cos x))

lemma foldA_eq_cos_mul_foldW (a x : ℝ) : foldA a x = Real.cos (2 * x) * foldW a x := rfl

lemma foldW_pos (a x : ℝ) : 0 < foldW a x := by
  unfold foldW; positivity

lemma continuous_foldW (a : ℝ) : Continuous (foldW a) := by
  unfold foldW; fun_prop

lemma intervalIntegrable_foldW (a c d : ℝ) :
    IntervalIntegrable (foldW a) volume c d :=
  (continuous_foldW a).intervalIntegrable c d

lemma foldW_eq_two_mul_cosh (a x : ℝ) : foldW a x = 2 * Real.cosh (a * Real.cos x) := by
  rw [Real.cosh_eq]; unfold foldW; ring

/-! ### The partition function, folded the same way

§5 folded `C₂`; the comparison needs `Z` folded by the same two steps, and the
proof is the one of `vonMisesC2_eq_two_mul` and `integral_c2_eq_foldA` with the
`cos 2θ` factor deleted. -/

lemma z_integrand_neg (a x : ℝ) : vonMisesWeight a (-x) = vonMisesWeight a x := by
  simp [vonMisesWeight]

lemma z_integrand_pi_sub (a x : ℝ) :
    vonMisesWeight a (π - x) = Real.exp (-(a * Real.cos x)) := by
  rw [vonMisesWeight, Real.cos_pi_sub, mul_neg]

theorem vonMisesZ_eq_two_mul (a : ℝ) :
    vonMisesZ a = 2 * ∫ θ in (0:ℝ)..π, vonMisesWeight a θ := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := -π) (b := (0:ℝ)) (c := π)
    (intervalIntegrable_vonMisesWeight a _ _) (intervalIntegrable_vonMisesWeight a _ _)
  have hneg := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := π)
    (f := vonMisesWeight a)
  simp only [z_integrand_neg, neg_zero] at hneg
  unfold vonMisesZ
  linarith [hadd, hneg]

theorem integral_weight_eq_foldW (a : ℝ) :
    (∫ θ in (0:ℝ)..π, vonMisesWeight a θ) = ∫ x in (0:ℝ)..(π/2), foldW a x := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := π/2) (c := π)
    (intervalIntegrable_vonMisesWeight a _ _) (intervalIntegrable_vonMisesWeight a _ _)
  have hsub := intervalIntegral.integral_comp_sub_left
    (a := (0:ℝ)) (b := π/2) (f := vonMisesWeight a) π
  simp only [z_integrand_pi_sub] at hsub
  have e1 : π - π/2 = π/2 := by ring
  have e2 : π - (0:ℝ) = π := by ring
  rw [e1, e2] at hsub
  have hsplit : (∫ x in (0:ℝ)..(π/2), foldW a x)
      = (∫ θ in (0:ℝ)..(π/2), vonMisesWeight a θ)
        + ∫ x in (0:ℝ)..(π/2), Real.exp (-(a * Real.cos x)) := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_vonMisesWeight a _ _)
      (by refine Continuous.intervalIntegrable ?_ _ _; fun_prop)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    unfold foldW vonMisesWeight
    ring
  rw [hsplit, hsub, hadd]

/-- `Z(a) = 2∫_0^{π/2} W(a, x) dx`: all of `[-π, π]` carried onto the quarter
period where `cos` is non-negative. -/
theorem vonMisesZ_eq_foldW (a : ℝ) :
    vonMisesZ a = 2 * ∫ x in (0:ℝ)..(π/2), foldW a x := by
  rw [vonMisesZ_eq_two_mul, integral_weight_eq_foldW]

/-- `C₂(a) = 2∫_0^{π/2} cos 2x · W(a, x) dx`, the two folds of §5 composed. -/
theorem vonMisesC2_eq_foldA (a : ℝ) :
    vonMisesC2 a = 2 * ∫ x in (0:ℝ)..(π/2), foldA a x := by
  rw [vonMisesC2_eq_two_mul, integral_c2_eq_foldA]

/-- A continuous function non-negative on `[A, B]` and strictly positive on some
non-degenerate open subinterval has strictly positive integral. Both crossing
arguments below need exactly this: their integrands vanish at the crossing point,
so strictness has to be harvested off a subinterval that misses it. -/
lemma integral_pos_of_pos_on_subinterval {f : ℝ → ℝ} {A B c d : ℝ}
    (hf : Continuous f) (hAc : A ≤ c) (hcd : c < d) (hdB : d ≤ B)
    (hnn : ∀ x ∈ Icc A B, 0 ≤ f x) (hpos : ∀ x ∈ Ioo c d, 0 < f x) :
    0 < ∫ x in A..B, f x := by
  have hAd : A ≤ d := hAc.trans hcd.le
  have hcB : c ≤ B := hcd.le.trans hdB
  have hfi : ∀ u v : ℝ, IntervalIntegrable f volume u v := fun u v => hf.intervalIntegrable u v
  have h1 : 0 ≤ ∫ x in A..c, f x :=
    intervalIntegral.integral_nonneg hAc (fun x hx => hnn x ⟨hx.1, hx.2.trans hcB⟩)
  have h2 : 0 < ∫ x in c..d, f x :=
    intervalIntegral_pos_of_pos_on (hfi _ _) hpos hcd
  have h3 : 0 ≤ ∫ x in d..B, f x :=
    intervalIntegral.integral_nonneg hdB (fun x hx => hnn x ⟨hAd.trans hx.1, hx.2⟩)
  have e1 := intervalIntegral.integral_add_adjacent_intervals (a := A) (b := c) (c := d)
    (hfi _ _) (hfi _ _)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (a := A) (b := d) (c := B)
    (hfi _ _) (hfi _ _)
  linarith

/-! ### The hyperbolic cross inequality

`t ↦ cosh(bt)/cosh(at)` is increasing on `[0, ∞)` for `a ≤ b`, stated as a
product inequality so that no division appears. This is the only analytic input
of the `E` half of the section. -/

/-- For `0 ≤ a ≤ b` and `0 ≤ q ≤ p`: `cosh(ap)·cosh(bq) ≤ cosh(bp)·cosh(aq)`.

Product-to-sum turns both sides into `cosh(ap ± bq)` and `cosh(bp ± aq)`, and
`cosh` is increasing in `|·|`: the sums compare because `(b-a)(p-q) ≥ 0`, the
differences because `bp - aq` dominates `|ap - bq|`, which is `(b-a)(p+q) ≥ 0`
and `(a+b)(p-q) ≥ 0`. -/
lemma cosh_mul_cosh_cross {a b p q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hq : 0 ≤ q)
    (hqp : q ≤ p) :
    Real.cosh (a * p) * Real.cosh (b * q) ≤ Real.cosh (b * p) * Real.cosh (a * q) := by
  have hp : 0 ≤ p := hq.trans hqp
  have hb : 0 ≤ b := ha.trans hab
  have key : ∀ X Y : ℝ, 2 * (Real.cosh X * Real.cosh Y)
      = Real.cosh (X + Y) + Real.cosh (X - Y) := by
    intro X Y; rw [Real.cosh_add, Real.cosh_sub]; ring
  have h1 : Real.cosh (a * p + b * q) ≤ Real.cosh (b * p + a * q) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : (0:ℝ) ≤ a * p + b * q),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ b * p + a * q)]
    nlinarith
  have hbp : (0:ℝ) ≤ b * p - a * q := by nlinarith
  have h2 : Real.cosh (a * p - b * q) ≤ Real.cosh (b * p - a * q) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hbp, abs_le]
    constructor <;> nlinarith
  have e1 := key (a * p) (b * q)
  have e2 := key (b * p) (a * q)
  linarith

/-- The strict form: `a < b` and `q < p` make the comparison of the sums strict,
which is enough. -/
lemma cosh_mul_cosh_cross_lt {a b p q : ℝ} (ha : 0 ≤ a) (hab : a < b) (hq : 0 ≤ q)
    (hqp : q < p) :
    Real.cosh (a * p) * Real.cosh (b * q) < Real.cosh (b * p) * Real.cosh (a * q) := by
  have hp : 0 ≤ p := hq.trans hqp.le
  have hb : 0 ≤ b := ha.trans hab.le
  have key : ∀ X Y : ℝ, 2 * (Real.cosh X * Real.cosh Y)
      = Real.cosh (X + Y) + Real.cosh (X - Y) := by
    intro X Y; rw [Real.cosh_add, Real.cosh_sub]; ring
  have h1 : Real.cosh (a * p + b * q) < Real.cosh (b * p + a * q) := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg (by positivity : (0:ℝ) ≤ a * p + b * q),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ b * p + a * q)]
    nlinarith
  have hbp : (0:ℝ) ≤ b * p - a * q := by nlinarith
  have h2 : Real.cosh (a * p - b * q) ≤ Real.cosh (b * p - a * q) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hbp, abs_le]
    constructor <;> nlinarith
  have e1 := key (a * p) (b * q)
  have e2 := key (b * p) (a * q)
  linarith

/-! ### The crossing integrand -/

lemma cos_nonneg_of_mem_Icc_pi_div_two {x : ℝ} (hx : x ∈ Icc (0:ℝ) (π/2)) :
    0 ≤ Real.cos x :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩

/-- **The crossing integrand is non-negative.** For `0 ≤ a ≤ b` and `x, y` in
`[0, π/2]` the two factors `cos 2x - cos 2y` and
`W(b,x)·W(a,y) - W(a,x)·W(b,y)` have the same sign, because on `[0, π/2]` both
are governed by `cos x` against `cos y`: the first is `2(cos²x - cos²y)` and the
second is `4(cosh(b cos x)cosh(a cos y) - cosh(a cos x)cosh(b cos y))`.

This is the step the covariance form could not take. Off the fold, on
`[-π, π]`, `cos x` ranges over `[-1, 1]` and `cos²x - cos²y` is *not* governed by
`cos x - cos y`; the fold is what makes both factors monovarying. -/
lemma crossIntegrand_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {x y : ℝ}
    (hx : x ∈ Icc (0:ℝ) (π/2)) (hy : y ∈ Icc (0:ℝ) (π/2)) :
    0 ≤ (Real.cos (2 * x) - Real.cos (2 * y))
      * (foldW b x * foldW a y - foldW a x * foldW b y) := by
  have hcx : 0 ≤ Real.cos x := cos_nonneg_of_mem_Icc_pi_div_two hx
  have hcy : 0 ≤ Real.cos y := cos_nonneg_of_mem_Icc_pi_div_two hy
  rw [Real.cos_two_mul, Real.cos_two_mul, foldW_eq_two_mul_cosh, foldW_eq_two_mul_cosh,
    foldW_eq_two_mul_cosh, foldW_eq_two_mul_cosh]
  rcases le_total (Real.cos y) (Real.cos x) with h | h
  · have hc := cosh_mul_cosh_cross ha hab hcy h
    have h1 : 0 ≤ 2 * Real.cos x ^ 2 - 1 - (2 * Real.cos y ^ 2 - 1) := by nlinarith
    have h2 : 0 ≤ 2 * Real.cosh (b * Real.cos x) * (2 * Real.cosh (a * Real.cos y))
        - 2 * Real.cosh (a * Real.cos x) * (2 * Real.cosh (b * Real.cos y)) := by nlinarith
    nlinarith [mul_nonneg h1 h2]
  · have hc := cosh_mul_cosh_cross ha hab hcx h
    have h1 : 2 * Real.cos x ^ 2 - 1 - (2 * Real.cos y ^ 2 - 1) ≤ 0 := by nlinarith
    have h2 : 2 * Real.cosh (b * Real.cos x) * (2 * Real.cosh (a * Real.cos y))
        - 2 * Real.cosh (a * Real.cos x) * (2 * Real.cosh (b * Real.cos y)) ≤ 0 := by nlinarith
    nlinarith [mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)]

/-- Off the diagonal the crossing integrand is strictly positive. `cos` is
injective on `[0, π]`, so `x ≠ y` in `[0, π/2]` already gives `cos x ≠ cos y`. -/
lemma crossIntegrand_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {x y : ℝ}
    (hx : x ∈ Icc (0:ℝ) (π/2)) (hy : y ∈ Icc (0:ℝ) (π/2)) (hxy : x ≠ y) :
    0 < (Real.cos (2 * x) - Real.cos (2 * y))
      * (foldW b x * foldW a y - foldW a x * foldW b y) := by
  have hcx : 0 ≤ Real.cos x := cos_nonneg_of_mem_Icc_pi_div_two hx
  have hcy : 0 ≤ Real.cos y := cos_nonneg_of_mem_Icc_pi_div_two hy
  have hpi := Real.pi_pos
  have hne : Real.cos x ≠ Real.cos y := by
    intro h
    exact hxy (Real.injOn_cos ⟨hx.1, by linarith [hx.2]⟩ ⟨hy.1, by linarith [hy.2]⟩ h)
  rw [Real.cos_two_mul, Real.cos_two_mul, foldW_eq_two_mul_cosh, foldW_eq_two_mul_cosh,
    foldW_eq_two_mul_cosh, foldW_eq_two_mul_cosh]
  rcases lt_or_gt_of_ne hne with h | h
  · have hc := cosh_mul_cosh_cross_lt ha hab hcx h
    have h1 : 2 * Real.cos x ^ 2 - 1 - (2 * Real.cos y ^ 2 - 1) < 0 := by nlinarith
    have h2 : 2 * Real.cosh (b * Real.cos x) * (2 * Real.cosh (a * Real.cos y))
        - 2 * Real.cosh (a * Real.cos x) * (2 * Real.cosh (b * Real.cos y)) < 0 := by nlinarith
    nlinarith [mul_pos_of_neg_of_neg h1 h2]
  · have hc := cosh_mul_cosh_cross_lt ha hab hcy h
    have h1 : 0 < 2 * Real.cos x ^ 2 - 1 - (2 * Real.cos y ^ 2 - 1) := by nlinarith
    have h2 : 0 < 2 * Real.cosh (b * Real.cos x) * (2 * Real.cosh (a * Real.cos y))
        - 2 * Real.cosh (a * Real.cos x) * (2 * Real.cosh (b * Real.cos y)) := by nlinarith
    nlinarith [mul_pos h1 h2]

/-! ### `E` is strictly decreasing -/

/-- The crossing argument for `C₂` against `Z`, in folded coordinates.

`α` is the mean of `cos 2x` under `W(a, ·)` and `x₀` a point of `[0, π/2]` where
`cos 2x₀ = α`; such a point exists because `cos 2·` runs from `1` to `-1` there
and `|α| ≤ 1`. Integrating `crossIntegrand_nonneg` at `y = x₀` gives
`W(a,x₀)·(∫cos 2x·W(b,x) - α∫W(b,x)) ≥ 0`, the `W(b,x₀)` term having vanished by
the choice of `α`; `crossIntegrand_pos` on a subinterval missing `x₀` makes it
strict. -/
theorem foldA_mul_foldW_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (∫ x in (0:ℝ)..(π/2), foldA a x) * (∫ x in (0:ℝ)..(π/2), foldW b x)
      < (∫ x in (0:ℝ)..(π/2), foldA b x) * (∫ x in (0:ℝ)..(π/2), foldW a x) := by
  have hpi := Real.pi_pos
  have hlt : (0:ℝ) < π/2 := by linarith
  set Ia := ∫ x in (0:ℝ)..(π/2), foldW a x with hIadef
  set Ib := ∫ x in (0:ℝ)..(π/2), foldW b x with hIbdef
  set Ja := ∫ x in (0:ℝ)..(π/2), foldA a x with hJadef
  set Jb := ∫ x in (0:ℝ)..(π/2), foldA b x with hJbdef
  have hIa : 0 < Ia :=
    intervalIntegral_pos_of_pos_on (intervalIntegrable_foldW a _ _)
      (fun x _ => foldW_pos a x) hlt
  have hJale : Ja ≤ Ia := by
    rw [hJadef, hIadef]
    refine intervalIntegral.integral_mono_on hlt.le (intervalIntegrable_foldA a _ _)
      (intervalIntegrable_foldW a _ _) (fun x _ => ?_)
    rw [foldA_eq_cos_mul_foldW]
    nlinarith [Real.cos_le_one (2 * x), foldW_pos a x]
  have hJage : -Ia ≤ Ja := by
    rw [hJadef, hIadef, neg_le]
    have h : (∫ x in (0:ℝ)..(π/2), -foldA a x) ≤ ∫ x in (0:ℝ)..(π/2), foldW a x := by
      refine intervalIntegral.integral_mono_on hlt.le
        ((intervalIntegrable_foldA a _ _).neg) (intervalIntegrable_foldW a _ _) (fun x _ => ?_)
      rw [foldA_eq_cos_mul_foldW]
      nlinarith [Real.neg_one_le_cos (2 * x), foldW_pos a x]
    rwa [intervalIntegral.integral_neg] at h
  set α := Ja / Ia with hαdef
  have e1 : Real.cos (2 * (π/2)) = -1 := by
    rw [show 2 * (π/2) = π by ring, Real.cos_pi]
  have e2 : Real.cos (2 * (0:ℝ)) = 1 := by norm_num
  have hmem : α ∈ Icc (Real.cos (2 * (π/2))) (Real.cos (2 * (0:ℝ))) := by
    rw [e1, e2]
    exact ⟨by rw [hαdef, le_div_iff₀ hIa]; linarith, by rw [hαdef, div_le_one hIa]; exact hJale⟩
  obtain ⟨x₀, hx₀mem, hx₀⟩ :=
    intermediate_value_Icc' hlt.le (by fun_prop : ContinuousOn (fun x => Real.cos (2 * x))
      (Icc 0 (π/2))) hmem
  replace hx₀ : Real.cos (2 * x₀) = α := hx₀
  set g : ℝ → ℝ := fun x => (Real.cos (2 * x) - Real.cos (2 * x₀))
      * (foldW b x * foldW a x₀ - foldW a x * foldW b x₀) with hgdef
  have hgcont : Continuous g := by rw [hgdef]; unfold foldW; fun_prop
  have hgnonneg : ∀ x ∈ Icc (0:ℝ) (π/2), 0 ≤ g x :=
    fun x hx => crossIntegrand_nonneg ha hab.le hx hx₀mem
  have hgpos : ∀ x ∈ Icc (0:ℝ) (π/2), x ≠ x₀ → 0 < g x :=
    fun x hx hne => crossIntegrand_pos ha hab hx hx₀mem hne
  have hint : 0 < ∫ x in (0:ℝ)..(π/2), g x := by
    rcases eq_or_lt_of_le hx₀mem.1 with h0 | h0
    · refine integral_pos_of_pos_on_subinterval hgcont le_rfl hlt le_rfl hgnonneg
        (fun x hx => hgpos x ⟨hx.1.le, hx.2.le⟩ ?_)
      rw [← h0]; exact ne_of_gt hx.1
    · exact integral_pos_of_pos_on_subinterval hgcont le_rfl h0 hx₀mem.2 hgnonneg
        (fun x hx => hgpos x ⟨hx.1.le, hx.2.le.trans hx₀mem.2⟩ (ne_of_lt hx.2))
  have i1 : IntervalIntegrable (fun x => foldW a x₀ * foldA b x) volume 0 (π/2) :=
    (intervalIntegrable_foldA b _ _).const_mul _
  have i2 : IntervalIntegrable (fun x => foldW b x₀ * foldA a x) volume 0 (π/2) :=
    (intervalIntegrable_foldA a _ _).const_mul _
  have i3 : IntervalIntegrable (fun x => foldA a x₀ * foldW b x) volume 0 (π/2) :=
    (intervalIntegrable_foldW b _ _).const_mul _
  have i4 : IntervalIntegrable (fun x => foldA b x₀ * foldW a x) volume 0 (π/2) :=
    (intervalIntegrable_foldW a _ _).const_mul _
  have hexp : (∫ x in (0:ℝ)..(π/2), g x)
      = foldW a x₀ * Jb - foldW b x₀ * Ja - foldA a x₀ * Ib + foldA b x₀ * Ia := by
    have hpt : ∀ x, g x = (foldW a x₀ * foldA b x - foldW b x₀ * foldA a x)
        - (foldA a x₀ * foldW b x - foldA b x₀ * foldW a x) := by
      intro x; rw [hgdef]; unfold foldA foldW; ring
    rw [intervalIntegral.integral_congr (fun x _ => hpt x),
      intervalIntegral.integral_sub (i1.sub i2) (i3.sub i4),
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_sub i3 i4,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [← hIadef, ← hIbdef, ← hJadef, ← hJbdef]
    ring
  have hJa : α * Ia = Ja := div_mul_cancel₀ Ja hIa.ne'
  have hfA : foldA a x₀ = α * foldW a x₀ := by rw [foldA_eq_cos_mul_foldW, hx₀]
  have hfB : foldA b x₀ = α * foldW b x₀ := by rw [foldA_eq_cos_mul_foldW, hx₀]
  have hval : (∫ x in (0:ℝ)..(π/2), g x) = foldW a x₀ * (Jb - α * Ib) := by
    rw [hexp, hfA, hfB]
    linear_combination foldW b x₀ * hJa
  rw [hval] at hint
  have h2 : 0 < Jb - α * Ib := by
    rcases le_or_gt (Jb - α * Ib) 0 with h | h
    · have := mul_nonneg (foldW_pos a x₀).le (neg_nonneg.mpr h)
      nlinarith
    · exact h
  rw [hαdef, sub_pos, div_mul_eq_mul_div, div_lt_iff₀ hIa] at h2
  linarith

/-- `I₂/I₀` is strictly increasing: `C₂(a)·Z(b) < C₂(b)·Z(a)` for `0 ≤ a < b`.
Unfolded from `foldA_mul_foldW_lt`; the common factor `4` from the two folds
cancels. -/
theorem vonMisesC2_mul_vonMisesZ_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    vonMisesC2 a * vonMisesZ b < vonMisesC2 b * vonMisesZ a := by
  rw [vonMisesC2_eq_foldA, vonMisesC2_eq_foldA, vonMisesZ_eq_foldW, vonMisesZ_eq_foldW]
  nlinarith [foldA_mul_foldW_lt ha hab]

/-- **`E(a) = E_a[sin²θ]` is strictly decreasing on `[0, ∞)`.**

`vonMisesS_eq` writes `E = 1/2 - C₂/(2Z)`, so this is exactly
`vonMisesC2_mul_vonMisesZ_lt`. It strengthens `vonMisesSRatio_lt_half`, which is
the special case `a = 0` of the same statement.

**Scope.** Order only: `E` is not shown differentiable, and no rate is claimed.
The restriction to `[0, ∞)` is real and not an artifact — `E` is even, so it is
strictly *increasing* on `(-∞, 0]`, and the fold that makes both factors
monovarying is what uses `a ≥ 0`. Concentrations are non-negative in the
application (`a = K r / D` with `K, D, r > 0`), so nothing is lost. -/
theorem vonMisesSRatio_strictAntiOn : StrictAntiOn vonMisesSRatio (Ici (0:ℝ)) := by
  intro a ha b _ hab
  have hZa := vonMisesZ_pos a
  have hZb := vonMisesZ_pos b
  have key := vonMisesC2_mul_vonMisesZ_lt ha hab
  rw [vonMisesSRatio, vonMisesSRatio, vonMisesS_eq, vonMisesS_eq,
    div_lt_div_iff₀ hZb hZa]
  linarith

/-- **The injectivity that `coherent_iff_sRatio_eq` asked for.** Each level of
`E` on `[0, ∞)` is attained at most once, so the coherent branch — the level set
of `E` at height `D/K` — has at most one point. -/
theorem vonMisesSRatio_injOn : InjOn vonMisesSRatio (Ici (0:ℝ)) :=
  vonMisesSRatio_strictAntiOn.injOn

/-! ### `R` is strictly increasing

The same crossing argument, with `cos θ` in place of `sin²θ`. No fold is needed:
`R(a) = E_a[cos θ]` is the mean of the variable the family is tilted by, so the
two factors are monovarying on all of `[-π, π]`, and the sign of
`e^{b cos x + a cos y} - e^{a cos x + b cos y}` is that of `cos x - cos y`
outright. -/

lemma weightCross_nonneg {a b : ℝ} (hab : a ≤ b) (x y : ℝ) :
    0 ≤ (Real.cos x - Real.cos y)
      * (vonMisesWeight b x * vonMisesWeight a y
        - vonMisesWeight a x * vonMisesWeight b y) := by
  unfold vonMisesWeight
  rcases le_total (Real.cos y) (Real.cos x) with h | h
  · have h1 : Real.exp (a * Real.cos x) * Real.exp (b * Real.cos y)
        ≤ Real.exp (b * Real.cos x) * Real.exp (a * Real.cos y) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]; nlinarith
    exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h1)
  · have h1 : Real.exp (b * Real.cos x) * Real.exp (a * Real.cos y)
        ≤ Real.exp (a * Real.cos x) * Real.exp (b * Real.cos y) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]; nlinarith
    have := mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr h))
      (neg_nonneg.mpr (sub_nonpos.mpr h1))
    nlinarith

lemma weightCross_pos {a b : ℝ} (hab : a < b) {x y : ℝ} (hxy : Real.cos x ≠ Real.cos y) :
    0 < (Real.cos x - Real.cos y)
      * (vonMisesWeight b x * vonMisesWeight a y
        - vonMisesWeight a x * vonMisesWeight b y) := by
  unfold vonMisesWeight
  rcases lt_or_gt_of_ne hxy with h | h
  · have h1 : Real.exp (b * Real.cos x) * Real.exp (a * Real.cos y)
        < Real.exp (a * Real.cos x) * Real.exp (b * Real.cos y) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_lt_exp]; nlinarith
    have := mul_pos (neg_pos.mpr (sub_neg.mpr h)) (neg_pos.mpr (sub_neg.mpr h1))
    nlinarith
  · have h1 : Real.exp (a * Real.cos x) * Real.exp (b * Real.cos y)
        < Real.exp (b * Real.cos x) * Real.exp (a * Real.cos y) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_lt_exp]; nlinarith
    exact mul_pos (sub_pos.mpr h) (sub_pos.mpr h1)

/-- `M(a)·Z(b) < M(b)·Z(a)` for `a < b`: the crossing argument on `[-π, π]`,
with the crossing point taken in `[0, π]` where `cos` is injective. -/
theorem vonMisesM_mul_vonMisesZ_lt {a b : ℝ} (hab : a < b) :
    vonMisesM a * vonMisesZ b < vonMisesM b * vonMisesZ a := by
  have hpi := Real.pi_pos
  unfold vonMisesM vonMisesZ
  set Ia := ∫ θ in (-π)..π, vonMisesWeight a θ with hIadef
  set Ib := ∫ θ in (-π)..π, vonMisesWeight b θ with hIbdef
  set Ja := ∫ θ in (-π)..π, Real.cos θ * vonMisesWeight a θ with hJadef
  set Jb := ∫ θ in (-π)..π, Real.cos θ * vonMisesWeight b θ with hJbdef
  have hIa : 0 < Ia := vonMisesZ_pos a
  have hJale : Ja ≤ Ia := vonMisesM_le_vonMisesZ a
  have hJage : -Ia ≤ Ja := by
    rw [hJadef, hIadef, neg_le]
    have h : (∫ θ in (-π)..π, -(Real.cos θ * vonMisesWeight a θ))
        ≤ ∫ θ in (-π)..π, vonMisesWeight a θ := by
      refine intervalIntegral.integral_mono_on (by linarith)
        ((intervalIntegrable_cos_mul a _ _).neg) (intervalIntegrable_vonMisesWeight a _ _)
        (fun θ _ => ?_)
      nlinarith [Real.neg_one_le_cos θ, vonMisesWeight_pos a θ]
    rwa [intervalIntegral.integral_neg] at h
  set α := Ja / Ia with hαdef
  have hmem : α ∈ Icc (Real.cos π) (Real.cos 0) := by
    rw [Real.cos_pi, Real.cos_zero]
    exact ⟨by rw [hαdef, le_div_iff₀ hIa]; linarith, by rw [hαdef, div_le_one hIa]; exact hJale⟩
  obtain ⟨x₀, hx₀mem, hx₀⟩ :=
    intermediate_value_Icc' hpi.le Real.continuous_cos.continuousOn hmem
  set g : ℝ → ℝ := fun x => (Real.cos x - Real.cos x₀)
      * (vonMisesWeight b x * vonMisesWeight a x₀
        - vonMisesWeight a x * vonMisesWeight b x₀) with hgdef
  have hgcont : Continuous g := by rw [hgdef]; unfold vonMisesWeight; fun_prop
  have hgnonneg : ∀ x ∈ Icc (-π) π, 0 ≤ g x := fun x _ => weightCross_nonneg hab.le x x₀
  have hint : 0 < ∫ x in (-π)..π, g x := by
    rcases le_or_gt (π/2) x₀ with h | h
    · refine integral_pos_of_pos_on_subinterval (c := 0) (d := π/2) hgcont (by linarith)
        (by linarith) (by linarith) hgnonneg (fun x hx => ?_)
      exact weightCross_pos hab
        (Real.cos_lt_cos_of_nonneg_of_le_pi hx.1.le hx₀mem.2 (lt_of_lt_of_le hx.2 h)).ne'
    · refine integral_pos_of_pos_on_subinterval (c := π/2) (d := π) hgcont (by linarith)
        (by linarith) (by linarith) hgnonneg (fun x hx => ?_)
      exact weightCross_pos hab
        (Real.cos_lt_cos_of_nonneg_of_le_pi hx₀mem.1 hx.2.le (lt_trans h hx.1)).ne
  have i1 : IntervalIntegrable (fun x => vonMisesWeight a x₀ * (Real.cos x * vonMisesWeight b x))
      volume (-π) π := (intervalIntegrable_cos_mul b _ _).const_mul _
  have i2 : IntervalIntegrable (fun x => vonMisesWeight b x₀ * (Real.cos x * vonMisesWeight a x))
      volume (-π) π := (intervalIntegrable_cos_mul a _ _).const_mul _
  have i3 : IntervalIntegrable
      (fun x => Real.cos x₀ * vonMisesWeight a x₀ * vonMisesWeight b x) volume (-π) π :=
    (intervalIntegrable_vonMisesWeight b _ _).const_mul _
  have i4 : IntervalIntegrable
      (fun x => Real.cos x₀ * vonMisesWeight b x₀ * vonMisesWeight a x) volume (-π) π :=
    (intervalIntegrable_vonMisesWeight a _ _).const_mul _
  have hexp : (∫ x in (-π)..π, g x)
      = vonMisesWeight a x₀ * Jb - vonMisesWeight b x₀ * Ja
        - Real.cos x₀ * vonMisesWeight a x₀ * Ib
        + Real.cos x₀ * vonMisesWeight b x₀ * Ia := by
    have hpt : ∀ x, g x
        = (vonMisesWeight a x₀ * (Real.cos x * vonMisesWeight b x)
            - vonMisesWeight b x₀ * (Real.cos x * vonMisesWeight a x))
          - (Real.cos x₀ * vonMisesWeight a x₀ * vonMisesWeight b x
            - Real.cos x₀ * vonMisesWeight b x₀ * vonMisesWeight a x) := by
      intro x; rw [hgdef]; ring
    rw [intervalIntegral.integral_congr (fun x _ => hpt x),
      intervalIntegral.integral_sub (i1.sub i2) (i3.sub i4),
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_sub i3 i4,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [← hIadef, ← hIbdef, ← hJadef, ← hJbdef]
    ring
  have hJa : α * Ia = Ja := div_mul_cancel₀ Ja hIa.ne'
  have hval : (∫ x in (-π)..π, g x) = vonMisesWeight a x₀ * (Jb - α * Ib) := by
    rw [hexp, hx₀]
    linear_combination vonMisesWeight b x₀ * hJa
  rw [hval] at hint
  have h2 : 0 < Jb - α * Ib := by
    rcases le_or_gt (Jb - α * Ib) 0 with h | h
    · have := mul_nonneg (vonMisesWeight_pos a x₀).le (neg_nonneg.mpr h)
      nlinarith
    · exact h
  rw [hαdef, sub_pos, div_mul_eq_mul_div, div_lt_iff₀ hIa] at h2
  linarith

/-- **`R` is strictly increasing on all of `ℝ`.** The "Monotonicity of `R`" that
the header of this file listed as not proved: the mean of `cos θ` grows strictly
with the concentration, so a more strongly coupled von Mises density is strictly
more aligned.

Note the domain: unlike `E`, this needs no sign condition on `a`, because no fold
is involved. It is *not* used by the threshold theorems — those still go through
the bounds of §5 and §6 — so nothing above depends on it; it is what makes
`coherent_branch_strictMono` available. -/
theorem besselRatio_strictMono : StrictMono besselRatio := by
  intro a b hab
  rw [besselRatio, besselRatio, div_lt_div_iff₀ (vonMisesZ_pos a) (vonMisesZ_pos b)]
  exact vonMisesM_mul_vonMisesZ_lt hab

/-! ### Uniqueness, and the branch as a function of the coupling -/

/-- **Uniqueness of the coherent solution.** For `K, D > 0` the self-consistency
equation has at most one strictly positive solution.

`coherent_iff_sRatio_eq` turns each solution into the equation
`E(K rᵢ / D) = D/K`; `vonMisesSRatio_injOn` identifies the two concentrations,
and `K, D > 0` identifies the two solutions.

**Scope.** This is uniqueness for the *fixed-point equation*, which presupposes
the von Mises stationary density — see the file header. It says nothing about
which solution a trajectory converges to: that is a dynamical selection
statement, and there is no dynamics in this file. Note also that `r = 0` always
solves the equation, so "unique" means unique among positive solutions; the full
picture is `supercritical_solution_set`. -/
theorem coherent_fixed_point_unique {K D r₁ r₂ : ℝ} (hD : 0 < D) (hK : 0 < K)
    (h1 : 0 < r₁) (h2 : 0 < r₂)
    (hf1 : r₁ = selfConsistency K D r₁) (hf2 : r₂ = selfConsistency K D r₂) :
    r₁ = r₂ := by
  have e1 := (coherent_iff_sRatio_eq hD hK h1.ne').mp hf1
  have e2 := (coherent_iff_sRatio_eq hD hK h2.ne').mp hf2
  have ha1 : K * r₁ / D ∈ Ici (0:ℝ) := by simp only [mem_Ici]; positivity
  have ha2 : K * r₂ / D ∈ Ici (0:ℝ) := by simp only [mem_Ici]; positivity
  have h := vonMisesSRatio_injOn ha1 ha2 (e1.trans e2.symm)
  field_simp at h
  exact h

/-- **Above threshold there is exactly one coherent solution**, existence from
§6 and uniqueness from `coherent_fixed_point_unique`. This is the statement the
doc-string of `supercritical_fixed_point_exists` recorded as missing. -/
theorem supercritical_fixed_point_existsUnique {K D : ℝ} (hD : 0 < D)
    (hKD : critical_coupling D < K) :
    ∃! r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency K D r := by
  have hK : 0 < K := by rw [critical_coupling] at hKD; linarith
  obtain ⟨r, hr0, hr1, hrfix⟩ := supercritical_fixed_point_exists hD hKD
  exact ⟨r, ⟨hr0, hr1, hrfix⟩,
    fun y hy => coherent_fixed_point_unique hD hK hy.1 hr0 hy.2.2 hrfix⟩

/-- **The complete solution set above threshold: exactly two points.** For
`K > 2D` there is an `r ∈ (0, 1]` such that the non-negative solutions of
`s = R(K, s)` are precisely `0` and `r`.

Below threshold `fixed_point_eq_zero_of_le_critical` says the set is `{0}`, so
the two regimes are now described exactly rather than by an existence statement
on one side and a uniqueness statement on the other. -/
theorem supercritical_solution_set {K D : ℝ} (hD : 0 < D)
    (hKD : critical_coupling D < K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ s : ℝ, 0 ≤ s → (s = selfConsistency K D s ↔ s = 0 ∨ s = r) := by
  have hK : 0 < K := by rw [critical_coupling] at hKD; linarith
  obtain ⟨r, hr0, hr1, hrfix⟩ := supercritical_fixed_point_exists hD hKD
  refine ⟨r, hr0, hr1, fun s hs => ⟨fun hfix => ?_, fun h => ?_⟩⟩
  · rcases eq_or_lt_of_le hs with h | hpos
    · exact Or.inl h.symm
    · exact Or.inr (coherent_fixed_point_unique hD hK hpos hr0 hfix hrfix)
  · rcases h with h | h
    · rw [h]; simp
    · rw [h]; exact hrfix

/-- **`K_c = 2D`, with the coherent side sharpened to uniqueness.** The
strengthening of `critical_coupling_is_threshold` that this section makes
available: at or below threshold the incoherent state is the only non-negative
solution, and strictly above it there is exactly one coherent solution. -/
theorem critical_coupling_is_threshold_unique {K D : ℝ} (hD : 0 < D) (hK : 0 ≤ K) :
    (K ≤ critical_coupling D →
      ∀ r : ℝ, 0 ≤ r → r = selfConsistency K D r → r = 0)
    ∧ (critical_coupling D < K →
      ∃! r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency K D r) :=
  ⟨fun h r hr hfix => fixed_point_eq_zero_of_le_critical (r := r) hD hK h hr hfix,
    fun h => supercritical_fixed_point_existsUnique hD h⟩

/-- The concentration of the coherent branch is strictly increasing in the
coupling: a larger `K` puts the von Mises density at a strictly larger `a`.

`E` is strictly decreasing and `E(aᵢ) = D/Kᵢ`, which falls with `K`. -/
theorem coherent_concentration_strictMono {K₁ K₂ D r₁ r₂ : ℝ} (hD : 0 < D)
    (hK₁ : 0 < K₁) (hK : K₁ < K₂) (h1 : 0 < r₁) (h2 : 0 < r₂)
    (hf1 : r₁ = selfConsistency K₁ D r₁) (hf2 : r₂ = selfConsistency K₂ D r₂) :
    K₁ * r₁ / D < K₂ * r₂ / D := by
  have hK₂ : 0 < K₂ := hK₁.trans hK
  have e1 := (coherent_iff_sRatio_eq hD hK₁ h1.ne').mp hf1
  have e2 := (coherent_iff_sRatio_eq hD hK₂ h2.ne').mp hf2
  have hlt : D / K₂ < D / K₁ := by rw [div_lt_div_iff₀ hK₂ hK₁]; nlinarith
  have ha1 : K₁ * r₁ / D ∈ Ici (0:ℝ) := by simp only [mem_Ici]; positivity
  have ha2 : K₂ * r₂ / D ∈ Ici (0:ℝ) := by simp only [mem_Ici]; positivity
  by_contra hcon
  rw [not_lt] at hcon
  have := vonMisesSRatio_strictAntiOn.antitoneOn ha2 ha1 hcon
  rw [e1, e2] at this
  linarith

/-- **The coherent order parameter is strictly increasing in the coupling.**
Both halves of the section are needed: `E` strictly decreasing to move the
concentration, `R` strictly increasing to move the order parameter with it.

With `coherent_fixed_point_unique` this says the coherent branch is a strictly
increasing function of `K` on `(2D, ∞)` — the qualitative shape of the
bifurcation diagram, of which `coherent_branch_continuous_at_threshold` gave the
behaviour at the left endpoint.

**Scope.** Still a statement about solutions of the fixed-point equation, not
about trajectories, and it presupposes that both couplings admit a positive
solution (which `supercritical_fixed_point_exists` supplies above threshold). -/
theorem coherent_branch_strictMono {K₁ K₂ D r₁ r₂ : ℝ} (hD : 0 < D)
    (hK₁ : 0 < K₁) (hK : K₁ < K₂) (h1 : 0 < r₁) (h2 : 0 < r₂)
    (hf1 : r₁ = selfConsistency K₁ D r₁) (hf2 : r₂ = selfConsistency K₂ D r₂) :
    r₁ < r₂ := by
  have ha := coherent_concentration_strictMono hD hK₁ hK h1 h2 hf1 hf2
  calc r₁ = besselRatio (K₁ * r₁ / D) := hf1
    _ < besselRatio (K₂ * r₂ / D) := besselRatio_strictMono ha
    _ = r₂ := hf2.symm

section PhaseTransitionUnique

variable {M : Type*} [MeasureSpace M] [TopologicalSpace M]

/-- **A substrate above threshold has exactly one coherent order parameter.**
`exhibits_phase_transition_coherent` produced one; this says there is no second.

**Scope.** Unchanged from that theorem: the solution is a fixed point of
`selfConsistency`, which rests on the von Mises stationary density, and the link
to `is_continuous_kuramoto_trajectory` is still missing. -/
theorem exhibits_phase_transition_unique_coherent
    [IsProbabilityMeasure (volume : Measure M)]
    (sys : StochasticNeuralField M) (h : exhibits_phase_transition sys) :
    ∃! r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency (mean_field_coupling sys) sys.D r :=
  supercritical_fixed_point_existsUnique sys.h_D_pos h

end PhaseTransitionUnique

/-! ## 8. The density, and why the equation deserves its name

Everything above treats `selfConsistency K D r = besselRatio (K * r / D)` as a
function of `r` and asks when it has fixed points. Nothing above says it is a
*self-consistency* condition — as a Lean definition it could be any function at
all, and the reading "`r` is the mean of `cos θ` under the density that `r`
itself induces" lives only in the doc-strings.

This section supplies the missing identification. `vonMisesDensity a` is the
normalized weight, a genuine probability density on `[-π, π]`;
`circularOrderParameter` is the continuum analogue of `Phase4`'s
`order_parameter_complex`, the average of `e^{iθ}` — over a density here rather
than over finitely many oscillators. The content is
`circularOrderParameter_vonMises`: that average is exactly `besselRatio a`, real
because the density is even. `fixedPoint_iff_selfReproducing` then says a fixed
point of `selfConsistency` is precisely a density that reproduces its own order
parameter, which is what self-consistency means.

Two things this does *not* do. It does not link `circularOrderParameter` to
`order_parameter_complex`: that one is the empirical average `(1/N) ∑ e^{iθⱼ}`
over a finite system, and relating the two is the mean-field limit, not a lemma.
And it says nothing about any trajectory. -/

/-- The von Mises probability density at concentration `a`: the weight of §1
divided by its own partition function. -/
noncomputable def vonMisesDensity (a θ : ℝ) : ℝ := vonMisesWeight a θ / vonMisesZ a

theorem vonMisesDensity_pos (a θ : ℝ) : 0 < vonMisesDensity a θ :=
  div_pos (vonMisesWeight_pos a θ) (vonMisesZ_pos a)

theorem intervalIntegrable_vonMisesDensity (a c d : ℝ) :
    IntervalIntegrable (vonMisesDensity a) volume c d :=
  ((continuous_vonMisesWeight a).div_const _).intervalIntegrable c d

/-- It is a probability density: positive, and of total mass `1` on `[-π, π]`.
Without this the "mean of `cos θ` under the density" reading would be an abuse
of language. -/
theorem vonMisesDensity_integral_eq_one (a : ℝ) :
    ∫ θ in (-π)..π, vonMisesDensity a θ = 1 := by
  unfold vonMisesDensity
  rw [intervalIntegral.integral_div]
  exact div_self (vonMisesZ_pos a).ne'

/-- At zero concentration the density is uniform. This is the incoherent state,
and it is the density the fixed point `r = 0` induces. -/
@[simp] theorem vonMisesDensity_zero (θ : ℝ) : vonMisesDensity 0 θ = 1 / (2 * π) := by
  simp [vonMisesDensity, vonMisesWeight, vonMisesZ_zero]

/-- `E_a[cos θ] = R(a)`. The Bessel ratio of §3, read as a mean rather than as a
ratio of integrals. -/
theorem vonMises_mean_cos (a : ℝ) :
    ∫ θ in (-π)..π, Real.cos θ * vonMisesDensity a θ = besselRatio a := by
  unfold vonMisesDensity besselRatio vonMisesM
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  ring

lemma sin_density_neg (a x : ℝ) :
    Real.sin (-x) * vonMisesDensity a (-x) = -(Real.sin x * vonMisesDensity a x) := by
  simp [vonMisesDensity, vonMisesWeight, Real.cos_neg, Real.sin_neg]

/-- `E_a[sin θ] = 0`: the density is even, so its mean direction is `0` and the
order parameter is real. -/
theorem vonMises_mean_sin (a : ℝ) :
    ∫ θ in (-π)..π, Real.sin θ * vonMisesDensity a θ = 0 := by
  have hint : ∀ c d : ℝ, IntervalIntegrable
      (fun θ => Real.sin θ * vonMisesDensity a θ) volume c d := fun c d =>
    (Real.continuous_sin.mul
      ((continuous_vonMisesWeight a).div_const _)).intervalIntegrable c d
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := -π) (b := (0:ℝ)) (c := π) (hint _ _) (hint _ _)
  have hneg := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := π)
    (f := fun θ => Real.sin θ * vonMisesDensity a θ)
  simp only [sin_density_neg, intervalIntegral.integral_neg, neg_zero] at hneg
  linarith [hadd, hneg]

/-- The order parameter of a density on the circle: the average of `e^{iθ}`.

This is the continuum analogue of `Phase4_KuramotoDynamics.order_parameter_complex`,
which averages `e^{iθⱼ}` over finitely many oscillators. **No theorem in this
development relates the two** — that relation is the mean-field limit. -/
noncomputable def circularOrderParameter (rho : ℝ → ℝ) : ℂ :=
  ∫ θ in (-π)..π, Complex.exp (Complex.I * θ) * (rho θ : ℂ)

/-- **The Bessel ratio is an order parameter.** The average of `e^{iθ}` under the
von Mises density of concentration `a` is exactly `R(a)` — real, because the
density is even (`vonMises_mean_sin`), and equal to `E_a[cos θ]`
(`vonMises_mean_cos`). -/
theorem circularOrderParameter_vonMises (a : ℝ) :
    circularOrderParameter (vonMisesDensity a) = (besselRatio a : ℂ) := by
  have hfun : ∀ θ : ℝ, Complex.exp (Complex.I * θ) * (vonMisesDensity a θ : ℂ)
      = ((Real.cos θ * vonMisesDensity a θ : ℝ) : ℂ)
        + ((Real.sin θ * vonMisesDensity a θ : ℝ) : ℂ) * Complex.I := by
    intro θ
    rw [mul_comm Complex.I, Complex.exp_mul_I]
    push_cast
    ring
  have hc : IntervalIntegrable
      (fun θ => ((Real.cos θ * vonMisesDensity a θ : ℝ) : ℂ)) volume (-π) π := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold vonMisesDensity vonMisesWeight; fun_prop
  have hs : IntervalIntegrable
      (fun θ => ((Real.sin θ * vonMisesDensity a θ : ℝ) : ℂ) * Complex.I) volume (-π) π := by
    refine Continuous.intervalIntegrable ?_ _ _
    unfold vonMisesDensity vonMisesWeight; fun_prop
  unfold circularOrderParameter
  rw [intervalIntegral.integral_congr (g := fun θ =>
        ((Real.cos θ * vonMisesDensity a θ : ℝ) : ℂ)
          + ((Real.sin θ * vonMisesDensity a θ : ℝ) : ℂ) * Complex.I)
      (fun θ _ => hfun θ),
    intervalIntegral.integral_add hc hs, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    vonMises_mean_cos, vonMises_mean_sin]
  simp

theorem selfConsistency_eq_orderParameter (K D r : ℝ) :
    ((selfConsistency K D r : ℝ) : ℂ)
      = circularOrderParameter (vonMisesDensity (K * r / D)) := by
  rw [circularOrderParameter_vonMises, selfConsistency]

/-- **The equation deserves its name.** `r` solves `r = R(K, r)` exactly when the
von Mises density it induces, at concentration `K r / D`, has order parameter
`r`. This is the statement the whole file has been *about*; until now it was in
the doc-strings only. -/
theorem fixedPoint_iff_selfReproducing (K D r : ℝ) :
    r = selfConsistency K D r
      ↔ circularOrderParameter (vonMisesDensity (K * r / D)) = (r : ℂ) := by
  constructor
  · intro h; rw [← selfConsistency_eq_orderParameter, ← h]
  · intro h; rw [← selfConsistency_eq_orderParameter] at h; exact_mod_cast h.symm

/-- The incoherent solution, read through the density: `r = 0` induces the
uniform density, whose order parameter is `0`. -/
theorem incoherent_density_uniform (K D : ℝ) :
    (∀ θ, vonMisesDensity (K * 0 / D) θ = 1 / (2 * π))
      ∧ circularOrderParameter (vonMisesDensity (K * 0 / D)) = 0 := by
  refine ⟨fun θ => by simp, by simp [circularOrderParameter_vonMises]⟩

/-- **The supercritical theorem, restated as physics.** Above threshold there is
a von Mises density whose own order parameter is positive — a coherent
stationary state, rather than a fixed point of an unexplained function.

Still an existence statement about a *density*, not about a trajectory; see the
file header. -/
theorem supercritical_coherent_density {K D : ℝ} (hD : 0 < D)
    (hKD : critical_coupling D < K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      circularOrderParameter (vonMisesDensity (K * r / D)) = (r : ℂ) := by
  obtain ⟨r, hr0, hr1, hfix⟩ := supercritical_fixed_point_exists hD hKD
  exact ⟨r, hr0, hr1, (fixedPoint_iff_selfReproducing K D r).mp hfix⟩

/-! ## 9. Non-vacuity

The uniqueness theorem quantifies over solutions of `r = R(K, r)`; if that
equation had no solutions it would be an empty statement, so we exhibit one and
check that the theorem returns it. The existence theorem has the opposite
failure mode — vacuous hypotheses — so we discharge those at a concrete `K` and
`D` too, on both sides of the threshold and in both readings of the equation. -/

/-- The incoherent state solves the self-consistency equation. -/
example (K D : ℝ) : (0 : ℝ) = selfConsistency K D 0 := (selfConsistency_zero K D).symm

/-- Below threshold, the theorem applied to that solution returns `0` — and the
hypotheses are all dischargeable, so the theorem fires. -/
example : (0 : ℝ) = 0 :=
  subcritical_fixed_point_eq_zero' (K := 1) (D := 1) (r := 0) one_pos zero_le_one
    (by rw [critical_coupling]; norm_num) le_rfl (selfConsistency_zero 1 1).symm

/-- Above threshold the hypotheses are dischargeable as well: at `D = 1`,
`K = 3` exceeds `critical_coupling 1 = 2`, and a coherent solution exists. -/
example : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency 3 1 r :=
  supercritical_fixed_point_exists one_pos (by rw [critical_coupling]; norm_num)

/-- The same `K` is subcritical for a noisier substrate: at `D = 2`,
`critical_coupling 2 = 4 > 3`, and only the incoherent state survives. Together
with the previous example this shows the threshold separates two genuinely
different regimes rather than always falling on one side. -/
example (r : ℝ) (hr : 0 ≤ r) (hfix : r = selfConsistency 3 2 r) : r = 0 :=
  subcritical_fixed_point_eq_zero' (by norm_num) (by norm_num)
    (by rw [critical_coupling]; norm_num) hr hfix

/-- **The threshold case fires, and is not vacuous.** At `D = 1`, `K = 2` sits
exactly on `critical_coupling 1 = 2` — the case neither older theorem covered —
and the only non-negative solution is the incoherent one. -/
example (r : ℝ) (hr : 0 ≤ r) (hfix : r = selfConsistency 2 1 r) : r = 0 :=
  fixed_point_eq_zero_of_le_critical (by norm_num) (by norm_num)
    (by rw [critical_coupling]; norm_num) hr hfix

/-- The strict bound it rests on is not vacuous either: `R(1) < 1/2`. -/
example : besselRatio 1 < 1 / 2 := by
  simpa using besselRatio_lt_half_self (a := 1) one_pos

/-- The no-jump statement, instantiated: at `D = 1` there is a band above the
threshold on which every coherent solution is smaller than `1/10`. -/
example : ∃ δ : ℝ, 0 < δ ∧ ∀ K r : ℝ, critical_coupling 1 < K →
    K < critical_coupling 1 + δ → 0 < r → r = selfConsistency K 1 r → r < 1 / 10 :=
  coherent_branch_continuous_at_threshold one_pos (by norm_num)

/-- The level-set reading, on the supercritical solution of the example above:
its concentration is where the mean of `sin²` equals `D/K`. -/
example : ∃ r : ℝ, 0 < r ∧ vonMisesSRatio (3 * r / 1) = 1 / 3 := by
  obtain ⟨r, hrpos, _, hfix⟩ :=
    supercritical_fixed_point_exists (D := 1) (K := 3) one_pos (by rw [critical_coupling]; norm_num)
  exact ⟨r, hrpos, (coherent_iff_sRatio_eq one_pos (by norm_num) (ne_of_gt hrpos)).mp hfix⟩

/-- The same statement read through §8: at `D = 1`, `K = 3` there is a von Mises
density whose own order parameter is positive. -/
example : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    circularOrderParameter (vonMisesDensity (3 * r / 1)) = (r : ℂ) :=
  supercritical_coherent_density one_pos (by rw [critical_coupling]; norm_num)

/-- §7 is not vacuous either: `E` is strictly decreasing, witnessed on a concrete
pair of concentrations. -/
example : vonMisesSRatio 2 < vonMisesSRatio 1 :=
  vonMisesSRatio_strictAntiOn (by norm_num) (by norm_num) (by norm_num)

/-- And `R` is strictly increasing, on the same pair. -/
example : besselRatio 1 < besselRatio 2 := besselRatio_strictMono (by norm_num)

/-- **Uniqueness fires at a concrete coupling.** At `D = 1`, `K = 3` the coherent
solution exists and is the only positive one. -/
example : ∃! r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency 3 1 r :=
  supercritical_fixed_point_existsUnique one_pos (by rw [critical_coupling]; norm_num)

/-- The complete solution set at that coupling: the non-negative solutions are
exactly two. -/
example : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    ∀ s : ℝ, 0 ≤ s → (s = selfConsistency 3 1 s ↔ s = 0 ∨ s = r) :=
  supercritical_solution_set one_pos (by rw [critical_coupling]; norm_num)

/-- **The branch really moves.** At `D = 1` the coherent solutions at `K = 3` and
`K = 4` both exist and are *strictly* ordered — so `coherent_branch_strictMono`
is not a statement about an empty or constant family. -/
example : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ 0 < r₂ ∧ r₁ = selfConsistency 3 1 r₁
    ∧ r₂ = selfConsistency 4 1 r₂ ∧ r₁ < r₂ := by
  obtain ⟨r₁, h₁, _, hf₁⟩ := supercritical_fixed_point_exists (D := 1) (K := 3)
    one_pos (by rw [critical_coupling]; norm_num)
  obtain ⟨r₂, h₂, _, hf₂⟩ := supercritical_fixed_point_exists (D := 1) (K := 4)
    one_pos (by rw [critical_coupling]; norm_num)
  exact ⟨r₁, r₂, h₁, h₂, hf₁, hf₂,
    coherent_branch_strictMono one_pos (by norm_num) (by norm_num) h₁ h₂ hf₁ hf₂⟩

end PhysicsOfConsciousness
