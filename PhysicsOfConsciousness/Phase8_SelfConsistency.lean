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
* `critical_coupling_is_threshold` — the two halves packaged: below `2D` the
  incoherent state is the only solution, above it a coherent one exists.
* `exhibits_phase_transition_coherent` — a substrate satisfying
  `exhibits_phase_transition` of `Phase8_ContinuousField.lean` admits a positive
  stationary order parameter. This is what stops `critical_coupling` from being
  an inert stipulation: exceeding it now *implies* something.
* `circularOrderParameter_vonMises` and `fixedPoint_iff_selfReproducing` — §7.
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

**Anything about the coherent branch beyond its existence.**
`supercritical_fixed_point_exists` produces *some* `r ∈ (0, 1]`; it does not
prove that it is unique, that it is the dynamically selected one, or that it
depends continuously on `K` — so nothing here rules out a discontinuous jump at
threshold rather than the continuous (supercritical) bifurcation the physics
literature describes. At `K = 2D` exactly, neither theorem applies.

**Monotonicity of `R`.** The argument uses `R(a) ≤ a/2` globally but only
`R(a) ≥ a·(1/2 - o(1))` near `a = 0`; `R` is never shown increasing, which is
why the coherent solution is found by the intermediate value theorem rather than
by iterating the map.

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

/-- **`I₂(a) ≥ 0`.** The second moment of the von Mises weight is non-negative
for every non-negative concentration. -/
theorem vonMisesC2_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ vonMisesC2 a := by
  have hpi := Real.pi_pos
  rw [vonMisesC2_eq_two_mul, integral_c2_eq_foldA, integral_foldA_eq_foldB]
  have : 0 ≤ ∫ x in (0:ℝ)..(π/4), foldB a x :=
    intervalIntegral.integral_nonneg (by linarith) (fun x hx => foldB_nonneg ha hx)
  linarith

/-- **The sharp bound.** Under the von Mises weight the mean of `sin²` is at
most `1/2` — the pointwise bound `sin² ≤ 1` of `vonMisesS_le_vonMisesZ` loses
exactly a factor of two, and this recovers it. -/
theorem vonMisesS_le_half_vonMisesZ {a : ℝ} (ha : 0 ≤ a) :
    vonMisesS a ≤ vonMisesZ a / 2 := by
  rw [vonMisesS_eq]
  linarith [vonMisesC2_nonneg ha]

/-- `R(a) ≤ a/2` — the slope of the Bessel ratio at the origin, as an upper
bound for all `a ≥ 0`. This is what puts the threshold at `2D` rather than
`D`. -/
theorem besselRatio_le_half_self {a : ℝ} (ha : 0 ≤ a) : besselRatio a ≤ a / 2 := by
  rw [besselRatio, vonMisesM_eq_mul_vonMisesS, div_le_iff₀ (vonMisesZ_pos a)]
  nlinarith [mul_le_mul_of_nonneg_left (vonMisesS_le_half_vonMisesZ ha) ha,
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

**What it does not establish.** Existence, not uniqueness: nothing here says the
positive solution is unique, that it is the dynamically selected branch, or that
it varies continuously with `K`, so a discontinuous jump at threshold is not
excluded. The case `K = 2D` is untouched by this theorem and by the subcritical
one. And the von Mises density remains an input — see the file header. -/
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

/-- **`K_c = 2D` for the self-consistency equation**, both halves in one
statement: strictly below the threshold the incoherent state is the only
non-negative solution, strictly above it a coherent one exists.

The threshold itself, `K = critical_coupling D`, is not covered — neither half
applies there. The von Mises ansatz is assumed throughout; see the file
header. -/
theorem critical_coupling_is_threshold {K D : ℝ} (hD : 0 < D) (hK : 0 ≤ K) :
    (K < critical_coupling D →
      ∀ r : ℝ, 0 ≤ r → r = selfConsistency K D r → r = 0)
    ∧ (critical_coupling D < K →
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency K D r) :=
  ⟨fun h r hr hfix => subcritical_fixed_point_eq_zero' (r := r) hD hK h hr hfix,
    fun h => supercritical_fixed_point_exists hD h⟩

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

/-! ## 7. The density, and why the equation deserves its name

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

/-! ## 8. Non-vacuity

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

/-- The same statement read through §7: at `D = 1`, `K = 3` there is a von Mises
density whose own order parameter is positive. -/
example : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    circularOrderParameter (vonMisesDensity (3 * r / 1)) = (r : ℂ) :=
  supercritical_coherent_density one_pos (by rw [critical_coupling]; norm_num)

end PhysicsOfConsciousness
