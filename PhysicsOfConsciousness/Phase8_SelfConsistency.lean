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

`subcritical_fixed_point_eq_zero` and `besselRatio_le_self` are the crude
versions of the last two, obtained from the pointwise bound `sin² ≤ 1` alone.
They are kept because they isolate where the factor of two comes from: the
entire difference between a threshold at `D` and the physical one at `2D` is the
sharpening of `sin² ≤ 1` to its *mean* value under the von Mises weight.

## What is NOT proved here

**The supercritical direction.** That a positive solution branches off for
`K > 2D` does not follow from anything above. It needs a *lower* bound on `R`
near the origin — a second-order expansion of the Bessel ratio — rather than the
single monotonicity argument used here, so the results above establish that
`2D` is an upper bound on where coherence can begin, not that coherence begins
there.

**The ansatz.** Nothing here derives the von Mises stationary density from the
SDE `dθ = (ω + K·mean-field) dt + √(2D) dW`. That needs the Fokker–Planck
operator, existence and uniqueness of its stationary solution, and a spectral
stability argument, none of which Mathlib has. The density is an input to this
file, not an output of it.

**The dynamics.** `selfConsistency` is not connected to
`is_continuous_kuramoto_trajectory`, `order_parameter_r_sq` or
`entropy_production_rate`. What is now a theorem is a statement about the
self-consistency equation; `exhibits_phase_transition` still stands on the
ansatz, and Table 1 of the manuscript accordingly still reads "Numerical" for
this row.
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

This is the sharp form of `subcritical_fixed_point_eq_zero`, and the sense in
which `critical_coupling D = 2 * D` of `Phase8_ContinuousField.lean` is the
right number: below it, no coherent stationary order parameter exists. The
converse — that a positive solution *does* branch off for `K > 2D` — is not
proved here; it needs a lower bound on `R` near the origin (a second-order
expansion of the Bessel ratio) rather than the single monotonicity argument
used above. -/
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


/-! ## 6. Non-vacuity

The uniqueness theorems above quantify over solutions of `r = R(K, r)`. If that
equation had no solutions they would be empty statements, so we exhibit one, and
check that the sharp theorem then returns it. -/

/-- The incoherent state solves the self-consistency equation. -/
example (K D : ℝ) : (0 : ℝ) = selfConsistency K D 0 := (selfConsistency_zero K D).symm

/-- Below threshold, the theorem applied to that solution returns `0` — and the
hypotheses are all dischargeable, so the theorem fires. -/
example : (0 : ℝ) = 0 :=
  subcritical_fixed_point_eq_zero' (K := 1) (D := 1) (r := 0) one_pos zero_le_one
    (by rw [critical_coupling]; norm_num) le_rfl (selfConsistency_zero 1 1).symm

end PhysicsOfConsciousness
