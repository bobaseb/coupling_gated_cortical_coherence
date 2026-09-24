import PhysicsOfConsciousness.Phase8_FokkerPlanck
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Current cost with the observable's second moment retained

The spatial inequality is a first step toward the magnitude-speed bound in G22.
It does not identify a time derivative of circular order or prove an arcsine
endpoint bound. No conversion of probability-current cost to heat is assumed.
-/

open Real MeasureTheory intervalIntegral Set
namespace PhysicsOfConsciousness.FokkerPlanck

/-- Weighted Cauchy--Schwarz for the density's own current. Unlike the bounded
observable estimate, this retains the second moment. Positivity and continuity
are spatial assumptions; no evolving density or physical heat law is supplied. -/
theorem weighted_current_variance_bound {D : ℝ} (hD : 0 < D) {v ρ g : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ θ, 0 < ρ θ)
    (hJ : Continuous (current D v ρ)) (hg : Continuous g) :
    (∫ θ in (-π)..π, g θ * current D v ρ θ) ^ 2 ≤
      D * currentDissipation D v ρ * (∫ θ in (-π)..π, g θ ^ 2 * ρ θ) := by
  let m := ∫ θ in (-π)..π, g θ * current D v ρ θ
  let q := ∫ θ in (-π)..π, current D v ρ θ ^ 2 / ρ θ
  let s := ∫ θ in (-π)..π, g θ ^ 2 * ρ θ
  have hq : IntervalIntegrable (fun θ => current D v ρ θ ^ 2 / ρ θ) volume (-π) π := ((hJ.pow 2).div hρ (fun θ => (hpos θ).ne')).intervalIntegrable (-π) π
  have hs : IntervalIntegrable (fun θ => g θ ^ 2 * ρ θ) volume (-π) π := ((hg.pow 2).mul hρ).intervalIntegrable (-π) π
  have hm : IntervalIntegrable (fun θ => g θ * current D v ρ θ) volume (-π) π := (hg.mul hJ).intervalIntegrable (-π) π
  have hpoly (c : ℝ) : 0 ≤ s * (c * c) + (-2 * m) * c + q := by
    have hexpand : (∫ θ in (-π)..π, (current D v ρ θ - c * g θ * ρ θ) ^ 2 / ρ θ) =
        q - 2 * c * m + c ^ 2 * s := by
      have heq : (fun θ => (current D v ρ θ - c * g θ * ρ θ) ^ 2 / ρ θ) =
          fun θ => current D v ρ θ ^ 2 / ρ θ - 2 * c * (g θ * current D v ρ θ) +
            c ^ 2 * (g θ ^ 2 * ρ θ) := by
        funext θ
        field_simp [(hpos θ).ne']
        ring
      rw [heq, intervalIntegral.integral_add (hq.sub (hm.const_mul _)) (hs.const_mul _),
        intervalIntegral.integral_sub hq (hm.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hn : 0 ≤ ∫ θ in (-π)..π, (current D v ρ θ - c * g θ * ρ θ) ^ 2 / ρ θ :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
        (fun θ _ => div_nonneg (sq_nonneg _) (hpos θ).le)
    rw [hexpand] at hn
    nlinarith
  have hd := discrim_le_zero hpoly
  have hscale : D * currentDissipation D v ρ = q := by
    rw [currentDissipation, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp
    field_simp
  rw [hscale]
  change m ^ 2 ≤ q * s
  unfold discrim at hd
  nlinarith

/-- The squared mean of a continuous observable is bounded by its second
moment under a normalized positive density. This supplies no time regularity. -/
lemma moment_sq_le_second {ρ f : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ θ, 0 < ρ θ) (hnorm : (∫ θ in (-π)..π, ρ θ) = 1)
    (hf : Continuous f) :
    (∫ θ in (-π)..π, f θ * ρ θ) ^ 2 ≤ ∫ θ in (-π)..π, f θ ^ 2 * ρ θ := by
  let m := ∫ θ in (-π)..π, f θ * ρ θ
  have hi : IntervalIntegrable (fun θ => f θ ^ 2 * ρ θ) volume (-π) π :=
    ((hf.pow 2).mul hρ).intervalIntegrable _ _
  have hm : IntervalIntegrable (fun θ => 2 * m * (f θ * ρ θ)) volume (-π) π :=
    ((hf.mul hρ).const_mul _).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun θ => m ^ 2 * ρ θ) volume (-π) π :=
    (hρ.const_mul _).intervalIntegrable _ _
  have hn : 0 ≤ ∫ θ in (-π)..π, (f θ - m) ^ 2 * ρ θ :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
      (fun θ _ => mul_nonneg (sq_nonneg _) (hpos θ).le)
  have heq : (fun θ => (f θ - m) ^ 2 * ρ θ) =
      fun θ => f θ ^ 2 * ρ θ - 2 * m * (f θ * ρ θ) + m ^ 2 * ρ θ := by
    funext θ; ring
  rw [heq, intervalIntegral.integral_add (hi.sub hm) hc,
    intervalIntegral.integral_sub hi hm, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hnorm] at hn
  change m ^ 2 ≤ _
  nlinarith

/-- In any chosen angular direction the sine-weighted current pays the factor
one minus squared cosine mean. Choosing the instantaneous mean direction is
allowed spatially; identifying this flux with the derivative of order magnitude
still requires the continuity equation and differentiation under the integral. -/
theorem directional_current_order_bound {D : ℝ} (hD : 0 < D) {v ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ θ, 0 < ρ θ)
    (hnorm : (∫ θ in (-π)..π, ρ θ) = 1)
    (hJ : Continuous (current D v ρ)) (φ : ℝ) :
    (∫ θ in (-π)..π, Real.sin (θ - φ) * current D v ρ θ) ^ 2 ≤
      D * currentDissipation D v ρ *
        (1 - (∫ θ in (-π)..π, Real.cos (θ - φ) * ρ θ) ^ 2) := by
  have hs : Continuous (fun θ => Real.sin (θ - φ)) :=
    Real.continuous_sin.comp (continuous_id.sub continuous_const)
  have hc : Continuous (fun θ => Real.cos (θ - φ)) :=
    Real.continuous_cos.comp (continuous_id.sub continuous_const)
  have hcs := moment_sq_le_second hρ hpos hnorm hc
  have hsum : (∫ θ in (-π)..π, Real.sin (θ - φ) ^ 2 * ρ θ) +
      (∫ θ in (-π)..π, Real.cos (θ - φ) ^ 2 * ρ θ) = 1 := by
    have his : IntervalIntegrable (fun θ => Real.sin (θ - φ) ^ 2 * ρ θ)
        volume (-π) π := ((hs.pow 2).mul hρ).intervalIntegrable _ _
    have hic : IntervalIntegrable (fun θ => Real.cos (θ - φ) ^ 2 * ρ θ)
        volume (-π) π := ((hc.pow 2).mul hρ).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add his hic]
    simp_rw [← add_mul, Real.sin_sq_add_cos_sq, one_mul]
    exact hnorm
  have hnonneg : 0 ≤ D * currentDissipation D v ρ := by
    apply mul_nonneg hD.le
    apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    intro θ _
    exact div_nonneg (sq_nonneg _) (mul_pos hD (hpos θ)).le
  exact (weighted_current_variance_bound hD hρ hpos hJ hs).trans
    (mul_le_mul_of_nonneg_left (by linarith) hnonneg)

/-- Mixing two positive density cohorts cannot increase their quadratic
current cost: the cost of the mean current under the mean density is bounded
by the mean of cohort costs. This is pointwise algebra for a common diffusion
constant, not a heat theorem or a bound for frequency-resolved observations. -/
theorem two_cohort_current_cost_le {D ρ₁ ρ₂ J₁ J₂ : ℝ}
    (hD : 0 < D) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) :
    ((J₁ + J₂) / 2) ^ 2 / (D * ((ρ₁ + ρ₂) / 2)) ≤
      (J₁ ^ 2 / (D * ρ₁) + J₂ ^ 2 / (D * ρ₂)) / 2 := by
  have hcore : (J₁ + J₂) ^ 2 / (ρ₁ + ρ₂) ≤
      J₁ ^ 2 / ρ₁ + J₂ ^ 2 / ρ₂ := by
    field_simp [ne_of_gt hρ₁, ne_of_gt hρ₂, ne_of_gt (add_pos hρ₁ hρ₂)]
    nlinarith [sq_nonneg (J₁ * ρ₂ - J₂ * ρ₁)]
  have hscale : 0 ≤ 1 / (2 * D) := by positivity
  calc
    ((J₁ + J₂) / 2) ^ 2 / (D * ((ρ₁ + ρ₂) / 2)) =
        (1 / (2 * D)) * ((J₁ + J₂) ^ 2 / (ρ₁ + ρ₂)) := by
          field_simp [ne_of_gt hD, ne_of_gt (add_pos hρ₁ hρ₂)]
    _ ≤ (1 / (2 * D)) * (J₁ ^ 2 / ρ₁ + J₂ ^ 2 / ρ₂) :=
      mul_le_mul_of_nonneg_left hcore hscale
    _ = (J₁ ^ 2 / (D * ρ₁) + J₂ ^ 2 / (D * ρ₂)) / 2 := by
      field_simp [ne_of_gt hD, ne_of_gt hρ₁, ne_of_gt hρ₂]

#print axioms directional_current_order_bound
#print axioms weighted_current_variance_bound
#print axioms two_cohort_current_cost_le
end PhysicsOfConsciousness.FokkerPlanck
