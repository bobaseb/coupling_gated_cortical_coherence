import PhysicsOfConsciousness.Phase8_CircleForm

/-!
# A weighted Poincaré estimate on the circle

The primitive of a zero-mass density perturbation is fixed by requiring its
mean against `1/q` to vanish. The fundamental theorem of calculus and weighted
Cauchy–Schwarz bound its squared norm by the density perturbation's squared
norm. The constant is finite and explicit, although not sharp. No Poincaré or
spectral-gap assumption is introduced.
-/

open Real MeasureTheory intervalIntegral Set

namespace PhysicsOfConsciousness.FokkerPlanck

noncomputable def inverseDensity (a : ℝ) : CircleFunction :=
  ⟨fun θ => 1 / vonMisesDensity a θ,
    continuous_const.div (density a).continuous (fun θ => (vonMisesDensity_pos a θ).ne')⟩

noncomputable def inverseAverage (a : ℝ) : CircleFunction →ₗ[ℝ] ℝ :=
  weightedIntegral (-π) π (inverseDensity a)

@[simp] lemma density_mul_inverse (a : ℝ) : density a * inverseDensity a = 1 := by
  ext θ
  change vonMisesDensity a θ * (1 / vonMisesDensity a θ) = 1
  exact mul_one_div_cancel (vonMisesDensity_pos a θ).ne'

lemma inverseAverage_square_nonneg (a : ℝ) (f : CircleFunction) :
    0 ≤ inverseAverage a (f * f) :=
  weightedIntegral_square_nonneg (by linarith [pi_pos]) (inverseDensity a) f
    (fun θ _ => (one_div_pos.mpr (vonMisesDensity_pos a θ)).le)

/-- A periodic primitive makes the density perturbation mass preserving.
Zero mass is thus derived in the operator estimate, not a second premise. -/
lemma primitive_mass_zero (a : ℝ) (U f : CircleFunction)
    (hU : ∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ)
    (hp : U (-π) = U π) : average a f = 0 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -π) (b := π) (fun θ _ => hU θ)
    (((density a).continuous.mul f.continuous).intervalIntegrable _ _)
  rw [hp, sub_self] at hi
  change (∫ θ in (-π)..π, f θ * vonMisesDensity a θ) = 0
  simpa only [mul_comm] using hi

lemma inverseAverage_odd (a : ℝ) (f : CircleFunction) (hf : ∀ θ, f (-θ) = -f θ) :
    inverseAverage a f = 0 := by
  let g := fun θ => f θ * (1 / vonMisesDensity a θ)
  have hg : Continuous g := f.continuous.mul (inverseDensity a).continuous
  have ho : (fun θ => g (-θ)) = fun θ => -g θ := by
    funext θ
    dsimp [g]
    rw [hf]
    simp [vonMisesDensity, vonMisesWeight]
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (-π) 0) (hg.intervalIntegrable 0 π)
  have hn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := π) (f := g)
  rw [ho, intervalIntegral.integral_neg] at hn
  simp only [neg_zero] at hn
  change (∫ θ in (-π)..π, g θ) = 0
  linarith

theorem inverseAverage_one_pos (a : ℝ) : 0 < inverseAverage a 1 := by
  change 0 < ∫ θ in (-π)..π, 1 * (1 / vonMisesDensity a θ)
  simp only [one_mul]
  exact intervalIntegral.integral_pos (by linarith [pi_pos])
    (inverseDensity a).continuous.continuousOn
    (fun θ _ => (one_div_pos.mpr (vonMisesDensity_pos a θ)).le)
    ⟨0, by constructor <;> linarith [pi_pos], one_div_pos.mpr (vonMisesDensity_pos a 0)⟩

lemma average_abs_sq_bound (a : ℝ) (f : CircleFunction) :
    (∫ θ in (-π)..π, |vonMisesDensity a θ * f θ|) ^ 2 ≤ average a (f * f) := by
  let af : CircleFunction := ⟨fun θ => |f θ|, f.continuous.abs⟩
  have hc := average_cauchy a af 1
  simp only [mul_one, average_one] at hc
  have he : af * af = f * f := by
    ext θ
    change |f θ| * |f θ| = f θ * f θ
    nlinarith [sq_abs (f θ)]
  rw [he] at hc
  have hi : (∫ θ in (-π)..π, |vonMisesDensity a θ * f θ|) = average a af := by
    apply intervalIntegral.integral_congr
    intro θ _
    change |vonMisesDensity a θ * f θ| = |f θ| * vonMisesDensity a θ
    rw [abs_mul, abs_of_pos (vonMisesDensity_pos a θ), mul_comm]
  rwa [hi]

/-- The anchored primitive is pointwise controlled by the full weighted
density norm. This estimate uses the declared derivative on the entire
interval; it is not a regularity or evolution existence theorem. -/
theorem primitive_pointwise_bound (a : ℝ) (U f : CircleFunction)
    (hU : ∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ)
    {θ : ℝ} (hθ : θ ∈ Icc (-π) π) :
    (U θ - U (-π)) ^ 2 ≤ average a (f * f) := by
  have hc : Continuous (fun x => vonMisesDensity a x * f x) :=
    (density a).continuous.mul f.continuous
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -π) (b := θ) (fun x _ => hU x) (hc.intervalIntegrable _ _)
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun x =>
    vonMisesDensity a x * f x) hθ.1
  rw [hi] at hn
  simp only [Real.norm_eq_abs] at hn
  have hm := intervalIntegral.integral_mono_interval (μ := volume)
    (a := -π) (b := θ) (c := -π) (d := π) le_rfl hθ.1 hθ.2
    (Filter.Eventually.of_forall (fun x => abs_nonneg (vonMisesDensity a x * f x)))
    (hc.abs.intervalIntegrable _ _)
  have hb := hn.trans hm
  have hs := average_abs_sq_bound a f
  have hz : 0 ≤ ∫ x in (-π)..π, |vonMisesDensity a x * f x| :=
    intervalIntegral.integral_nonneg (by linarith [pi_pos]) (fun x _ => abs_nonneg _)
  have hsq := (sq_le_sq₀ (abs_nonneg (U θ - U (-π))) hz).mpr hb
  simpa only [sq_abs] using hsq.trans hs

/-- A proved weighted Poincaré estimate. The additive constant in the
primitive is fixed by its weighted mean, not by a boundary value. The constant
`∫1/q` is positive and finite for each von Mises density, but not sharp. -/
theorem weighted_poincare (a : ℝ) (U f : CircleFunction)
    (hU : ∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ)
    (hmean : inverseAverage a U = 0) :
    inverseAverage a (U * U) ≤ inverseAverage a 1 * average a (f * f) := by
  let W : CircleFunction := U + (-U (-π)) • 1
  have hb : inverseAverage a (W * W) ≤
      inverseAverage a ((average a (f * f)) • (1 : CircleFunction)) := by
    apply intervalIntegral.integral_mono_on (by linarith [pi_pos])
      (((W * W).continuous.mul (inverseDensity a).continuous).intervalIntegrable _ _)
      (((average a (f * f) • (1 : CircleFunction)).continuous.mul
        (inverseDensity a).continuous).intervalIntegrable _ _)
    intro θ hθ
    have hp := primitive_pointwise_bound a U f hU hθ
    change (W θ * W θ) * (1 / vonMisesDensity a θ) ≤
      (average a (f * f) * 1) * (1 / vonMisesDensity a θ)
    apply mul_le_mul_of_nonneg_right _ (one_div_pos.mpr (vonMisesDensity_pos a θ)).le
    change (U θ + -U (-π) * 1) * (U θ + -U (-π) * 1) ≤ average a (f * f) * 1
    nlinarith
  rw [map_smul] at hb
  have he := form_square (inverseAverage a) U 1 (-U (-π))
  simp only [mul_one, hmean, mul_zero, add_zero] at he
  change inverseAverage a (W * W) = _ at he
  have hn := mul_nonneg (sq_nonneg (-U (-π))) (inverseAverage_one_pos a).le
  rw [he] at hb
  change inverseAverage a (U * U) + (-U (-π)) ^ 2 * inverseAverage a 1 ≤
    average a (f * f) * inverseAverage a 1 at hb
  nlinarith

/-- A normalized primitive of the rotation mode. Subtracting its inverse-
density mean is essential for the natural `H⁻¹(1/q)` metric. -/
noncomputable def rotationPrimitive (a : ℝ) : CircleFunction :=
  density a - ((2 * π) / inverseAverage a 1) • 1

lemma inverseAverage_density (a : ℝ) : inverseAverage a (density a) = 2 * π := by
  change (∫ θ in (-π)..π, vonMisesDensity a θ * (1 / vonMisesDensity a θ)) = 2 * π
  calc
    _ = ∫ _θ in (-π)..π, (1 : ℝ) := intervalIntegral.integral_congr
      (fun θ _ => mul_one_div_cancel (vonMisesDensity_pos a θ).ne')
    _ = 2 * π := by simp; ring

lemma rotationPrimitive_mean (a : ℝ) : inverseAverage a (rotationPrimitive a) = 0 := by
  simp [rotationPrimitive, inverseAverage_density, (inverseAverage_one_pos a).ne']

lemma rotationPrimitive_hasDerivAt (a θ : ℝ) :
    HasDerivAt (rotationPrimitive a) (-a * sin θ * vonMisesDensity a θ) θ := by
  change HasDerivAt (fun x => vonMisesDensity a x -
    ((2 * π) / inverseAverage a 1) * 1) _ _
  exact (density_hasDerivAt a θ).sub_const _

/-- Poincaré control after removing rotation. Orthogonality here is in the
weighted primitive metric; the density projection used by `transverse` is in
another metric. Positivity of the extra square relates the two projections. -/
theorem transverse_poincare {a : ℝ} (ha : 0 < a) (U f : CircleFunction)
    (hU : ∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ)
    (hmean : inverseAverage a U = 0)
    (horth : inverseAverage a (U * rotationPrimitive a) = 0) :
    inverseAverage a (U * U) ≤
      inverseAverage a 1 * average a (transverse a f * transverse a f) := by
  let b := average a (f * circleSin) / vonMisesSRatio a
  let W := U + (b / a) • rotationPrimitive a
  have hd (θ : ℝ) : HasDerivAt W (vonMisesDensity a θ * transverse a f θ) θ := by
    apply ((hU θ).add ((rotationPrimitive_hasDerivAt a θ).const_mul (b / a))).congr_deriv
    change vonMisesDensity a θ * f θ + (b / a) * (-a * sin θ * vonMisesDensity a θ) =
      vonMisesDensity a θ * (f θ - b * sin θ)
    field_simp
    ring
  have hm : inverseAverage a W = 0 := by simp [W, hmean, rotationPrimitive_mean]
  have hp := weighted_poincare a W (transverse a f) hd hm
  have he := form_square (inverseAverage a) U (rotationPrimitive a) (b / a)
  rw [horth, mul_zero, add_zero] at he
  have hz := mul_nonneg (sq_nonneg (b / a))
    (inverseAverage_square_nonneg a (rotationPrimitive a))
  change inverseAverage a W = 0 at hm
  change inverseAverage a (W * W) = _ at he
  rw [he] at hp
  linarith

#print axioms weighted_poincare
#print axioms transverse_poincare

end PhysicsOfConsciousness.FokkerPlanck
