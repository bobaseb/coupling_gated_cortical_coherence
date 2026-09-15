import PhysicsOfConsciousness.Phase8_Linearization
import PhysicsOfConsciousness.Phase8_StabilityMoments
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The coherent state's quadratic form

Continuous functions provide an algebra on which all interval integrals are
integrable. The positive integral functional proves Cauchy–Schwarz by a
nonnegative square. Its application to the von Mises density gives a strictly
positive form transverse to rotation. These estimates concern the full function
space on the circle, not a Fourier truncation. The operator and its primitive
energy are treated in the following module.
-/

open Real MeasureTheory intervalIntegral Set

namespace PhysicsOfConsciousness.FokkerPlanck

abbrev CircleFunction := C(ℝ, ℝ)

/-- Integration against a continuous weight on a finite interval. This is a
linear map because every continuous integrand here is interval integrable. -/
noncomputable def weightedIntegral (l r : ℝ) (w : CircleFunction) :
    CircleFunction →ₗ[ℝ] ℝ where
  toFun f := ∫ θ in l..r, f θ * w θ
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_mul]
    exact intervalIntegral.integral_add
      ((f.continuous.mul w.continuous).intervalIntegrable _ _)
      ((g.continuous.mul w.continuous).intervalIntegrable _ _)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact intervalIntegral.integral_const_mul _ _

lemma weightedIntegral_nonneg {l r : ℝ} (hlr : l ≤ r) (w f : CircleFunction)
    (hw : ∀ θ ∈ Icc l r, 0 ≤ w θ) (hf : ∀ θ ∈ Icc l r, 0 ≤ f θ) :
    0 ≤ weightedIntegral l r w f :=
  intervalIntegral.integral_nonneg hlr (fun θ hθ => mul_nonneg (hf θ hθ) (hw θ hθ))

lemma weightedIntegral_square_nonneg {l r : ℝ} (hlr : l ≤ r) (w f : CircleFunction)
    (hw : ∀ θ ∈ Icc l r, 0 ≤ w θ) :
    0 ≤ weightedIntegral l r w (f * f) :=
  weightedIntegral_nonneg hlr w (f * f) hw (fun θ _ => mul_self_nonneg (f θ))

lemma form_square (M : CircleFunction →ₗ[ℝ] ℝ) (f g : CircleFunction) (t : ℝ) :
    M ((f + t • g) * (f + t • g)) = M (f * f) + 2 * t * M (f * g) + t ^ 2 * M (g * g) := by
  have hf : (f + t • g) * (f + t • g) =
      f * f + (2 * t) • (f * g) + (t ^ 2) • (g * g) := by
    ext θ
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    ring
  rw [hf, map_add, map_add, map_smul, map_smul]
  rfl

/-- Cauchy–Schwarz for the specified weighted integral, obtained from
nonnegative squares. No covariance bound is supplied as a hypothesis. -/
theorem weighted_cauchy {l r : ℝ} (hlr : l ≤ r) (w f g : CircleFunction)
    (hw : ∀ θ ∈ Icc l r, 0 ≤ w θ) :
    weightedIntegral l r w (f * g) ^ 2 ≤
      weightedIntegral l r w (f * f) * weightedIntegral l r w (g * g) := by
  let M := weightedIntegral l r w
  have hp (t : ℝ) := weightedIntegral_square_nonneg hlr w (f + t • g) hw
  have hd := discrim_le_zero (a := M (g * g)) (b := 2 * M (f * g))
    (c := M (f * f)) (fun t => by
      have ht := hp t
      rw [form_square] at ht
      dsimp [M]
      nlinarith)
  dsimp [discrim, M] at hd
  nlinarith

noncomputable def circleCos : CircleFunction := ⟨cos, continuous_cos⟩
noncomputable def circleSin : CircleFunction := ⟨sin, continuous_sin⟩
noncomputable def density (a : ℝ) : CircleFunction :=
  ⟨vonMisesDensity a, (continuous_vonMisesWeight a).div_const _⟩

/-- Expectation under the normalized, derived stationary density. -/
noncomputable def average (a : ℝ) : CircleFunction →ₗ[ℝ] ℝ :=
  weightedIntegral (-π) π (density a)

@[simp] lemma average_one (a : ℝ) : average a 1 = 1 := by
  change (∫ θ in (-π)..π, 1 * vonMisesDensity a θ) = 1
  simpa using vonMisesDensity_integral_eq_one a

@[simp] lemma average_cos (a : ℝ) : average a circleCos = besselRatio a :=
  vonMises_mean_cos a

@[simp] lemma average_sin (a : ℝ) : average a circleSin = 0 := vonMises_mean_sin a

@[simp] lemma average_sin_sq (a : ℝ) : average a (circleSin * circleSin) = vonMisesSRatio a := by
  change (∫ θ in (-π)..π, (sin θ * sin θ) * (vonMisesWeight a θ / vonMisesZ a)) = _
  simp_rw [← sq, ← mul_div_assoc]
  rw [intervalIntegral.integral_div]
  rfl

@[simp] lemma average_cos_sq (a : ℝ) : average a (circleCos * circleCos) = 1 - vonMisesSRatio a := by
  have hf : circleSin * circleSin + circleCos * circleCos = (1 : CircleFunction) := by
    ext θ
    change sin θ * sin θ + cos θ * cos θ = 1
    nlinarith [sin_sq_add_cos_sq θ]
  have h := congrArg (average a) hf
  rw [map_add, average_sin_sq, average_one] at h
  linarith

@[simp] lemma average_sin_cos (a : ℝ) : average a (circleSin * circleCos) = 0 := by
  let f := fun θ => sin θ * cos θ * vonMisesDensity a θ
  have hf : Continuous f := (continuous_sin.mul continuous_cos).mul (density a).continuous
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-π) 0) (hf.intervalIntegrable 0 π)
  have hn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := π) (f := f)
  have ho : (fun x => f (-x)) = fun x => -f x := by
    funext x
    simp [f, vonMisesDensity, vonMisesWeight]
  rw [ho, intervalIntegral.integral_neg] at hn
  simp only [neg_zero] at hn
  change (∫ θ in (-π)..π, f θ) = 0
  linarith

lemma average_square_nonneg (a : ℝ) (f : CircleFunction) : 0 ≤ average a (f * f) :=
  weightedIntegral_square_nonneg (by linarith [pi_pos]) (density a) f
    (fun θ _ => (vonMisesDensity_pos a θ).le)

lemma average_cauchy (a : ℝ) (f g : CircleFunction) :
    average a (f * g) ^ 2 ≤ average a (f * f) * average a (g * g) :=
  weighted_cauchy (by linarith [pi_pos]) (density a) f g
    (fun θ _ => (vonMisesDensity_pos a θ).le)

noncomputable def centeredCos (a : ℝ) : CircleFunction := circleCos - besselRatio a • 1

@[simp] lemma average_centeredCos (a : ℝ) : average a (centeredCos a) = 0 := by
  simp [centeredCos]

@[simp] lemma average_centeredCos_sq (a : ℝ) :
    average a (centeredCos a * centeredCos a) =
      1 - vonMisesSRatio a - besselRatio a ^ 2 := by
  have h := form_square (average a) circleCos 1 (-besselRatio a)
  simp only [mul_one, average_cos, average_cos_sq, average_one] at h
  have he : centeredCos a = circleCos + (-besselRatio a) • (1 : CircleFunction) := by
    simp [centeredCos, sub_eq_add_neg]
  rw [he, h]
  ring

@[simp] lemma average_sin_centeredCos (a : ℝ) :
    average a (circleSin * centeredCos a) = 0 := by
  simp [centeredCos, mul_sub]

/-- Density perturbation after removing its rotation component, expressed
relative to the stationary density. This is the projection in `L²(q)`. -/
noncomputable def transverse (a : ℝ) (f : CircleFunction) : CircleFunction :=
  f - (average a (f * circleSin) / vonMisesSRatio a) • circleSin

lemma transverse_sin {a : ℝ} (ha : 0 < a) (f : CircleFunction) :
    average a (transverse a f * circleSin) = 0 := by
  simp [transverse, sub_mul, (sRatio_pos ha).ne']

lemma transverse_centeredCos (a : ℝ) (f : CircleFunction)
    (hf : average a f = 0) :
    average a (transverse a f * centeredCos a) = average a (f * circleCos) := by
  simp [transverse, sub_mul, centeredCos, mul_sub,
    hf, average_sin_cos]

lemma transverse_square {a : ℝ} (ha : 0 < a) (f : CircleFunction) :
    average a (transverse a f * transverse a f) =
      average a (f * f) - average a (f * circleSin) ^ 2 / vonMisesSRatio a := by
  have h := form_square (average a) f circleSin
    (-(average a (f * circleSin) / vonMisesSRatio a))
  rw [average_sin_sq] at h
  have he : transverse a f = f + (-(average a (f * circleSin) / vonMisesSRatio a)) • circleSin := by
    simp [transverse, sub_eq_add_neg]
  rw [he, h]
  field_simp [(sRatio_pos ha).ne']
  ring

/-- The second variation of free energy divided by diffusion, on a density
perturbation `u = q f`. This phase-space form is unrelated to the substrate
functional `sigmaContinuum`. -/
noncomputable def coherentForm (a : ℝ) (f : CircleFunction) : ℝ :=
  average a (f * f) -
    (average a (f * circleCos) ^ 2 + average a (f * circleSin) ^ 2) / vonMisesSRatio a

/-- Strict coefficient in the transverse form bound. It is positive for every
coherent concentration; it is not asserted uniformly at threshold. -/
noncomputable def coherenceGap (a : ℝ) : ℝ :=
  1 - (1 - vonMisesSRatio a - besselRatio a ^ 2) / vonMisesSRatio a

theorem coherenceGap_pos {a : ℝ} (ha : 0 < a) : 0 < coherenceGap a := by
  have := (div_lt_one (sRatio_pos ha)).mpr (cosine_variance_lt_sine ha)
  unfold coherenceGap
  linarith

/-- Coercivity on the entire continuous zero-mass perturbation space modulo
rotation. The covariance estimate is derived from the density. This is a
quadratic-form bound; the following module identifies its operator meaning. -/
theorem coherent_form_gap {a : ℝ} (ha : 0 < a) (f : CircleFunction)
    (hf : average a f = 0) :
    coherenceGap a * average a (transverse a f * transverse a f) ≤ coherentForm a f := by
  have hc := average_cauchy a (transverse a f) (centeredCos a)
  rw [average_centeredCos_sq, transverse_centeredCos a f hf] at hc
  have hs := sRatio_pos ha
  have he : coherentForm a f = average a (transverse a f * transverse a f) -
      average a (f * circleCos) ^ 2 / vonMisesSRatio a := by
    rw [transverse_square ha]
    dsimp [coherentForm]; ring
  rw [he]
  have hd := div_le_div_of_nonneg_right hc hs.le
  dsimp [coherenceGap]
  calc
    _ = average a (transverse a f * transverse a f) -
        (average a (transverse a f * transverse a f) *
          (1 - vonMisesSRatio a - besselRatio a ^ 2)) / vonMisesSRatio a := by ring
    _ ≤ _ := sub_le_sub_left hd _

/-- Nonnegativity, with the genuine rotational null direction removed by the
projection above. No arbitrary positive stability parameter is assumed. -/
theorem coherent_form_nonneg {a : ℝ} (ha : 0 < a) (f : CircleFunction)
    (hf : average a f = 0) : 0 ≤ coherentForm a f :=
  (mul_nonneg (coherenceGap_pos ha).le (average_square_nonneg a _)).trans
    (coherent_form_gap ha f hf)

theorem rotation_form_zero {a : ℝ} (ha : 0 < a) : coherentForm a circleSin = 0 := by
  simp [coherentForm, average_sin_cos,
    average_sin_sq, (sRatio_pos ha).ne', pow_two]

#print axioms weighted_cauchy
#print axioms coherent_form_gap
#print axioms coherent_form_nonneg
#print axioms rotation_form_zero

end PhysicsOfConsciousness.FokkerPlanck
