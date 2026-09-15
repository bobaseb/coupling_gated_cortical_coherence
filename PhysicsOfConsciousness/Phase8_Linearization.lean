import PhysicsOfConsciousness.Phase8_FokkerPlanck

/-!
# The actual mean-field current and its linearization

The coupling reads the density's sine and cosine moments. Expanding the current
at `q + ε u` gives the declared linear current plus an explicit quadratic
remainder. The Fourier calculation below concerns the uniform state of this
operator, not a separately assigned list of growth rates. It does not prove a
finite-particle limit or nonlinear stability at the critical coupling.
-/

open Real MeasureTheory intervalIntegral Set

namespace PhysicsOfConsciousness.FokkerPlanck

noncomputable def cosMoment (ρ : ℝ → ℝ) : ℝ := ∫ θ in (-π)..π, cos θ * ρ θ
noncomputable def sinMoment (ρ : ℝ → ℝ) : ℝ := ∫ θ in (-π)..π, sin θ * ρ θ

/-- The sinusoidal convolution, expressed by its two trigonometric moments. -/
noncomputable def meanDrift (K : ℝ) (ρ : ℝ → ℝ) (θ : ℝ) : ℝ :=
  K * (sinMoment ρ * cos θ - cosMoment ρ * sin θ)

/-- The moment expression is the integral of the original interaction. This
identifies the operator's coupling; no closure approximation is made here. -/
theorem meanDrift_eq_integral (K : ℝ) {ρ : ℝ → ℝ} (hρ : Continuous ρ) (θ : ℝ) :
    meanDrift K ρ θ = -K * ∫ φ in (-π)..π, sin (θ - φ) * ρ φ := by
  have hf : (fun φ => sin (θ - φ) * ρ φ) =
      fun φ => sin θ * (cos φ * ρ φ) - cos θ * (sin φ * ρ φ) := by
    funext φ; rw [sin_sub]; ring
  have hc : IntervalIntegrable (fun φ => sin θ * (cos φ * ρ φ)) volume (-π) π :=
    ((continuous_const.mul (continuous_cos.mul hρ)).intervalIntegrable _ _)
  have hs : IntervalIntegrable (fun φ => cos θ * (sin φ * ρ φ)) volume (-π) π :=
    ((continuous_const.mul (continuous_sin.mul hρ)).intervalIntegrable _ _)
  rw [hf, intervalIntegral.integral_sub hc hs,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  dsimp [meanDrift, sinMoment, cosMoment]
  ring

lemma cosMoment_add_mul {q u : ℝ → ℝ} (hq : Continuous q) (hu : Continuous u) (ε : ℝ) :
    cosMoment (fun θ => q θ + ε * u θ) = cosMoment q + ε * cosMoment u := by
  unfold cosMoment
  simp_rw [mul_add, ← mul_left_comm ε]
  have h1 : IntervalIntegrable (fun θ => cos θ * q θ) volume (-π) π :=
    (continuous_cos.mul hq).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => ε * (cos θ * u θ)) volume (-π) π :=
    (continuous_const.mul (continuous_cos.mul hu)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul]

lemma sinMoment_add_mul {q u : ℝ → ℝ} (hq : Continuous q) (hu : Continuous u) (ε : ℝ) :
    sinMoment (fun θ => q θ + ε * u θ) = sinMoment q + ε * sinMoment u := by
  unfold sinMoment
  simp_rw [mul_add, ← mul_left_comm ε]
  have h1 : IntervalIntegrable (fun θ => sin θ * q θ) volume (-π) π :=
    (continuous_sin.mul hq).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => ε * (sin θ * u θ)) volume (-π) π :=
    (continuous_const.mul (continuous_sin.mul hu)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul]

lemma meanDrift_add_mul (K : ℝ) {q u : ℝ → ℝ} (hq : Continuous q) (hu : Continuous u)
    (ε θ : ℝ) : meanDrift K (fun x => q x + ε * u x) θ =
      meanDrift K q θ + ε * meanDrift K u θ := by
  rw [meanDrift, sinMoment_add_mul hq hu, cosMoment_add_mul hq hu]
  dsimp [meanDrift]; ring

/-- The first variation of current at a declared background density. -/
noncomputable def linearCurrent (D K : ℝ) (q u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  meanDrift K q θ * u θ + meanDrift K u θ * q θ - D * deriv u θ

/-- The linearized forward operator on classical perturbations. -/
noncomputable def linearOperator (D K : ℝ) (q u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -deriv (linearCurrent D K q u) θ

/-- Exact expansion of the nonlinear current, including its quadratic
remainder. Differentiability is supplied for the actual two functions. -/
theorem current_expansion (D K : ℝ) {q u : ℝ → ℝ}
    (hq : Differentiable ℝ q) (hu : Differentiable ℝ u) (ε θ : ℝ) :
    current D (meanDrift K (fun x => q x + ε * u x)) (fun x => q x + ε * u x) θ =
      current D (meanDrift K q) q θ + ε * linearCurrent D K q u θ +
        ε ^ 2 * meanDrift K u θ * u θ := by
  have hd := (((hq θ).hasDerivAt).add ((hu θ).hasDerivAt.const_mul ε)).deriv
  change deriv (fun x => q x + ε * u x) θ = deriv q θ + ε * deriv u θ at hd
  rw [current, meanDrift_add_mul K hq.continuous hu.continuous, hd]
  dsimp [current, linearCurrent]
  ring

/-- The derivative in perturbation amplitude is the named linear current.
An evolution theorem additionally needs regularity in time and space. -/
theorem current_linearization (D K : ℝ) {q u : ℝ → ℝ}
    (hq : Differentiable ℝ q) (hu : Differentiable ℝ u) (θ : ℝ) :
    HasDerivAt (fun ε =>
      current D (meanDrift K (fun x => q x + ε * u x)) (fun x => q x + ε * u x) θ)
      (linearCurrent D K q u θ) 0 := by
  simp_rw [current_expansion D K hq hu]
  apply (((hasDerivAt_const 0 (current D (meanDrift K q) q θ)).add
    ((hasDerivAt_id 0).mul_const (linearCurrent D K q u θ))).add
      ((((hasDerivAt_id 0).pow 2).mul_const (meanDrift K u θ)).mul_const (u θ))).congr_deriv
  simp

lemma meanDrift_vonMises (K a θ : ℝ) :
    meanDrift K (vonMisesDensity a) θ = drift K (besselRatio a) θ := by
  simp [meanDrift, sinMoment, cosMoment, vonMises_mean_sin, vonMises_mean_cos, drift]
  ring

/-- A fixed point is stationary for the drift computed from its own density.
This consumes both the stationary classification and the mean-field coupling. -/
theorem selfConsistent_stationary {D : ℝ} (hD : 0 < D) {K r : ℝ}
    (hr : r = selfConsistency K D r) :
    IsStationary D (meanDrift K (vonMisesDensity (K * r / D)))
      (vonMisesDensity (K * r / D)) := by
  have hd : meanDrift K (vonMisesDensity (K * r / D)) = drift K r := by
    funext θ
    rw [meanDrift_vonMises]
    change drift K (selfConsistency K D r) θ = drift K r θ
    rw [← hr]
  rw [hd]
  exact vonMises_stationary hD K r

lemma integral_cos_int (n : ℤ) (hn : n ≠ 0) :
    (∫ θ in (-π)..π, cos ((n : ℝ) * θ)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left _ (by exact_mod_cast hn), integral_cos]
  simp [mul_neg, sin_int_mul_pi]

lemma integral_sin_int (n : ℤ) :
    (∫ θ in (-π)..π, sin ((n : ℝ) * θ)) = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [intervalIntegral.integral_comp_mul_left _ (by exact_mod_cast hn), integral_sin]
  simp [mul_neg, cos_neg]

lemma first_cos_cos (n : ℕ) (hn : 2 ≤ n) :
    cosMoment (fun θ => cos ((n : ℝ) * θ)) = 0 := by
  have hf : (fun θ => cos θ * cos ((n : ℝ) * θ)) = fun θ =>
      (cos (((n : ℤ) - 1 : ℤ) * θ) + cos (((n : ℤ) + 1 : ℤ) * θ)) / 2 := by
    funext θ
    push_cast
    rw [sub_mul, add_mul, one_mul, cos_sub, cos_add]
    ring
  rw [cosMoment, hf, intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int _ (by omega), integral_cos_int _ (by omega)]
  norm_num

lemma first_sin_sin (n : ℕ) (hn : 2 ≤ n) :
    sinMoment (fun θ => sin ((n : ℝ) * θ)) = 0 := by
  have hf : (fun θ => sin θ * sin ((n : ℝ) * θ)) = fun θ =>
      (cos (((n : ℤ) - 1 : ℤ) * θ) - cos (((n : ℤ) + 1 : ℤ) * θ)) / 2 := by
    funext θ
    push_cast
    rw [sub_mul, add_mul, one_mul, cos_sub, cos_add]
    ring
  rw [sinMoment, hf, intervalIntegral.integral_div, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int _ (by omega), integral_cos_int _ (by omega)]
  norm_num

lemma first_sin_cos (n : ℕ) : sinMoment (fun θ => cos ((n : ℝ) * θ)) = 0 := by
  have hf : (fun θ => sin θ * cos ((n : ℝ) * θ)) = fun θ =>
      (sin (((n : ℤ) + 1 : ℤ) * θ) - sin (((n : ℤ) - 1 : ℤ) * θ)) / 2 := by
    funext θ
    push_cast
    rw [sub_mul, add_mul, one_mul, sin_sub, sin_add]
    ring
  rw [sinMoment, hf, intervalIntegral.integral_div, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), integral_sin_int, integral_sin_int]
  norm_num

lemma first_cos_sin (n : ℕ) : cosMoment (fun θ => sin ((n : ℝ) * θ)) = 0 := by
  have hf : (fun θ => cos θ * sin ((n : ℝ) * θ)) = fun θ =>
      (sin (((n : ℤ) + 1 : ℤ) * θ) + sin (((n : ℤ) - 1 : ℤ) * θ)) / 2 := by
    funext θ
    push_cast
    rw [sub_mul, add_mul, one_mul, sin_sub, sin_add]
    ring
  rw [cosMoment, hf, intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), integral_sin_int, integral_sin_int]
  norm_num

lemma cosMoment_cos : cosMoment cos = π := by
  simp [cosMoment, ← sq, integral_cos_sq]

lemma sinMoment_sin : sinMoment sin = π := by
  simp [sinMoment, ← sq, integral_sin_sq]

lemma cosMoment_sin : cosMoment sin = 0 := by simpa using first_cos_sin 1
lemma sinMoment_cos : sinMoment cos = 0 := by simpa using first_sin_cos 1

lemma uniform_drift (K θ : ℝ) : meanDrift K (vonMisesDensity 0) θ = 0 := by
  simp [meanDrift_vonMises, drift]

/-- First-harmonic rates of the actual linearized operator. Both real
components change sign at `K = 2D`; mass conservation removes the zeroth mode. -/
theorem incoherent_first_modes (D K θ : ℝ) :
    linearOperator D K (vonMisesDensity 0) cos θ = (K / 2 - D) * cos θ ∧
    linearOperator D K (vonMisesDensity 0) sin θ = (K / 2 - D) * sin θ := by
  have hc : linearCurrent D K (vonMisesDensity 0) cos = fun x => (D - K / 2) * sin x := by
    funext x
    rw [linearCurrent, uniform_drift]
    simp [meanDrift, sinMoment_cos, cosMoment_cos,
      (hasDerivAt_cos x).deriv]
    field_simp [pi_ne_zero]; ring
  have hs : linearCurrent D K (vonMisesDensity 0) sin = fun x => (K / 2 - D) * cos x := by
    funext x
    rw [linearCurrent, uniform_drift]
    simp [meanDrift, sinMoment_sin, cosMoment_sin,
      (hasDerivAt_sin x).deriv]
    field_simp [pi_ne_zero]
  constructor
  · rw [linearOperator, hc, ((hasDerivAt_sin θ).const_mul (D - K / 2)).deriv]; ring
  · rw [linearOperator, hs, ((hasDerivAt_cos θ).const_mul (K / 2 - D)).deriv]; ring

/-- Every higher harmonic decays at its diffusion rate. This is a per-mode
calculation, with no claim about convergence of arbitrary Fourier series. -/
theorem incoherent_higher_modes (D K : ℝ) (n : ℕ) (hn : 2 ≤ n) (θ : ℝ) :
    linearOperator D K (vonMisesDensity 0) (fun x => cos (n * x)) θ =
      (-D * (n : ℝ) ^ 2) * cos (n * θ) ∧
    linearOperator D K (vonMisesDensity 0) (fun x => sin (n * x)) θ =
      (-D * (n : ℝ) ^ 2) * sin (n * θ) := by
  have hc : linearCurrent D K (vonMisesDensity 0) (fun x => cos (n * x)) =
      fun x => D * n * sin (n * x) := by
    funext x
    have hd := (((hasDerivAt_id x).const_mul (n : ℝ)).cos).deriv
    simp only [id_eq, mul_one] at hd
    rw [linearCurrent, uniform_drift, hd]
    simp [meanDrift, first_sin_cos, first_cos_cos n hn]
    ring
  have hs : linearCurrent D K (vonMisesDensity 0) (fun x => sin (n * x)) =
      fun x => -D * n * cos (n * x) := by
    funext x
    have hd := (((hasDerivAt_id x).const_mul (n : ℝ)).sin).deriv
    simp only [id_eq, mul_one] at hd
    rw [linearCurrent, uniform_drift, hd]
    simp [meanDrift, first_sin_sin n hn, first_cos_sin]
    ring
  constructor
  · have hd := ((((hasDerivAt_id θ).const_mul (n : ℝ)).sin).const_mul (D * n)).deriv
    simp only [id_eq, mul_one] at hd
    rw [linearOperator, hc, hd]; ring
  · have hd := ((((hasDerivAt_id θ).const_mul (n : ℝ)).cos).const_mul (-D * n)).deriv
    simp only [id_eq, mul_one] at hd
    rw [linearOperator, hs, hd]; ring

/-- Positive modes have rate `K/2-D` at one and `-D n²` thereafter. The
constant mode is excluded by the zero-mass perturbation condition. -/
noncomputable def incoherentRate (D K : ℝ) (n : ℕ) : ℝ :=
  if n = 1 then K / 2 - D else -D * (n : ℝ) ^ 2

/-- Unified rate theorem for each real Fourier mode of positive index.
The operator is derived from `current_expansion`, not from this rate formula. -/
theorem incoherent_mode_rate (D K : ℝ) (n : ℕ) (hn : 0 < n) (θ : ℝ) :
    linearOperator D K (vonMisesDensity 0) (fun x => cos (n * x)) θ =
      incoherentRate D K n * cos (n * θ) ∧
    linearOperator D K (vonMisesDensity 0) (fun x => sin (n * x)) θ =
      incoherentRate D K n * sin (n * θ) := by
  by_cases h : n = 1
  · subst n; simpa [incoherentRate] using incoherent_first_modes D K θ
  · simpa [incoherentRate, h] using incoherent_higher_modes D K n (by omega) θ

/-- The uniform solution has a growing Fourier mode exactly above `2D`.
At equality its first modes are neutral, so no nonlinear conclusion follows. -/
theorem incoherent_instability_iff {D : ℝ} (hD : 0 < D) (K : ℝ) :
    (∃ n : ℕ, 0 < n ∧ 0 < incoherentRate D K n) ↔ 2 * D < K := by
  constructor
  · rintro ⟨n, _, h⟩
    by_cases hn : n = 1
    · simp [incoherentRate, hn] at h; linarith
    · have := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD.le) (sq_nonneg (n : ℝ))
      simp [incoherentRate, hn] at h
      linarith
  · intro h; exact ⟨1, by omega, by simp [incoherentRate]; linarith⟩

#print axioms current_linearization
#print axioms selfConsistent_stationary
#print axioms incoherent_mode_rate
#print axioms incoherent_instability_iff

end PhysicsOfConsciousness.FokkerPlanck
