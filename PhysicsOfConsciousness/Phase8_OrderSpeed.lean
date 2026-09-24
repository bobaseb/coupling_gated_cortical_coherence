import PhysicsOfConsciousness.Phase8_OrderCurrent

/-!
# Rotation-invariant phase-order speed and finite-time current cost

For a smooth positive normalized periodic density obeying the continuity
operator, the magnitude of its first Fourier moment obeys the current-speed
bound. When order stays strictly between zero and one, integrating the arcsine
rate gives the endpoint cost floor. The moment differentiation under the
spatial integral, continuity of the cost and derivative, and global interior
order range are explicit regularity hypotheses. No PDE solution, heat law,
metabolic conversion or cortical model is constructed here.
-/

open Real MeasureTheory intervalIntegral Set
namespace PhysicsOfConsciousness.FokkerPlanck

noncomputable def orderMagnitude (C S : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (C t ^ 2 + S t ^ 2)

lemma orderMagnitude_hasDerivAt {C S : ℝ → ℝ} {t c' s' : ℝ}
    (hC : HasDerivAt C c' t) (hS : HasDerivAt S s' t)
    (hpos : 0 < orderMagnitude C S t) :
    HasDerivAt (orderMagnitude C S)
      ((C t * c' + S t * s') / orderMagnitude C S t) t := by
  have hsum := (hC.pow 2).add (hS.pow 2)
  have hzero : C t ^ 2 + S t ^ 2 ≠ 0 := by
    intro h
    simp [orderMagnitude, h] at hpos
  have hderiv := hsum.sqrt hzero
  simp only [Pi.add_apply, Pi.pow_apply, Nat.reduceSub, pow_one] at hderiv
  change HasDerivAt (orderMagnitude C S)
    ((2 * C t * c' + 2 * S t * s') / (2 * orderMagnitude C S t)) t at hderiv
  convert hderiv using 1
  field_simp

lemma directional_mean_eq {ρ : ℝ → ℝ} (hρ : Continuous ρ) (φ r : ℝ)
    (hC : (∫ θ in (-π)..π, Real.cos θ * ρ θ) = r * Real.cos φ)
    (hS : (∫ θ in (-π)..π, Real.sin θ * ρ θ) = r * Real.sin φ) :
    (∫ θ in (-π)..π, Real.cos (θ - φ) * ρ θ) = r := by
  have hc : IntervalIntegrable (fun θ => Real.cos θ * ρ θ) volume (-π) π :=
    (Real.continuous_cos.mul hρ).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun θ => Real.sin θ * ρ θ) volume (-π) π :=
    (Real.continuous_sin.mul hρ).intervalIntegrable _ _
  have heq : (fun θ => Real.cos (θ - φ) * ρ θ) =
      fun θ => Real.cos φ * (Real.cos θ * ρ θ) +
        Real.sin φ * (Real.sin θ * ρ θ) := by
    funext θ
    rw [Real.cos_sub]
    ring
  rw [heq, intervalIntegral.integral_add (hc.const_mul _) (hs.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hC, hS]
  calc
    Real.cos φ * (r * Real.cos φ) + Real.sin φ * (r * Real.sin φ) =
        r * (Real.sin φ ^ 2 + Real.cos φ ^ 2) := by ring
    _ = r := by rw [Real.sin_sq_add_cos_sq]; ring

lemma directional_flux_eq {J : ℝ → ℝ} (hJ : Continuous J) (φ : ℝ) :
    -(∫ θ in (-π)..π, Real.sin (θ - φ) * J θ) =
      Real.cos φ * -(∫ θ in (-π)..π, Real.sin θ * J θ) +
        Real.sin φ * (∫ θ in (-π)..π, Real.cos θ * J θ) := by
  have hc : IntervalIntegrable (fun θ => Real.cos θ * J θ) volume (-π) π :=
    (Real.continuous_cos.mul hJ).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun θ => Real.sin θ * J θ) volume (-π) π :=
    (Real.continuous_sin.mul hJ).intervalIntegrable _ _
  have heq : (fun θ => Real.sin (θ - φ) * J θ) =
      fun θ => Real.cos φ * (Real.sin θ * J θ) -
        Real.sin φ * (Real.cos θ * J θ) := by
    funext θ
    rw [Real.sin_sub]
    ring
  rw [heq, intervalIntegral.integral_sub (hs.const_mul _) (hc.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring


/-- Periodic integration by parts turns the cosine moment of the continuity
operator into the sine-weighted current. It does not differentiate in time. -/
lemma cosine_operator_rate_eq_flux {D : ℝ} {v ρ : ℝ → ℝ}
    (hJ : Differentiable ℝ (current D v ρ))
    (hJ' : Continuous (deriv (current D v ρ)))
    (hper : Function.Periodic (current D v ρ) (2 * π)) :
    (∫ θ in (-π)..π, Real.cos θ * operator D v ρ θ) =
      -(∫ θ in (-π)..π, Real.sin θ * current D v ρ θ) := by
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    Real.continuous_cos.continuousOn hJ.continuous.continuousOn
    (fun θ _ => Real.hasDerivAt_cos θ) (fun θ _ => (hJ θ).hasDerivAt)
    (Real.continuous_sin.neg.intervalIntegrable (-π) π) (hJ'.intervalIntegrable (-π) π)
  have hends : current D v ρ π = current D v ρ (-π) := by
    simpa only [show -π + 2 * π = π by ring] using hper (-π)
  simp only [Real.cos_pi, Real.cos_neg, hends, sub_self, neg_mul,
    intervalIntegral.integral_neg, zero_sub, neg_neg] at hi
  simp only [operator, mul_neg, intervalIntegral.integral_neg, hi]

/-- The sine moment has no boundary term because sine vanishes at both ends.
A periodic current is still required by the model, though this identity alone
uses only spatial differentiability. -/
lemma sine_operator_rate_eq_flux {D : ℝ} {v ρ : ℝ → ℝ}
    (hJ : Differentiable ℝ (current D v ρ))
    (hJ' : Continuous (deriv (current D v ρ))) :
    (∫ θ in (-π)..π, Real.sin θ * operator D v ρ θ) =
      ∫ θ in (-π)..π, Real.cos θ * current D v ρ θ := by
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    Real.continuous_sin.continuousOn hJ.continuous.continuousOn
    (fun θ _ => Real.hasDerivAt_sin θ) (fun θ _ => (hJ θ).hasDerivAt)
    (Real.continuous_cos.intervalIntegrable (-π) π) (hJ'.intervalIntegrable (-π) π)
  simp only [Real.sin_pi, Real.sin_neg, neg_zero, zero_mul, sub_zero, zero_sub] at hi
  simp only [operator, mul_neg, intervalIntegral.integral_neg, hi, neg_neg]


/-- The cosine and sine moments are the real and imaginary coordinates of the
existing complex order parameter. No time evolution is used. -/
lemma circularOrderParameter_eq_moments {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    circularOrderParameter ρ =
      ((∫ θ in (-π)..π, Real.cos θ * ρ θ : ℝ) : ℂ) +
        ((∫ θ in (-π)..π, Real.sin θ * ρ θ : ℝ) : ℂ) * Complex.I := by
  have hfun : ∀ θ : ℝ, Complex.exp (Complex.I * θ) * (ρ θ : ℂ) =
      ((Real.cos θ * ρ θ : ℝ) : ℂ) +
        ((Real.sin θ * ρ θ : ℝ) : ℂ) * Complex.I := by
    intro θ
    rw [mul_comm Complex.I, Complex.exp_mul_I]
    push_cast
    ring
  have hc : IntervalIntegrable
      (fun θ => ((Real.cos θ * ρ θ : ℝ) : ℂ)) volume (-π) π := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hs : IntervalIntegrable
      (fun θ => ((Real.sin θ * ρ θ : ℝ) : ℂ) * Complex.I) volume (-π) π := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold circularOrderParameter
  rw [intervalIntegral.integral_congr (g := fun θ =>
        ((Real.cos θ * ρ θ : ℝ) : ℂ) +
          ((Real.sin θ * ρ θ : ℝ) : ℂ) * Complex.I)
      (fun θ _ => hfun θ),
    intervalIntegral.integral_add hc hs, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]


lemma norm_circularOrderParameter_eq {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    ‖circularOrderParameter ρ‖ = Real.sqrt
      ((∫ θ in (-π)..π, Real.cos θ * ρ θ) ^ 2 +
        (∫ θ in (-π)..π, Real.sin θ * ρ θ) ^ 2) := by
  rw [circularOrderParameter_eq_moments hρ, Complex.norm_def,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  congr 1
  ring


noncomputable def cosineMoment (ρ : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in (-π)..π, Real.cos θ * ρ t θ

noncomputable def sineMoment (ρ : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ θ in (-π)..π, Real.sin θ * ρ t θ

lemma exists_order_angle (C S : ℝ) (hpos : 0 < Real.sqrt (C ^ 2 + S ^ 2)) :
    ∃ φ : ℝ, C = Real.sqrt (C ^ 2 + S ^ 2) * Real.cos φ ∧
      S = Real.sqrt (C ^ 2 + S ^ 2) * Real.sin φ := by
  let z : ℂ := ⟨C, S⟩
  have hnorm : ‖z‖ = Real.sqrt (C ^ 2 + S ^ 2) := by
    rw [Complex.norm_def]
    rw [Complex.normSq_apply]
    change Real.sqrt (C * C + S * S) = Real.sqrt (C ^ 2 + S ^ 2)
    congr 1
    ring
  have hz : z ≠ 0 := by
    intro h
    have : ‖z‖ = 0 := by rw [h]; simp
    linarith
  have hzn : ‖z‖ ≠ 0 := ne_of_gt (by rw [hnorm]; exact hpos)
  refine ⟨z.arg, ?_, ?_⟩
  · rw [Complex.cos_arg hz, ← hnorm]
    change C = ‖z‖ * (C / ‖z‖)
    field_simp [hzn]
  · rw [Complex.sin_arg, ← hnorm]
    change S = ‖z‖ * (S / ‖z‖)
    field_simp [hzn]


/-- A classical continuity equation gives both moment rates when differentiation
under the spatial integral is justified. The current is periodic and spatially
smooth; the PDE holds pointwise at the named time. This does not construct a
solution or justify the interchange hypothesis automatically. -/
lemma classical_moment_rates {D t : ℝ} {ρ v : ℝ → ℝ → ℝ}
    (hJ : Differentiable ℝ (current D (v t) (ρ t)))
    (hJ' : Continuous (deriv (current D (v t) (ρ t))))
    (hper : Function.Periodic (current D (v t) (ρ t)) (2 * π))
    (hPDE : ∀ θ, deriv (fun u => ρ u θ) t = operator D (v t) (ρ t) θ)
    (hC : HasDerivAt (cosineMoment ρ)
      (∫ θ in (-π)..π, Real.cos θ * deriv (fun u => ρ u θ) t) t)
    (hS : HasDerivAt (sineMoment ρ)
      (∫ θ in (-π)..π, Real.sin θ * deriv (fun u => ρ u θ) t) t) :
    HasDerivAt (cosineMoment ρ)
      (-(∫ θ in (-π)..π, Real.sin θ * current D (v t) (ρ t) θ)) t ∧
    HasDerivAt (sineMoment ρ)
      (∫ θ in (-π)..π, Real.cos θ * current D (v t) (ρ t) θ) t := by
  have hcpoint : (fun θ => Real.cos θ * deriv (fun u => ρ u θ) t) =
      fun θ => Real.cos θ * operator D (v t) (ρ t) θ := by
    funext θ
    rw [hPDE θ]
  have hspoint : (fun θ => Real.sin θ * deriv (fun u => ρ u θ) t) =
      fun θ => Real.sin θ * operator D (v t) (ρ t) θ := by
    funext θ
    rw [hPDE θ]
  rw [hcpoint, cosine_operator_rate_eq_flux hJ hJ' hper] at hC
  rw [hspoint, sine_operator_rate_eq_flux hJ hJ'] at hS
  exact ⟨hC, hS⟩


/-- The real-coordinate order magnitude is exactly the norm of the repository's
complex circular order parameter. This identifies the rate theorem's `r`. -/
lemma orderMagnitude_eq_norm_circular {ρ : ℝ → ℝ → ℝ} (t : ℝ)
    (hρ : Continuous (ρ t)) :
    orderMagnitude (cosineMoment ρ) (sineMoment ρ) t =
      ‖circularOrderParameter (ρ t)‖ := by
  rw [norm_circularOrderParameter_eq hρ]
  rfl


/-- A positive order magnitude has squared rate bounded by the instantaneous
probability-current cost and one minus squared order. The moment-rate hypotheses
are the differentiated continuity equation, including differentiation under the
spatial integral and periodic cancellation. They are explicit obligations for a
classical density solution; this theorem does not construct such a solution. -/
theorem order_magnitude_speed_bound_of_angle {D t : ℝ} (hD : 0 < D)
    {ρ v : ℝ → ℝ → ℝ}
    (hρ : Continuous (ρ t)) (hpos : ∀ θ, 0 < ρ t θ)
    (hnorm : (∫ θ in (-π)..π, ρ t θ) = 1)
    (hJ : Continuous (current D (v t) (ρ t)))
    (hC : HasDerivAt (cosineMoment ρ)
      (-(∫ θ in (-π)..π, Real.sin θ * current D (v t) (ρ t) θ)) t)
    (hS : HasDerivAt (sineMoment ρ)
      (∫ θ in (-π)..π, Real.cos θ * current D (v t) (ρ t) θ) t)
    (hrpos : 0 < orderMagnitude (cosineMoment ρ) (sineMoment ρ) t)
    (φ : ℝ)
    (hcalign : cosineMoment ρ t =
      orderMagnitude (cosineMoment ρ) (sineMoment ρ) t * Real.cos φ)
    (hsalign : sineMoment ρ t =
      orderMagnitude (cosineMoment ρ) (sineMoment ρ) t * Real.sin φ) :
    (deriv (orderMagnitude (cosineMoment ρ) (sineMoment ρ)) t) ^ 2 ≤
      D * currentDissipation D (v t) (ρ t) *
        (1 - orderMagnitude (cosineMoment ρ) (sineMoment ρ) t ^ 2) := by
  let C := cosineMoment ρ
  let S := sineMoment ρ
  let r := orderMagnitude C S t
  have hderiv := orderMagnitude_hasDerivAt hC hS hrpos
  have hrate : deriv (orderMagnitude C S) t =
      -(∫ θ in (-π)..π, Real.sin (θ - φ) * current D (v t) (ρ t) θ) := by
    rw [hderiv.deriv, directional_flux_eq hJ φ]
    rw [hcalign, hsalign]
    field_simp [hrpos.ne']
  have hmean : (∫ θ in (-π)..π, Real.cos (θ - φ) * ρ t θ) = r :=
    directional_mean_eq hρ φ r hcalign hsalign
  have hb := directional_current_order_bound hD hρ hpos hnorm hJ φ
  rw [hmean] at hb
  rw [hrate, neg_sq]
  exact hb

lemma interval_integral_sq_le (τ : ℝ) (hτ : 0 < τ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    (∫ t in (0 : ℝ)..τ, f t) ^ 2 ≤
      τ * ∫ t in (0 : ℝ)..τ, f t ^ 2 := by
  let m := ∫ t in (0 : ℝ)..τ, f t
  let q := m / τ
  have hq : q * τ = m := by
    dsimp [q]
    field_simp
  have hi : IntervalIntegrable (fun t => f t ^ 2) volume 0 τ :=
    (hf.pow 2).intervalIntegrable _ _
  have hif : IntervalIntegrable f volume 0 τ := hf.intervalIntegrable _ _
  have hn : 0 ≤ ∫ t in (0 : ℝ)..τ, (f t - q) ^ 2 :=
    intervalIntegral.integral_nonneg hτ.le (fun t _ => sq_nonneg _)
  have heq : (fun t => (f t - q) ^ 2) =
      fun t => f t ^ 2 - (2 * q) * f t + q ^ 2 := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_add (hi.sub (hif.const_mul _))
      intervalIntegrable_const, intervalIntegral.integral_sub hi (hif.const_mul _),
    intervalIntegral.integral_const_mul] at hn
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hn
  dsimp [m] at hq ⊢
  rw [← hq] at hn ⊢
  nlinarith [mul_nonneg hτ.le hn]


/-- A smooth positive subunit order path pays an integrated current-cost floor.
The rate inequality is a separate hypothesis, supplied by
`order_magnitude_speed_bound` for a regular classical density trajectory. This
uses global smoothness for a simple FTC statement; zero-order and unit-order
times are outside this theorem's domain. -/
theorem arcsin_endpoint_cost_bound {D τ : ℝ} (hD : 0 < D) (hτ : 0 < τ)
    {r σ : ℝ → ℝ} (hr : Differentiable ℝ r)
    (hr' : Continuous (deriv r)) (hσ : Continuous σ)
    (hrange : ∀ t, 0 < r t ∧ r t < 1)
    (hspeed : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      (deriv r t) ^ 2 ≤ D * σ t * (1 - r t ^ 2)) :
    (Real.arcsin (r τ) - Real.arcsin (r 0)) ^ 2 / (D * τ) ≤
      ∫ t in (0 : ℝ)..τ, σ t := by
  let F := fun t => Real.arcsin (r t)
  let f := fun t => deriv r t / Real.sqrt (1 - r t ^ 2)
  have hden (t : ℝ) : 0 < 1 - r t ^ 2 := by
    have ⟨h0, h1⟩ := hrange t
    nlinarith
  have hFderiv (t : ℝ) : HasDerivAt F (f t) t := by
    have hx := Real.hasDerivAt_arcsin (x := r t) (by linarith [(hrange t).1])
      (by linarith [(hrange t).2])
    simpa only [F, f, Function.comp_def, one_div, one_mul, div_eq_mul_inv, mul_comm] using
      hx.comp t (hr t).hasDerivAt
  have hf : Continuous f := by
    have hroot : Continuous (fun t => Real.sqrt (1 - r t ^ 2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub (hr.continuous.pow 2))
    exact hr'.div hroot (fun t => (Real.sqrt_pos.2 (hden t)).ne')
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) τ) : f t ^ 2 ≤ D * σ t := by
    have hs := hspeed t ht
    have hroot := Real.sq_sqrt (hden t).le
    dsimp [f]
    rw [div_pow, hroot]
    exact (div_le_iff₀ (hden t)).mpr hs
  have hmono : (∫ t in (0 : ℝ)..τ, f t ^ 2) ≤
      D * (∫ t in (0 : ℝ)..τ, σ t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hτ.le
      ((hf.pow 2).intervalIntegrable _ _) ((hσ.const_mul D).intervalIntegrable _ _)
    intro t ht
    exact hpoint t ht
  have hCS := interval_integral_sq_le τ hτ hf
  have hFTC : (∫ t in (0 : ℝ)..τ, f t) = F τ - F 0 := by
    have heq : deriv F = f := funext fun t => (hFderiv t).deriv
    rw [← heq]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun t _ => (hFderiv t).differentiableAt) (by rw [heq]; exact hf.intervalIntegrable _ _)
  rw [hFTC] at hCS
  have hprod := mul_le_mul_of_nonneg_left hmono hτ.le
  dsimp [F] at hCS
  apply (div_le_iff₀ (mul_pos hD hτ)).mpr
  nlinarith

/-- Rotation-invariant pointwise rate bound. The mean direction exists whenever
the order magnitude is positive, so no angle is supplied by the caller. The two
moment-rate hypotheses remain the explicit continuity-equation obligation. -/
theorem order_magnitude_speed_bound {D t : ℝ} (hD : 0 < D)
    {ρ v : ℝ → ℝ → ℝ}
    (hρ : Continuous (ρ t)) (hpos : ∀ θ, 0 < ρ t θ)
    (hnorm : (∫ θ in (-π)..π, ρ t θ) = 1)
    (hJ : Continuous (current D (v t) (ρ t)))
    (hC : HasDerivAt (cosineMoment ρ)
      (-(∫ θ in (-π)..π, Real.sin θ * current D (v t) (ρ t) θ)) t)
    (hS : HasDerivAt (sineMoment ρ)
      (∫ θ in (-π)..π, Real.cos θ * current D (v t) (ρ t) θ) t)
    (hrpos : 0 < orderMagnitude (cosineMoment ρ) (sineMoment ρ) t) :
    (deriv (orderMagnitude (cosineMoment ρ) (sineMoment ρ)) t) ^ 2 ≤
      D * currentDissipation D (v t) (ρ t) *
        (1 - orderMagnitude (cosineMoment ρ) (sineMoment ρ) t ^ 2) := by
  obtain ⟨φ, hc, hs⟩ := exists_order_angle
    (cosineMoment ρ t) (sineMoment ρ t) hrpos
  exact order_magnitude_speed_bound_of_angle hD hρ hpos hnorm hJ hC hS hrpos φ hc hs

/-- Finite-time cost bound for a smooth classical density trajectory whose order
stays strictly between zero and one. The moment-rate hypotheses specify the
continuity equation after differentiation under the integral and periodic
integration by parts. Continuity of the cost and order derivative is assumed;
this result does not cover zero-order instants or prove existence of a PDE
solution. -/
theorem density_order_endpoint_cost_bound {D τ : ℝ} (hD : 0 < D) (hτ : 0 < τ)
    {ρ v : ℝ → ℝ → ℝ}
    (hr : Differentiable ℝ (orderMagnitude (cosineMoment ρ) (sineMoment ρ)))
    (hr' : Continuous (deriv (orderMagnitude (cosineMoment ρ) (sineMoment ρ))))
    (hσ : Continuous (fun t => currentDissipation D (v t) (ρ t)))
    (hrange : ∀ t, 0 < orderMagnitude (cosineMoment ρ) (sineMoment ρ) t ∧
      orderMagnitude (cosineMoment ρ) (sineMoment ρ) t < 1)
    (hshape : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      Continuous (ρ t) ∧ (∀ θ, 0 < ρ t θ) ∧
      (∫ θ in (-π)..π, ρ t θ) = 1)
    (hcurrent : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      Differentiable ℝ (current D (v t) (ρ t)) ∧
      Continuous (deriv (current D (v t) (ρ t))) ∧
      Function.Periodic (current D (v t) (ρ t)) (2 * π))
    (hPDE : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ θ,
      deriv (fun u => ρ u θ) t = operator D (v t) (ρ t) θ)
    (hinterchange : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      HasDerivAt (cosineMoment ρ)
        (∫ θ in (-π)..π, Real.cos θ * deriv (fun u => ρ u θ) t) t ∧
      HasDerivAt (sineMoment ρ)
        (∫ θ in (-π)..π, Real.sin θ * deriv (fun u => ρ u θ) t) t) :
    (Real.arcsin (orderMagnitude (cosineMoment ρ) (sineMoment ρ) τ) -
      Real.arcsin (orderMagnitude (cosineMoment ρ) (sineMoment ρ) 0)) ^ 2 /
        (D * τ) ≤ ∫ t in (0 : ℝ)..τ, currentDissipation D (v t) (ρ t) := by
  apply arcsin_endpoint_cost_bound hD hτ hr hr' hσ hrange
  intro t ht
  obtain ⟨hρ, hpos, hnorm⟩ := hshape t ht
  obtain ⟨hJ, hJ', hper⟩ := hcurrent t ht
  obtain ⟨hC, hS⟩ := classical_moment_rates hJ hJ' hper (hPDE t ht)
    (hinterchange t ht).1 (hinterchange t ht).2
  exact order_magnitude_speed_bound hD hρ hpos hnorm hJ.continuous
    hC hS (hrange t).1

#print axioms order_magnitude_speed_bound
#print axioms density_order_endpoint_cost_bound
#print axioms classical_moment_rates
#print axioms orderMagnitude_eq_norm_circular

#print axioms arcsin_endpoint_cost_bound


end PhysicsOfConsciousness.FokkerPlanck
