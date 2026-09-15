import PhysicsOfConsciousness.Phase8_SelfConsistency

/-!
# The periodic Fokker–Planck equation

The drift, current and operator below are functions of the named density.
`IsStationary` includes differentiability: an undefined, totalized derivative
cannot certify stationarity. A periodic gradient drift has zero stationary
current, and normalization then determines its Gibbs density. Specializing to
the cosine potential derives the von Mises form used by self-consistency.

This is the classical stationary equation in the identical-frequency rotating
frame. It does not construct the stochastic process, prove convergence of a
finite oscillator system, or assert stability of a stationary solution.
-/

open Real MeasureTheory intervalIntegral Set

namespace PhysicsOfConsciousness.FokkerPlanck

/-- Current for the declared drift and diffusion, with no stationarity input. -/
noncomputable def current (D : ℝ) (v ρ : ℝ → ℝ) (θ : ℝ) : ℝ := v θ * ρ θ - D * deriv ρ θ

/-- The forward differential operator `-∂θ J`. -/
noncomputable def operator (D : ℝ) (v ρ : ℝ → ℝ) (θ : ℝ) : ℝ := -deriv (current D v ρ) θ

/-- Classical stationary probability density on the circle. Positivity and
regularity describe the density; the equation refers to its own current. -/
def IsStationary (D : ℝ) (v ρ : ℝ → ℝ) : Prop :=
  Differentiable ℝ ρ ∧ Function.Periodic ρ (2 * π) ∧ (∀ θ, 0 < ρ θ) ∧
    (∫ θ in (-π)..π, ρ θ) = 1 ∧ Differentiable ℝ (current D v ρ) ∧
      ∀ θ, operator D v ρ θ = 0

/-- Cosine-potential drift in the mean-direction-zero rotating frame. -/
noncomputable def drift (K r θ : ℝ) : ℝ := -K * r * Real.sin θ

/-- Current dissipation integrates over phase space, unlike the substrate
squared-drift objective `sigmaContinuum`. The density is required positive in
the stationary theorems; division at zero is not an infinite-cost convention. -/
noncomputable def currentDissipation (D : ℝ) (v ρ : ℝ → ℝ) : ℝ :=
  ∫ θ in (-π)..π, current D v ρ θ ^ 2 / (D * ρ θ)

/-- The cosine drift is the gradient of the cosine potential. Stated so that the
gradient theorems below apply to it without a second definition. -/
theorem drift_eq_gradient (K r : ℝ) :
    drift K r = fun θ => -deriv (fun x => -K * r * Real.cos x) θ := by
  funext θ
  have h : HasDerivAt (fun x => -K * r * Real.cos x) (-K * r * -Real.sin θ) θ :=
    (Real.hasDerivAt_cos θ).const_mul (-K * r)
  rw [h.deriv, drift]
  ring

theorem density_hasDerivAt (a θ : ℝ) :
    HasDerivAt (vonMisesDensity a) (-a * Real.sin θ * vonMisesDensity a θ) θ := by
  have hw : HasDerivAt (vonMisesWeight a) (-a * Real.sin θ * vonMisesWeight a θ) θ := by
    have h : HasDerivAt (fun θ => Real.exp (a * Real.cos θ))
        (Real.exp (a * Real.cos θ) * (a * -Real.sin θ)) θ :=
      ((Real.hasDerivAt_cos θ).const_mul a).exp
    unfold vonMisesWeight
    convert h using 1
    ring
  have h := hw.div_const (vonMisesZ a)
  rw [show -a * Real.sin θ * vonMisesWeight a θ / vonMisesZ a
      = -a * Real.sin θ * vonMisesDensity a θ from by rw [vonMisesDensity]; ring] at h
  exact h

theorem density_periodic (a : ℝ) : Function.Periodic (vonMisesDensity a) (2 * π) := by
  intro θ
  simp [vonMisesDensity, vonMisesWeight, Real.cos_add_two_pi]

/-- The integrating factor differentiates to minus the current divided by
diffusion. This is an identity for a gradient drift, not a postulate about it. -/
theorem integratingFactor_hasDerivAt {D : ℝ} (hD : D ≠ 0) {V ρ : ℝ → ℝ}
    (hV : Differentiable ℝ V) (hρ : Differentiable ℝ ρ) (θ : ℝ) :
    HasDerivAt (fun x => ρ x * Real.exp (V x / D))
      (-current D (fun x => -deriv V x) ρ θ / D * Real.exp (V θ / D)) θ := by
  have hx : HasDerivAt (fun x => ρ x * Real.exp (V x / D))
      (deriv ρ θ * Real.exp (V θ / D) + ρ θ * (Real.exp (V θ / D) * (deriv V θ / D))) θ :=
    (hρ θ).hasDerivAt.mul (((hV θ).hasDerivAt.div_const D).exp)
  convert hx using 1
  simp only [current]
  field_simp
  ring

/-- Stationarity makes the current constant. Differentiability of that current
is necessary; an equation using `deriv` alone would admit spurious solutions. -/
theorem stationary_current_const {D : ℝ} {v ρ : ℝ → ℝ} (h : IsStationary D v ρ) (x y : ℝ) :
    current D v ρ x = current D v ρ y :=
  is_const_of_deriv_eq_zero h.2.2.2.2.1
    (fun θ => neg_eq_zero.mp (h.2.2.2.2.2 θ)) x y

/-- A periodic gradient potential cannot carry a nonzero stationary current.
Rolle's theorem on the positive integrating factor forces the constant current
to zero. A drift with nonzero circulation is outside this statement. -/
theorem stationary_current_zero {D : ℝ} (hD : 0 < D) {V ρ : ℝ → ℝ}
    (hV : Differentiable ℝ V) (hVper : Function.Periodic V (2 * π))
    (h : IsStationary D (fun x => -deriv V x) ρ) (θ : ℝ) :
    current D (fun x => -deriv V x) ρ θ = 0 := by
  set J := current D (fun x => -deriv V x) ρ 0 with hJ
  have hderiv : ∀ x, HasDerivAt (fun y => ρ y * Real.exp (V y / D))
      (-J / D * Real.exp (V x / D)) x := by
    intro x
    have hx := integratingFactor_hasDerivAt hD.ne' hV h.1 x
    rwa [stationary_current_const h x 0] at hx
  have hcont : Continuous (fun x => -J / D * Real.exp (V x / D)) := by
    have hVc := hV.continuous
    fun_prop
  have hftc : ∫ x in (-π)..π, -J / D * Real.exp (V x / D)
      = ρ π * Real.exp (V π / D) - ρ (-π) * Real.exp (V (-π) / D) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hcont.intervalIntegrable _ _)
  have hper : ρ π * Real.exp (V π / D) = ρ (-π) * Real.exp (V (-π) / D) := by
    have hρπ := h.2.1 (-π)
    have hVπ := hVper (-π)
    rw [show -π + 2 * π = π by ring] at hρπ hVπ
    rw [hρπ, hVπ]
  have hPpos : 0 < ∫ x in (-π)..π, Real.exp (V x / D) := by
    have hVc := hV.continuous
    refine intervalIntegral_pos_of_pos_on ((by fun_prop : Continuous
      (fun x => Real.exp (V x / D))).intervalIntegrable _ _) (fun x _ => Real.exp_pos _) ?_
    linarith [Real.pi_pos]
  rw [intervalIntegral.integral_const_mul, hper, sub_self] at hftc
  have hJ0 : J = 0 := by
    rcases mul_eq_zero.1 hftc with h1 | h1
    · field_simp at h1; linarith
    · exact absurd h1 hPpos.ne'
  rw [stationary_current_const h θ 0, ← hJ, hJ0]

/-- The stationary density is proportional to the Gibbs weight. Normalization
is used separately; this result supplies no dynamical selection. -/
theorem stationary_gibbs {D : ℝ} (hD : 0 < D) {V ρ : ℝ → ℝ} (hV : Differentiable ℝ V)
    (hVper : Function.Periodic V (2 * π)) (h : IsStationary D (fun x => -deriv V x) ρ) :
    ∃ c, 0 < c ∧ ∀ θ, ρ θ = c * Real.exp (-V θ / D) := by
  refine ⟨ρ 0 * Real.exp (V 0 / D), mul_pos (h.2.2.1 0) (Real.exp_pos _), fun θ => ?_⟩
  have h0 : ∀ x, HasDerivAt (fun y => ρ y * Real.exp (V y / D)) 0 x := by
    intro x
    have hx := integratingFactor_hasDerivAt hD.ne' hV h.1 x
    rw [stationary_current_zero hD hV hVper h x] at hx
    simpa using hx
  have hconst : ρ θ * Real.exp (V θ / D) = ρ 0 * Real.exp (V 0 / D) :=
    is_const_of_deriv_eq_zero (fun x => (h0 x).differentiableAt) (fun x => (h0 x).deriv) θ 0
  have hcancel : Real.exp (V θ / D) * Real.exp (-V θ / D) = 1 := by
    rw [← Real.exp_add, show V θ / D + -V θ / D = 0 by ring, Real.exp_zero]
  calc ρ θ = ρ θ * Real.exp (V θ / D) * Real.exp (-V θ / D) := by
        rw [mul_assoc, hcancel, mul_one]
    _ = ρ 0 * Real.exp (V 0 / D) * Real.exp (-V θ / D) := by rw [hconst]

/-- The stationary gradient state has zero current dissipation. This does not
identify it with the substrate's squared-drift functional. -/
theorem stationary_dissipation_zero {D : ℝ} (hD : 0 < D) {V ρ : ℝ → ℝ}
    (hV : Differentiable ℝ V) (hVper : Function.Periodic V (2 * π))
    (h : IsStationary D (fun x => -deriv V x) ρ) :
    currentDissipation D (fun x => -deriv V x) ρ = 0 := by
  unfold currentDissipation
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
    (fun θ _ => by rw [stationary_current_zero hD hV hVper h θ]; simp)]
  simp

/-- The von Mises density has zero current for the drift that generated its
concentration. Self-consistency is a separate condition on `r`. -/
theorem vonMises_current_zero {D : ℝ} (hD : D ≠ 0) (K r θ : ℝ) :
    current D (drift K r) (vonMisesDensity (K * r / D)) θ = 0 := by
  rw [current, (density_hasDerivAt (K * r / D) θ).deriv, drift]
  field_simp
  ring

/-- The normalized Gibbs density solves the classical stationary equation.
This alone does not require or prove that its imposed `r` is its own mean. -/
theorem vonMises_stationary {D : ℝ} (hD : 0 < D) (K r : ℝ) :
    IsStationary D (drift K r) (vonMisesDensity (K * r / D)) := by
  have hzero : current D (drift K r) (vonMisesDensity (K * r / D)) = fun _ => 0 :=
    funext (vonMises_current_zero hD.ne' K r)
  refine ⟨fun θ => (density_hasDerivAt (K * r / D) θ).differentiableAt,
    density_periodic _, fun θ => vonMisesDensity_pos _ θ,
    vonMisesDensity_integral_eq_one _, ?_, fun θ => ?_⟩
  · rw [hzero]
    exact differentiable_const 0
  · simp only [operator, hzero, deriv_const', neg_zero]

/-- Classification of positive classical stationary probability densities for
the cosine drift. The mean direction is fixed to zero by coordinates; no
uniqueness across rotated mean directions is asserted. -/
theorem stationary_iff_vonMises {D : ℝ} (hD : 0 < D) (K r : ℝ) (ρ : ℝ → ℝ) :
    IsStationary D (drift K r) ρ ↔ ρ = vonMisesDensity (K * r / D) := by
  constructor
  · intro h
    have hV : Differentiable ℝ (fun x : ℝ => -K * r * Real.cos x) :=
      (Real.differentiable_cos).const_mul _
    have hVper : Function.Periodic (fun x : ℝ => -K * r * Real.cos x) (2 * π) := by
      intro x
      simp only
      rw [Real.cos_add_two_pi]
    rw [drift_eq_gradient K r] at h
    obtain ⟨c, hc, hρ⟩ := stationary_gibbs hD hV hVper h
    have hweight : ∀ θ, ρ θ = c * vonMisesWeight (K * r / D) θ := by
      intro θ
      rw [hρ θ, vonMisesWeight]
      congr 2
      field_simp
    have hnorm : (∫ θ in (-π)..π, ρ θ) = 1 := h.2.2.2.1
    have h1 : (∫ θ in (-π)..π, ρ θ) = c * vonMisesZ (K * r / D) := by
      simp only [hweight, intervalIntegral.integral_const_mul, vonMisesZ]
    rw [hnorm] at h1
    have hcZ : c = 1 / vonMisesZ (K * r / D) := by
      field_simp [(vonMisesZ_pos (K * r / D)).ne'] at h1 ⊢
      linarith
    funext θ
    rw [hweight θ, hcZ, vonMisesDensity]
    ring
  · rintro rfl
    exact vonMises_stationary hD K r

/-- Above threshold there is exactly one positive self-consistent mean
magnitude with a stationary density in the chosen mean-direction-zero frame.
Uniform density also remains stationary; phase rotations give an orbit. -/
theorem supercritical_stationary_existsUnique {D K : ℝ} (hD : 0 < D)
    (hKD : critical_coupling D < K) :
    ∃! r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∃ ρ, IsStationary D (drift K r) ρ ∧ circularOrderParameter ρ = (r : ℂ) := by
  have hiff : ∀ r : ℝ, (0 < r ∧ r ≤ 1 ∧
      ∃ ρ, IsStationary D (drift K r) ρ ∧ circularOrderParameter ρ = (r : ℂ))
      ↔ (0 < r ∧ r ≤ 1 ∧ r = selfConsistency K D r) := by
    intro r
    refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
    constructor
    · rintro ⟨ρ, hstat, hop⟩
      rw [(stationary_iff_vonMises hD K r ρ).mp hstat] at hop
      exact (fixedPoint_iff_selfReproducing K D r).mpr hop
    · intro hfix
      exact ⟨vonMisesDensity (K * r / D), vonMises_stationary hD K r,
        (fixedPoint_iff_selfReproducing K D r).mp hfix⟩
  simpa only [existsUnique_congr hiff] using supercritical_fixed_point_existsUnique hD hKD

#print axioms stationary_current_zero
#print axioms stationary_gibbs
#print axioms stationary_iff_vonMises
#print axioms supercritical_stationary_existsUnique

end PhysicsOfConsciousness.FokkerPlanck
