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

/-! ## Order, current, and dissipation -/


/-- Above threshold, positive self-consistent stationary order coexists with
zero current dissipation. The constant-in-time state also refutes a strictly
positive time-averaged bound based only on order and diffusion. No driven
cortical steady state or convergence to this equilibrium is asserted. -/
theorem supercritical_zero_dissipation {D K : ℝ} (hD : 0 < D)
    (hKD : critical_coupling D < K) :
    ∃ r ρ, 0 < r ∧ r ≤ 1 ∧ IsStationary D (drift K r) ρ ∧
      circularOrderParameter ρ = (r : ℂ) ∧ currentDissipation D (drift K r) ρ = 0 := by
  obtain ⟨r, ⟨hr, hr1, ρ, hstat, horder⟩, _⟩ :=
    supercritical_stationary_existsUnique hD hKD
  refine ⟨r, ρ, hr, hr1, hstat, horder, ?_⟩
  rw [(stationary_iff_vonMises hD K r ρ).mp hstat]
  simp [currentDissipation, vonMises_current_zero hD.ne']

/-- A bounded test function's integrated current has squared magnitude at
most diffusion times current dissipation. The proof is weighted square
completion, not a physical speed postulate. Normalization, positivity and
continuity are explicit; a bound on the test function is required. -/
lemma weighted_current_sq_le {D : ℝ} (hD : 0 < D) {v ρ g : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ θ, 0 < ρ θ)
    (hnorm : (∫ θ in (-π)..π, ρ θ) = 1)
    (hJ : Continuous (current D v ρ)) (hg : Continuous g) (hgb : ∀ θ, g θ ^ 2 ≤ 1) :
    (∫ θ in (-π)..π, g θ * current D v ρ θ) ^ 2 ≤ D * currentDissipation D v ρ := by
  let m := ∫ θ in (-π)..π, g θ * current D v ρ θ
  have hq : Continuous (fun θ => current D v ρ θ ^ 2 / ρ θ) :=
    (hJ.pow 2).div hρ (fun θ => (hpos θ).ne')
  have hw : Continuous (fun θ => g θ ^ 2 * ρ θ) := (hg.pow 2).mul hρ
  have hmass : (∫ θ in (-π)..π, g θ ^ 2 * ρ θ) ≤ 1 := by
    rw [← hnorm]
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (hw.intervalIntegrable _ _) (hρ.intervalIntegrable _ _)
    intro θ _
    nlinarith [hgb θ, hpos θ]
  have hexpand : (∫ θ in (-π)..π,
      (current D v ρ θ - m * g θ * ρ θ) ^ 2 / ρ θ) =
      (∫ θ in (-π)..π, current D v ρ θ ^ 2 / ρ θ) - 2 * m ^ 2 +
        m ^ 2 * (∫ θ in (-π)..π, g θ ^ 2 * ρ θ) := by
    have heq : (fun θ => (current D v ρ θ - m * g θ * ρ θ) ^ 2 / ρ θ) =
        fun θ => current D v ρ θ ^ 2 / ρ θ - 2 * m * (g θ * current D v ρ θ) +
          m ^ 2 * (g θ ^ 2 * ρ θ) := by
      funext θ
      field_simp [(hpos θ).ne']
      ring
    have hiq : IntervalIntegrable (fun θ => current D v ρ θ ^ 2 / ρ θ)
        volume (-π) π := hq.intervalIntegrable _ _
    have hiJ : IntervalIntegrable (fun θ => 2 * m * (g θ * current D v ρ θ))
        volume (-π) π := ((hg.mul hJ).const_mul _).intervalIntegrable _ _
    have hir : IntervalIntegrable (fun θ => m ^ 2 * (g θ ^ 2 * ρ θ))
        volume (-π) π := (hw.const_mul _).intervalIntegrable _ _
    have hisub : IntervalIntegrable
        (fun θ => current D v ρ θ ^ 2 / ρ θ - 2 * m * (g θ * current D v ρ θ))
        volume (-π) π := hiq.sub hiJ
    rw [heq, intervalIntegral.integral_add hisub hir,
      intervalIntegral.integral_sub hiq hiJ,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    dsimp [m]
    ring
  have hnonneg : 0 ≤ ∫ θ in (-π)..π,
      (current D v ρ θ - m * g θ * ρ θ) ^ 2 / ρ θ :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
      (fun θ _ => div_nonneg (sq_nonneg _) (hpos θ).le)
  have hscale : D * currentDissipation D v ρ =
      ∫ θ in (-π)..π, current D v ρ θ ^ 2 / ρ θ := by
    rw [currentDissipation, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    field_simp
  rw [hexpand] at hnonneg
  rw [hscale]
  have hmass' := mul_le_mul_of_nonneg_left hmass (sq_nonneg m)
  dsimp [m] at *
  nlinarith


/-- The normalized positive density pays at least squared mean current divided
by diffusion. This square-completion bound uses the density and its own current;
positive order alone does not ensure nonzero mean current. Conversion to power
requires a thermal scale and a physical identification of this entropy production. -/
theorem current_integral_sq_le {D : ℝ} (hD : 0 < D) {v ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ θ, 0 < ρ θ)
    (hnorm : (∫ θ in (-π)..π, ρ θ) = 1)
    (hJ : Continuous (current D v ρ)) :
    (∫ θ in (-π)..π, current D v ρ θ) ^ 2 ≤ D * currentDissipation D v ρ := by
  simpa using weighted_current_sq_le hD hρ hpos hnorm hJ
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))) (fun _ => by norm_num)

/-- No bound strictly positive at every positive order holds for all stationary
self-consistent states above threshold. A nonequilibrium drive or current constraint
is additional physical information; this result does not rule out bounds using it. -/
theorem no_positive_order_only_bound {D K : ℝ} (hD : 0 < D)
    (hKD : critical_coupling D < K) (f : ℝ → ℝ) (hf : ∀ r, 0 < r → 0 < f r) :
    ¬ ∀ r ρ, 0 < r → r ≤ 1 → IsStationary D (drift K r) ρ →
      circularOrderParameter ρ = (r : ℂ) → f r ≤ currentDissipation D (drift K r) ρ := by
  obtain ⟨r, ρ, hr, hr1, hs, ho, hd⟩ := supercritical_zero_dissipation hD hKD
  intro h
  have hb := h r ρ hr hr1 hs ho
  rw [hd] at hb
  exact (not_le_of_gt (hf r hr)) hb

/-- Uniform density under a constant drive carries its explicit constant current. -/
theorem uniform_current (D ω θ : ℝ) :
    current D (fun _ => ω) (fun _ => 1 / (2 * π)) θ = ω / (2 * π) := by
  simp [current, div_eq_mul_inv]

/-- A uniform driven state attains the current lower bound exactly. The drive
is prescribed; its units and physical work source are not derived here. -/
theorem uniform_current_dissipation (D ω : ℝ) :
    currentDissipation D (fun _ => ω) (fun _ => 1 / (2 * π)) = ω ^ 2 / D := by
  simp only [currentDissipation, uniform_current, intervalIntegral.integral_const, smul_eq_mul]
  by_cases hD : D = 0
  · simp [hD]
  · field_simp
    ring

/-- The constant-drive uniform state solves the stationary equation. With
nonzero drive it has nonzero current, so the current bound has nontrivial
equality cases. This witness has zero phase order. -/
theorem uniform_driven_stationary (D ω : ℝ) :
    IsStationary D (fun _ => ω) (fun _ => 1 / (2 * π)) := by
  have hcur : current D (fun _ => ω) (fun _ => 1 / (2 * π)) = fun _ => ω / (2 * π) :=
    funext (uniform_current D ω)
  refine ⟨differentiable_const _, fun _ => rfl, fun _ => by positivity, ?_, ?_, ?_⟩
  · rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp
    ring
  · rw [hcur]
    exact differentiable_const _
  · intro θ
    simp only [operator, hcur, deriv_const, neg_zero]


#print axioms supercritical_zero_dissipation
#print axioms current_integral_sq_le
#print axioms no_positive_order_only_bound
#print axioms uniform_current_dissipation
#print axioms uniform_driven_stationary

/-- The cosine moment of the Fokker--Planck operator obeys a speed bound.
Integration by parts identifies its rate with minus the sine-weighted current.
For a classical evolving density, this is its mean-cosine speed whenever time
differentiation under the integral is justified. This theorem constructs no
evolution and bounds neither the magnitude of the complex order parameter nor
the speed of an externally specified coupling parameter. -/
lemma cosine_rate_sq_le_dissipation {D : ℝ} (hD : 0 < D) {v ρ : ℝ → ℝ}
    (hρ : Continuous ρ) (hpos : ∀ θ, 0 < ρ θ)
    (hnorm : (∫ θ in (-π)..π, ρ θ) = 1)
    (hJ : Differentiable ℝ (current D v ρ))
    (hJ' : Continuous (deriv (current D v ρ)))
    (hper : Function.Periodic (current D v ρ) (2 * π)) :
    (∫ θ in (-π)..π, Real.cos θ * operator D v ρ θ) ^ 2 ≤
      D * currentDissipation D v ρ := by
  have hb := weighted_current_sq_le hD hρ hpos hnorm hJ.continuous
    Real.continuous_sin (fun θ => by nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)])
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    Real.continuous_cos.continuousOn hJ.continuous.continuousOn
    (fun θ _ => Real.hasDerivAt_cos θ) (fun θ _ => (hJ θ).hasDerivAt)
    (Real.continuous_sin.neg.intervalIntegrable (-π) π) (hJ'.intervalIntegrable (-π) π)
  have hends : current D v ρ π = current D v ρ (-π) := by
    simpa only [show -π + 2 * π = π by ring] using hper (-π)
  simp only [Real.cos_pi, Real.cos_neg, hends, sub_self, neg_mul,
    intervalIntegral.integral_neg, zero_sub, neg_neg] at hi
  have hrate : (∫ θ in (-π)..π, Real.cos θ * operator D v ρ θ) =
      -(∫ θ in (-π)..π, Real.sin θ * current D v ρ θ) := by
    simp only [operator, mul_neg, intervalIntegral.integral_neg, hi]
  rwa [hrate, neg_sq]

/-- A positive coupling can have any prescribed derivative while the uniform
self-consistent state has zero current dissipation at all times. This refutes
an unrestricted coupling-speed bound from phase-current cost alone. It does not
refute a bound assuming positive order, an actuator cost, or a calibrated
relation between coupling and the changing density. -/
lemma arbitrary_coupling_speed_zero_cost (D a : ℝ) (hD : 0 < D) :
    ∃ K : ℝ → ℝ, HasDerivAt K a 0 ∧ ∀ t, 0 < K t ∧
      IsStationary D (drift (K t) 0) (vonMisesDensity 0) ∧
      currentDissipation D (drift (K t) 0) (vonMisesDensity 0) = 0 := by
  refine ⟨fun t => Real.exp (a * t), ?_, fun t => ?_⟩
  · simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).exp
  · have hs := vonMises_stationary hD (Real.exp (a * t)) 0
    simp only [mul_zero, zero_div] at hs
    refine ⟨Real.exp_pos _, hs, ?_⟩
    have hzero (θ : ℝ) : current D (drift (Real.exp (a * t)) 0) (vonMisesDensity 0) θ = 0 := by
      simpa only [mul_zero, zero_div] using vonMises_current_zero hD.ne' (Real.exp (a * t)) 0 θ
    simp [currentDissipation, hzero]

/-- The uniform density is an actual constant-in-time solution of the
nonautonomous continuity equation for every prescribed coupling schedule.
This rules out dismissing the zero-cost ramp as merely successive unrelated
stationary states. It is an incoherent solution, not an ordered recovery path. -/
theorem uniform_time_dependent_solution {D : ℝ} (hD : 0 < D) (K : ℝ → ℝ) (t θ : ℝ) :
    HasDerivAt (fun _t : ℝ => vonMisesDensity 0 θ)
      (operator D (drift (K t) 0) (vonMisesDensity 0) θ) t := by
  have hs := vonMises_stationary hD (K t) 0
  simp only [mul_zero, zero_div] at hs
  rw [hs.2.2.2.2.2 θ]
  exact hasDerivAt_const t _

#print axioms weighted_current_sq_le
#print axioms cosine_rate_sq_le_dissipation
#print axioms arbitrary_coupling_speed_zero_cost
#print axioms uniform_time_dependent_solution

end PhysicsOfConsciousness.FokkerPlanck
