import PhysicsOfConsciousness.Phase8_WeightedPoincare

/-!
# Linear stability of the coherent phase orbit

At concentration `a > 0`, put `K = D / E(a)`, with `E` the sine second
moment. This parametrizes the supercritical self-consistent branch. The
primitive generator below is the negative of the linearized current of that
same density. Integration by parts makes its weighted primitive pairing
symmetric and identifies its negative with the coherent quadratic form.

`coherent_linear_stability` is the spectral-gap inequality on the classical
form domain, transverse to rotation in the natural weighted primitive metric.
The diffusion and gap constants are proved positive. The rotation mode is
nonzero and has zero generator, so a gap on the entire space would be false.

Scope: these are linear operator and energy estimates for regular periodic
perturbations. They do not construct a self-adjoint operator closure or its
semigroup, prove existence of time-dependent PDE solutions, nonlinear orbital
stability, dynamical selection, or a finite-particle mean-field limit.
-/

open Real MeasureTheory intervalIntegral Set

namespace PhysicsOfConsciousness.FokkerPlanck

/-- Coupling corresponding to concentration `a` on the coherent branch. -/
noncomputable def branchCoupling (D a : ℝ) : ℝ := D / vonMisesSRatio a

theorem branchCoupling_supercritical {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    2 * D < branchCoupling D a := by
  have hs := sRatio_pos ha
  have hh := vonMisesSRatio_lt_half ha
  unfold branchCoupling
  apply (lt_div_iff₀ hs).mpr
  nlinarith

lemma branchCoupling_mean {a : ℝ} (ha : 0 < a) (D : ℝ) :
    branchCoupling D a * besselRatio a = D * a := by
  rw [branchCoupling, besselRatio_eq_mul]
  field_simp [(sRatio_pos ha).ne']

/-- This concentration parametrization uses a density whose order parameter
is its own mean-field input, not an externally fixed preferred direction. -/
theorem branch_stationary {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    IsStationary D (meanDrift (branchCoupling D a) (vonMisesDensity a))
      (vonMisesDensity a) := by
  have hc : branchCoupling D a * besselRatio a / D = a := by
    rw [branchCoupling_mean ha]; exact mul_div_cancel_left₀ a hD.ne'
  have hf : besselRatio a = selfConsistency (branchCoupling D a) D (besselRatio a) := by
    rw [selfConsistency, hc]
  simpa only [hc] using selfConsistent_stationary hD hf

/-- First variation of the phase-space free energy; an arbitrary constant
would give the same derivative and the same zero-mass pairing. -/
noncomputable def chemical (a D K : ℝ) (f : CircleFunction) : CircleFunction :=
  D • f - K • (average a (f * circleCos) • circleCos +
    average a (f * circleSin) • circleSin)

noncomputable def chemicalDeriv (a D K : ℝ) (f df : CircleFunction) : CircleFunction :=
  D • df + (K * average a (f * circleCos)) • circleSin -
    (K * average a (f * circleSin)) • circleCos

noncomputable def primitiveGenerator (a D K : ℝ) (f df : CircleFunction) : CircleFunction :=
  density a * chemicalDeriv a D K f df

lemma chemical_hasDerivAt (a D K : ℝ) (f df : CircleFunction)
    (hf : ∀ θ, HasDerivAt f (df θ) θ) (θ : ℝ) :
    HasDerivAt (chemical a D K f) (chemicalDeriv a D K f df θ) θ := by
  apply (((hf θ).const_mul D).sub
    ((((hasDerivAt_cos θ).const_mul (average a (f * circleCos))).add
      ((hasDerivAt_sin θ).const_mul (average a (f * circleSin)))).const_mul K)).congr_deriv
  change D * df θ - K * (average a (f * circleCos) * -sin θ +
      average a (f * circleSin) * cos θ) =
    D * df θ + (K * average a (f * circleCos)) * sin θ -
      (K * average a (f * circleSin)) * cos θ
  ring

lemma cosMoment_density_mul (a : ℝ) (f : CircleFunction) :
    cosMoment (fun θ => vonMisesDensity a θ * f θ) = average a (f * circleCos) := by
  apply intervalIntegral.integral_congr
  intro θ _
  change cos θ * (vonMisesDensity a θ * f θ) = (f θ * cos θ) * vonMisesDensity a θ
  ring

lemma sinMoment_density_mul (a : ℝ) (f : CircleFunction) :
    sinMoment (fun θ => vonMisesDensity a θ * f θ) = average a (f * circleSin) := by
  apply intervalIntegral.integral_congr
  intro θ _
  change sin θ * (vonMisesDensity a θ * f θ) = (f θ * sin θ) * vonMisesDensity a θ
  ring

/-- The primitive generator is minus the actual linearized current. The
background drift comes from the same self-consistent density. This equality
is the connection required before interpreting the quadratic form dynamically. -/
theorem generator_eq_neg_linearCurrent {a : ℝ} (ha : 0 < a) (D : ℝ)
    (f df : CircleFunction) (hf : ∀ θ, HasDerivAt f (df θ) θ) (θ : ℝ) :
    primitiveGenerator a D (branchCoupling D a) f df θ =
      -linearCurrent D (branchCoupling D a) (vonMisesDensity a)
        (fun x => vonMisesDensity a x * f x) θ := by
  have hd := ((density_hasDerivAt a θ).mul (hf θ)).deriv
  change deriv (fun x => vonMisesDensity a x * f x) θ = _ at hd
  rw [linearCurrent, hd, meanDrift_vonMises]
  unfold drift
  rw [show -branchCoupling D a * besselRatio a = -(D * a) by
    rw [neg_mul, branchCoupling_mean ha]]
  rw [meanDrift, cosMoment_density_mul, sinMoment_density_mul]
  change vonMisesDensity a θ *
      (D * df θ + (branchCoupling D a * average a (f * circleCos)) * sin θ -
        (branchCoupling D a * average a (f * circleSin)) * cos θ) = _
  ring

lemma chemical_periodic_boundary (a D K : ℝ) (g : CircleFunction)
    (hg : g (-π) = g π) : chemical a D K g (-π) = chemical a D K g π := by
  change D * g (-π) - K * (average a (g * circleCos) * cos (-π) +
    average a (g * circleSin) * sin (-π)) =
    D * g π - K * (average a (g * circleCos) * cos π + average a (g * circleSin) * sin π)
  rw [hg]
  simp

/-- Integration by parts identifies the weighted primitive pairing with the
symmetric density form. Regularity and periodic boundaries are explicit; no
claim about an operator's closed domain is hidden in the identity. -/
theorem generator_pairing (a D K : ℝ) (U f g dg : CircleFunction)
    (hU : ∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ)
    (hg : ∀ θ, HasDerivAt g (dg θ) θ)
    (hUp : U (-π) = U π) (hgp : g (-π) = g π) :
    inverseAverage a (U * primitiveGenerator a D K g dg) =
      -D * average a (f * g) + K * (average a (f * circleCos) * average a (g * circleCos) +
        average a (f * circleSin) * average a (g * circleSin)) := by
  have hi := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := -π) (b := π) U.continuous.continuousOn (chemical a D K g).continuous.continuousOn
    (fun θ _ => hU θ) (fun θ _ => chemical_hasDerivAt a D K g dg hg θ)
    (((density a).continuous.mul f.continuous).intervalIntegrable _ _)
    ((chemicalDeriv a D K g dg).continuous.intervalIntegrable _ _)
  rw [hUp, chemical_periodic_boundary a D K g hgp, sub_self] at hi
  have hfun : (fun θ => vonMisesDensity a θ * f θ * chemical a D K g θ +
      U θ * chemicalDeriv a D K g dg θ) = fun θ =>
      (f * chemical a D K g) θ * vonMisesDensity a θ +
        (U * primitiveGenerator a D K g dg) θ * (1 / vonMisesDensity a θ) := by
    funext θ
    change vonMisesDensity a θ * f θ * chemical a D K g θ + U θ * chemicalDeriv a D K g dg θ =
      (f θ * chemical a D K g θ) * vonMisesDensity a θ +
        (U θ * (vonMisesDensity a θ * chemicalDeriv a D K g dg θ)) * (1 / vonMisesDensity a θ)
    field_simp [(vonMisesDensity_pos a θ).ne']
  rw [hfun] at hi
  have h1 : IntervalIntegrable (fun θ => (f * chemical a D K g) θ * vonMisesDensity a θ)
      volume (-π) π := ((f * chemical a D K g).continuous.mul (density a).continuous).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => (U * primitiveGenerator a D K g dg) θ *
      (1 / vonMisesDensity a θ)) volume (-π) π :=
    ((U * primitiveGenerator a D K g dg).continuous.mul (inverseDensity a).continuous).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2] at hi
  change average a (f * chemical a D K g) +
    inverseAverage a (U * primitiveGenerator a D K g dg) = 0 at hi
  simp only [chemical, mul_sub, mul_add, mul_smul_comm, map_sub, map_add, map_smul,
    smul_eq_mul] at hi
  linarith

/-- Symmetry in the weighted primitive metric. It is symmetry on the regular
periodic form domain, not a construction of an essentially self-adjoint closure. -/
theorem generator_symmetric (a D K : ℝ) (U V f g df dg : CircleFunction)
    (hU : ∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ)
    (hV : ∀ θ, HasDerivAt V (vonMisesDensity a θ * g θ) θ)
    (hf : ∀ θ, HasDerivAt f (df θ) θ) (hg : ∀ θ, HasDerivAt g (dg θ) θ)
    (hUp : U (-π) = U π) (hVp : V (-π) = V π)
    (hfp : f (-π) = f π) (hgp : g (-π) = g π) :
    inverseAverage a (U * primitiveGenerator a D K g dg) =
      inverseAverage a (V * primitiveGenerator a D K f df) := by
  rw [generator_pairing a D K U f g dg hU hg hUp hgp,
    generator_pairing a D K V g f df hV hf hVp hfp, mul_comm f g]
  ring

lemma generator_energy (a D : ℝ) (U f df : CircleFunction)
    (hU : ∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ)
    (hf : ∀ θ, HasDerivAt f (df θ) θ)
    (hUp : U (-π) = U π) (hfp : f (-π) = f π) :
    inverseAverage a (U * primitiveGenerator a D (branchCoupling D a) f df) =
      -D * coherentForm a f := by
  rw [generator_pairing a D (branchCoupling D a) U f f df hU hf hUp hfp]
  dsimp [branchCoupling, coherentForm]
  ring

noncomputable def linearStabilityRate (D a : ℝ) : ℝ :=
  D * coherenceGap a / inverseAverage a 1

theorem linearStabilityRate_pos {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    0 < linearStabilityRate D a :=
  div_pos (mul_pos hD (coherenceGap_pos ha)) (inverseAverage_one_pos a)

/-- The coherent branch's spectral-gap inequality, modulo its phase orbit.
The form is strictly dissipative in the weighted primitive norm on the
orthogonal complement of rotation. Together with `generator_symmetric` this
is the classical linear stability estimate. It constructs no PDE solution,
semigroup or operator closure and proves no nonlinear stability or selection. -/
theorem coherent_linear_stability {D a : ℝ} (hD : 0 < D) (ha : 0 < a)
    (U f df : CircleFunction)
    (hU : ∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ)
    (hf : ∀ θ, HasDerivAt f (df θ) θ)
    (hUp : U (-π) = U π) (hfp : f (-π) = f π)
    (hmean : inverseAverage a U = 0)
    (horth : inverseAverage a (U * rotationPrimitive a) = 0) :
    inverseAverage a (U * primitiveGenerator a D (branchCoupling D a) f df) ≤
      -linearStabilityRate D a * inverseAverage a (U * U) := by
  have hp := transverse_poincare ha U f hU hmean horth
  have hg := coherent_form_gap ha f (primitive_mass_zero a U f hU hUp)
  have hA := inverseAverage_one_pos a
  have hgap := coherenceGap_pos ha
  have hbound : coherenceGap a * inverseAverage a (U * U) ≤
      inverseAverage a 1 * coherentForm a f := by
    have h1 := mul_le_mul_of_nonneg_left hp hgap.le
    have h2 := mul_le_mul_of_nonneg_left hg hA.le
    nlinarith
  have hb : linearStabilityRate D a * inverseAverage a (U * U) ≤ D * coherentForm a f := by
    calc
      _ = D * (coherenceGap a * inverseAverage a (U * U)) / inverseAverage a 1 := by
        dsimp [linearStabilityRate]; ring
      _ ≤ D * (inverseAverage a 1 * coherentForm a f) / inverseAverage a 1 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound hD.le) hA.le
      _ = D * coherentForm a f := by field_simp
  rw [generator_energy a D U f df hU hf hUp hfp]
  linarith

/-- The rotation direction has zero generator. Its nonzero value at `π/2`
rules out a positive spectral gap on the full perturbation space. -/
theorem rotation_generator_zero {a : ℝ} (ha : 0 < a) (D : ℝ) :
    primitiveGenerator a D (branchCoupling D a) circleSin circleCos = 0 := by
  have hh : chemicalDeriv a D (branchCoupling D a) circleSin circleCos = 0 := by
    simp [chemicalDeriv, average_sin_cos, average_sin_sq, branchCoupling,
      (sRatio_pos ha).ne']
  simp [primitiveGenerator, hh]

/-- A compact predicate for the proved classical gap estimate. It is a
property of a named scalar model, with its rate fixed by that density; it is
never an assumed field of a physical data class. -/
def HasCoherentLinearGap (D K a : ℝ) : Prop :=
  0 < linearStabilityRate D a ∧ ∀ U f df : CircleFunction,
    (∀ θ, HasDerivAt U (vonMisesDensity a θ * f θ) θ) →
    (∀ θ, HasDerivAt f (df θ) θ) → U (-π) = U π → f (-π) = f π →
    inverseAverage a U = 0 → inverseAverage a (U * rotationPrimitive a) = 0 →
    inverseAverage a (U * primitiveGenerator a D K f df) ≤
      -linearStabilityRate D a * inverseAverage a (U * U)

/-- Packaging of the derived estimate for consumers of the scalar phase
model. It carries the same regularity and linear scope as the theorem. -/
theorem branch_hasLinearGap {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    HasCoherentLinearGap D (branchCoupling D a) a :=
  ⟨linearStabilityRate_pos hD ha, coherent_linear_stability hD ha⟩

/-- At the coherent stationary state current dissipation vanishes while the
phase-averaged squared drift is positive. Both quantities here are on phase
space; this proves no identification with `sigmaContinuum` on substrate sites. -/
theorem stationary_current_separation {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    currentDissipation D (meanDrift (branchCoupling D a) (vonMisesDensity a))
      (vonMisesDensity a) = 0 ∧
    0 < average a (((-D * a) • circleSin) * ((-D * a) • circleSin)) / D := by
  have he : branchCoupling D a * besselRatio a / D = a := by
    rw [branchCoupling_mean ha]; exact mul_div_cancel_left₀ a hD.ne'
  constructor
  · have hj (θ : ℝ) := vonMises_current_zero hD.ne' (branchCoupling D a) (besselRatio a) θ
    rw [he] at hj
    simp only [currentDissipation]
    have hv : meanDrift (branchCoupling D a) (vonMisesDensity a) =
        drift (branchCoupling D a) (besselRatio a) := funext (meanDrift_vonMises _ _)
    simp [hv, hj]
  · simp only [smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul, average_sin_sq]
    have hs := sRatio_pos ha
    apply div_pos _ hD
    calc
      _ = (D * a) ^ 2 * vonMisesSRatio a := by ring
      _ > 0 := mul_pos (sq_pos_of_pos (mul_pos hD ha)) hs

#print axioms branch_stationary
#print axioms generator_eq_neg_linearCurrent
#print axioms generator_symmetric
#print axioms coherent_linear_stability
#print axioms rotation_generator_zero
#print axioms stationary_current_separation

end PhysicsOfConsciousness.FokkerPlanck
