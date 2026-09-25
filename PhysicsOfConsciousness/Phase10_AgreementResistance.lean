import Mathlib

/-!
# Phase 10 — typical agreement is set by effective resistance

The chaining bound through overlapping patches is a worst case: it is attained
by a phase gradient, and it grows linearly in the number of hops. Noise does not
produce that configuration. At identical natural frequencies a noisy coupled
sheet is a gradient system whose stationary density is `∝ exp(−E_K(θ)/D)`, and
in the harmonic approximation the variance of the phase difference between two
sites is `D` times their effective resistance, the couplings `K i j` acting as
conductances. That identity is Gaussian algebra and is checked numerically in
`simulations/unity_agreement.py`; this module proves the parts that hold without
the approximation.

* **`energy K u`.** The Dirichlet energy `½ Σ_{i,j} K i j (u i − u j)²` of a
  phase configuration `u`.
* **`conductance K a b`.** The effective conductance between `a` and `b`: the
  least energy of a configuration whose phase difference across them is one.
  The effective resistance is its reciprocal.

The results:

* **`conductance_mul_sq_le_energy`.** Every configuration's phase difference
  across `a, b` is bounded by its energy: `C (u a − u b)² ≤ E_K(u)`. The
  resistance is thus the best constant turning energy into disagreement.
* **`conductance_mono`** (Rayleigh monotonicity). Adding coupling never lowers
  the conductance. A long-range tail added to a short-range kernel can
  therefore only improve the typical agreement, whatever its shape.
* **`le_conductance_of_edge`.** A direct coupling caps the resistance:
  `K a b ≤ C`, at any distance between `a` and `b`.
* **`integral_dist_sq_le`.** A Lipschitz encoder transfers phase agreement to
  content agreement in mean square: the mean-square content discrepancy is at
  most `L²` times the mean-square phase difference, under any distribution of
  configurations. With the harmonic identity the root-mean-square content
  discrepancy is at most `L √(D / C)`.

Non-vacuity — a series pair of couplings with conductance `½`, raised to at least
`1` by a direct edge — is `Examples/AgreementResistance.lean`.
-/

open MeasureTheory

namespace PhysicsOfConsciousness.PhysicalUnity

variable {ι : Type*} [Fintype ι]

/-- The Dirichlet energy of a phase configuration `u` under the couplings `K`. -/
noncomputable def energy (K : ι → ι → ℝ) (u : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ p : ι × ι, K p.1 p.2 * (u p.1 - u p.2) ^ 2

/-- The effective conductance between `a` and `b`: the least energy of a
configuration with unit phase difference across them. -/
noncomputable def conductance (K : ι → ι → ℝ) (a b : ι) : ℝ :=
  sInf (energy K '' {u | u a - u b = 1})

lemma energy_nonneg {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) (u : ι → ℝ) :
    0 ≤ energy K u :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => mul_nonneg (hK _ _) (sq_nonneg _))

lemma energy_smul (K : ι → ι → ℝ) (c : ℝ) (u : ι → ℝ) :
    energy K (c • u) = c ^ 2 * energy K u := by
  have h (p : ι × ι) : K p.1 p.2 * ((c • u) p.1 - (c • u) p.2) ^ 2 =
      c ^ 2 * (K p.1 p.2 * (u p.1 - u p.2) ^ 2) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [energy, h, ← Finset.mul_sum]
  ring

lemma energy_mono {K K' : ι → ι → ℝ} (hKK' : ∀ i j, K i j ≤ K' i j) (u : ι → ℝ) :
    energy K u ≤ energy K' u := by
  unfold energy
  gcongr with p
  exact hKK' _ _

lemma bddBelow_energy {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) (s : Set (ι → ℝ)) :
    BddBelow (energy K '' s) :=
  ⟨0, by rintro _ ⟨u, -, rfl⟩; exact energy_nonneg hK u⟩

lemma conductance_nonneg {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) (a b : ι) :
    0 ≤ conductance K a b :=
  Real.sInf_nonneg (by rintro _ ⟨u, -, rfl⟩; exact energy_nonneg hK u)

lemma nonempty_unitDrop [DecidableEq ι] {a b : ι} (hab : a ≠ b) :
    (energy K '' {u : ι → ℝ | u a - u b = 1}).Nonempty :=
  ⟨_, Pi.single a 1, by simp [hab.symm], rfl⟩

/-- **Energy bounds disagreement.** The squared phase difference across `a, b`,
weighted by their effective conductance, never exceeds the configuration's
energy. -/
theorem conductance_mul_sq_le_energy {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (a b : ι) (u : ι → ℝ) : conductance K a b * (u a - u b) ^ 2 ≤ energy K u := by
  set d := u a - u b
  rcases eq_or_ne d 0 with hd | hd
  · simp [hd, energy_nonneg hK u]
  have hv : (d⁻¹ • u) a - (d⁻¹ • u) b = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub]
    exact inv_mul_cancel₀ hd
  have hle : conductance K a b ≤ energy K (d⁻¹ • u) :=
    csInf_le (bddBelow_energy hK _) ⟨_, hv, rfl⟩
  rw [energy_smul, inv_pow] at hle
  have hd2 : 0 < d ^ 2 := by positivity
  calc conductance K a b * d ^ 2 ≤ (d ^ 2)⁻¹ * energy K u * d ^ 2 :=
        mul_le_mul_of_nonneg_right hle hd2.le
    _ = energy K u := by field_simp

/-- **Rayleigh monotonicity.** Adding coupling never lowers the effective
conductance, so it never raises the effective resistance. -/
theorem conductance_mono [DecidableEq ι] {K K' : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hKK' : ∀ i j, K i j ≤ K' i j) {a b : ι} (hab : a ≠ b) :
    conductance K a b ≤ conductance K' a b := by
  refine le_csInf (nonempty_unitDrop hab) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact (csInf_le (bddBelow_energy hK _) ⟨u, hu, rfl⟩).trans (energy_mono hKK' u)

/-- **A direct coupling caps the resistance.** Whatever the distance between `a`
and `b`, their effective conductance is at least the coupling that joins them
directly. -/
theorem le_conductance_of_edge [DecidableEq ι] {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hsym : ∀ i j, K i j = K j i) {a b : ι} (hab : a ≠ b) :
    K a b ≤ conductance K a b := by
  refine le_csInf (nonempty_unitDrop hab) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' : u b - u a = -1 := by simp only [Set.mem_ofPred_eq] at hu; linarith
  have hsub : ({(a, b), (b, a)} : Finset (ι × ι)) ⊆ Finset.univ := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p : ι × ι => K p.1 p.2 * (u p.1 - u p.2) ^ 2)
    (fun p _ _ => mul_nonneg (hK _ _) (sq_nonneg _))
  have hne : (a, b) ≠ (b, a) := fun h => hab (Prod.mk.inj h).1
  rw [Finset.sum_pair hne] at hsum
  simp only [Set.mem_ofPred_eq] at hu
  rw [hu, hu', hsym b a] at hsum
  unfold energy
  linarith

omit [Fintype ι] in
/-- **Phase agreement becomes content agreement.** Under any distribution of
configurations, an `L`-Lipschitz encoder's mean-square content discrepancy
between `a` and `b` is at most `L²` times their mean-square phase difference. -/
theorem integral_dist_sq_le {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace (ι → ℝ)]
    {μ : Measure (ι → ℝ)} {Φ : ℝ → Y} {L : NNReal} (hΦ : LipschitzWith L Φ) (a b : ι)
    (hint : Integrable (fun θ : ι → ℝ => (θ a - θ b) ^ 2) μ) :
    ∫ θ, dist (Φ (θ a)) (Φ (θ b)) ^ 2 ∂μ ≤ (L : ℝ) ^ 2 * ∫ θ, (θ a - θ b) ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (hint.const_mul _) (Filter.Eventually.of_forall fun θ => ?_)
  have h := hΦ.dist_le_mul (θ a) (θ b)
  rw [Real.dist_eq] at h
  calc dist (Φ (θ a)) (Φ (θ b)) ^ 2 ≤ ((L : ℝ) * |θ a - θ b|) ^ 2 :=
        pow_le_pow_left₀ dist_nonneg h 2
    _ = (L : ℝ) ^ 2 * (θ a - θ b) ^ 2 := by rw [mul_pow, sq_abs]

end PhysicsOfConsciousness.PhysicalUnity
