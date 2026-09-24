import PhysicsOfConsciousness.Phase6_AttentionRank

/-! # Reconstruction under diagonal input second moments
The weights are input second moments in the target eigenbasis. This theorem
bounds the weighted basis error; connecting it to a data distribution requires
zero off-diagonal second moments. It does not bound nonlinear decoders.
-/
open scoped BigOperators RealInnerProductSpace
open Module
namespace PhysicsOfConsciousness.AttentionRank
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A rank-limited linear decoder pays the omitted input-weighted spectral mass.
Selection is ordered by variance times squared eigenvalue, not eigenvalue alone.
The second moments are supplied; a general covariance need not share this basis. -/
theorem input_weighted_spectral_tail_le_error (b : OrthonormalBasis ι ℝ E)
    (K A : E →ₗ[ℝ] E) (lam variance : ι → ℝ)
    (hvariance : ∀ i, 0 ≤ variance i) (S : Finset ι) (τ : ℝ)
    (heigen : ∀ i, K (b i) = lam i • b i)
    (hrank : finrank ℝ A.range ≤ S.card)
    (hτ : 0 ≤ τ) (hin : ∀ i ∈ S, τ ≤ variance i * lam i ^ 2)
    (hout : ∀ i ∉ S, variance i * lam i ^ 2 ≤ τ) :
    ∑ i ∈ Sᶜ, variance i * lam i ^ 2 ≤ ∑ i, variance i * ‖K (b i) - A (b i)‖ ^ 2 := by
  let W := A.range
  let p := fun i => ‖W.starProjection (b i)‖ ^ 2
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i
    refine ⟨sq_nonneg _, ?_⟩
    have h := W.norm_starProjection_apply_le (b i)
    rw [b.norm_eq_one] at h
    dsimp [p]
    nlinarith [norm_nonneg (W.starProjection (b i))]
  have hmass : ∑ i, p i ≤ S.card := by
    rw [show (∑ i, p i) = (finrank ℝ W : ℝ) from projection_mass b W]
    exact_mod_cast hrank
  refine (weighted_tail (fun i => variance i * lam i ^ 2) p S τ hτ hp hmass hin hout).trans ?_
  apply Finset.sum_le_sum
  intro i _
  have hpy := W.norm_sq_eq_add_norm_sq_starProjection (b i)
  rw [b.norm_eq_one] at hpy
  have hnorm := Wᗮ.norm_starProjection_apply_le (K (b i) - A (b i))
  have hz : Wᗮ.starProjection (A (b i)) = 0 := by
    apply (Wᗮ.starProjection_apply_eq_zero_iff).mpr
    simpa only [Submodule.orthogonal_orthogonal] using (A.mem_range_self (b i))
  rw [map_sub, heigen i, map_smul, hz, sub_zero, norm_smul,
    Real.norm_eq_abs, ← heigen i] at hnorm
  have hsq : lam i ^ 2 * ‖Wᗮ.starProjection (b i)‖ ^ 2 ≤
      ‖K (b i) - A (b i)‖ ^ 2 := by
    have h := (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mpr hnorm
    simpa only [mul_pow, sq_abs] using h
  dsimp [p]
  have hw := mul_le_mul_of_nonneg_left hsq (hvariance i)
  nlinarith [mul_nonneg (hvariance i) (sq_nonneg (lam i))]


#print axioms input_weighted_spectral_tail_le_error
end PhysicsOfConsciousness.AttentionRank
