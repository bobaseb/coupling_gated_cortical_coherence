import PhysicsOfConsciousness.Phase6_AttentionRank

/-!
# Singular-tail rank floor after a supplied input covariance factor

For a linear input factor `R`, the basis sum below is the squared error of
`(K-A) ∘ R`. A factorization of a measured second-moment operator as `R R*`
turns it into the input-weighted reconstruction error, including correlated
inputs. The theorem assumes singular bases and values for `K ∘ R`; it does
not construct an SVD, estimate a covariance from data, or bound nonlinear
decoders. The output and input spaces are the same finite-dimensional space.
-/

open scoped BigOperators RealInnerProductSpace
open Module
namespace PhysicsOfConsciousness.AttentionRank

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A rank-limited linear decoder pays the omitted squared singular values of
the covariance-weighted target `K ∘ R`. The supplied singular-vector identity
carries the spectral hypothesis; no empirical distribution or nonlinear model
is characterized by this theorem alone. -/
theorem covariance_root_singular_tail_le_error
    (b c : OrthonormalBasis ι ℝ E) (R K A : E →ₗ[ℝ] E)
    (lam : ι → ℝ) (S : Finset ι) (τ : ℝ)
    (hsingular : ∀ i, K (R (b i)) = lam i • c i)
    (hrank : finrank ℝ A.range ≤ S.card)
    (hτ : 0 ≤ τ) (hin : ∀ i ∈ S, τ ≤ lam i ^ 2)
    (hout : ∀ i ∉ S, lam i ^ 2 ≤ τ) :
    ∑ i ∈ Sᶜ, lam i ^ 2 ≤
      ∑ i, ‖K (R (b i)) - A (R (b i))‖ ^ 2 := by
  let W := A.range
  let p := fun i => ‖W.starProjection (c i)‖ ^ 2
  have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i
    refine ⟨sq_nonneg _, ?_⟩
    have h := W.norm_starProjection_apply_le (c i)
    rw [c.norm_eq_one] at h
    dsimp [p]
    nlinarith [norm_nonneg (W.starProjection (c i))]
  have hmass : ∑ i, p i ≤ S.card := by
    rw [show (∑ i, p i) = (finrank ℝ W : ℝ) from projection_mass c W]
    exact_mod_cast hrank
  refine (weighted_tail (fun i => lam i ^ 2) p S τ hτ hp hmass hin hout).trans ?_
  apply Finset.sum_le_sum
  intro i _
  have hpy := W.norm_sq_eq_add_norm_sq_starProjection (c i)
  rw [c.norm_eq_one] at hpy
  have hnorm := Wᗮ.norm_starProjection_apply_le (K (R (b i)) - A (R (b i)))
  have hz : Wᗮ.starProjection (A (R (b i))) = 0 := by
    apply (Wᗮ.starProjection_apply_eq_zero_iff).mpr
    simpa only [Submodule.orthogonal_orthogonal] using (A.mem_range_self (R (b i)))
  rw [map_sub, hsingular i, map_smul, hz, sub_zero, norm_smul,
    Real.norm_eq_abs, ← hsingular i] at hnorm
  have hsq : lam i ^ 2 * ‖Wᗮ.starProjection (c i)‖ ^ 2 ≤
      ‖K (R (b i)) - A (R (b i))‖ ^ 2 := by
    have h := (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mpr hnorm
    simpa only [mul_pow, sq_abs] using h
  dsimp [p]
  nlinarith [sq_nonneg (lam i)]

/-- Truncate a supplied singular decomposition of the weighted target. This
operator acts on covariance-factor inputs; factoring it as a decoder after
`R` is a separate existence question when `R` is singular. -/
noncomputable def singularTruncation (b c : OrthonormalBasis ι ℝ E)
    (lam : ι → ℝ) (S : Finset ι) : E →ₗ[ℝ] E :=
  b.toBasis.constr ℝ (fun i => if i ∈ S then lam i • c i else 0)

omit [FiniteDimensional ℝ E] in
lemma singularTruncation_apply (b c : OrthonormalBasis ι ℝ E)
    (lam : ι → ℝ) (S : Finset ι) (i : ι) :
    singularTruncation b c lam S (b i) = if i ∈ S then lam i • c i else 0 := by
  exact b.toBasis.constr_basis ℝ _ i

omit [FiniteDimensional ℝ E] in
/-- The supplied singular truncation attains the tail for the weighted target
`K ∘ R` on its right singular basis. It does not estimate the basis from data. -/
theorem singularTruncation_error (b c : OrthonormalBasis ι ℝ E)
    (R K : E →ₗ[ℝ] E) (lam : ι → ℝ) (S : Finset ι)
    (hsingular : ∀ i, K (R (b i)) = lam i • c i) :
    ∑ i, ‖K (R (b i)) - singularTruncation b c lam S (b i)‖ ^ 2 =
      ∑ i ∈ Sᶜ, lam i ^ 2 := by
  calc
    _ = ∑ i, if i ∈ Sᶜ then lam i ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;>
        simp [hsingular, singularTruncation_apply, hi, norm_smul, Real.norm_eq_abs]
    _ = _ := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i; simp
      · intro i _; rfl

/-- The singular truncation uses at most one output dimension per retained
mode. This rank bound is on a linear operator, not attention query dimension. -/
theorem singularTruncation_rank (b c : OrthonormalBasis ι ℝ E)
    (lam : ι → ℝ) (S : Finset ι) :
    finrank ℝ (singularTruncation b c lam S).range ≤ S.card := by
  classical
  let W := Submodule.span ℝ (c '' (S : Set ι))
  have hr : (singularTruncation b c lam S).range ≤ W := by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, singularTruncation_apply]
    apply Submodule.smul_mem
    split_ifs with hi
    · exact W.smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · exact W.zero_mem
  have hspan : finrank ℝ W ≤ S.card := by
    have h := finrank_span_finset_le_card (R := ℝ) (S.image c)
    rw [Finset.coe_image] at h
    exact h.trans (Finset.card_image_le)
  exact (Submodule.finrank_mono hr).trans hspan

#print axioms covariance_root_singular_tail_le_error
#print axioms singularTruncation_error
#print axioms singularTruncation_rank
end PhysicsOfConsciousness.AttentionRank
