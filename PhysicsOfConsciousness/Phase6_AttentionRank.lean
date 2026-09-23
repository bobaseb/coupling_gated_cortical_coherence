import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Spectral approximation with an explicit rank budget

For a real operator with an orthonormal eigenbasis, every rank-constrained
linear approximation pays the squared eigenvalue tail in squared
Hilbert--Schmidt error. The approximating map need not share the eigenbasis.
Orthogonal projection onto its range supplies weights between zero and one,
whose total is the range dimension; a finite exchange inequality bounds the
retained spectral weight. Spectral truncation attains the bound.

This is a finite-dimensional statement. It neither constructs a Mercer
expansion nor supplies the spectrum of a physical coupling kernel. The rank
constraint must hold for the actual approximating operator. In particular,
row softmax can raise rank: the explicit two-position example below has
rank-one logits and rank-two attention, even at query/key dimension one.
-/

open scoped BigOperators RealInnerProductSpace Matrix
open Module
namespace PhysicsOfConsciousness.AttentionRank

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [DecidableEq ι] in
/-- Projection onto a subspace retains total squared basis mass equal to its
dimension. This is a finite-dimensional identity, with no hardware model. -/
lemma projection_mass (b : OrthonormalBasis ι ℝ E) (W : Submodule ℝ E) :
    ∑ i, ‖W.starProjection (b i)‖ ^ 2 = (finrank ℝ W : ℝ) := by
  let c := stdOrthonormalBasis ℝ W
  have h (i : ι) : ‖W.starProjection (b i)‖ ^ 2 =
      ∑ j, ⟪(c j : E), b i⟫ ^ 2 := by
    change ‖W.orthogonalProjectionOnto (b i)‖ ^ 2 = _
    rw [← c.sum_sq_inner_right]
    congr 1
    ext j
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  simp_rw [h]
  rw [Finset.sum_comm]
  simp_rw [b.sum_sq_inner_left]
  change (∑ j, ‖c j‖ ^ 2) = _
  simp

/-- A unit-capacity weight allocation of total mass at most `S.card` cannot
retain more than the modes above the declared threshold. No spectrum is assumed. -/
lemma weighted_tail (w p : ι → ℝ) (S : Finset ι) (τ : ℝ)
    (hτ : 0 ≤ τ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hmass : ∑ i, p i ≤ S.card)
    (hin : ∀ i ∈ S, τ ≤ w i) (hout : ∀ i ∉ S, w i ≤ τ) :
    ∑ i ∈ Sᶜ, w i ≤ ∑ i, w i * (1 - p i) := by
  have hin' : τ * ∑ i ∈ S, (1 - p i) ≤ ∑ i ∈ S, w i * (1 - p i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hin i hi) (by linarith [(hp i).2])
  have hout' : ∑ i ∈ Sᶜ, w i * p i ≤ τ * ∑ i ∈ Sᶜ, p i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
      (hout i (Finset.mem_compl.mp hi)) (hp i).1
  have hmass' : ∑ i ∈ Sᶜ, p i ≤ ∑ i ∈ S, (1 - p i) := by
    rw [Finset.sum_sub_distrib]
    have hsplit := S.sum_add_sum_compl p
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at *
    linarith
  have hmul := mul_le_mul_of_nonneg_left hmass' hτ
  have hsplit := S.sum_add_sum_compl (fun i => w i * (1 - p i))
  have hexpand : ∑ i ∈ Sᶜ, w i * (1 - p i) =
      (∑ i ∈ Sᶜ, w i) - ∑ i ∈ Sᶜ, w i * p i := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hexpand] at hsplit
  linarith

/-- Every linear approximation whose range dimension fits the selected modes
pays the omitted squared eigenvalue tail. The eigenbasis and spectral ordering
are explicit inputs; this does not bound softmax rank or construct a kernel spectrum. -/
lemma spectral_tail_le_error (b : OrthonormalBasis ι ℝ E)
    (K A : E →ₗ[ℝ] E) (lam : ι → ℝ) (S : Finset ι) (τ : ℝ)
    (heigen : ∀ i, K (b i) = lam i • b i)
    (hrank : finrank ℝ A.range ≤ S.card)
    (hτ : 0 ≤ τ) (hin : ∀ i ∈ S, τ ≤ lam i ^ 2)
    (hout : ∀ i ∉ S, lam i ^ 2 ≤ τ) :
    ∑ i ∈ Sᶜ, lam i ^ 2 ≤ ∑ i, ‖K (b i) - A (b i)‖ ^ 2 := by
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
  refine (weighted_tail (fun i => lam i ^ 2) p S τ hτ hp hmass hin hout).trans ?_
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
  nlinarith [sq_nonneg (lam i)]

/-- The usual tail bound, with modes indexed from zero and sorted by squared
eigenvalue. `d < n`; at full dimension the omitted tail is empty. The rank
hypothesis is on the approximating map itself, not on its parameter matrix. -/
lemma spectral_tail_le_error_of_antitone {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ E) (K A : E →ₗ[ℝ] E) (lam : Fin n → ℝ)
    (d : Fin n) (heigen : ∀ i, K (b i) = lam i • b i)
    (hrank : finrank ℝ A.range ≤ d.val) (horder : Antitone (fun i => lam i ^ 2)) :
    ∑ i ∈ (Finset.Iio d)ᶜ, lam i ^ 2 ≤ ∑ i, ‖K (b i) - A (b i)‖ ^ 2 := by
  apply spectral_tail_le_error b K A lam (Finset.Iio d) (lam d ^ 2) heigen
  · simpa only [Fin.card_Iio] using hrank
  · positivity
  · intro i hi
    exact horder (Finset.mem_Iio.mp hi).le
  · intro i hi
    exact horder (le_of_not_gt (fun h => hi (Finset.mem_Iio.mpr h)))

/-- Retain exactly the declared eigenmodes, expressed in their orthonormal basis. -/
noncomputable def spectralTruncation (b : OrthonormalBasis ι ℝ E)
    (lam : ι → ℝ) (S : Finset ι) : E →ₗ[ℝ] E :=
  b.toBasis.constr ℝ (fun i => if i ∈ S then lam i • b i else 0)

omit [FiniteDimensional ℝ E] in
/-- The truncation acts diagonally on the supplied basis. -/
lemma spectralTruncation_apply (b : OrthonormalBasis ι ℝ E)
    (lam : ι → ℝ) (S : Finset ι) (i : ι) :
    spectralTruncation b lam S (b i) = if i ∈ S then lam i • b i else 0 := by
  exact b.toBasis.constr_basis ℝ _ i

omit [FiniteDimensional ℝ E] in
/-- Spectral truncation has exactly the omitted squared spectral mass as
error. This gives equality in the lower bound when the selected modes are largest;
it supplies no mechanism that computes this approximation. -/
lemma spectralTruncation_error (b : OrthonormalBasis ι ℝ E)
    (K : E →ₗ[ℝ] E) (lam : ι → ℝ) (S : Finset ι)
    (heigen : ∀ i, K (b i) = lam i • b i) :
    ∑ i, ‖K (b i) - spectralTruncation b lam S (b i)‖ ^ 2 = ∑ i ∈ Sᶜ, lam i ^ 2 := by
  calc
    _ = ∑ i, if i ∈ Sᶜ then lam i ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;>
        simp [heigen, spectralTruncation_apply, hi, norm_smul, Real.norm_eq_abs]
    _ = _ := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i; simp
      · intro i _; rfl

/-- Truncation has at most one range dimension per retained mode, including
when some eigenvalues vanish. This is a linear dimension budget, not a bit budget. -/
lemma spectralTruncation_rank (b : OrthonormalBasis ι ℝ E)
    (lam : ι → ℝ) (S : Finset ι) :
    finrank ℝ (spectralTruncation b lam S).range ≤ S.card := by
  classical
  let W := Submodule.span ℝ (b '' (S : Set ι))
  have hr : (spectralTruncation b lam S).range ≤ W := by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, spectralTruncation_apply]
    apply Submodule.smul_mem
    split_ifs with hi
    · exact W.smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · exact W.zero_mem
  have hspan : finrank ℝ W ≤ S.card := by
    have h := finrank_span_finset_le_card (R := ℝ) (S.image b)
    rw [Finset.coe_image] at h
    exact h.trans (Finset.card_image_le)
  exact (Submodule.finrank_mono hr).trans hspan

/-- Row normalization of entrywise exponentiated logits. -/
noncomputable def rowSoftmax {n : Type*} [Fintype n] (L : Matrix n n ℝ) : Matrix n n ℝ :=
  fun i j => Real.exp (L i j) / ∑ k, Real.exp (L i k)
/-- Two-position logits realizable by scalar queries and keys `(0, 1)`. -/
noncomputable def rankOneLogits : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
/-- The scalar-query/key logit matrix has rank one. -/
lemma rankOneLogits_rank : rankOneLogits.rank = 1 := by
  classical
  have h : rankOneLogits = Matrix.diagonal ![0, (1 : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [rankOneLogits, Matrix.diagonal]
  rw [h, Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton]
/-- Exact rank can increase under row softmax. This refutes a universal
attention-rank bound by query/key dimension; it asserts no threshold-dependent
numerical or effective rank bound. -/
lemma softmax_rank_counterexample :
    rankOneLogits.rank = 1 ∧ (rowSoftmax rankOneLogits).rank = 2 := by
  refine ⟨rankOneLogits_rank, ?_⟩
  have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  have hdet : (rowSoftmax rankOneLogits).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    norm_num [rowSoftmax, rankOneLogits, Fin.sum_univ_two]
    have hden : 1 + Real.exp 1 ≠ 0 := by positivity
    field_simp
    linarith
  simpa using Matrix.rank_of_det_ne_zero hdet

#print axioms spectral_tail_le_error
#print axioms spectral_tail_le_error_of_antitone
#print axioms spectralTruncation_error
#print axioms spectralTruncation_rank
#print axioms softmax_rank_counterexample

end PhysicsOfConsciousness.AttentionRank
