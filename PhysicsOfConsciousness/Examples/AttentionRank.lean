import PhysicsOfConsciousness.Phase6_AttentionRank
open scoped BigOperators
open Module PhysicsOfConsciousness.AttentionRank
/-! Nondegenerate regressions for the spectral lower bound: two positive,
unequal eigenvalues, a rank-one truncation with nonzero error, and arbitrary
rank-one competitors. The softmax control checks why logit rank is insufficient. -/
namespace PhysicsOfConsciousness.Examples.AttentionRankWitness
noncomputable def basis : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  EuclideanSpace.basisFun (Fin 2) ℝ
noncomputable def spectrum : Fin 2 → ℝ := ![3, 1]
noncomputable def kernel : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  spectralTruncation basis spectrum Finset.univ
noncomputable def approximation : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  spectralTruncation basis spectrum {0}
/-- The target has the declared two positive eigenvalues. -/
lemma kernel_eigen (i : Fin 2) : kernel (basis i) = spectrum i • basis i := by
  simp [kernel, spectralTruncation_apply]
/-- The proposed approximation meets the one-dimensional budget. -/
lemma approximation_rank : finrank ℝ approximation.range ≤ 1 := by
  exact spectralTruncation_rank basis spectrum {0}
/-- The truncation pays a nonzero error equal to the spectral tail. -/
lemma truncation_error_one : ∑ i, ‖kernel (basis i) - approximation (basis i)‖ ^ 2 = 1 := by
  rw [show approximation = spectralTruncation basis spectrum {0} from rfl,
    spectralTruncation_error basis kernel spectrum {0} kernel_eigen]
  norm_num [Finset.univ_fin2, Finset.compl_eq_univ_sdiff, spectrum]
/-- Every rank-one competitor pays the same lower bound; this includes
competitors that mix the two modes. The example supplies no neural spectrum. -/
lemma every_rank_one_pays (A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hA : finrank ℝ A.range ≤ 1) : 1 ≤ ∑ i, ‖kernel (basis i) - A (basis i)‖ ^ 2 := by
  have h := spectral_tail_le_error basis kernel A spectrum {0} 1 kernel_eigen
    (by simpa using hA) (by norm_num)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; norm_num [spectrum])
    (by intro i hi; fin_cases i <;> simp_all [spectrum])
  simpa [Finset.univ_fin2, Finset.compl_eq_univ_sdiff, spectrum] using h
/-- Scalar logits do not force scalar-dimensional attention range. -/
lemma softmax_increases_rank : rankOneLogits.rank = 1 ∧
    (rowSoftmax rankOneLogits).rank = 2 := softmax_rank_counterexample

#print axioms every_rank_one_pays
#print axioms truncation_error_one
#print axioms softmax_increases_rank

end PhysicsOfConsciousness.Examples.AttentionRankWitness
