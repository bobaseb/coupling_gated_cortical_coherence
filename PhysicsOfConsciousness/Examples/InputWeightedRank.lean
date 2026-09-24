import PhysicsOfConsciousness.Phase6_SampledRank
import PhysicsOfConsciousness.Examples.AttentionRank

open scoped BigOperators
open Module PhysicsOfConsciousness.AttentionRank
namespace PhysicsOfConsciousness.Examples.InputWeightedRankWitness
open AttentionRankWitness

/-- Anisotropic input makes the smaller target eigenvalue the more valuable
mode: weighted energies are 9 and 16. This finite example is not a benchmark. -/
theorem weighted_rank_one_floor
    (A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hA : finrank ℝ A.range ≤ 1) :
    9 ≤ ∑ i, (![1, 16] : Fin 2 → ℝ) i * ‖kernel (basis i) - A (basis i)‖ ^ 2 := by
  have h := input_weighted_spectral_tail_le_error basis kernel A AttentionRankWitness.spectrum ![1, 16]
    (by intro i; fin_cases i <;> norm_num) {1} 9 kernel_eigen
    (by simpa using hA) (by norm_num)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; norm_num [AttentionRankWitness.spectrum])
    (by intro i hi; fin_cases i <;> norm_num [AttentionRankWitness.spectrum] at *)
  norm_num [Finset.univ_fin2, Finset.compl_eq_univ_sdiff, AttentionRankWitness.spectrum] at h ⊢
  exact h

/-- The second eigenmode occurs sixteen times as often as the first. This is an
actual normalized nonisotropic input law, not arbitrary error weights. -/
noncomputable def modeLaw : PhysicsOfConsciousness.ProbDist (Fin 2) where
  p i := if i = 0 then (1 / 17 : ℝ) else 16 / 17
  nonneg i := by fin_cases i <;> norm_num
  sum_one := by norm_num [Fin.sum_univ_two]

/-- Every rank-one decoder pays at least 9/17 expected squared error on the
sampled basis task. The lower-weight mode has the larger target eigenvalue. -/
theorem sampled_rank_one_floor
    (A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hA : finrank ℝ A.range ≤ 1) :
    (9 / 17 : ℝ) ≤ sampledError modeLaw basis kernel A := by
  have h := sampled_spectral_tail_le_error modeLaw basis kernel A
    AttentionRankWitness.spectrum {1} (9 / 17) kernel_eigen
    (by simpa using hA) (by norm_num)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; norm_num [modeLaw, AttentionRankWitness.spectrum])
    (by intro i hi; fin_cases i <;> norm_num [modeLaw, AttentionRankWitness.spectrum] at *)
  norm_num [Finset.univ_fin2, Finset.compl_eq_univ_sdiff, modeLaw,
    AttentionRankWitness.spectrum] at h ⊢
  exact h

/-- Retaining the frequently sampled smaller-eigenvalue mode attains that
floor exactly; this checks tightness on the declared input law. -/
theorem sampled_truncation_attains :
    sampledError modeLaw basis kernel
      (spectralTruncation basis AttentionRankWitness.spectrum {1}) = 9 / 17 := by
  rw [sampled_spectralTruncation_error modeLaw basis kernel
    AttentionRankWitness.spectrum {1} kernel_eigen]
  norm_num [Finset.univ_fin2, Finset.compl_eq_univ_sdiff, modeLaw,
    AttentionRankWitness.spectrum]

#print axioms sampled_rank_one_floor
#print axioms sampled_truncation_attains
#print axioms weighted_rank_one_floor
end PhysicsOfConsciousness.Examples.InputWeightedRankWitness
