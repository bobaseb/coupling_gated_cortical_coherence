import PhysicsOfConsciousness.Phase6_InputWeightedRank
import PhysicsOfConsciousness.Phase3_FiniteInformation

/-!
# An actual anisotropic input law for the spectral rank bound

The input law samples one eigenbasis vector at a time. The probability of each
mode is its input second-moment weight, so the weighted theorem becomes an
expected reconstruction-error floor and spectral truncation attains it. This
does not treat a general correlated input law or a nonlinear decoder.
-/
open scoped BigOperators RealInnerProductSpace
open Module
namespace PhysicsOfConsciousness.AttentionRank
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Expected squared reconstruction error when the input law samples actual
basis vectors. The sample law is an input distribution, not a parameter count. -/
noncomputable def sampledError (P : PhysicsOfConsciousness.ProbDist ι)
    (b : OrthonormalBasis ι ℝ E) (K A : E →ₗ[ℝ] E) : ℝ :=
  ∑ i, P.p i * ‖K (b i) - A (b i)‖ ^ 2

/-- The weighted spectral tail is a lower bound on error under a concrete
nonisotropic input law. Selection uses probability-weighted squared eigenvalues.
The theorem applies to the rank of the decoder operator itself. -/
theorem sampled_spectral_tail_le_error (P : PhysicsOfConsciousness.ProbDist ι)
    (b : OrthonormalBasis ι ℝ E) (K A : E →ₗ[ℝ] E)
    (lam : ι → ℝ) (S : Finset ι) (τ : ℝ)
    (heigen : ∀ i, K (b i) = lam i • b i)
    (hrank : finrank ℝ A.range ≤ S.card)
    (hτ : 0 ≤ τ) (hin : ∀ i ∈ S, τ ≤ P.p i * lam i ^ 2)
    (hout : ∀ i ∉ S, P.p i * lam i ^ 2 ≤ τ) :
    ∑ i ∈ Sᶜ, P.p i * lam i ^ 2 ≤ sampledError P b K A := by
  exact input_weighted_spectral_tail_le_error b K A lam P.p P.nonneg
    S τ heigen hrank hτ hin hout

omit [FiniteDimensional ℝ E] in
/-- Spectral truncation attains the weighted tail under the same input law.
This is a finite linear witness, not a trainable reconstruction benchmark. -/
theorem sampled_spectralTruncation_error (P : PhysicsOfConsciousness.ProbDist ι)
    (b : OrthonormalBasis ι ℝ E) (K : E →ₗ[ℝ] E)
    (lam : ι → ℝ) (S : Finset ι)
    (heigen : ∀ i, K (b i) = lam i • b i) :
    sampledError P b K (spectralTruncation b lam S) =
      ∑ i ∈ Sᶜ, P.p i * lam i ^ 2 := by
  unfold sampledError
  calc
    _ = ∑ i, if i ∈ Sᶜ then P.p i * lam i ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S <;>
        simp [heigen, spectralTruncation_apply, hi, norm_smul, Real.norm_eq_abs]
    _ = _ := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i; simp
      · intro i _; rfl

#print axioms sampled_spectral_tail_le_error
#print axioms sampled_spectralTruncation_error
end PhysicsOfConsciousness.AttentionRank
