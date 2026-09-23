import PhysicsOfConsciousness.Examples.Phase3
import PhysicsOfConsciousness.Phase3_FiniteInformation
import PhysicsOfConsciousness.Phase6_Reconstruction
open PhysicsOfConsciousness MeasureTheory
/-! Checks the capacity ceiling on correlated and independent binary laws,
including zero joint atoms, and on arbitrary binary token-sequence laws. -/
namespace PhysicsOfConsciousness.Examples
/-- The correlated binary copy saturates the one-bit output ceiling. -/
lemma binary_copy_one_bit : (mutualInfo corrJoint).toReal / Real.log 2 = 1 := by
  rw [memory_toReal, div_self (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
/-- The general theorem applies to a joint law with zero off-diagonal atoms. -/
lemma binary_copy_capacity : (mutualInfo corrJoint).toReal / Real.log 2 ≤ 1 := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simpa [hl] using mutualInfo_bits_le_log_card corrJoint
/-- An output of the same alphabet size can convey no information at all. -/
lemma independent_output_zero_bits : (mutualInfo indepJoint).toReal / Real.log 2 = 0 := by
  simp [indepJoint, mutualInfo_prod]
/-- Arbitrary dependent binary token sequences obey the k-bit ceiling. No
independence of successive emissions is assumed. -/
lemma token_sequence_capacity (k : ℕ) (μ : Measure (Bool × (Fin k → Bool)))
    [IsProbabilityMeasure μ] : (mutualInfo μ).toReal / Real.log 2 ≤ k := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simpa [hl] using Reconstruction.token_information_bits_le k μ
#print axioms binary_copy_one_bit
#print axioms binary_copy_capacity
#print axioms independent_output_zero_bits
#print axioms token_sequence_capacity
end PhysicsOfConsciousness.Examples
