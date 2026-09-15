import PhysicsOfConsciousness.Phase8_CriticalExponent
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Strict moment inequality for the coherent branch

The radial covariance must be strictly smaller than the sine second moment.
Strict monotonicity of `vonMisesSRatio` alone only bounds its derivative weakly.
Its Riccati identity rules out a zero derivative at a positive concentration:
such a zero would be a local maximum of the nonpositive derivative, contradicting
the derivative of that identity. No stability or covariance gap is postulated.
-/

open Real MeasureTheory intervalIntegral Set Filter
open scoped Topology

namespace PhysicsOfConsciousness.FokkerPlanck

lemma besselRatio_hasDerivAt (a : ℝ) :
    HasDerivAt besselRatio (1 - vonMisesSRatio a - besselRatio a ^ 2) a := by
  have hz : vmMoment 0 a ≠ 0 := by
    simpa [vmMoment, vonMisesZ, vonMisesWeight] using (vonMisesZ_pos a).ne'
  have hf : besselRatio = fun x => vmMoment 1 x / vmMoment 0 x := by
    funext x; simp [besselRatio, vmMoment, vonMisesM, vonMisesZ, vonMisesWeight]
  rw [hf]
  apply ((hasDerivAt_vmMoment 1 a).div (hasDerivAt_vmMoment 0 a) hz).congr_deriv
  rw [vonMisesSRatio_eq_moments]
  norm_num only [Nat.reduceAdd]
  field_simp
  ring

/-- The exact differential identity for the sine second moment. It is
obtained by differentiating the defining integrals, with positive denominator. -/
lemma sRatio_riccati (a : ℝ) :
    a * sRatioDeriv a = 1 - 2 * vonMisesSRatio a - a ^ 2 * vonMisesSRatio a ^ 2 := by
  have h1 := besselRatio_hasDerivAt a
  have h2 := (hasDerivAt_id a).mul (hasDerivAt_vonMisesSRatio a)
  have hf : (fun x => x * vonMisesSRatio x) = besselRatio := by
    funext x; exact (besselRatio_eq_mul x).symm
  simp only [id_eq, one_mul] at h2
  change HasDerivAt (fun x => x * vonMisesSRatio x) _ _ at h2
  rw [hf] at h2
  have he := h1.unique h2
  rw [besselRatio_eq_mul] at he
  nlinarith

lemma sRatioDeriv_nonpos {a : ℝ} (ha : 0 < a) : sRatioDeriv a ≤ 0 := by
  have h := (vonMisesSRatio_strictAntiOn.antitoneOn).derivWithin_nonpos (x := a)
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ha), deriv_vonMisesSRatio] at h
  exact h

lemma differentiable_sRatioDeriv : Differentiable ℝ sRatioDeriv := by
  have h : ContDiff ℝ (1 + 1) vonMisesSRatio := contDiff_two_vonMisesSRatio
  rw [contDiff_succ_iff_deriv] at h
  rw [← deriv_vonMisesSRatio]
  exact h.2.2.differentiable (by norm_num)

lemma sRatio_pos {a : ℝ} (ha : 0 < a) : 0 < vonMisesSRatio a := by
  have hr : 0 < besselRatio a := by
    simpa using besselRatio_strictMono ha
  rw [besselRatio_eq_mul] at hr
  exact (mul_pos_iff.mp hr).resolve_right (fun h => (not_lt_of_ge ha.le) h.1) |>.2

/-- Strict radial covariance gap at every positive concentration. This
strengthens monotonicity at the derivative level, needed for coherent linear
stability. It makes no claim about an evolution or the critical endpoint. -/
theorem sRatioDeriv_neg {a : ℝ} (ha : 0 < a) : sRatioDeriv a < 0 := by
  have hn := sRatioDeriv_nonpos ha
  by_contra hnot
  have he : sRatioDeriv a = 0 := le_antisymm hn (le_of_not_gt hnot)
  have hm : IsLocalMax sRatioDeriv a := by
    filter_upwards [Ioi_mem_nhds ha] with x hx
    rw [he]
    exact sRatioDeriv_nonpos hx
  have hder := hm.deriv_eq_zero
  have hl := (hasDerivAt_id a).mul (differentiable_sRatioDeriv a).hasDerivAt
  have hr := ((hasDerivAt_const a 1).sub
    ((hasDerivAt_vonMisesSRatio a).const_mul 2)).sub
      (((hasDerivAt_id a).pow 2).mul ((hasDerivAt_vonMisesSRatio a).pow 2))
  have hf : (fun x => x * sRatioDeriv x) =
      fun x => 1 - 2 * vonMisesSRatio x - x ^ 2 * vonMisesSRatio x ^ 2 := by
    funext x; exact sRatio_riccati x
  simp only [id_eq] at hl hr
  change HasDerivAt (fun x => x * sRatioDeriv x) _ _ at hl
  change HasDerivAt (fun x => 1 - 2 * vonMisesSRatio x -
    x ^ 2 * vonMisesSRatio x ^ 2) _ _ at hr
  rw [hf] at hl
  have hh := hl.unique hr
  simp only [Pi.pow_apply, id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one] at hh
  rw [hder, he] at hh
  have hp := sRatio_pos ha
  nlinarith [sq_pos_of_pos hp]

/-- The variance of cosine is strictly below the sine second moment for a
positive concentration. The two agree at zero; keeping the strict hypothesis
prevents a claimed spectral gap at the bifurcation. -/
theorem cosine_variance_lt_sine {a : ℝ} (ha : 0 < a) :
    1 - vonMisesSRatio a - besselRatio a ^ 2 < vonMisesSRatio a := by
  have h := sRatio_riccati a
  have hn := mul_neg_of_pos_of_neg ha (sRatioDeriv_neg ha)
  rw [besselRatio_eq_mul]
  nlinarith

#print axioms sRatioDeriv_neg
#print axioms cosine_variance_lt_sine

end PhysicsOfConsciousness.FokkerPlanck
