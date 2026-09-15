import PhysicsOfConsciousness.Phase3_AgencyThermodynamics

/-!
# Finite thermodynamics with zeros in the path laws

Forward paths must have reverse support; zero-mass paths need no logarithmic
identity. This is weaker than positive initial and transition masses everywhere.
The entropy balance and Gibbs inequality hold in this regime. A separate
extended value records infinity when a forward path has no reverse support;
the totalized real logarithm is never used to price that irreversible case.
These are finite path-law results, not a construction of physical reverse
protocols or a continuous-state entropy balance.
-/

namespace PhysicsOfConsciousness

open scoped ENNReal

namespace ProbDist

/-- Every positive forward atom has positive reference mass. In finite spaces
this is the support condition for absolute continuity. -/
def SupportIncluded {V : Type*} [Fintype V] (P Q : ProbDist V) : Prop :=
  ∀ v, 0 < P.p v → 0 < Q.p v

end ProbDist

/-- Gibbs inequality only needs reference positivity on the forward support.
If support inclusion fails, the real `KL` is not the extended divergence. -/
theorem KL_nonneg_of_support {V : Type*} [Fintype V] (P Q : ProbDist V)
    (h : P.SupportIncluded Q) : 0 ≤ KL P Q := by
  have hi (v : V) : P.p v - Q.p v ≤ P.p v * Real.log (P.p v / Q.p v) := by
    by_cases hp : P.p v = 0
    · simp only [hp, zero_sub, zero_mul]
      exact neg_nonpos.mpr (Q.nonneg v)
    · have hp' : 0 < P.p v := lt_of_le_of_ne (P.nonneg v) (Ne.symm hp)
      have hq := h v hp'
      have hl := Real.log_le_sub_one_of_pos (div_pos hq hp')
      have hm := mul_le_mul_of_nonneg_left hl hp'.le
      have hid : P.p v * (Q.p v / P.p v - 1) = Q.p v - P.p v := by
        field_simp
      rw [Real.log_div hq.ne' hp'.ne'] at hm
      rw [Real.log_div hp'.ne' hq.ne']
      rw [hid] at hm
      nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hi v)
  simpa only [Finset.sum_sub_distrib, P.sum_one, Q.sum_one, sub_self, KL] using hs

namespace ProbDist

/-- Extended finite divergence, retaining infinity for missing reverse support.
It is a finite-sum definition; equality with Mathlib's measure divergence is a
separate bridge. No infinite quantity is converted to a real cost. -/
noncomputable def extendedKL {V : Type*} [Fintype V] (P Q : ProbDist V) : ℝ≥0∞ := by
  classical
  exact if P.SupportIncluded Q then ENNReal.ofReal (KL P Q) else ⊤

theorem extendedKL_toReal_of_support {V : Type*} [Fintype V] (P Q : ProbDist V)
    (h : P.SupportIncluded Q) : (P.extendedKL Q).toReal = KL P Q := by
  simp only [extendedKL, ite_eq_left h]
  exact ENNReal.toReal_ofReal (KL_nonneg_of_support P Q h)

/-- A single unsupported positive forward atom gives infinite divergence,
including for deterministic erasure under the same-channel reverse convention. -/
theorem extendedKL_top_of_missing {V : Type*} [Fintype V] (P Q : ProbDist V) (v : V)
    (hp : 0 < P.p v) (hq : Q.p v = 0) : P.extendedKL Q = ⊤ := by
  have hn : ¬ P.SupportIncluded Q := by
    intro h
    have hv := h v hp
    rw [hq] at hv
    exact (lt_irrefl 0) hv
  simp only [extendedKL, ite_eq_right hn]

end ProbDist

namespace FiniteFeedbackStep

variable {X S : Type*} [Fintype X] [Fintype S]

/-- Forward support is contained in the same-channel reversed path support. -/
def ReversibleSupport (M : FiniteFeedbackStep X S) : Prop :=
  M.forward.SupportIncluded M.reverse

/-- The prior full-support regime implies the weaker path condition. The
converse fails for reversible deterministic channels and sparse initial laws. -/
theorem reversibleSupport_of_positive [Nonempty S] (M : FiniteFeedbackStep X S)
    (h : M.Positive) : M.ReversibleSupport := by
  intro z _
  exact mul_pos (M.final_positive h _) (h.2 _ _ _)

/-- Finite production is nonnegative under forward/reverse support inclusion.
Reservoir heat still requires a physical local-balance identification. -/
theorem entropyProduction_nonneg_of_support (M : FiniteFeedbackStep X S)
    (h : M.ReversibleSupport) : 0 ≤ M.entropyProduction :=
  KL_nonneg_of_support M.forward M.reverse h

/-- Expand log ratios only on paths actually taken. Zero initial or transition
masses are allowed; unsupported forward paths are excluded by `h`. -/
theorem entropy_balance_of_support (M : FiniteFeedbackStep X S)
    (h : M.ReversibleSupport) :
    M.entropyProduction =
      shannon_entropy M.final.p - shannon_entropy M.initial.p + M.bathEntropy := by
  have hlog (z : X × (S × S)) :
      M.forward.p z * Real.log (M.forward.p z / M.reverse.p z) =
        M.forward.p z * (Real.log (M.initial.p (z.1, z.2.1)) -
          Real.log (M.final.p (z.1, z.2.2)) +
          Real.log ((M.transition z.1 z.2.1).p z.2.2 /
            (M.transition z.1 z.2.2).p z.2.1)) := by
    by_cases hz : M.forward.p z = 0
    · simp only [hz, zero_mul]
    · have hf : 0 < M.forward.p z := lt_of_le_of_ne (M.forward.nonneg z) (Ne.symm hz)
      have hr := h z hf
      have hp := (mul_pos_iff.mp hf).resolve_right
        (fun hn => (not_lt_of_ge (M.initial.nonneg _)) hn.1)
      have hq := (mul_pos_iff.mp hr).resolve_right
        (fun hn => (not_lt_of_ge (M.final.nonneg _)) hn.1)
      congr 1
      rw [forward, reverse, Real.log_div (mul_pos hp.1 hp.2).ne' (mul_pos hq.1 hq.2).ne',
        Real.log_mul hp.1.ne' hp.2.ne', Real.log_mul hq.1.ne' hq.2.ne',
        Real.log_div hp.2.ne' hq.2.ne']
      ring
  unfold entropyProduction KL
  simp_rw [hlog, mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    forward_expect_initial M (fun z => Real.log (M.initial.p z)),
    forward_expect_final M (fun z => Real.log (M.final.p z))]
  unfold shannon_entropy bathEntropy
  ring

end FiniteFeedbackStep

#print axioms KL_nonneg_of_support
#print axioms ProbDist.extendedKL_top_of_missing
#print axioms FiniteFeedbackStep.entropy_balance_of_support

end PhysicsOfConsciousness
