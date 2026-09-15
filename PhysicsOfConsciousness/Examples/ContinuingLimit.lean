import PhysicsOfConsciousness.Examples.ContinuingAgent

/-!
# Longer horizons for the existing observational learner

The recurrence is derived in `ContinuingAgent` from the same act/observe/update/
reset law whose heat is charged there. Its geometric rate therefore concerns
actual expected task performance, not independently prepared evaluations of a
register with encoded rewards. The mathematical infinite run has unbounded
expected work. No almost-sure convergence, optimality or infinite funding is
claimed; the limiting reward is strictly below one.
-/

namespace PhysicsOfConsciousness.Examples.Continuing

/-- Exact error of the executed learner's agreement recurrence. The law and
channels are the fixed witness's; this is not a general learning theorem. -/
theorem agreement_error (m : ℕ) :
    65 / 127 - agreement m = (65 / 127 - 65 / 128) * (1 / 128 : ℝ) ^ m := by
  induction m with
  | zero => norm_num [agreement]
  | succ m ih =>
    simp only [agreement, pow_succ]
    nlinarith [ih]

/-- A rate for the task reward at completed cycles of the actual protocol.
The finite store only funds a prefix of this mathematical sequence. -/
theorem performance_error (m : ℕ) :
    65 / 127 - agent.performance (3 * (m + 1)) =
      (65 / 127 - 65 / 128) * (1 / 128 : ℝ) ^ m := by
  rw [performance_cycle]
  exact agreement_error m

/-- Expected performance converges to `65/127` along completed cycles. This
does not assert pathwise convergence or convergence to the optimal policy. -/
theorem performance_tendsto :
    Filter.Tendsto (fun m => agent.performance (3 * (m + 1)))
      Filter.atTop (nhds (65 / 127 : ℝ)) := by
  have hf (m : ℕ) : agent.performance (3 * (m + 1)) =
      65 / 127 - (65 / 127 - 65 / 128) * (1 / 128 : ℝ) ^ m := by
    linarith [performance_error m]
  simp_rw [hf]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : 0 ≤ (1 / 128 : ℝ)) (by norm_num : (1 / 128 : ℝ) < 1)
  simpa only [mul_zero, sub_zero] using
    (tendsto_const_nhds (x := (65 / 127 : ℝ))).sub
      (hp.const_mul (65 / 127 - 65 / 128 : ℝ))

/-- The limiting expected reward remains below perfect task performance. -/
theorem performance_limit_lt_one : (65 / 127 : ℝ) < 1 := by norm_num

/-- Every finite expected allowance is eventually exceeded by the same
learning process. This uses its existing recurring cost, including reset;
it does not compute an exact exhaustion time or a pathwise battery law. -/
theorem work_unbounded (b : ℝ) : ∃ m, b < process.totalWork (3 * m) := by
  let c : ℝ := 3 / 16 * Real.log 3 + 1 / 16 * Real.log (5 / 3)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (b / c)
  have hm' : b < (m : ℝ) * c := (div_lt_iff₀ hc).mp hm
  exact ⟨m, hm'.trans_le (totalWork_cycles_lower m)⟩

#print axioms performance_error
#print axioms performance_tendsto
#print axioms work_unbounded

end PhysicsOfConsciousness.Examples.Continuing
