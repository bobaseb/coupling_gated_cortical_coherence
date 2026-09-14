import PhysicsOfConsciousness.Examples.AgencyControl

/-!
# Thermal policy adaptation: witness and regression specifications

The policy register adapts toward a supplied model-based objective.
Its autonomous transitions account for register heat and energy. Task rewards
and task heat are prospective L2 expectations at the prepared task law; the
learning clock does not execute or reset task episodes.
-/

namespace PhysicsOfConsciousness.Examples

section GenericRegression

variable {X S : Type*} [Fintype X] [Fintype S] [Nonempty S]
  (M : FiniteFeedbackStep X S)

example (n : ℕ) : (M.iterate (n + 1)).initial = (M.iterate n).final :=
  M.iterate_initial_succ n

example (h : M.Positive) (n : ℕ) : (M.iterate n).Positive :=
  M.iterate_positive h n

example (E : X × S → ℝ) (q : X → S → S → ℝ)
    (h : ∀ x s t, E (x, t) - E (x, s) + q x s t = 0) (n : ℕ) :
    (∑ k ∈ Finset.range n, (M.iterate k).meanHeat q) =
      (∑ z, M.initial.p z * E z) -
        (∑ z, (M.iterate n).initial.p z * E z) :=
  M.sum_meanHeat_eq_energy_drop E q h n

example (h : M.Positive) (n : ℕ) :
    (∑ k ∈ Finset.range n, (M.iterate k).entropyProduction) =
      shannon_entropy (M.iterate n).initial.p - shannon_entropy M.initial.p +
        ∑ k ∈ Finset.range n, (M.iterate k).bathEntropy :=
  M.sum_entropy_balance h n

end GenericRegression

namespace PolicyLearning

/-- The register selects between two policies whose L2 task costs are feasible.
This readout specifies prospective task behaviour, not a physical installation. -/
def policy (b : Bool) : Bool → Bool :=
  if b then LampControl.copy else LampControl.baseline

/-- A lazy thermal channel biased toward the higher-reward policy. Its reverse
transition is positive, so individual updates need not improve reward. -/
noncomputable def channel (b : Bool) : ProbDist Bool where
  p c := if c then (if b then 7 / 8 else 3 / 8) else (if b then 1 / 8 else 5 / 8)
  nonneg c := by cases b <;> cases c <;> norm_num
  sum_one := by cases b <;> norm_num [Fintype.sum_bool]

/-- Initial preparation places probability 1/4 on copy. Its preparation cost
is not part of the subsequent autonomous relaxation. -/
noncomputable def initial : ProbDist (Unit × Bool) where
  p z := if z.2 then 1 / 4 else 3 / 4
  nonneg z := by cases z.2 <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

noncomputable def learner : FiniteFeedbackStep Unit Bool := ⟨initial, fun _ => channel⟩

/-- Energy is chosen to favour the known task reward; `energy_objective`
identifies this choice exactly. Thermodynamics does not supply the objective. -/
noncomputable def energy (z : Unit × Bool) : ℝ := if z.2 then 0 else Real.log 3

noncomputable def heat (_u : Unit) (b c : Bool) : ℝ := energy ((), b) - energy ((), c)

/-- The chosen energy explicitly encodes L2's known reward. It does not derive
the objective or estimate it from observations. -/
theorem energy_objective (b : Bool) :
    energy ((), b) = 4 * Real.log 3 *
      (LampControl.task.performance LampControl.copy -
        LampControl.task.performance (policy b)) := by
  cases b <;> norm_num [energy, policy, LampControl.copy_performance,
    LampControl.baseline_performance]
  ring

theorem positive : learner.Positive := by
  constructor
  · intro ⟨u, b⟩; cases b <;> norm_num [learner, initial]
  · intro u b c; cases b <;> cases c <;> norm_num [learner, channel]

/-- Every register transition obeys local detailed balance at thermal scale
one. Calling the log-ratio heat uses this explicitly chosen reservoir model. -/
theorem local_balance (n : ℕ) : (learner.iterate n).LocalDetailedBalance 1 heat := by
  intro u b c
  simp only [FiniteFeedbackStep.iterate_transition]
  cases b <;> cases c <;> norm_num [learner, channel, heat, energy, Real.log_div]

/-- The actual path heat is the energy loss, so the register needs no external
work during relaxation. This excludes preparation and readout implementation. -/
theorem zero_work (u : Unit) (b c : Bool) :
    energy (u, c) - energy (u, b) + heat u b c = 0 := by
  cases u
  unfold heat
  ring

private theorem law_false (μ : ProbDist (Unit × Bool)) :
    μ.p ((), false) = 1 - μ.p ((), true) := by
  have h := μ.sum_one
  norm_num [Fintype.sum_prod_type, Fintype.sum_bool] at h
  linarith

private theorem expectation (μ : ProbDist (Unit × Bool)) (f : Bool → ℝ) :
    (∑ z, μ.p z * f z.2) =
      (1 - μ.p ((), true)) * f false + μ.p ((), true) * f true := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_unique]
  rw [law_false]
  ring

/-- The recurrence is derived from the actual iterated channel, not used as
the definition of the law. Resetting each step to the initial law violates it. -/
theorem probability_recurrence (n : ℕ) :
    (learner.iterate (n + 1)).initial.p ((), true) =
      3 / 8 + (learner.iterate n).initial.p ((), true) / 2 := by
  simp only [FiniteFeedbackStep.iterate_initial_succ, FiniteFeedbackStep.final,
    FiniteFeedbackStep.iterate_transition, Fintype.sum_bool]
  norm_num [learner, channel]
  rw [law_false]
  ring

/-- Exact approach to a non-optimal mixture from the specified initial law.
It concerns distributions, not monotone improvement on individual paths. -/
theorem copy_probability (n : ℕ) : (learner.iterate n).initial.p ((), true) =
    3 / 4 - 1 / 2 * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num [learner, initial]
  | succ n ih => rw [probability_recurrence, ih, pow_succ]; ring

/-- Prospective reward of the decoded policy on L2's prepared task law.
The learner does not execute task episodes or estimate their rewards. -/
noncomputable def performance (n : ℕ) : ℝ :=
  ∑ z, (learner.iterate n).initial.p z * LampControl.task.performance (policy z.2)

/-- The reward is evaluated on the held policy's prepared L2 task, which is
not executed during the register's learning updates. -/
theorem performance_formula (n : ℕ) :
    performance n = 7 / 16 - 1 / 8 * (1 / 2 : ℝ) ^ n := by
  unfold performance
  rw [expectation _ (fun b => LampControl.task.performance (policy b)), copy_probability]
  norm_num [policy, LampControl.baseline_performance, LampControl.copy_performance]
  ring

/-- Expected task reward strictly improves from this initial preparation.
The objective is supplied; arbitrary initial distributions need not improve. -/
theorem performance_improves (n : ℕ) : performance n < performance (n + 1) := by
  rw [performance_formula, performance_formula, pow_succ]
  have h : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  linarith

/-- Distributional convergence leaves a positive probability of the baseline.
This is convergence of model-based adaptation, not optimal-policy learning. -/
theorem performance_limit : Filter.Tendsto performance Filter.atTop (nhds (7 / 16 : ℝ)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  change Filter.Tendsto (fun n => performance n) Filter.atTop _
  simp_rw [performance_formula]
  simpa only [mul_zero, sub_zero] using
    ((tendsto_const_nhds (x := (7 / 16 : ℝ))).sub (hp.const_mul (1 / 8 : ℝ)))

/-- The limiting distribution is stationary for the same autonomous channel.
Its positive baseline mass prevents convergence to the optimal pure policy. -/
noncomputable def stationary : FiniteFeedbackStep Unit Bool where
  initial := {
    p z := if z.2 then 3 / 4 else 1 / 4
    nonneg z := by cases z.2 <;> norm_num
    sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool] }
  transition _ := channel

theorem stationary_law : stationary.final = stationary.initial := by
  apply ProbDist.ext
  funext z
  cases z.2 <;> norm_num [FiniteFeedbackStep.final, stationary, channel, Fintype.sum_bool]

/-- Every state mass converges to the stationary mixture. This distributional
limit does not say that an individual register stops switching. -/
theorem law_limit (z : Unit × Bool) :
    Filter.Tendsto (fun n => (learner.iterate n).initial.p z) Filter.atTop
      (nhds (stationary.initial.p z)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  have hc : Filter.Tendsto (fun n => (learner.iterate n).initial.p ((), true))
      Filter.atTop (nhds (3 / 4 : ℝ)) := by
    simpa only [copy_probability, mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (hp.const_mul (1 / 2 : ℝ)))
  rcases z with ⟨⟨⟩, b⟩
  cases b
  · simpa [law_false, stationary] using (tendsto_const_nhds.sub hc)
  · exact hc

/-- Exact mean register heat on the actual forward paths at update n. -/
theorem update_heat (n : ℕ) : (learner.iterate n).meanHeat heat =
    Real.log 3 / 4 * (1 / 2 : ℝ) ^ n := by
  simp only [FiniteFeedbackStep.meanHeat, FiniteFeedbackStep.forward,
    FiniteFeedbackStep.iterate_transition]
  change (∑ z : Unit × (Bool × Bool), (learner.iterate n).initial.p (z.1, z.2.1) *
    (channel z.2.1).p z.2.2 * heat z.1 z.2.1 z.2.2) = _
  norm_num [channel, heat, energy, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [law_false, copy_probability]
  ring

theorem update_heat_positive (n : ℕ) : 0 < (learner.iterate n).meanHeat heat := by
  rw [update_heat]
  exact mul_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (pow_pos (by norm_num) n)

/-- Energy remaining in the policy register alone; task and preparation
resources are not included in this observable. -/
theorem mean_energy (n : ℕ) :
    (∑ z, (learner.iterate n).initial.p z * energy z) =
      Real.log 3 * (1 / 4 + 1 / 2 * (1 / 2 : ℝ) ^ n) := by
  change (∑ z, (learner.iterate n).initial.p z * (if z.2 then 0 else Real.log 3)) = _
  rw [expectation _ (fun b => if b then 0 else Real.log 3), copy_probability]
  norm_num
  ring

/-- Cumulative update heat is funded by the register's finite energy loss.
Task execution, preparation, value estimation and readout installation are
separate physical processes, so their costs are not included in this sum. -/
theorem cumulative_heat (n : ℕ) :
    (∑ k ∈ Finset.range n, (learner.iterate k).meanHeat heat) =
      Real.log 3 / 2 * (1 - (1 / 2 : ℝ) ^ n) := by
  rw [learner.sum_meanHeat_eq_energy_drop energy heat zero_work n, mean_energy]
  have h0 := mean_energy 0
  simp only [FiniteFeedbackStep.iterate_zero, pow_zero] at h0
  rw [h0]
  ring

/-- A finite upper bound on cumulative register heat; this is not an upper
budget for repeatedly executing the lamp task. -/
theorem cumulative_heat_budget (n : ℕ) :
    (∑ k ∈ Finset.range n, (learner.iterate k).meanHeat heat) ≤ Real.log 3 / 2 := by
  rw [cumulative_heat]
  have h := mul_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
    (pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) n)
  nlinarith

/-- The KL-based entropy balance telescopes on the same register laws used
for reward and heat. It does not impose a passive information-flow condition. -/
theorem entropy_accounting (n : ℕ) :
    (∑ k ∈ Finset.range n, (learner.iterate k).entropyProduction) =
      shannon_entropy (learner.iterate n).initial.p - shannon_entropy initial.p +
        Real.log 3 / 2 * (1 - (1 / 2 : ℝ) ^ n) := by
  rw [learner.sum_entropy_balance positive n]
  have hb (k : ℕ) : (learner.iterate k).bathEntropy = (learner.iterate k).meanHeat heat := by
    simpa only [one_mul] using
      ((learner.iterate k).heat_eq_thermal_bathEntropy 1 heat (local_balance k)).symm
  simp_rw [hb]
  rw [cumulative_heat]
  rfl

/-- Prospective task heat is a mixture of actual L2 cycle costs, retaining
the policy register in the accounting rather than hiding its paths. -/
noncomputable def taskHeat (n : ℕ) : ℝ :=
  ∑ z, (learner.iterate n).initial.p z * LampControl.task.heat 1 (policy z.2)

/-- Every prospective mixture fits L2's one-task heat budget. This does not
bound a sequence of task executions or pay for their preparation. -/
theorem task_heat (n : ℕ) : taskHeat n = LampControl.budget := by
  unfold taskHeat
  rw [expectation _ (fun b => LampControl.task.heat 1 (policy b))]
  norm_num [policy, LampControl.heat_formula, LampControl.copy, LampControl.baseline,
    LampControl.budget]
  ring

/-- Each prospective task has zero expected work in L2's common convention.
The physical implementation of the register's readout is outside that task. -/
theorem task_work (n : ℕ) :
    (∑ z, (learner.iterate n).initial.p z *
      LampControl.task.work ThermalAgency.energy 1 (policy z.2)) = 0 := by
  rw [expectation _ (fun b => LampControl.task.work ThermalAgency.energy 1 (policy b))]
  norm_num [policy, LampControl.work_formula, LampControl.copy, LampControl.baseline]

/-- A positive-probability transition lowers task reward, even though the
expectation improves along the chosen distributional trajectory. -/
theorem reward_decreasing_transition : (channel true).p false = 1 / 8 ∧
    LampControl.task.performance (policy false) <
      LampControl.task.performance (policy true) := by
  norm_num [channel, policy, LampControl.baseline_performance, LampControl.copy_performance]

theorem reward_decreasing_path_positive (n : ℕ) :
    0 < (learner.iterate n).forward.p ((), true, false) := by
  exact mul_pos ((learner.iterate_positive positive n).1 _)
    ((learner.iterate_positive positive n).2 _ _ _)

theorem limit_below_optimum : (7 / 16 : ℝ) <
    LampControl.task.performance LampControl.copy := by
  rw [LampControl.copy_performance]
  norm_num

/-- This strictly positive preparation puts more mass on copy than the
stationary law does. The same reward-biased channel lowers expected reward. -/
noncomputable def overprepared : FiniteFeedbackStep Unit Bool where
  initial := {
    p z := if z.2 then 7 / 8 else 1 / 8
    nonneg z := by cases z.2 <;> norm_num
    sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool] }
  transition _ := channel

theorem overprepared_positive : overprepared.Positive := by
  constructor
  · intro ⟨u, b⟩; cases b <;> norm_num [overprepared]
  · intro u b c; cases b <;> cases c <;> norm_num [overprepared, channel]

/-- Improvement depends on initialization, not just on detailed balance or a
reward-biased energy. This rules out a universal learning-improvement claim. -/
theorem overprepared_reward_decreases :
    (∑ z, overprepared.final.p z * LampControl.task.performance (policy z.2)) <
      ∑ z, overprepared.initial.p z * LampControl.task.performance (policy z.2) := by
  norm_num [FiniteFeedbackStep.final, overprepared, channel, Fintype.sum_prod_type,
    Fintype.sum_bool, policy, LampControl.copy_performance, LampControl.baseline_performance]

/-- The shared-law iteration changes the actual register distribution. This
rejects both frozen learning and resetting each step to the initial law. -/
theorem successive_laws_differ (n : ℕ) :
    (learner.iterate (n + 1)).initial ≠ (learner.iterate n).initial := by
  intro heq
  have hp := congrArg (fun μ : ProbDist (Unit × Bool) => μ.p ((), true)) heq
  rw [copy_probability, copy_probability, pow_succ] at hp
  have h : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  linarith

-- Regression specifications: first run before the definitions and proofs.

example (n : ℕ) : (learner.iterate n).initial.p ((), true) =
    3 / 4 - 1 / 2 * (1 / 2 : ℝ) ^ n := copy_probability n

example (n : ℕ) : performance n < performance (n + 1) :=
  performance_improves n

example : Filter.Tendsto performance Filter.atTop (nhds (7 / 16 : ℝ)) :=
  performance_limit

example (n : ℕ) : (learner.iterate n).meanHeat heat =
    Real.log 3 / 4 * (1 / 2 : ℝ) ^ n := update_heat n

example (n : ℕ) : (∑ k ∈ Finset.range n, (learner.iterate k).meanHeat heat) =
    Real.log 3 / 2 * (1 - (1 / 2 : ℝ) ^ n) := cumulative_heat n

example (n : ℕ) : taskHeat n = LampControl.budget := task_heat n

example : (channel true).p false = 1 / 8 ∧
    LampControl.task.performance (policy false) <
      LampControl.task.performance (policy true) := reward_decreasing_transition

example : (7 / 16 : ℝ) < LampControl.task.performance LampControl.copy :=
  limit_below_optimum

example :
    (∑ z, overprepared.final.p z * LampControl.task.performance (policy z.2)) <
      ∑ z, overprepared.initial.p z * LampControl.task.performance (policy z.2) :=
  overprepared_reward_decreases

end PolicyLearning

#print axioms FiniteFeedbackStep.sum_first_law
#print axioms FiniteFeedbackStep.sum_entropy_balance
#print axioms PolicyLearning.energy_objective
#print axioms PolicyLearning.copy_probability
#print axioms PolicyLearning.performance_improves
#print axioms PolicyLearning.performance_limit
#print axioms PolicyLearning.law_limit
#print axioms PolicyLearning.cumulative_heat
#print axioms PolicyLearning.entropy_accounting
#print axioms PolicyLearning.overprepared_reward_decreases

end PhysicsOfConsciousness.Examples
