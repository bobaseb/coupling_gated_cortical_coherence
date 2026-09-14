import PhysicsOfConsciousness.Phase3_ObservationalLearning
import PhysicsOfConsciousness.Examples.PolicyLearning

/-!
# Learning from experience: witness and regression specifications

A two-action choice task whose rewarding action is an unknown environmental
bit. The register's value is the action executed; the only thing that ever
changes it is the realized outcome of the action it just took. Nothing in the
model hands it the parameter or the actions' values.
-/

namespace PhysicsOfConsciousness.Examples

section GenericRegression

variable {W R A O : Type*} [Fintype W] [Fintype R] [Fintype A] [Fintype O]
  (L : FiniteObservationalLearner W R A O)

example (n : ℕ) : L.law (n + 1) = (L.step.iterate n).final := L.law_succ n

example (θ : ℝ) (E : R → ℝ) (h : ∀ w r r', E r' - E r + L.heat θ w r r' = 0)
    (w w' : W) (r r' : R) : L.heat θ w r r' = L.heat θ w' r r' :=
  L.zero_work_needs_parameter_independent_heat θ E h w w' r r'

example [Nonempty R] (h : L.step.Positive) (θ : ℝ) (hθ : 0 < θ) (N : ℕ) :
    θ * (shannon_entropy (L.law 0).p - shannon_entropy (L.law N).p) ≤
      ∑ n ∈ Finset.range N, (L.step.iterate n).meanHeat (L.heat θ) :=
  L.cumulative_entropy_budget h θ hθ N

example [DecidableEq R] (n : ℕ) : L.frozen.law n = L.prior := L.frozen_law n

end GenericRegression

namespace ObservationalLearning

open FiniteObservationalLearner

/-- The register's value is the action executed. It decodes no policy value:
the map has no access to the environmental parameter. -/
def readout : Bool → Bool := id

/-- The rewarding action is unknown and the register has no preference: the
declared initial uncertainty is the uniform product law. -/
noncomputable def prior : ProbDist (Bool × Bool) where
  p _ := 1 / 4
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The world returns success with probability `3/4` for the rewarding action
and `1/4` for the other. The outcome is a realized noisy consequence of the
action taken, not the action's expected value. -/
noncomputable def world (w a : Bool) : ProbDist Bool where
  p o := if o then (if a = w then 3 / 4 else 1 / 4) else (if a = w then 1 / 4 else 3 / 4)
  nonneg o := by cases o <;> cases a <;> cases w <;> norm_num
  sum_one := by cases w <;> cases a <;> norm_num [Fintype.sum_bool]

/-- Win-stay, lose-resample: success leaves the register alone, failure
redraws it uniformly. The rule reads the observation and nothing else. -/
noncomputable def update (o r : Bool) : ProbDist Bool where
  p r' := if o then (if r' = r then 1 else 0) else 1 / 2
  nonneg r' := by cases o <;> cases r <;> cases r' <;> norm_num
  sum_one := by cases o <;> cases r <;> norm_num [Fintype.sum_bool]

/-- The evaluation criterion. It appears in no channel of the learner. -/
def reward (w a : Bool) : ℝ := if a = w then 1 else 0

noncomputable def learner : FiniteObservationalLearner Bool Bool Bool Bool :=
  ⟨prior, readout, world, update, reward⟩

/-- The composite act--observe--update channel, at the fixed unknown parameter.
A register holding the rewarding action keeps it with probability `7/8`; one
holding the other action moves to it with probability `3/8`. -/
theorem transition_apply (w r r' : Bool) :
    (learner.transition w r).p r' =
      if r' = r then (if r = w then 7 / 8 else 5 / 8)
      else (if r = w then 1 / 8 else 3 / 8) := by
  show (∑ o, (learner.world w (learner.readout r)).p o * (learner.update o r).p r') = _
  cases w <;> cases r <;> cases r' <;>
    norm_num [learner, world, update, readout, Fintype.sum_bool]

theorem positive : learner.step.Positive := by
  constructor
  · intro z; norm_num [FiniteObservationalLearner.step, learner, prior]
  · intro w r r'
    show 0 < (learner.transition w r).p r'
    rw [transition_apply]
    cases w <;> cases r <;> cases r' <;> norm_num

/-- Outward heat of one register transition, at thermal scale one, in the
declared reservoir model for the drive that implements the update. -/
noncomputable def heat : Bool → Bool → Bool → ℝ := learner.heat 1

theorem heat_apply (w r r' : Bool) :
    heat w r r' = if r' = r then 0 else (if r = w then -Real.log 3 else Real.log 3) := by
  show 1 * Real.log ((learner.transition w r).p r' / (learner.transition w r').p r) = _
  rw [transition_apply, transition_apply]
  cases w <;> cases r <;> cases r' <;>
    norm_num [Real.log_div, Real.log_inv, show (1 : ℝ) / 3 = 3⁻¹ by norm_num]

theorem heat_def : heat = learner.heat 1 := rfl

theorem local_balance (n : ℕ) :
    (learner.step.iterate n).LocalDetailedBalance 1 heat :=
  learner.local_balance 1 n

/-! ### The actual evolving law -/

/-- Every mass of the joint parameter--register law, at every horizon. The
learner's whole trajectory is one geometric approach of the agreeing pairs. -/
theorem law_apply (n : ℕ) (z : Bool × Bool) :
    (learner.law n).p z =
      if z.1 = z.2 then 3 / 8 - 1 / 8 * (1 / 2 : ℝ) ^ n
      else 1 / 8 + 1 / 8 * (1 / 2 : ℝ) ^ n := by
  induction n generalizing z with
  | zero =>
    rcases z with ⟨w, r⟩
    cases w <;> cases r <;> norm_num [FiniteObservationalLearner.law_zero, learner, prior]
  | succ n ih =>
    rw [FiniteObservationalLearner.law_succ_apply]
    rcases z with ⟨w, r⟩
    cases w <;> cases r <;>
      simp only [Fintype.sum_bool, ih, transition_apply] <;> norm_num <;> ring

/-- Learning here is correlation, not preference: the frequency with which each
action is executed is exactly one half at every horizon. What changes is which
action is executed at which value of the unknown parameter. -/
theorem action_marginal_unchanged (n : ℕ) :
    (learner.law n).p (true, true) + (learner.law n).p (false, true) = 1 / 2 := by
  rw [law_apply, law_apply]
  norm_num

/-- At the first update the register is already correlated with the parameter:
the agreeing mass exceeds the product of the two marginals. -/
theorem register_correlates :
    (learner.law 1).p (true, true) = 5 / 16 ∧
      ((learner.law 1).p (true, true) + (learner.law 1).p (true, false)) *
        ((learner.law 1).p (true, true) + (learner.law 1).p (false, true)) = 1 / 4 := by
  constructor
  · rw [law_apply]; norm_num
  · rw [law_apply, law_apply, law_apply]; norm_num

/-- The shared-law iteration changes the actual joint law at every horizon,
rejecting both a frozen register and a reset to the prior. -/
theorem successive_laws_differ (n : ℕ) : learner.law (n + 1) ≠ learner.law n := by
  intro heq
  have hp := congrArg (fun μ : ProbDist (Bool × Bool) => μ.p (true, true)) heq
  simp only [law_apply] at hp
  norm_num [pow_succ] at hp

/-! ### Performance of the action actually executed -/

/-- Expected reward of the action the register executes at update `n`,
evaluated on the same law the heat and entropy balances use. -/
theorem performance_formula (n : ℕ) :
    learner.performance n = 3 / 4 - 1 / 4 * (1 / 2 : ℝ) ^ n := by
  unfold FiniteObservationalLearner.performance
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, law_apply]
  norm_num [learner, reward, readout]
  ring

theorem performance_zero : learner.performance 0 = 1 / 2 := by
  rw [performance_formula]; norm_num

/-- Strict improvement at every update, from the declared uniform prior. -/
theorem performance_improves (n : ℕ) :
    learner.performance n < learner.performance (n + 1) := by
  rw [performance_formula, performance_formula, pow_succ]
  have h : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  linarith

theorem performance_limit :
    Filter.Tendsto learner.performance Filter.atTop (nhds (3 / 4 : ℝ)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
  change Filter.Tendsto (fun n => learner.performance n) Filter.atTop _
  simp_rw [performance_formula]
  simpa only [mul_zero, sub_zero] using
    ((tendsto_const_nhds (x := (3 / 4 : ℝ))).sub (hp.const_mul (1 / 4 : ℝ)))

/-- The learner never reaches the reward of always executing the rewarding
action: its noisy outcomes keep a positive mass on the other one. -/
theorem performance_below_certainty (n : ℕ) : learner.performance n < 1 := by
  rw [performance_formula]
  have h : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  linarith

/-! ### Resource accounting on the same process -/

/-- The supplied work allowance, common to the learner and to both baselines. -/
noncomputable def budget : ℝ := Real.log 3 / 4

theorem update_heat (n : ℕ) :
    (learner.step.iterate n).meanHeat heat = Real.log 3 / 8 * (1 / 2 : ℝ) ^ n := by
  rw [heat_def, learner.meanHeat_apply]
  simp only [Fintype.sum_bool, law_apply, transition_apply, ← heat_def, heat_apply]
  norm_num
  ring

theorem update_heat_positive (n : ℕ) : 0 < (learner.step.iterate n).meanHeat heat := by
  rw [update_heat]
  exact mul_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (pow_pos (by norm_num) n)

theorem cumulative_heat (N : ℕ) :
    (∑ n ∈ Finset.range N, (learner.step.iterate n).meanHeat heat) =
      budget * (1 - (1 / 2 : ℝ) ^ N) := by
  simp only [update_heat]
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  unfold budget
  field_simp
  ring

theorem cumulative_heat_le_budget (N : ℕ) :
    (∑ n ∈ Finset.range N, (learner.step.iterate n).meanHeat heat) ≤ budget := by
  rw [cumulative_heat]
  have h := mul_nonneg (div_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
    (by norm_num : (0 : ℝ) ≤ 4)) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N)
  unfold budget at *
  nlinarith

/-- The register's two states are energetically degenerate, so it stores
nothing: the entire cumulative heat is work supplied by whatever drives the
observation-conditioned update. Learning here is not a relaxation. -/
theorem cumulative_work (N : ℕ) :
    (∑ n ∈ Finset.range N,
        (learner.step.iterate n).meanHeat (learner.work (fun _ => 0) 1)) =
      budget * (1 - (1 / 2 : ℝ) ^ N) := by
  rw [learner.cumulative_work_eq_heat 0 1 N, ← heat_def]
  exact cumulative_heat N

theorem cumulative_work_positive (N : ℕ) :
    0 < ∑ n ∈ Finset.range (N + 1),
      (learner.step.iterate n).meanHeat (learner.work (fun _ => 0) 1) := by
  rw [cumulative_work]
  have h : (1 / 2 : ℝ) ^ (N + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hb : 0 < budget := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  nlinarith

/-- **Nothing is learned for free.** A register energy that made every update a
free relaxation would force the drive's heat to be the same at both parameter
values, and this drive's heat is not. The obstruction is the content of the
model: an energy landscape that paid for the learning would be one that already
encoded the answer. -/
theorem no_zero_work_energy :
    ¬ ∃ E : Bool → ℝ, ∀ w r r', E r' - E r + heat w r r' = 0 := by
  rintro ⟨E, hE⟩
  have h : heat true false true = heat false false true :=
    learner.zero_work_needs_parameter_independent_heat 1 E hE true false false true
  rw [heat_apply, heat_apply] at h
  norm_num at h
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne' (by linarith)

/-- The joint entropy the learner removes is paid for by the same process's
cumulative heat, within the supplied allowance, at every horizon. -/
theorem learning_entropy_budget (N : ℕ) :
    shannon_entropy (learner.law 0).p - shannon_entropy (learner.law N).p ≤ budget := by
  have h := learner.cumulative_entropy_budget positive 1 (by norm_num) N
  rw [one_mul, ← heat_def] at h
  exact h.trans (cumulative_heat_le_budget N)

/-! ### Baselines under the same allowance -/

/-- The frozen register executes actions and observes outcomes but writes
nothing down. Its expected reward is the prior's at every horizon. -/
theorem frozen_performance (n : ℕ) : learner.frozen.performance n = 1 / 2 := by
  unfold FiniteObservationalLearner.performance
  rw [FiniteObservationalLearner.frozen_law]
  norm_num [FiniteObservationalLearner.frozen, learner, prior, reward, readout,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- An uninformative world: success has probability one half whatever is done. -/
noncomputable def blindWorld (_w _a : Bool) : ProbDist Bool where
  p _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- The same register, readout, prior, update rule and reward, observing a
world whose outcomes carry nothing about the parameter. -/
noncomputable def blind : FiniteObservationalLearner Bool Bool Bool Bool :=
  { learner with world := blindWorld }

theorem blind_transition (w r r' : Bool) :
    (blind.transition w r).p r' = if r' = r then 3 / 4 else 1 / 4 := by
  show (∑ o, (blind.world w (blind.readout r)).p o * (blind.update o r).p r') = _
  cases r <;> cases r' <;>
    norm_num [blind, learner, blindWorld, update, readout, Fintype.sum_bool]

theorem blind_positive : blind.step.Positive := by
  constructor
  · intro z; norm_num [FiniteObservationalLearner.step, blind, learner, prior]
  · intro w r r'
    show 0 < (blind.transition w r).p r'
    rw [blind_transition]
    cases r <;> cases r' <;> norm_num

theorem blind_law (n : ℕ) : blind.law n = prior := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply ProbDist.ext
    funext z
    rw [FiniteObservationalLearner.law_succ_apply, ih]
    rcases z with ⟨w, r⟩
    cases r <;> simp only [Fintype.sum_bool, blind_transition] <;> norm_num [prior]

/-- Uninformative observations buy no improvement. The claim depends on the
observations carrying task information, not on the update rule or the heat. -/
theorem blind_performance (n : ℕ) : blind.performance n = 1 / 2 := by
  unfold FiniteObservationalLearner.performance
  rw [blind_law]
  norm_num [blind, learner, prior, reward, readout, Fintype.sum_prod_type, Fintype.sum_bool]

/-- Its transitions are parameter-independent and reversible, so it spends
nothing: the uninformative learner is free and learns nothing. -/
theorem blind_heat (w r r' : Bool) : blind.heat 1 w r r' = 0 := by
  show 1 * Real.log ((blind.transition w r).p r' / (blind.transition w r').p r) = _
  rw [blind_transition, blind_transition]
  cases r <;> cases r' <;> norm_num

/-- Strict improvement over both baselines at every update, under a common
supplied allowance that each of the three processes respects. -/
theorem improves_on_baselines (n : ℕ) :
    learner.frozen.performance n < learner.performance (n + 1) ∧
      blind.performance n < learner.performance (n + 1) ∧
      (∑ k ∈ Finset.range (n + 1), (learner.step.iterate k).meanHeat heat) ≤ budget := by
  have h : (1 / 2 : ℝ) < learner.performance (n + 1) := by
    rw [performance_formula]
    have hp : (1 / 2 : ℝ) ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  exact ⟨by rw [frozen_performance]; exact h, by rw [blind_performance]; exact h,
    cumulative_heat_le_budget (n + 1)⟩

/-! ### What the observations do, and what they do not -/

/-- The outcome is informative about the parameter given the action executed. -/
theorem observation_informative :
    (learner.outcome true true).p true = 3 / 4 ∧
      (learner.outcome false true).p true = 1 / 4 := by
  constructor <;> norm_num [FiniteObservationalLearner.outcome, learner, world, readout]

/-- It is not informative unconditionally: at the uniform prior the joint mass
of each parameter value with success is the product of the two marginals. An
observation is evidence only in the context of the action that produced it. -/
theorem outcome_marginal_uninformative (w : Bool) :
    (∑ r, (learner.law 0).p (w, r) * (learner.outcome w r).p true) = 1 / 4 := by
  cases w <;>
    norm_num [Fintype.sum_bool, FiniteObservationalLearner.law_zero,
      FiniteObservationalLearner.outcome, learner, prior, world, readout]

/-- The update depends on the observation, so the policy it holds can change. -/
theorem update_depends_on_observation :
    (learner.update true true).p true = 1 ∧ (learner.update false true).p true = 1 / 2 := by
  constructor <;> norm_num [learner, update]

/-- The next world transition depends on the register through the readout, so
a changed policy is a changed process and not only a changed label. -/
theorem world_depends_on_policy (w : Bool) :
    (learner.world w (learner.readout w)).p true = 3 / 4 ∧
      (learner.world w (learner.readout (!w))).p true = 1 / 4 := by
  cases w <;> constructor <;> norm_num [learner, world, readout]

/-- Expected improvement is not improvement of every path: the register leaves
the rewarding action with probability one eighth at every update. -/
theorem reward_decreasing_transition (w : Bool) :
    (learner.transition w w).p (!w) = 1 / 8 := by
  rw [transition_apply]
  cases w <;> norm_num

theorem reward_decreasing_path_positive (n : ℕ) (w : Bool) :
    0 < (learner.step.iterate n).forward.p (w, w, !w) :=
  mul_pos ((learner.step.iterate_positive positive n).1 _)
    ((learner.step.iterate_positive positive n).2 _ _ _)

end ObservationalLearning

-- Regression specifications: first run before the definitions and proofs.

section Regression

open ObservationalLearning

example : learner.performance 0 = 1 / 2 := performance_zero

example (n : ℕ) : learner.performance n = 3 / 4 - 1 / 4 * (1 / 2 : ℝ) ^ n :=
  performance_formula n

example (n : ℕ) : learner.performance n < learner.performance (n + 1) :=
  performance_improves n

example : Filter.Tendsto learner.performance Filter.atTop (nhds (3 / 4 : ℝ)) :=
  performance_limit

example (n : ℕ) : learner.performance n < 1 := performance_below_certainty n

example (n : ℕ) : (learner.step.iterate n).meanHeat heat =
    Real.log 3 / 8 * (1 / 2 : ℝ) ^ n := update_heat n

example (N : ℕ) : (∑ n ∈ Finset.range N, (learner.step.iterate n).meanHeat heat) ≤ budget :=
  cumulative_heat_le_budget N

example (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (learner.step.iterate n).meanHeat (learner.work (fun _ => 0) 1)) =
        budget * (1 - (1 / 2 : ℝ) ^ N) := cumulative_work N

example : ¬ ∃ E : Bool → ℝ, ∀ w r r', E r' - E r + heat w r r' = 0 :=
  no_zero_work_energy

example (N : ℕ) :
    shannon_entropy (learner.law 0).p - shannon_entropy (learner.law N).p ≤ budget :=
  learning_entropy_budget N

example (n : ℕ) :
    learner.frozen.performance n < learner.performance (n + 1) ∧
      blind.performance n < learner.performance (n + 1) ∧
      (∑ k ∈ Finset.range (n + 1), (learner.step.iterate k).meanHeat heat) ≤ budget :=
  improves_on_baselines n

example (n : ℕ) : blind.performance n = 1 / 2 := blind_performance n

example (w r r' : Bool) : blind.heat 1 w r r' = 0 := blind_heat w r r'

example : (learner.outcome true true).p true = 3 / 4 ∧
    (learner.outcome false true).p true = 1 / 4 := observation_informative

example (w : Bool) :
    (∑ r, (learner.law 0).p (w, r) * (learner.outcome w r).p true) = 1 / 4 :=
  outcome_marginal_uninformative w

example (w : Bool) : (learner.transition w w).p (!w) = 1 / 8 :=
  reward_decreasing_transition w

example (n : ℕ) : learner.law (n + 1) ≠ learner.law n := successive_laws_differ n

example (n : ℕ) :
    (learner.law n).p (true, true) + (learner.law n).p (false, true) = 1 / 2 :=
  action_marginal_unchanged n

example : (learner.law 1).p (true, true) = 5 / 16 ∧
    ((learner.law 1).p (true, true) + (learner.law 1).p (true, false)) *
      ((learner.law 1).p (true, true) + (learner.law 1).p (false, true)) = 1 / 4 :=
  register_correlates

example : (learner.update true true).p true = 1 ∧
    (learner.update false true).p true = 1 / 2 := update_depends_on_observation

example (w : Bool) : (learner.world w (learner.readout w)).p true = 3 / 4 ∧
    (learner.world w (learner.readout (!w))).p true = 1 / 4 :=
  world_depends_on_policy w

example (n : ℕ) (w : Bool) : 0 < (learner.step.iterate n).forward.p (w, w, !w) :=
  reward_decreasing_path_positive n w

example (n : ℕ) : 0 < (learner.step.iterate n).meanHeat heat := update_heat_positive n

example (N : ℕ) : 0 < ∑ n ∈ Finset.range (N + 1),
    (learner.step.iterate n).meanHeat (learner.work (fun _ => 0) 1) :=
  cumulative_work_positive N

example (N : ℕ) : (∑ n ∈ Finset.range N, (learner.step.iterate n).meanHeat heat) =
    budget * (1 - (1 / 2 : ℝ) ^ N) := cumulative_heat N

example (n : ℕ) : learner.frozen.performance n = 1 / 2 := frozen_performance n

example : blind.step.Positive := blind_positive

example (n : ℕ) : (learner.step.iterate n).LocalDetailedBalance 1 heat := local_balance n

end Regression

end PhysicsOfConsciousness.Examples

#print axioms PhysicsOfConsciousness.FiniteObservationalLearner.law_succ_apply
#print axioms PhysicsOfConsciousness.FiniteObservationalLearner.frozen_law
#print axioms
  PhysicsOfConsciousness.FiniteObservationalLearner.zero_work_needs_parameter_independent_heat
#print axioms PhysicsOfConsciousness.FiniteObservationalLearner.cumulative_entropy_budget
#print axioms PhysicsOfConsciousness.Examples.ObservationalLearning.law_apply
#print axioms PhysicsOfConsciousness.Examples.ObservationalLearning.performance_improves
#print axioms PhysicsOfConsciousness.Examples.ObservationalLearning.improves_on_baselines
#print axioms PhysicsOfConsciousness.Examples.ObservationalLearning.cumulative_heat
#print axioms PhysicsOfConsciousness.Examples.ObservationalLearning.no_zero_work_energy
#print axioms PhysicsOfConsciousness.Examples.ObservationalLearning.learning_entropy_budget
#print axioms PhysicsOfConsciousness.Examples.ObservationalLearning.blind_performance
