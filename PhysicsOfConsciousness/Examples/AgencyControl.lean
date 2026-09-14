import PhysicsOfConsciousness.Examples.AgencyCycle

/-!
# Budgeted finite control: witnesses and regression specifications

All four deterministic policies share a task, initial law, world and memory
channels, reservoir convention and energy. The comparison covers one complete
update; policy learning, installation and switching are outside its scope.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PhysicsOfConsciousness.Examples

section GenericRegression

variable {X S A : Type*} [Fintype X] [Fintype S] [Fintype A]
  (P : FiniteControlProblem X S A) (θ B : ℝ)

example (allowed : Finset (X → A)) (π₀ : X → A) (hmem : π₀ ∈ allowed)
    (hbudget : P.heat θ π₀ ≤ B) :
    ∃ π ∈ allowed, P.heat θ π ≤ B ∧
      ∀ ρ ∈ allowed, P.heat θ ρ ≤ B → P.performance ρ ≤ P.performance π :=
  P.exists_optimal θ B allowed π₀ hmem hbudget

example (E : X × S → ℝ) (π : X → A) :
    P.work E θ π = (∑ z, (P.cycle π).final.p z * E z) -
      (∑ z, P.initial.p z * E z) + P.heat θ π := P.first_law E θ π

variable [Nonempty X] [Nonempty S]

example (π : X → A) (h : P.Positive) (hθ : 0 < θ) (hB : P.heat θ π ≤ B) :
    shannon_entropy P.initial.p - shannon_entropy (P.cycle π).final.p ≤ B / θ :=
  P.entropy_budget π h θ hθ B hB

variable [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace A]
  [MeasurableSingletonClass X] [MeasurableSingletonClass S] [MeasurableSingletonClass A]

example (π : X → A) :
    (P.toAgency π).cycle ∘ₘ P.initial.toMeasure = (P.cycle π).final.toMeasure :=
  P.cycle_law π

end GenericRegression

namespace LampControl

open ThermalAgency (channel energy)

/-- Independent uniform memory and a lamp initially true with probability 1/4. -/
noncomputable def initial : ProbDist (Bool × Bool) where
  p z := if z.2 then 1 / 8 else 3 / 8
  nonneg z := by split <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The declared task rewards a true final lamp. Its channels, initial law and
objective are fixed before comparing policies; thermodynamics supplies no goal. -/
noncomputable def task : FiniteControlProblem Bool Bool Bool where
  initial := initial
  world := channel
  memory := channel
  reward z := if z.2 then 1 else 0

def baseline : Bool → Bool := fun _ => false
def copy : Bool → Bool := id
def invert : Bool → Bool := Bool.not
def alwaysTrue : Bool → Bool := fun _ => true

/-- The supplied upper heat allowance for one update. It is not identified
with the cost of a separate register or a continuing energy source. -/
noncomputable def budget : ℝ := Real.log 3 / 4

theorem positive : task.Positive := by
  refine ⟨?_, ThermalAgency.actuation_positive.2, ThermalAgency.sensing_positive.2⟩
  intro z
  cases z with | mk x s => cases s <;> norm_num [task, initial]

/-- Exhaustiveness fences the allowed policy class: all deterministic bit maps,
with no unaccounted stochastic action or additional physical register. -/
theorem policies_exhaustive (π : Bool → Bool) :
    π = baseline ∨ π = copy ∨ π = invert ∨ π = alwaysTrue := by
  cases hf : π false <;> cases ht : π true
  · left; funext x; cases x <;> simp [baseline, hf, ht]
  · right; left; funext x; cases x <;> simp [copy, hf, ht]
  · right; right; left; funext x; cases x <;> simp [invert, hf, ht]
  · right; right; right; funext x; cases x <;> simp [alwaysTrue, hf, ht]

theorem actuationHeat_eq (π : Bool → Bool) (x s t : Bool) :
    task.actuationHeat 1 π x s t = ThermalAgency.heat (π x) s t :=
  (ThermalAgency.channel_local_balance (π x) s t).symm

theorem memoryHeat_eq (s x y : Bool) :
    task.memoryHeat 1 s x y = ThermalAgency.heat s x y :=
  (ThermalAgency.channel_local_balance s x y).symm

/-- Exact reward from the final law of the two composed channels. -/
theorem performance_formula (π : Bool → Bool) :
    task.performance π =
      ((if π false then (3 : ℝ) else 1) + (if π true then (3 : ℝ) else 1)) / 8 := by
  cases hf : π false <;> cases ht : π true <;>
    norm_num [FiniteControlProblem.performance, FiniteControlProblem.cycle, task,
      FiniteFeedbackCycle.final, FiniteFeedbackCycle.sensing, ProbDist.swap,
      FiniteFeedbackStep.final, initial, channel, Fintype.sum_prod_type,
      Fintype.sum_bool, hf, ht]

/-- Mean actuation heat on its own actual forward paths, before memory updates. -/
theorem actuation_heat_formula (π : Bool → Bool) :
    (task.cycle π).actuation.meanHeat (task.actuationHeat 1 π) =
      ((if π false then (1 : ℝ) else 0) + (if π true then (1 : ℝ) else 0)) *
        Real.log 3 / 4 := by
  simp only [FiniteFeedbackStep.meanHeat, actuationHeat_eq]
  cases hf : π false <;> cases ht : π true <;>
    norm_num [FiniteFeedbackStep.forward, FiniteControlProblem.cycle, task, initial,
      ThermalAgency.heat, energy, channel, Fintype.sum_prod_type,
      Fintype.sum_bool, hf, ht] <;> ring

/-- Memory heat uses the policy-dependent, swapped intermediate law. Counting
only actuation would misclassify policies under the whole-update budget. -/
theorem memory_heat_formula (π : Bool → Bool) :
    (task.cycle π).sensing.meanHeat (task.memoryHeat 1) =
      ((if π false then (1 : ℝ) else 0) + (if π true then (0 : ℝ) else 1)) *
        Real.log 3 / 4 := by
  simp only [FiniteFeedbackStep.meanHeat, memoryHeat_eq]
  cases hf : π false <;> cases ht : π true <;>
    norm_num [FiniteFeedbackStep.forward,
      FiniteControlProblem.cycle, FiniteFeedbackCycle.sensing, ProbDist.swap,
      FiniteFeedbackStep.final, task, initial, ThermalAgency.heat, energy,
      channel, Fintype.sum_prod_type, Fintype.sum_bool, hf, ht] <;> ring

/-- The complete expected heat depends on the policy even at equal final law. -/
theorem heat_formula (π : Bool → Bool) :
    task.heat 1 π = if π false then 3 * Real.log 3 / 4 else Real.log 3 / 4 := by
  unfold FiniteControlProblem.heat FiniteFeedbackCycle.meanHeat
  rw [actuation_heat_formula, memory_heat_formula]
  cases π false <;> cases π true <;> norm_num <;> ring

/-- The initial mean energy is shared by every comparison. -/
theorem initial_energy : (∑ z, task.initial.p z * energy z) = Real.log 3 / 2 := by
  norm_num [task, initial, energy, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- Thermal memory leaves the same mean interaction energy for each policy;
this does not say that their final distributions or heat costs are equal. -/
theorem final_energy (π : Bool → Bool) :
    (∑ z, (task.cycle π).final.p z * energy z) = Real.log 3 / 4 := by
  cases hf : π false <;> cases ht : π true <;>
    norm_num [FiniteControlProblem.cycle, FiniteFeedbackCycle.final,
      FiniteFeedbackCycle.sensing, ProbDist.swap, FiniteFeedbackStep.final,
      task, initial, energy, channel, Fintype.sum_prod_type, Fintype.sum_bool,
      hf, ht] <;> ring

/-- Total mean work follows from both path observables and the common first law.
Zero expected work does not assert that work vanishes on each individual path. -/
theorem work_formula (π : Bool → Bool) :
    task.work energy 1 π = if π false then Real.log 3 / 2 else 0 := by
  rw [task.first_law, initial_energy, final_energy, heat_formula]
  cases π false <;> norm_num <;> ring

theorem copy_performance : task.performance copy = 1 / 2 := by
  norm_num [performance_formula, copy]

theorem baseline_performance : task.performance baseline = 1 / 4 := by
  norm_num [performance_formula, baseline]

theorem copy_heat : task.heat 1 copy = Real.log 3 / 4 := by
  simp [heat_formula, copy]

theorem copy_work : task.work energy 1 copy = 0 := by
  simp [work_formula, copy]

private theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

/-- Exactly two of the four permitted policies fit the supplied budget.
Feasibility alone cannot distinguish their different task performances. -/
theorem feasible_iff (π : Bool → Bool) :
    task.heat 1 π ≤ budget ↔ π = baseline ∨ π = copy := by
  rcases policies_exhaustive π with rfl | rfl | rfl | rfl <;>
    norm_num [heat_formula, budget, baseline, copy, invert, alwaysTrue, funext_iff]
  all_goals linarith [log_three_pos]

/-- A feasible policy misses the declared target of success probability 1/2.
This refutes task success as a consequence of the thermodynamic budget alone. -/
theorem feasible_failure :
    task.heat 1 baseline ≤ budget ∧ task.performance baseline < 1 / 2 := by
  constructor
  · exact (feasible_iff baseline).mpr (Or.inl rfl)
  · rw [baseline_performance]; norm_num

/-- Copy strictly improves the same task over the feasible baseline and
maximizes performance over every feasible deterministic bit policy. The goal,
fixed channels and budget are specified inputs, not consequences of heat. -/
theorem budgeted_improvement :
    task.performance baseline < task.performance copy ∧ task.heat 1 copy ≤ budget ∧
      ∀ π : Bool → Bool, task.heat 1 π ≤ budget →
        task.performance π ≤ task.performance copy := by
  refine ⟨?_, (feasible_iff copy).mpr (Or.inr rfl), ?_⟩
  · rw [baseline_performance, copy_performance]; norm_num
  · intro π hπ
    rcases (feasible_iff π).mp hπ with rfl | rfl
    · rw [baseline_performance, copy_performance]; norm_num
    · exact le_rfl

/-- The finite optimizer is uniquely the explicit copy policy at this budget.
This is selection among fixed policies, not a learning-convergence theorem. -/
theorem unique_optimum (π : Bool → Bool) :
    (task.heat 1 π ≤ budget ∧ ∀ ρ : Bool → Bool, task.heat 1 ρ ≤ budget →
      task.performance ρ ≤ task.performance π) ↔ π = copy := by
  constructor
  · rintro ⟨hπ, hmax⟩
    rcases (feasible_iff π).mp hπ with rfl | rfl
    · have h := hmax copy budgeted_improvement.2.1
      rw [baseline_performance, copy_performance] at h
      norm_num at h
    · rfl
  · rintro rfl
    exact budgeted_improvement.2

/-- The higher-reward constant-true policy violates the actual heat budget. -/
theorem stronger_policy_infeasible :
    task.performance copy < task.performance alwaysTrue ∧
      ¬ task.heat 1 alwaysTrue ≤ budget := by
  rw [copy_performance, performance_formula, heat_formula]
  norm_num [alwaysTrue, budget]
  linarith [log_three_pos]

/-- Equal outputs can hide different thermodynamic processes: invert spends
more heat and work than copy. Endpoint reward cannot replace path accounting. -/
theorem equal_output_different_heat :
    (task.cycle copy).final = (task.cycle invert).final ∧
      task.heat 1 copy < task.heat 1 invert := by
  constructor
  · apply ProbDist.ext
    funext z
    rcases z with ⟨x, s⟩
    cases x <;> cases s <;>
      norm_num [FiniteControlProblem.cycle, FiniteFeedbackCycle.final,
        FiniteFeedbackCycle.sensing, ProbDist.swap, FiniteFeedbackStep.final,
        task, initial, channel, copy, invert, Fintype.sum_bool]
  · rw [copy_heat, heat_formula]
    norm_num [invert]
    linarith [log_three_pos]

/-- The selected actuator depends on memory and the memory channel can change
the bit. Neither substep is an identity channel. -/
theorem nontrivial_updates :
    ((task.cycle copy).actuation.transition true false).p true = 3 / 4 ∧
    ((task.cycle copy).actuation.transition false false).p true = 1 / 4 ∧
    ((task.cycle copy).memory true false).p true = 3 / 4 := by
  norm_num [FiniteControlProblem.cycle, task, channel, copy]

/-- The selected policy inherits the whole-update entropy theorem at its exact
heat budget. This does not identify that budget with any erasing register. -/
theorem selected_entropy_budget :
    shannon_entropy task.initial.p - shannon_entropy (task.cycle copy).final.p ≤ budget := by
  simpa only [div_one] using
    task.entropy_budget copy positive 1 (by norm_num) budget budgeted_improvement.2.1

end LampControl

section Regression

open LampControl
open ThermalAgency (energy)

example : task.performance copy = 1 / 2 := copy_performance

example : task.performance baseline = 1 / 4 := baseline_performance

example : task.heat 1 copy = Real.log 3 / 4 := copy_heat

example : task.work energy 1 copy = 0 := copy_work

example : (1 : ℝ) / 2 ≤ task.performance copy := copy_performance.ge

example : ∃ π ∈ (Finset.univ : Finset (Bool → Bool)), task.heat 1 π ≤ budget ∧
    ∀ ρ ∈ (Finset.univ : Finset (Bool → Bool)), task.heat 1 ρ ≤ budget →
      task.performance ρ ≤ task.performance π :=
  task.exists_optimal 1 budget Finset.univ baseline (Finset.mem_univ _) feasible_failure.1

example : task.heat 1 baseline ≤ budget ∧ task.performance baseline < 1 / 2 :=
  feasible_failure

example : task.performance baseline < task.performance copy ∧
    task.heat 1 copy ≤ budget ∧
    ∀ π : Bool → Bool, task.heat 1 π ≤ budget →
      task.performance π ≤ task.performance copy := budgeted_improvement

example : task.performance copy < task.performance alwaysTrue ∧
    ¬ task.heat 1 alwaysTrue ≤ budget := stronger_policy_infeasible

example : (task.cycle copy).final = (task.cycle invert).final ∧
    task.heat 1 copy < task.heat 1 invert := equal_output_different_heat

end Regression

#print axioms FiniteControlProblem.exists_optimal
#print axioms FiniteControlProblem.cycle_law
#print axioms FiniteControlProblem.first_law
#print axioms FiniteControlProblem.entropy_budget
#print axioms LampControl.budgeted_improvement
#print axioms LampControl.unique_optimum
#print axioms LampControl.feasible_failure
#print axioms LampControl.stronger_policy_infeasible
#print axioms LampControl.equal_output_different_heat

end PhysicsOfConsciousness.Examples
