import PhysicsOfConsciousness.Examples.AgencyThermodynamics

/-!
# Complete finite-update witnesses and regression specifications

The reciprocal and biased two-bit models exercise the same general composition.
They establish realizability and reject an incompatible intermediate law, not a
cortical identification, learned policy or continuing supply of useful work.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PhysicsOfConsciousness.Examples

section Regression

variable {X S : Type*} [Fintype X] [Fintype S] [Nonempty X] [Nonempty S]
  (C : FiniteFeedbackCycle X S) (h : C.Positive)

example : C.sensing.initial = C.actuation.final.swap := rfl

example : C.entropyProduction =
    shannon_entropy C.final.p - shannon_entropy C.actuation.initial.p +
      C.actuation.bathEntropy + C.sensing.bathEntropy := C.entropy_balance h

example (θ : ℝ) (hθ : 0 < θ) (qa : X → S → S → ℝ) (qm : S → X → X → ℝ)
    (ha : C.actuation.LocalDetailedBalance θ qa)
    (hm : C.sensing.LocalDetailedBalance θ qm) (B : ℝ)
    (hB : C.meanHeat qa qm ≤ B) :
    shannon_entropy C.actuation.initial.p - shannon_entropy C.final.p ≤ B / θ :=
  C.entropy_budget h θ hθ qa qm ha hm B hB

example (E : X × S → ℝ) (qa wa : X → S → S → ℝ) (qm wm : S → X → X → ℝ)
    (ha : ∀ x s t, wa x s t = E (x, t) - E (x, s) + qa x s t)
    (hm : ∀ s x y, wm s x y = E (y, s) - E (x, s) + qm s x y) :
    C.meanHeat wa wm = (∑ z, C.final.p z * E z) -
      (∑ z, C.actuation.initial.p z * E z) + C.meanHeat qa qm :=
  C.mean_first_law E qa wa qm wm ha hm

variable [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSingletonClass X] [MeasurableSingletonClass S]

example : C.toAgency.cycle ∘ₘ C.actuation.initial.toMeasure = C.final.toMeasure :=
  C.cycle_law

end Regression

namespace ThermalAgency

/-- The existing reciprocal example, now carried by the generic construction. -/
noncomputable def reciprocalCycle : FiniteFeedbackCycle Bool Bool := ⟨actuation, channel⟩

theorem correlated_swap : correlated.swap = correlated := by
  apply ProbDist.ext
  funext z
  simp [ProbDist.swap, correlated, eq_comm]

theorem reciprocal_sensing : reciprocalCycle.sensing = sensing := by
  change (⟨actuation.final.swap, channel⟩ : FiniteFeedbackStep Bool Bool) = sensing
  rw [actuation_final, correlated_swap]
  rfl

theorem reciprocal_positive : reciprocalCycle.Positive :=
  ⟨actuation_positive, sensing_positive.2⟩

theorem reciprocal_final : reciprocalCycle.final = correlated := by
  rw [FiniteFeedbackCycle.final, reciprocal_sensing, sensing_final, correlated_swap]

theorem reciprocal_agent : reciprocalCycle.toAgency = agent := rfl

theorem reciprocal_initial : reciprocalCycle.actuation.initial = independent := rfl

/-- The generic channel-law identification specializes to the original model. -/
theorem reciprocal_cycle_law :
    agent.cycle ∘ₘ independent.toMeasure = correlated.toMeasure := by
  simpa only [reciprocal_agent, reciprocal_final, reciprocal_initial] using
    reciprocalCycle.cycle_law

/-- Both substep costs in the generic cycle equal the previous exact values;
the final law differs from the initial law, despite equilibrium in sensing. -/
theorem reciprocal_costs :
    reciprocalCycle.meanHeat heat heat = Real.log 3 / 4 ∧
      reciprocalCycle.entropyProduction = Real.log 2 - Real.log 3 / 2 := by
  simp only [FiniteFeedbackCycle.meanHeat, FiniteFeedbackCycle.entropyProduction,
    reciprocal_sensing]
  change actuation.meanHeat heat + sensing.meanHeat heat = _ ∧
    actuation.entropyProduction + sensing.entropyProduction = _
  rw [actuation_heat, sensing_heat, actuation_entropy_production, sensing_entropy_production]
  simp

/-- A zero budget cannot fund the complete update's strictly positive heat. -/
theorem reciprocal_zero_budget_rejected : ¬ reciprocalCycle.meanHeat heat heat ≤ 0 := by
  rw [reciprocal_costs.1]
  exact (div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 3)) (by norm_num)).not_ge

/-- The complete update obeys the derived entropy budget on its actual laws.
This finite relaxation supplies no budget allocation from a separate register. -/
theorem reciprocal_entropy_budget :
    shannon_entropy independent.p - shannon_entropy correlated.p ≤ Real.log 3 / 4 := by
  have hm : reciprocalCycle.sensing.LocalDetailedBalance 1 heat := by
    rw [reciprocal_sensing]
    exact sensing_local_balance
  simpa only [reciprocal_final, reciprocal_initial, div_one] using
    reciprocalCycle.entropy_budget reciprocal_positive 1 (by norm_num) heat heat
      actuation_local_balance hm (Real.log 3 / 4) reciprocal_costs.1.le

private theorem energy_comm (x s : Bool) : energy (x, s) = energy (s, x) := by
  simp [energy, eq_comm]

private theorem memory_first_law (s x y : Bool) :
    0 = energy (y, s) - energy (x, s) + heat s x y := by
  rw [energy_comm y s, energy_comm x s]
  exact zero_work_first_law s x y

/-- The total first law uses the same interaction energy during actuation and
memory update. The zero-work model consumes its initial nonequilibrium energy. -/
theorem reciprocal_energy_budget :
    (∑ z, independent.p z * energy z) - (∑ z, correlated.p z * energy z) =
      reciprocalCycle.meanHeat heat heat := by
  have h := reciprocalCycle.mean_first_law energy heat (fun _ _ _ => 0)
    heat (fun _ _ _ => 0) zero_work_first_law memory_first_law
  rw [reciprocal_final] at h
  have hz : reciprocalCycle.meanHeat (fun _ _ _ => 0) (fun _ _ _ => 0) = 0 := by
    simp [FiniteFeedbackCycle.meanHeat, FiniteFeedbackStep.meanHeat]
  rw [hz] at h
  change 0 = (∑ z, correlated.p z * energy z) -
    (∑ z, independent.p z * energy z) + reciprocalCycle.meanHeat heat heat at h
  linarith

theorem reciprocal_not_stationary :
    reciprocalCycle.final ≠ reciprocalCycle.actuation.initial := by
  rw [reciprocal_final]
  intro h
  have hp := congrArg (fun P : ProbDist (Bool × Bool) => P.p (true, true)) h
  norm_num [reciprocalCycle, actuation, independent, correlated] at hp

/-- Biased memory and a uniform world. The same reciprocal thermal channels now
produce an asymmetric intermediate law and a nonstationary sensing substep. -/
noncomputable def biased : ProbDist (Bool × Bool) where
  p z := if z.1 then 1 / 6 else 1 / 3
  nonneg z := by split <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

noncomputable def biasedCycle : FiniteFeedbackCycle Bool Bool :=
  ⟨⟨biased, channel⟩, channel⟩

theorem biased_positive : biasedCycle.Positive := by
  refine ⟨⟨?_, actuation_positive.2⟩, sensing_positive.2⟩
  intro z
  cases z with | mk x s => cases x <;> norm_num [biasedCycle, biased]

/-- Regression against dropping the swap: the two differently ordered masses
are unequal, although the state types of both coordinates happen to be Bool. -/
theorem biased_intermediate_coordinates :
    biasedCycle.sensing.initial.p (false, true) = 1 / 12 ∧
      biasedCycle.actuation.final.p (false, true) = 1 / 6 := by
  norm_num [biasedCycle, FiniteFeedbackCycle.sensing, ProbDist.swap,
    FiniteFeedbackStep.final, biased, channel, Fintype.sum_bool]

/-- The wrong intermediate law still gives a positive step: the incompatibility
regression checks process identity, not a failure of the support condition. -/
theorem mismatched_step_positive :
    (⟨biasedCycle.actuation.final, channel⟩ : FiniteFeedbackStep Bool Bool).Positive :=
  ⟨biasedCycle.actuation.final_positive biased_positive.1, actuation_positive.2⟩

/-- A step with the unswapped intermediate law cannot be the sensing step of
any cycle with this actuation. Positivity alone would permit that wrong step. -/
theorem mismatched_intermediate_rejected :
    ¬ ∃ C : FiniteFeedbackCycle Bool Bool,
      C.actuation = biasedCycle.actuation ∧
        C.sensing = ⟨biasedCycle.actuation.final, channel⟩ := by
  rintro ⟨C, ha, hm⟩
  have heq := C.intermediate_required _ _ ha hm
  have hp := congrArg (fun P : ProbDist (Bool × Bool) => P.p (false, true)) heq
  change biasedCycle.actuation.final.p (false, true) =
    biasedCycle.sensing.initial.p (false, true) at hp
  rw [biased_intermediate_coordinates.1, biased_intermediate_coordinates.2] at hp
  norm_num at hp

/-- The memory step changes the joint law. Thus the generic result is exercised
away from the stationary sensing case of the original symmetric witness. -/
theorem biased_memory_changes_law : biasedCycle.final ≠ biasedCycle.actuation.final := by
  intro h
  have hp := congrArg (fun P : ProbDist (Bool × Bool) => P.p (true, true)) h
  norm_num [biasedCycle, FiniteFeedbackCycle.final, FiniteFeedbackCycle.sensing,
    ProbDist.swap, FiniteFeedbackStep.final, biased, channel, Fintype.sum_bool] at hp

/-- Biasing memory retains positive actuation heat under the same interaction.
This is a single relaxation cost, not a continuing source of energy. -/
theorem biased_actuation_heat_positive : 0 < biasedCycle.actuation.meanHeat heat := by
  have heq : biasedCycle.actuation.meanHeat heat = Real.log 3 / 4 := by
    norm_num [biasedCycle, FiniteFeedbackStep.meanHeat, FiniteFeedbackStep.forward,
      biased, channel, heat, energy, Fintype.sum_prod_type, Fintype.sum_bool]
    ring
  rw [heq]
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

end ThermalAgency

#print axioms FiniteFeedbackCycle.cycle_law
#print axioms FiniteFeedbackCycle.entropy_balance
#print axioms FiniteFeedbackCycle.heat_balance
#print axioms FiniteFeedbackCycle.mean_first_law
#print axioms FiniteFeedbackCycle.entropy_budget
#print axioms ThermalAgency.mismatched_intermediate_rejected

end PhysicsOfConsciousness.Examples
