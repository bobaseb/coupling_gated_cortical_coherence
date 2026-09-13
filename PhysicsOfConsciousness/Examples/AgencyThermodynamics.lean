import PhysicsOfConsciousness.Phase3_AgencyThermodynamics
import PhysicsOfConsciousness.Examples.Agency

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PhysicsOfConsciousness.Examples

section Regression

variable {X S : Type*} [Fintype X] [Fintype S] [Nonempty S]
  (M : FiniteFeedbackStep X S) (h : M.Positive)

example : 0 ≤ M.entropyProduction := M.entropyProduction_nonneg h

example : M.entropyProduction =
    shannon_entropy M.final.p - shannon_entropy M.initial.p + M.bathEntropy :=
  M.entropy_balance h

end Regression

namespace ThermalAgency

/-- Independent uniform controller and lamp before actuation. -/
noncomputable def independent : ProbDist (Bool × Bool) where
  p _ := 1 / 4
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The interaction's equilibrium law: agreement has probability 3/4,
while each individual bit remains uniform. -/
noncomputable def correlated : ProbDist (Bool × Bool) where
  p z := if z.1 = z.2 then 3 / 8 else 1 / 8
  nonneg z := by split <;> norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- A heat-bath update favours the other bit. The present updated bit can be
forgotten because its old value is accounted for in the reservoir log-ratio. -/
noncomputable def channel (x : Bool) (_s : Bool) : ProbDist Bool where
  p t := if t = x then 3 / 4 else 1 / 4
  nonneg t := by split <;> norm_num
  sum_one := by cases x <;> norm_num [Fintype.sum_bool]

noncomputable def actuation : FiniteFeedbackStep Bool Bool := ⟨independent, channel⟩

/-- The next elementary step swaps the roles: the world is fixed and the
internal bit updates. Symmetry makes its initial law `correlated` again. -/
noncomputable def sensing : FiniteFeedbackStep Bool Bool := ⟨correlated, channel⟩

theorem actuation_positive : actuation.Positive := by
  constructor
  · intro z; norm_num [actuation, independent]
  · intro x s t; cases x <;> cases t <;> norm_num [actuation, channel]

theorem sensing_positive : sensing.Positive := by
  constructor
  · intro z; cases z with | mk x s => cases x <;> cases s <;> norm_num [sensing, correlated]
  · intro x s t; cases x <;> cases t <;> norm_num [sensing, channel]

theorem actuation_final : actuation.final = correlated := by
  apply ProbDist.ext
  funext z
  rcases z with ⟨x, s⟩
  cases x <;> cases s <;> norm_num [FiniteFeedbackStep.final, actuation, independent,
    correlated, channel, Fintype.sum_bool]

theorem sensing_final : sensing.final = correlated := by
  apply ProbDist.ext
  funext z
  rcases z with ⟨x, s⟩
  cases x <;> cases s <;> norm_num [FiniteFeedbackStep.final, sensing,
    correlated, channel, Fintype.sum_bool]

/-- Interaction energy, in units k_B T = 1. Agreement is lower in energy by
log 3. Action and observation are aliases of existing bits, with no extra register. -/
noncomputable def energy (z : Bool × Bool) : ℝ := if z.1 = z.2 then 0 else Real.log 3

/-- Heat outward equals the interaction-energy drop. These autonomous
relaxation substeps require zero external work; their energy source is explicit. -/
noncomputable def heat (x s t : Bool) : ℝ := energy (x, s) - energy (x, t)

theorem channel_local_balance (x s t : Bool) :
    heat x s t = 1 * Real.log ((channel x s).p t / (channel x t).p s) := by
  cases x <;> cases s <;> cases t <;>
    norm_num [heat, energy, channel, Real.log_div]

theorem actuation_local_balance : actuation.LocalDetailedBalance 1 heat :=
  channel_local_balance

theorem sensing_local_balance : sensing.LocalDetailedBalance 1 heat :=
  channel_local_balance

theorem zero_work_first_law (x s t : Bool) :
    0 = energy (x, t) - energy (x, s) + heat x s t := by
  unfold heat
  ring

theorem actuation_heat : actuation.meanHeat heat = Real.log 3 / 4 := by
  norm_num [FiniteFeedbackStep.meanHeat, FiniteFeedbackStep.forward, actuation,
    independent, heat, energy, channel, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem sensing_heat : sensing.meanHeat heat = 0 := by
  norm_num [FiniteFeedbackStep.meanHeat, FiniteFeedbackStep.forward, sensing,
    correlated, heat, energy, channel, Fintype.sum_prod_type, Fintype.sum_bool]

private lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

private lemma log_eight : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num), log_four]
  ring

theorem entropy_independent : shannon_entropy independent.p = 2 * Real.log 2 := by
  norm_num [shannon_entropy, independent, Fintype.sum_prod_type, Fintype.sum_bool,
    Real.log_div, log_four]
  ring

theorem entropy_correlated :
    shannon_entropy correlated.p = 3 * Real.log 2 - 3 / 4 * Real.log 3 := by
  norm_num [shannon_entropy, correlated, Fintype.sum_prod_type, Fintype.sum_bool,
    Real.log_div, log_eight]
  ring

theorem actuation_entropy_production :
    actuation.entropyProduction = Real.log 2 - Real.log 3 / 2 := by
  rw [actuation.entropy_balance actuation_positive, actuation_final]
  have hb := actuation.heat_eq_thermal_bathEntropy 1 heat actuation_local_balance
  rw [actuation_heat, one_mul] at hb
  rw [← hb, entropy_correlated]
  change _ - shannon_entropy independent.p + _ = _
  rw [entropy_independent]
  ring

theorem sensing_entropy_production : sensing.entropyProduction = 0 := by
  rw [sensing.entropy_balance sensing_positive, sensing_final]
  have hb := sensing.heat_eq_thermal_bathEntropy 1 heat sensing_local_balance
  rw [sensing_heat, one_mul] at hb
  change shannon_entropy correlated.p - shannon_entropy correlated.p + _ = _
  rw [sub_self, zero_add, ← hb]

/-- The acting substep has strictly positive heat and entropy production.
This uses the actual transition probabilities, not an assigned cost field. -/
theorem actuation_cost_positive :
    0 < actuation.meanHeat heat ∧ 0 < actuation.entropyProduction := by
  rw [actuation_heat, actuation_entropy_production]
  have h3 := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  have h34 := Real.log_lt_log (show (0 : ℝ) < 3 by norm_num) (show (3 : ℝ) < 4 by norm_num)
  rw [log_four] at h34
  constructor <;> linarith

/-- The complete alternating update's energy and heat budget. Initial
interaction energy is consumed; stationarity is not a continuing power source. -/
theorem cycle_heat_and_work :
    actuation.meanHeat heat + sensing.meanHeat heat = Real.log 3 / 4 ∧
      actuation.meanHeat (fun _ _ _ => 0) + sensing.meanHeat (fun _ _ _ => 0) = 0 := by
  constructor
  · rw [actuation_heat, sensing_heat, add_zero]
  · simp [FiniteFeedbackStep.meanHeat]

theorem independent_measure : independent.toMeasure = indepJoint := by
  apply Measure.ext_of_singleton
  intro z
  rw [ProbDist.toMeasure_singleton, indepJoint_singleton]
  norm_num [independent, ENNReal.ofReal_div_of_pos]

theorem correlated_fst : correlated.toMeasure.fst = unifBool := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.fst_apply (measurableSet_singleton b), ProbDist.toMeasure_apply,
    unifBool_singleton]
  cases b <;> norm_num [correlated, Fintype.sum_prod_type, Fintype.sum_bool,
    ENNReal.ofReal_div_of_pos]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add]
    norm_num

theorem correlated_snd : correlated.toMeasure.snd = unifBool := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.snd_apply (measurableSet_singleton b), ProbDist.toMeasure_apply,
    unifBool_singleton]
  cases b <;> norm_num [correlated, Fintype.sum_prod_type, Fintype.sum_bool,
    ENNReal.ofReal_div_of_pos]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add]
    norm_num

/-- The physical example's information is computed with the same KL-based
definition as the passive theorem, via the proved finite-measure bridge. -/
theorem correlated_information :
    (mutualInfo correlated.toMeasure).toReal = 3 / 4 * Real.log 3 - Real.log 2 := by
  unfold mutualInfo
  rw [correlated_fst, correlated_snd]
  change (InformationTheory.klDiv correlated.toMeasure indepJoint).toReal = _
  rw [← independent_measure, ← correlated.KL_eq_klDiv independent (fun _ => by
    norm_num [independent])]
  norm_num [KL, correlated, independent, Fintype.sum_prod_type, Fintype.sum_bool,
    Real.log_div]
  ring

theorem correlated_information_positive : 0 < (mutualInfo correlated.toMeasure).toReal := by
  apply ENNReal.toReal_pos
  · intro h
    have heq := (mutualInfo_eq_zero_iff (μ := correlated.toMeasure)).mp h
    rw [correlated_fst, correlated_snd] at heq
    have ha := congrArg (fun μ : Measure (Bool × Bool) => μ {(true, true)}) heq
    change correlated.toMeasure {(true, true)} = indepJoint {(true, true)} at ha
    rw [ProbDist.toMeasure_singleton, indepJoint_singleton] at ha
    norm_num [correlated, ENNReal.ofReal_div_of_pos] at ha
    have hr := congrArg ENNReal.toReal ha
    norm_num at hr
  · exact mutualInfo_finite _

/-- Actuation creates future correlations while retaining positive heat and
entropy production. The passive information inequality fails on these paths. -/
theorem actuation_negative_waste : Feedback.signedWaste actuation.history < 0 := by
  simp only [Feedback.signedWaste, FiniteFeedbackStep.present_history,
    FiniteFeedbackStep.future_history, actuation_final]
  change (mutualInfo independent.toMeasure).toReal - _ < 0
  rw [independent_measure, mutualInfo_indepJoint, ENNReal.toReal_zero, zero_sub]
  exact neg_neg_of_pos correlated_information_positive

/-- Since both world marginals are uniform, the joint entropy change here is
minus the mutual-information gain. This checks the information contribution to
the physical entropy balance on the same process. -/
theorem actuation_information_heat_balance :
    actuation.entropyProduction = actuation.meanHeat heat -
      (mutualInfo correlated.toMeasure).toReal := by
  rw [actuation_entropy_production, actuation_heat, correlated_information]
  ring

/-- The observation supplies the fixed world bit to a thermal memory update.
Both controller and world can change over a full cycle. -/
noncomputable def memoryUpdate : Kernel ((Bool × Bool) × Bool) Bool :=
  ProbDist.kernel (fun z => channel z.2 z.1.1)

instance : IsMarkovKernel memoryUpdate := by
  unfold memoryUpdate
  infer_instance

noncomputable def agent : Agency Bool Bool Bool Bool := actuation.toAgency memoryUpdate

theorem agent_acts : agent.controlled (true, false) {true} = 3 / 4 ∧
    agent.controlled (false, false) {true} = 1 / 4 := by
  norm_num [agent, FiniteFeedbackStep.controlled_toAgency, actuation, channel,
    ENNReal.ofReal_div_of_pos]

theorem memory_really_updates : memoryUpdate ((false, false), true) {true} = 3 / 4 := by
  norm_num [memoryUpdate, channel, ENNReal.ofReal_div_of_pos]

theorem agent_history : agent.history independent.toMeasure = actuation.history :=
  actuation.history_toAgency memoryUpdate

/-- A full cycle includes both nontrivial thermal updates. This explicit
transition formula ties the model's channel composition to the two heat budgets. -/
theorem agent_cycle_transition (x s y t : Bool) :
    agent.cycle (x, s) {(y, t)} =
      ENNReal.ofReal ((channel x s).p t) * ENNReal.ofReal ((channel t x).p y) := by
  simp only [Agency.cycle, Agency.sense, Agency.act, Agency.select, agent,
    FiniteFeedbackStep.toAgency, memoryUpdate, Kernel.id_comap]
  simp only [ProbDist.comp_singleton, Fintype.sum_prod_type, Fintype.sum_bool,
    ProbDist.prod_singleton, Kernel.comap_apply, Kernel.id_apply,
    Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
    ProbDist.kernel_singleton]
  cases x <;> cases s <;> cases y <;> cases t <;>
    norm_num [actuation, channel, ENNReal.ofReal_div_of_pos, mul_comm]

theorem agent_cycle_law : agent.cycle ∘ₘ independent.toMeasure = correlated.toMeasure := by
  apply Measure.ext_of_singleton
  intro ⟨y, t⟩
  rw [ProbDist.comp_measure_singleton]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, agent_cycle_transition,
    ProbDist.toMeasure_singleton]
  cases y <;> cases t <;> norm_num [independent, correlated, channel, ENNReal.ofReal_div_of_pos]
  all_goals
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add]
    norm_num

/-- The measured heat is precisely the loss of mean interaction energy.
This applies the proved first-law expectation identity to the actual actuator. -/
theorem cycle_energy_budget :
    (∑ z, independent.p z * energy z) - (∑ z, correlated.p z * energy z) =
      actuation.meanHeat heat + sensing.meanHeat heat := by
  have h := actuation.mean_first_law energy heat (fun _ _ _ => 0) zero_work_first_law
  have hz : actuation.meanHeat (fun _ _ _ => 0) = 0 := by
    simp [FiniteFeedbackStep.meanHeat]
  rw [hz, actuation_final] at h
  change 0 = (∑ z, correlated.p z * energy z) -
    (∑ z, independent.p z * energy z) + actuation.meanHeat heat at h
  rw [sensing_heat, add_zero]
  linarith

end ThermalAgency

#print axioms FiniteFeedbackStep.entropy_balance
#print axioms FiniteFeedbackStep.heat_bound
#print axioms ThermalAgency.actuation_cost_positive

end PhysicsOfConsciousness.Examples
