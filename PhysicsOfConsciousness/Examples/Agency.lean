import PhysicsOfConsciousness.Phase3_Agency
import PhysicsOfConsciousness.Examples.Phase3

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PhysicsOfConsciousness.Examples

section Regression

variable {X S S' : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace S'] (μ : Measure (X × (S × S'))) [IsProbabilityMeasure μ]

example (h : mutualInfo μ ≠ ∞) : 0 ≤ Feedback.retained μ :=
  Feedback.retained_nonneg μ h

example (h : mutualInfo μ ≠ ∞) : 0 ≤ Feedback.feedback μ :=
  Feedback.feedback_nonneg μ h

example : Feedback.signedWaste μ = Feedback.retained μ - Feedback.feedback μ :=
  Feedback.information_balance μ

example (ν : Measure (X × S)) [IsProbabilityMeasure ν]
    (κ : Kernel S S') [IsMarkovKernel κ] :
    Feedback.feedback (Feedback.passiveLaw ν κ) = 0 :=
  Feedback.passive_feedback_zero ν κ

end Regression

/-- A controller writes its bit to the world, senses the result, and records
that observation. This witness specifies behaviour, not thermodynamic cost. -/
noncomputable def writingAgent : Agency Bool Bool Bool Bool where
  policy := Kernel.id
  world := Kernel.deterministic Prod.snd measurable_snd
  observe := Kernel.id
  update := Kernel.deterministic Prod.snd measurable_snd
  policy_markov := inferInstance
  world_markov := inferInstance
  observe_markov := inferInstance
  update_markov := inferInstance

theorem writingAgent_controlled : writingAgent.controlled =
    Kernel.deterministic (Prod.fst : Bool × Bool → Bool) measurable_fst := by
  simp only [Agency.controlled, writingAgent, Kernel.id_comap,
    Kernel.deterministic_prod_deterministic, Kernel.deterministic_comp_deterministic]
  rfl

/-- The action channel has a real effect: opposite internal states produce
opposite world states even with the same present environment. -/
theorem writingAgent_changes_world :
    writingAgent.controlled (true, false) {true} = 1 ∧
      writingAgent.controlled (false, false) {true} = 0 := by
  simp [writingAgent_controlled, Kernel.deterministic_apply]

theorem writingAgent_future :
    Feedback.futureLaw (writingAgent.history indepJoint) = corrJoint := by
  rw [Agency.future_history, writingAgent_controlled, Kernel.deterministic_prod_deterministic]
  exact writeKernel_comp

/-- A policy-generated history realizes the existing write counterexample.
The signed information difference is strictly negative, rather than clipped. -/
theorem writingAgent_negative_waste :
    Feedback.signedWaste (writingAgent.history indepJoint) < 0 := by
  simp only [Feedback.signedWaste, Agency.present_history, writingAgent_future,
    mutualInfo_indepJoint, ENNReal.toReal_zero, zero_sub]
  exact neg_neg_of_pos memory_pos

/-- The sensing and memory-update substep reads the new world into memory,
even when it differs from the previous internal state. -/
theorem writingAgent_sense : writingAgent.sense =
    Kernel.deterministic (fun z : (Bool × Bool) × Bool => (z.2, z.2)) (by fun_prop) := by
  simp only [Agency.sense, writingAgent, Kernel.id_comap]
  rw [← Kernel.comp_deterministic_eq_comap, Kernel.deterministic_comp_deterministic]
  simp only [Kernel.id, Kernel.deterministic_prod_deterministic,
    Kernel.deterministic_comp_deterministic]
  rfl

theorem writingAgent_updates_memory :
    writingAgent.sense ((false, false), true) {(true, true)} = 1 := by
  simp [writingAgent_sense, Kernel.deterministic_apply]

/-- The full cycle is built from policy, actuation, sensing and update. Its
agreement with the write kernel checks the timing of the composed channels. -/
theorem writingAgent_cycle : writingAgent.cycle = writeKernel := by
  unfold Agency.cycle
  rw [writingAgent_sense]
  simp only [Agency.act, Agency.select, writingAgent, Kernel.id_comap]
  rw [← Kernel.comp_deterministic_eq_comap, Kernel.deterministic_comp_deterministic]
  simp only [Kernel.id, Kernel.deterministic_prod_deterministic,
    Kernel.deterministic_comp_deterministic]
  rfl

theorem writingAgent_cycle_law : writingAgent.cycle ∘ₘ indepJoint = corrJoint := by
  rw [writingAgent_cycle, writeKernel_comp]

#print axioms Feedback.information_balance
#print axioms Feedback.retained_nonneg
#print axioms Feedback.passive_feedback_zero
#print axioms writingAgent_negative_waste
#print axioms writingAgent_cycle

end PhysicsOfConsciousness.Examples
