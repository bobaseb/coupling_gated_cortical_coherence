/-
  Examples/PhaseSensor.lean — the learner's observations, produced by phases

  §27. Four oscillators, a sign readout, and the learner of
  `Examples/ObservationalLearning.lean`. The observation law that file declares
  is here *computed* from a phase configuration: three oscillators in phase and
  one in antiphase when the executed action matches the unknown parameter, one
  and three when it does not. The composed learner is the same object, so its
  whole trajectory — correlation, performance, heat, work — is a trajectory of a
  phase-derived channel.

  The control has the identical order parameter at every parameter and action
  and observations that do not depend on the parameter: it never improves. The
  rejection reads every phase as the same symbol and never improves either.
  Coherence separates neither case from the informative one, which is the point.
-/

import PhysicsOfConsciousness.Phase3_PhaseSensor
import PhysicsOfConsciousness.Phase4_KuramotoDynamics
import PhysicsOfConsciousness.Examples.ObservationalLearning

namespace PhysicsOfConsciousness.Examples
namespace PhaseSensorWitness

open PhysicsOfConsciousness.Examples.ObservationalLearning

/-! ## 27. A sensor built from phases, and the learner that consumes it -/

/-- The sensor reads the sign of an oscillator's in-phase component. -/
noncomputable def sensorReadout (φ : ℝ) : Bool := decide (0 < Real.cos φ)

theorem readout_zero : sensorReadout 0 = true := by
  simp [sensorReadout]

theorem readout_pi : sensorReadout Real.pi = false := by
  simp [sensorReadout, Real.cos_pi]

/-- Which oscillators are in phase: three of four when the executed action
matches the unknown parameter, one of four when it does not. This is the
declared phase-to-world relation, and it is the only place the parameter
appears. -/
def inPhase (w a : Bool) (v : Fin 4) : Bool := if a = w then v ≠ 3 else v = 0

/-- The declared phase law: in phase at `0`, out of phase at `π`. -/
noncomputable def phaseLaw (w a : Bool) (v : Fin 4) : ℝ :=
  if inPhase w a v then 0 else Real.pi

noncomputable def sensor : PhaseSensor Bool Bool (Fin 4) Bool := ⟨phaseLaw, sensorReadout⟩

theorem readout_phaseLaw (w a : Bool) (v : Fin 4) :
    sensorReadout (phaseLaw w a v) = inPhase w a v := by
  unfold phaseLaw
  cases h : inPhase w a v
  · simp [readout_pi]
  · simp [readout_zero]

theorem fiberCount_eq (w a o : Bool) :
    sensor.fiberCount w a o = (Finset.univ.filter fun v => inPhase w a v = o).card := by
  unfold PhaseSensor.fiberCount
  congr 1
  apply Finset.filter_congr
  intro v _
  rw [show sensor.readout (sensor.phase w a v) = sensorReadout (phaseLaw w a v) from rfl,
    readout_phaseLaw]

theorem fiberCount_value (w a o : Bool) :
    sensor.fiberCount w a o = if (a == w) = o then 3 else 1 := by
  rw [fiberCount_eq]
  cases w <;> cases a <;> cases o <;> decide

/-- **The declared observation law is the computed one.** The world of
`Examples/ObservationalLearning.lean` — success with probability `3/4` for the
rewarding action and `1/4` for the other — is the fraction of the population the
readout reports, and not a postulate. -/
theorem channel_eq_world (w a : Bool) : sensor.channel w a = ObservationalLearning.world w a := by
  apply ProbDist.ext
  funext o
  rw [PhaseSensor.channel_apply, fiberCount_value,
    show Fintype.card (Fin 4) = 4 from rfl]
  cases w <;> cases a <;> cases o <;> norm_num [ObservationalLearning.world]

/-- The learner of §2, with its observations produced by the sensor. -/
noncomputable def learner : FiniteObservationalLearner Bool Bool Bool Bool :=
  FiniteObservationalLearner.ofPhaseSensor ObservationalLearning.prior
    ObservationalLearning.readout sensor ObservationalLearning.update
    ObservationalLearning.reward

/-- **It is the same learner.** Every result about the declared model is
therefore a result about the phase-derived one: nothing is re-derived, and the
observation law is the only thing that changed. -/
theorem learner_eq : learner = ObservationalLearning.learner := by
  unfold learner FiniteObservationalLearner.ofPhaseSensor ObservationalLearning.learner
  congr 1
  funext w a
  exact channel_eq_world w a

/-- Task performance on the actual composed law, at every horizon. -/
theorem performance_formula (n : ℕ) :
    learner.performance n = 3 / 4 - 1 / 4 * (1 / 2 : ℝ) ^ n := by
  rw [learner_eq]; exact ObservationalLearning.performance_formula n

/-- **The informative case improves, strictly, at every update.** -/
theorem performance_improves (n : ℕ) :
    learner.performance n < learner.performance (n + 1) := by
  rw [learner_eq]; exact ObservationalLearning.performance_improves n

/-! ### Coherence, computed, and what it does not decide -/

/-- Three oscillators in phase and one in antiphase: order parameter `1/4`. -/
theorem coherence_three_zero_one_pi (theta : Fin 4 → ℝ)
    (e0 : theta 0 = 0) (e1 : theta 1 = 0) (e2 : theta 2 = 0) (e3 : theta 3 = Real.pi) :
    order_parameter_r_sq theta = 1 / 4 := by
  have hid := order_parameter_r_sq_eq_mean_cos theta
  rw [show Fintype.card (Fin 4) = 4 from rfl] at hid
  simp only [Fin.sum_univ_four, e0, e1, e2, e3] at hid
  norm_num [Real.cos_pi, Real.cos_zero, Real.cos_neg, sub_self, sub_zero, zero_sub] at hid
  linarith

/-- One in phase and three in antiphase: the same order parameter. -/
theorem coherence_one_zero_three_pi (theta : Fin 4 → ℝ)
    (e0 : theta 0 = 0) (e1 : theta 1 = Real.pi) (e2 : theta 2 = Real.pi)
    (e3 : theta 3 = Real.pi) :
    order_parameter_r_sq theta = 1 / 4 := by
  have hid := order_parameter_r_sq_eq_mean_cos theta
  rw [show Fintype.card (Fin 4) = 4 from rfl] at hid
  simp only [Fin.sum_univ_four, e0, e1, e2, e3] at hid
  norm_num [Real.cos_pi, Real.cos_zero, Real.cos_neg, sub_self, sub_zero, zero_sub] at hid
  linarith

theorem coherence_informative_match (w : Bool) :
    order_parameter_r_sq (phaseLaw w w) = 1 / 4 :=
  coherence_three_zero_one_pi _ (by simp [phaseLaw, inPhase]) (by simp [phaseLaw, inPhase])
    (by simp [phaseLaw, inPhase]) (by simp [phaseLaw, inPhase])

theorem coherence_informative_mismatch (w : Bool) :
    order_parameter_r_sq (phaseLaw w (!w)) = 1 / 4 :=
  coherence_one_zero_three_pi _
    (by cases w <;> simp [phaseLaw, inPhase]) (by cases w <;> simp [phaseLaw, inPhase])
    (by cases w <;> simp [phaseLaw, inPhase]) (by cases w <;> simp [phaseLaw, inPhase])

/-! ### The control: same coherence, no parameter dependence -/

/-- A configuration that does not depend on the parameter or the action: three
oscillators in phase, one in antiphase, always. -/
def controlInPhase (v : Fin 4) : Bool := v ≠ 3

noncomputable def controlPhase (_ _ : Bool) (v : Fin 4) : ℝ :=
  if controlInPhase v then 0 else Real.pi

noncomputable def controlSensor : PhaseSensor Bool Bool (Fin 4) Bool :=
  ⟨controlPhase, sensorReadout⟩

/-- Its order parameter is `1/4`, the same as the informative sensor's in both
of its configurations. Coherence does not distinguish the two sensors. -/
theorem coherence_control (w a : Bool) :
    order_parameter_r_sq (controlPhase w a) = 1 / 4 :=
  coherence_three_zero_one_pi _ (by simp [controlPhase, controlInPhase])
    (by simp [controlPhase, controlInPhase]) (by simp [controlPhase, controlInPhase])
    (by simp [controlPhase, controlInPhase])

/-- **The observations carry nothing about the parameter**, and this is
`channel_eq_of_phase_eq`: the configuration is the same at both parameters, so
the sensor cannot separate them. -/
theorem control_channel_param_independent (w w' a : Bool) :
    controlSensor.channel w a = controlSensor.channel w' a :=
  PhaseSensor.channel_eq_of_phase_eq _ fun _ => rfl

theorem control_readout (w a : Bool) (v : Fin 4) :
    sensorReadout (controlPhase w a v) = controlInPhase v := by
  unfold controlPhase
  cases h : controlInPhase v
  · simp [readout_pi]
  · simp [readout_zero]

theorem control_fiberCount (w a o : Bool) :
    controlSensor.fiberCount w a o
      = (Finset.univ.filter fun v => controlInPhase v = o).card := by
  unfold PhaseSensor.fiberCount
  congr 1
  apply Finset.filter_congr
  intro v _
  rw [show controlSensor.readout (controlSensor.phase w a v)
      = sensorReadout (controlPhase w a v) from rfl, control_readout]

theorem control_fiberCount_value (w a o : Bool) :
    controlSensor.fiberCount w a o = if o then 3 else 1 := by
  rw [control_fiberCount]
  cases o <;> decide

theorem control_channel_apply (w a o : Bool) :
    (controlSensor.channel w a).p o = if o then 3 / 4 else 1 / 4 := by
  rw [PhaseSensor.channel_apply, control_fiberCount_value,
    show Fintype.card (Fin 4) = 4 from rfl]
  cases o <;> norm_num

noncomputable def controlLearner : FiniteObservationalLearner Bool Bool Bool Bool :=
  FiniteObservationalLearner.ofPhaseSensor ObservationalLearning.prior
    ObservationalLearning.readout controlSensor ObservationalLearning.update
    ObservationalLearning.reward

theorem control_transition_apply (w r r' : Bool) :
    (controlLearner.transition w r).p r' = if r' = r then 7 / 8 else 1 / 8 := by
  show (∑ o, (controlSensor.channel w (ObservationalLearning.readout r)).p o *
    (ObservationalLearning.update o r).p r') = _
  rw [Fintype.sum_bool, control_channel_apply, control_channel_apply]
  cases r <;> cases r' <;> norm_num [ObservationalLearning.update]

/-- The control's joint law never moves off its prior: no observation is
informative, so the register acquires no correlation with the parameter. -/
theorem control_law_apply (n : ℕ) (z : Bool × Bool) :
    (controlLearner.law n).p z = 1 / 4 := by
  induction n generalizing z with
  | zero =>
    rcases z with ⟨w, r⟩
    cases w <;> cases r <;>
      norm_num [FiniteObservationalLearner.law_zero, controlLearner,
        FiniteObservationalLearner.ofPhaseSensor, ObservationalLearning.prior]
  | succ n ih =>
    rw [FiniteObservationalLearner.law_succ_apply]
    rcases z with ⟨w, r⟩
    simp only [Fintype.sum_bool, ih, control_transition_apply]
    cases r <;> norm_num

/-- **The control never improves.** Same population, same coherence, same
update rule, same reward: what is missing is the dependence of the configuration
on the parameter. Coherence is not what carries the comparison. -/
theorem control_performance (n : ℕ) : controlLearner.performance n = 1 / 2 := by
  unfold FiniteObservationalLearner.performance
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, control_law_apply]
  norm_num [controlLearner, FiniteObservationalLearner.ofPhaseSensor,
    ObservationalLearning.reward, ObservationalLearning.readout]

theorem informative_beats_control (n : ℕ) (hn : 0 < n) :
    controlLearner.performance n < learner.performance n := by
  rw [control_performance, performance_formula]
  have h : (1 / 2 : ℝ) ^ n ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ = 1 / 2 := by norm_num
  linarith

/-! ### The rejection: phase-independent content -/

/-- A readout that reports the same symbol whatever the phase is. -/
noncomputable def blindSensor : PhaseSensor Bool Bool (Fin 4) Bool := ⟨phaseLaw, fun _ => true⟩

theorem blind_channel (w a : Bool) : blindSensor.channel w a = ProbDist.dirac true :=
  PhaseSensor.channel_eq_dirac_of_readout_const _ (fun _ => rfl) w a

noncomputable def blindLearner : FiniteObservationalLearner Bool Bool Bool Bool :=
  FiniteObservationalLearner.ofPhaseSensor ObservationalLearning.prior
    ObservationalLearning.readout blindSensor ObservationalLearning.update
    ObservationalLearning.reward

theorem blind_transition (w r : Bool) :
    blindLearner.transition w r = ProbDist.dirac r := by
  apply ProbDist.ext
  funext r'
  show (∑ o, (blindSensor.channel w (ObservationalLearning.readout r)).p o *
    (ObservationalLearning.update o r).p r') = _
  rw [Fintype.sum_bool, blind_channel]
  cases r <;> cases r' <;> norm_num [ObservationalLearning.update, ProbDist.dirac]

/-- **Phase-independent content teaches nothing.** The population is exactly the
informative one — same phase law, same coherence — and the register still never
moves, because the readout does not resolve it. The content of the positive
result is the readout's fibres, not the phases alone. -/
theorem blind_performance (n : ℕ) : blindLearner.performance n = blindLearner.performance 0 :=
  blindLearner.performance_const_of_transition_dirac blind_transition n

#print axioms channel_eq_world
#print axioms learner_eq
#print axioms performance_formula
#print axioms performance_improves
#print axioms coherence_informative_match
#print axioms coherence_informative_mismatch
#print axioms coherence_control
#print axioms control_channel_param_independent
#print axioms control_performance
#print axioms informative_beats_control
#print axioms blind_performance

end PhaseSensorWitness
end PhysicsOfConsciousness.Examples
