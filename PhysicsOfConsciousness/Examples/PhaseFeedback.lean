import PhysicsOfConsciousness.Phase3_FeedbackLedger

/-! A two-phase deterministic witness. The phase flips when the installed bit
is on, and the sensor copies the resulting phase into the register. The blind
control uses the same phase channel and learner but always observes false.
This witness has no thermal interpretation or strict path-support claim. -/
namespace PhysicsOfConsciousness.Examples.PhaseFeedbackWitness
open PhaseFeedback

def evolve (a p : Bool) : ProbDist Bool := ProbDist.dirac (xor p a)
def sensor (p : Bool) : ProbDist Bool := ProbDist.dirac p
def blind (_p : Bool) : ProbDist Bool := ProbDist.dirac false
def update (o _r : Bool) : ProbDist Bool := ProbDist.dirac o
noncomputable def informed := transition id evolve sensor update
noncomputable def control := transition id evolve blind update

/-- Installed occupancy changes the next phase, so this is a genuine feedback
witness rather than a prescribed phase observation. No noisy dynamics is claimed. -/
theorem actuator_changes_phase :
    (informed (false, true)).p (true, true) = 1 ∧
    (informed (false, false)).p (false, false) = 1 := by
  norm_num [informed, transition_apply, evolve, sensor, update, ProbDist.dirac_apply,
    Fintype.sum_bool]

/-- After the same first phase transition, the informative and blind sensors
write different registers. Marginal phase order alone cannot see that difference. -/
theorem sensor_changes_register :
    (informed (false, true)).p (true, true) = 1 ∧
    (control (false, true)).p (true, false) = 1 := by
  norm_num [informed, control, transition_apply, evolve, sensor, blind, update,
    ProbDist.dirac_apply, Fintype.sum_bool]

/-- The changed register feeds into the next phase transition. -/
theorem feedback_changes_next_phase :
    (informed (true, true)).p (false, false) = 1 ∧
    (control (true, false)).p (true, false) = 1 := by
  norm_num [informed, control, transition_apply, evolve, sensor, blind, update,
    ProbDist.dirac_apply, Fintype.sum_bool]

/-- A budget of two cannot fund three unit-cost steps without replenishment. -/
example : store 2 (fun _ => 1) (fun _ => 0) 3 < 0 := by norm_num [store]

/-- In the second feedback step the installed bit switches off and releases one
unit of declared mode energy. This is signed installation work, not heat. -/
def modePrice (b : Bool) : ℝ := if b then 1 else 0

theorem feedback_changes_installed_energy :
    expectedPathCost (ProbDist.dirac (true, true)) informed
      (fun z z' => modePrice z'.2 - modePrice z.2) 0 = -1 := by
  norm_num [expectedPathCost, law, ProbDist.dirac_apply, informed,
    transition_apply, evolve, sensor, update, modePrice,
    Fintype.sum_prod_type, Fintype.sum_bool]

#print axioms feedback_changes_installed_energy

#print axioms actuator_changes_phase
#print axioms sensor_changes_register
#print axioms feedback_changes_next_phase
end PhysicsOfConsciousness.Examples.PhaseFeedbackWitness
