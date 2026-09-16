/-
  Examples/LearnedCoupling.lean — one process: learning, coupling and its work

  §28. The register of §2/§27 *is* the switch of §9. The occupancy readout of
  `Examples/MicroscopicCoupling.lean` is attached to the learner's own
  configuration, so the kernel it installs, the energy standing in that kernel
  and the work of installing it are all computed from the one executed law the
  learner's performance and heat are read from.

  The comparison is against the uninformative controller of §27, which has the
  same hardware, the same prior, the same update rule and a sensor of the same
  coherence. It does no installation work and its installed coupling never
  leaves the forbidden region. The learner pays for its coupling, and one
  observation-driven update is what lifts it off the line.
-/

import PhysicsOfConsciousness.Examples.InstalledCoupling
import PhysicsOfConsciousness.Examples.PhaseSensor

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness.Examples.LearnedCoupling

open ThermalAgency MicroscopicCoupling InstalledCoupling
open PhysicsOfConsciousness.Examples.ObservationalLearning (law_apply heat_def update_heat)
open PhysicsOfConsciousness.Examples.PhaseSensorWitness
  (control_law_apply control_transition_apply)

/-! ## 28. The learner's register, read as installed hardware

`MicroscopicCoupling.hardware` is a `LocalActuator unitInterval Bool Bool Unit`:
its configuration is a pair of bits and its mode is installed when they agree.
`FiniteObservationalLearner.step` for the learner of §2 is a
`FiniteFeedbackStep Bool Bool` on that same pair — the unknown parameter and the
register. Attaching one to the other is therefore not a construction; it is an
identification, and everything below is computed from the learner's own
executed law. -/

/-- The arrangement the learner's hardware sits in after `n` updates. Only the
configuration law differs from §9's; the actuator, substrate, meshes, prices and
conversion factor are the same declared hardware. -/
noncomputable def learned (n : ℕ) : PricedArrangement unitInterval Bool Bool Unit :=
  { priced with law := ObservationalLearning.learner.law n }

/-- The same hardware driven by the uninformative sensor of §27. -/
noncomputable def uninformed (n : ℕ) : PricedArrangement unitInterval Bool Bool Unit :=
  { priced with law := PhaseSensorWitness.controlLearner.law n }

/-! ### Installed energy, on the executed law -/

theorem storedEnergy_apply (z : Bool × Bool) :
    hardware.storedEnergy z = if z.1 = z.2 then 1 else 0 := by
  simp [LocalActuator.storedEnergy, hardware]

theorem energySum_learned (n : ℕ) :
    (∑ z, (ObservationalLearning.learner.law n).p z * hardware.storedEnergy z)
      = 3 / 4 - 1 / 4 * (1 / 2 : ℝ) ^ n := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, storedEnergy_apply, law_apply]
  norm_num
  ring

theorem energySum_uninformed (n : ℕ) :
    (∑ z, (PhaseSensorWitness.controlLearner.law n).p z * hardware.storedEnergy z) = 1 / 2 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, control_law_apply, storedEnergy_apply]
  norm_num

theorem installedEnergy_learned (n : ℕ) :
    (learned n).installedEnergy = 3 / 4 - 1 / 4 * (1 / 2 : ℝ) ^ n :=
  energySum_learned n

theorem installedEnergy_uninformed (n : ℕ) : (uninformed n).installedEnergy = 1 / 2 :=
  energySum_uninformed n

/-- The learner's installed energy rises strictly at every update; the
uninformative controller's does not move. -/
theorem installedEnergy_increases (n : ℕ) :
    (learned n).installedEnergy < (learned (n + 1)).installedEnergy := by
  rw [installedEnergy_learned, installedEnergy_learned, pow_succ]
  have h : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  linarith

/-! ### The installed kernel, and where it comes from -/

theorem modeMass_learned (n : ℕ) : ∀ i, (learned n).toKernelArrangement.modeMass i = 2 :=
  fun _ => profileMass

theorem continuumEnergy_learned (n : ℕ) :
    (learned n).toKernelArrangement.continuumEnergy = 3 - (1 / 2 : ℝ) ^ n := by
  rw [KernelArrangement.continuumEnergy_eq_modes]
  simp only [modeMass_learned]
  show (∑ z, (ObservationalLearning.learner.law n).p z *
    ∑ i, hardware.occupancy z i * (2 : ℝ) ^ 2) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, law_apply, hardware,
    Finset.univ_unique, Finset.sum_singleton]
  norm_num
  ring

theorem continuumEnergy_uninformed (n : ℕ) :
    (uninformed n).toKernelArrangement.continuumEnergy = 2 := by
  rw [KernelArrangement.continuumEnergy_eq_modes]
  simp only [show ∀ i, (uninformed n).toKernelArrangement.modeMass i = 2 from fun _ => profileMass]
  show (∑ z, (PhaseSensorWitness.controlLearner.law n).p z *
    ∑ i, hardware.occupancy z i * (2 : ℝ) ^ 2) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, control_law_apply, hardware,
    Finset.univ_unique, Finset.sum_singleton]
  norm_num

/-- **The kernel change is read off the executed step.** The difference between
the ensemble kernels before and after one update is the path expectation of the
occupancy change over the learner's own forward paths — `expected_kernel_update`
at the learner's `FiniteFeedbackStep`, with no other law admitted. -/
theorem kernel_update_on_executed_step (n : ℕ) (x y : unitInterval) :
    hardware.expectedKernel (ObservationalLearning.learner.law (n + 1)) x y
        - hardware.expectedKernel (ObservationalLearning.learner.law n) x y =
      (ObservationalLearning.learner.step.iterate n).meanHeat (fun c s t => ∑ i,
        (hardware.occupancy (c, t) i - hardware.occupancy (c, s) i) *
          hardware.profile i x * hardware.profile i y) :=
  hardware.expected_kernel_update (ObservationalLearning.learner.step.iterate n) x y

/-! ### The work of installing it, on the same paths -/

/-- The common resource allowance: the total external work the learner's whole
trajectory requires, in the declared reservoir model at thermal scale one. -/
noncomputable def allowance : ℝ := (1 + Real.log 3) / 4

/-- **Installation work per update.** `installation_first_law` splits it into the
rise in installed energy and the update's mean heat, both on the same executed
paths. Neither half is a budget: the first is energy standing in the mode, the
second is delivered to the reservoir. -/
theorem work_learned (n : ℕ) :
    (ObservationalLearning.learner.step.iterate n).meanHeat (hardware.pathWork ObservationalLearning.heat)
      = (1 + Real.log 3) / 8 * (1 / 2 : ℝ) ^ n := by
  rw [hardware.installation_first_law,
    show (ObservationalLearning.learner.step.iterate n).final = ObservationalLearning.learner.law (n + 1) from rfl,
    show (ObservationalLearning.learner.step.iterate n).initial = ObservationalLearning.learner.law n from rfl,
    energySum_learned, energySum_learned, heat_def, ← heat_def, update_heat, pow_succ]
  ring

theorem work_learned_positive (n : ℕ) :
    0 < (ObservationalLearning.learner.step.iterate n).meanHeat (hardware.pathWork ObservationalLearning.heat) := by
  rw [work_learned]
  have h := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  positivity

theorem cumulative_work_learned (N : ℕ) :
    (∑ n ∈ Finset.range N, (ObservationalLearning.learner.step.iterate n).meanHeat (hardware.pathWork ObservationalLearning.heat))
      = allowance * (1 - (1 / 2 : ℝ) ^ N) := by
  simp only [work_learned]
  rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  unfold allowance
  field_simp
  ring

theorem cumulative_work_learned_le (N : ℕ) :
    (∑ n ∈ Finset.range N, (ObservationalLearning.learner.step.iterate n).meanHeat (hardware.pathWork ObservationalLearning.heat))
      ≤ allowance := by
  rw [cumulative_work_learned]
  have hb : 0 < allowance := by
    unfold allowance
    have := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
    positivity
  have h := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N
  nlinarith

/-- The uninformative controller's drive is reversible on every realized path,
so it delivers no heat. -/
theorem control_heat_zero (w r r' : Bool) : PhaseSensorWitness.controlLearner.heat 1 w r r' = 0 := by
  show 1 * Real.log ((PhaseSensorWitness.controlLearner.transition w r).p r' /
    (PhaseSensorWitness.controlLearner.transition w r').p r) = 0
  rw [control_transition_apply, control_transition_apply]
  cases r <;> cases r' <;> norm_num

theorem control_meanHeat (n : ℕ) :
    (PhaseSensorWitness.controlLearner.step.iterate n).meanHeat (PhaseSensorWitness.controlLearner.heat 1) = 0 := by
  rw [PhaseSensorWitness.controlLearner.meanHeat_apply]
  simp [control_heat_zero]

/-- **The uninformative controller installs nothing and pays nothing.** Its
installed energy does not move and its external work is exactly zero: same
hardware, same prior, same update rule, same order parameter, and no
installation. -/
theorem work_uninformed (n : ℕ) :
    (PhaseSensorWitness.controlLearner.step.iterate n).meanHeat (hardware.pathWork (PhaseSensorWitness.controlLearner.heat 1)) = 0 := by
  rw [hardware.installation_first_law,
    show (PhaseSensorWitness.controlLearner.step.iterate n).final = PhaseSensorWitness.controlLearner.law (n + 1) from rfl,
    show (PhaseSensorWitness.controlLearner.step.iterate n).initial = PhaseSensorWitness.controlLearner.law n from rfl,
    energySum_uninformed, energySum_uninformed, control_meanHeat]
  ring

/-- **No free installation.** The learner's per-path work cannot vanish
identically: its mean is positive. -/
theorem free_installation_rejected :
    ¬ (∀ c s t, hardware.pathWork ObservationalLearning.heat c s t = 0) := by
  intro h
  have hw := work_learned_positive 0
  simp [FiniteFeedbackStep.meanHeat, h] at hw

/-- **An unrelated final law is not a substitute.** The kernel the learner's
executed step installs after one update differs from the one the uninformative
controller's law carries, so the arrangement's law cannot be swapped for another
of the same hardware. -/
theorem substituted_law_rejected (n : ℕ) :
    (uninformed n).toKernelArrangement.continuumEnergy
      < (learned (n + 1)).toKernelArrangement.continuumEnergy := by
  rw [continuumEnergy_uninformed, continuumEnergy_learned]
  have h : (1 / 2 : ℝ) ^ (n + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
  linarith

/-! ### The necessary energy condition, on this hardware and this law -/

/-- The scalar field of unit noise carrying the coupling the learner's hardware
installs after `n` updates. The identification of a physical field's kernel with
this one is `Chain.E56` and is not made here. -/
noncomputable def learnedField (n : ℕ) : StochasticNeuralField unitInterval :=
  fieldOf (learned n).kernel

noncomputable def uninformedField (n : ℕ) : StochasticNeuralField unitInterval :=
  fieldOf (uninformed n).kernel

/-- **The uninformative controller is barred from the coherent branch at every
horizon.** Its installed energy sits exactly at `2 D / κ`, so K3 applies —
including at the boundary. This is the necessary condition, and it is
necessary only: nothing here says the learner's larger installed energy
produces coherence. -/
theorem uninformed_no_coherence (n : ℕ) :
    ¬ exhibits_phase_transition (uninformedField n) ∧
    (∀ r : ℝ, 0 ≤ r → r = selfConsistency (mean_field_coupling (uninformedField n))
        (uninformedField n).D r → r = 0) ∧
    ¬ ∃ k : ℕ, 0 < k ∧
      0 < FokkerPlanck.incoherentRate (uninformedField n).D
        (mean_field_coupling (uninformedField n)) k := by
  refine (uninformed n).no_coherence_of_installedEnergy (uninformedField n) rfl rfl ?_
  rw [installedEnergy_uninformed]
  show (4 : ℝ) * (1 / 2) ≤ critical_coupling 1
  rw [critical_coupling]; norm_num

/-- **Before any observation the learner is barred too.** At `n = 0` the prior's
agreement probability is one half and the arrangement sits on the same line. -/
theorem learned_zero_no_coherence :
    ¬ exhibits_phase_transition (learnedField 0) := by
  refine ((learned 0).no_coherence_of_installedEnergy (learnedField 0) rfl rfl ?_).1
  rw [installedEnergy_learned]
  show (4 : ℝ) * (3 / 4 - 1 / 4 * (1 / 2 : ℝ) ^ 0) ≤ critical_coupling 1
  rw [critical_coupling]; norm_num

/-- **One observation-driven update lifts the arrangement off the line**, and
that is all it does. The no-go's hypothesis fails from the first update onward;
the coherent branch is not thereby established, because K2 bounds the coupling
from above and `InstalledCoupling.converse_rejected` exhibits an arrangement
above the line with no transition. -/
theorem learned_above_line (n : ℕ) :
    critical_coupling (learnedField (n + 1)).D
      < (learned (n + 1)).couplingPerEnergy * (learned (n + 1)).installedEnergy := by
  rw [installedEnergy_learned]
  show critical_coupling (1 : ℝ) < 4 * (3 / 4 - 1 / 4 * (1 / 2 : ℝ) ^ (n + 1))
  rw [critical_coupling]
  have h : (1 / 2 : ℝ) ^ (n + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
  linarith

/-- The two sides in one statement: the same hardware, the same allowance, one
process that pays work and leaves the forbidden region and one that pays nothing
and does not. -/
theorem learning_installs_what_the_control_does_not (n : ℕ) :
    (PhaseSensorWitness.controlLearner.step.iterate n).meanHeat (hardware.pathWork (PhaseSensorWitness.controlLearner.heat 1)) = 0 ∧
    0 < (ObservationalLearning.learner.step.iterate n).meanHeat (hardware.pathWork ObservationalLearning.heat) ∧
    (uninformed n).installedEnergy < (learned (n + 1)).installedEnergy :=
  ⟨work_uninformed n, work_learned_positive n, by
    rw [installedEnergy_uninformed, installedEnergy_learned]
    have h : (1 / 2 : ℝ) ^ (n + 1) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
    linarith⟩

#print axioms installedEnergy_learned
#print axioms installedEnergy_uninformed
#print axioms continuumEnergy_learned
#print axioms kernel_update_on_executed_step
#print axioms work_learned
#print axioms cumulative_work_learned
#print axioms work_uninformed
#print axioms free_installation_rejected
#print axioms substituted_law_rejected
#print axioms uninformed_no_coherence
#print axioms learned_zero_no_coherence
#print axioms learned_above_line
#print axioms learning_installs_what_the_control_does_not

end PhysicsOfConsciousness.Examples.LearnedCoupling
