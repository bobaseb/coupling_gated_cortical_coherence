import PhysicsOfConsciousness.Examples.FundedCoupling

/-!
# The evolving kernel's no-go needs a supremum, not a mean

§30. K3 is a statement about one arrangement. A run is a sequence of them, and
`PricedArrangement.no_coherence_of_run` lifts the no-go stagewise: subcritical at
every stage, coherent at none. The hypothesis is a supremum over the run, and
this file is about why it cannot be anything weaker.

`approach` is the positive side — an arrangement that genuinely evolves, whose
installed energy rises at every stage towards the threshold from below and never
reaches it, so the run-level no-go applies at every horizon. `fence` is the
negative side: a stage sequence whose *mean* installed energy is under three
quarters of what the threshold needs, and one of whose stages exhibits the
transition. The no-go with a mean substituted for the supremum is therefore
false, not merely unproved.

The third result is what a decay of an installed coupling would take.
`LocalActuator.exists_lowering_of_installedEnergy_lt` says an installed energy
that falls identifies an executed transition that lowers an occupancy. The
funded run of §29 has no such transition, so its installation survives the
exhaustion of its source — and the maintenance channel a decay would need is
named here and supplied nowhere.

Everything here is about the stationary problem each stage poses. None of it
says anything about the phase trajectory: kernel convergence implies neither
trajectory convergence nor preservation of the threshold along a run.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness.Examples.EvolvingCoupling

open MicroscopicCoupling InstalledCoupling

/-! ### 30.1 An arrangement that evolves, subcritically, at every stage -/

/-- Agreement probability `1/2 - (1/4)(1/2)ⁿ`: rising, and short of the `1/2`
the threshold needs at every finite stage and in the limit. -/
noncomputable def agreement (n : ℕ) : ℝ := 1 / 2 - 1 / 4 * (1 / 2 : ℝ) ^ n

theorem agreement_bounds (n : ℕ) : 1 / 4 ≤ agreement n ∧ agreement n ≤ 1 / 2 := by
  have h0 : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  have h1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor <;> unfold agreement <;> linarith

/-- The configuration law at stage `n`: the same hardware, a law whose agreement
mass evolves. No preparation mechanism is claimed for any of them. -/
noncomputable def approachLaw (n : ℕ) : ProbDist (Bool × Bool) where
  p z := if z.1 = z.2 then agreement n / 2 else (1 - agreement n) / 2
  nonneg z := by
    have := agreement_bounds n
    split <;> linarith [this.1, this.2]
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
    ring

/-- The evolving arrangement. Only the law moves; actuator, prices, profiles,
substrate and `κ` are the declared hardware of §9. -/
noncomputable def approach (n : ℕ) : PricedArrangement unitInterval Bool Bool Unit :=
  { priced with law := approachLaw n }

noncomputable def approachField (n : ℕ) : StochasticNeuralField unitInterval :=
  fieldOf (approach n).kernel

theorem installedEnergy_approach (n : ℕ) : (approach n).installedEnergy = agreement n := by
  show (∑ z, (approachLaw n).p z * hardware.storedEnergy z) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, LearnedCoupling.storedEnergy_apply,
    approachLaw]
  norm_num

/-- The run evolves: its installed energy rises strictly at every stage. -/
theorem approach_evolves (n : ℕ) :
    (approach n).installedEnergy < (approach (n + 1)).installedEnergy := by
  rw [installedEnergy_approach, installedEnergy_approach]
  have h : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
  unfold agreement
  rw [pow_succ]
  linarith

/--
**The run-level no-go, on a run that actually moves.** Every stage satisfies
`κ Uₙ ≤ 2 D`, so no stage exhibits the transition, the incoherent solution is the
only nonnegative stationary one at each stage's own coupling, and no Fourier mode
of the uniform density grows at any of them.

The bound tightens to equality only in the limit; the run never reaches the
threshold and the conclusion never lapses. -/
theorem approach_no_coherence (n : ℕ) :
    ¬ exhibits_phase_transition (approachField n) ∧
    (∀ r : ℝ, 0 ≤ r → r = selfConsistency (mean_field_coupling (approachField n))
        (approachField n).D r → r = 0) ∧
    ¬ ∃ k : ℕ, 0 < k ∧
      0 < FokkerPlanck.incoherentRate (approachField n).D
        (mean_field_coupling (approachField n)) k := by
  refine PricedArrangement.no_coherence_of_run approach approachField
    (fun _ => rfl) (fun _ => rfl) (fun m => ?_) n
  rw [installedEnergy_approach]
  show (4 : ℝ) * agreement m ≤ critical_coupling 1
  have h : (0 : ℝ) < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) m
  rw [critical_coupling]
  unfold agreement
  linarith

/-! ### 30.2 The fence: a subcritical mean with a supercritical stage -/

/-- The coupling the learner's arrangement installs, as a mean-field strength.
K1 on the learned arrangement; nothing identifies it with a physical field. -/
theorem meanField_learned (n : ℕ) :
    mean_field_coupling (LearnedCoupling.learnedField n) = 3 - (1 / 2 : ℝ) ^ n := by
  rw [← (LearnedCoupling.learned n).toKernelArrangement.continuumEnergy_eq_mean_field_coupling
    (LearnedCoupling.learnedField n) rfl rfl]
  exact LearnedCoupling.continuumEnergy_learned n

/-- One supercritical stage followed by subcritical ones, on one hardware. -/
noncomputable def fence : ℕ → PricedArrangement unitInterval Bool Bool Unit
  | 0 => LearnedCoupling.learned 3
  | _ + 1 => below

noncomputable def fenceField (n : ℕ) : StochasticNeuralField unitInterval :=
  fieldOf (fence n).kernel

theorem fence_zero_installedEnergy : (fence 0).installedEnergy = 23 / 32 := by
  show (LearnedCoupling.learned 3).installedEnergy = _
  rw [LearnedCoupling.installedEnergy_learned]
  norm_num

theorem fence_succ_installedEnergy (n : ℕ) : (fence (n + 1)).installedEnergy = 1 / 4 :=
  below_installedEnergy

/-- The mean installed energy over the first four stages is `47/128`, so the
mean-substituted hypothesis holds with room to spare: `κ` times it is `47/32`,
against a threshold of `2`. -/
theorem fence_mean_subcritical :
    (fence 0).couplingPerEnergy * ((∑ n ∈ Finset.range 4, (fence n).installedEnergy) / 4)
      < critical_coupling (fenceField 0).D := by
  rw [show (∑ n ∈ Finset.range 4, (fence n).installedEnergy) = 47 / 32 by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, fence_zero_installedEnergy, fence_succ_installedEnergy,
      fence_succ_installedEnergy, fence_succ_installedEnergy]
    norm_num]
  show (4 : ℝ) * (47 / 32 / 4) < critical_coupling 1
  rw [critical_coupling]; norm_num

/-- And the first stage exhibits the transition. -/
theorem fence_zero_exhibits : exhibits_phase_transition (fenceField 0) := by
  show mean_field_coupling (LearnedCoupling.learnedField 3) > critical_coupling 1
  rw [meanField_learned, critical_coupling]
  norm_num

/--
**N11 — the mean-substituted no-go is false.** Four stages of one arrangement,
one hardware, one `κ`. The mean installed energy is subcritical; a stage exhibits
the transition. Anything that replaced the supremum in
`PricedArrangement.no_coherence_of_run` by a mean over the run would prove a
falsehood on this sequence.

The reason is not arithmetic delicacy. `exhibits_phase_transition` is a property
of the stage's own coupling, and averaging a sequence of couplings destroys the
supercritical stage that a run needs only one of. -/
theorem mean_substitution_rejected :
    (fence 0).couplingPerEnergy * ((∑ n ∈ Finset.range 4, (fence n).installedEnergy) / 4)
      < critical_coupling (fenceField 0).D ∧
    exhibits_phase_transition (fenceField 0) :=
  ⟨fence_mean_subcritical, fence_zero_exhibits⟩

/-! ### 30.3 Exhaustion does not uninstall -/

open FundedCoupling (level climb run actuator fuelled)

theorem level_le_climb (s : Fin 3) : level s ≤ level (climb s) := by
  fin_cases s <;> norm_num [level, climb]

/-- **The funded run never gives an installation back.** No transition it
executes lowers an occupancy, so `LocalActuator.storedEnergy_mono_of_stage`
applies at every stage — including the stages after its source is spent, at
which it draws nothing and installs nothing further. -/
theorem funded_installation_never_decays (n : ℕ) :
    (fuelled n).installedEnergy ≤ (fuelled (n + 1)).installedEnergy := by
  refine actuator.storedEnergy_mono_of_stage run n fun x s t _ ht => ?_
  have hts : t = climb s := by
    by_contra hne
    simp [run, FundedCoupling.run, ProbDist.dirac_apply, hne] at ht
  rw [FundedCoupling.storedEnergy_apply, FundedCoupling.storedEnergy_apply, hts]
  exact level_le_climb s

/--
**What a decay would take, and where it is not.** If the funded run's installed
energy ever fell, some transition it executes would have to lower the stored
energy: a stage that uninstalls. `funded_installation_never_decays` shows this
run has no such transition, and nothing in this development supplies one
anywhere. That is the deliverable: a maintenance channel is a physical
commitment about how an installed coupling is held in place, and declaring one
is not a formalization step.

Together with §29's spent-source run, this is the sense in which exhaustion does
not uninstall. The source reaching zero is a statement about a store coordinate;
the installed energy is a functional of the configuration law, and
`KernelArrangement.installedEnergy_congr` is what says the two do not meet. -/
theorem decay_would_need_a_lowering_stage (n : ℕ)
    (h : (fuelled (n + 1)).installedEnergy < (fuelled n).installedEnergy) :
    ∃ x s t, 0 < (run.law n).p (x, s) ∧ 0 < (run.stage n x s).p t ∧
      actuator.storedEnergy (x, t) < actuator.storedEnergy (x, s) :=
  actuator.exists_lowering_of_installedEnergy_lt run n h

/-- The two halves of §29–§30 in one statement: a spent source keeps what it
bought, and the run that spent it stays below the threshold at every horizon. -/
theorem spent_but_still_installed (k : ℕ) :
    (fuelled (k + 2)).installedEnergy = (fuelled 2).installedEnergy ∧
    ¬ exhibits_phase_transition (FundedCoupling.fuelledField (k + 2)) :=
  ⟨(FundedCoupling.spent_source_keeps_installation k).2,
    (FundedCoupling.fuelled_no_coherence (k + 2)).1⟩

#print axioms installedEnergy_approach
#print axioms approach_evolves
#print axioms approach_no_coherence
#print axioms meanField_learned
#print axioms fence_mean_subcritical
#print axioms fence_zero_exhibits
#print axioms mean_substitution_rejected
#print axioms funded_installation_never_decays
#print axioms decay_would_need_a_lowering_stage
#print axioms spent_but_still_installed

end PhysicsOfConsciousness.Examples.EvolvingCoupling
