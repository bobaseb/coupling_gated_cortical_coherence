import PhysicsOfConsciousness.Examples.LearnedCoupling

/-!
# A finite source that cannot fund coherence

§29. K3 forbids the coherent branch to an arrangement whose installed energy is
too small. It says nothing about where that energy came from. This file closes
that gap on a witness: a run whose store draws exactly the installation work of
every transition it executes, replenished by a declared source of size `3/8`,
and whose installed energy is therefore capped at `3/8` at *every* horizon —
below the `1/2` that `κ = 4` and `2 D = 2` require. The no-go is then read off
the fuel rather than off the energy standing in the modes.

The three levels of the installation are hardware data, as the thermal switch's
two are. What is new is the identification of `PathwiseStore.draw` with
`LocalActuator.pathWork`: the same number is the work the transition takes out
of the store and the work its installation costs.

Two controls sit on either side of that identification. A store that draws
nothing while its protocol installs satisfies every other hypothesis and breaks
the conclusion, so `hdraw` carries the bound rather than decorating it. And the
learner of §28 cannot be funded by any finite source at all: its channel has
full support, so a nonnegative net draw is forced to zero, and no source
coordinate on its register satisfies the source ledger either. The fuel bound is
therefore silent about the learner, which is the right outcome rather than a
gap — `learned_above_line` puts it above the threshold from its first update
onwards, so a bound whose hypotheses it satisfied would contradict a theorem.

Nothing here supplies a power source, prepares an initial law, or claims that a
sufficient source produces coherence.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness.Examples.FundedCoupling

open MicroscopicCoupling InstalledCoupling

/-! ### 29.1 Hardware with three installation levels -/

/-- Installed occupancy at each of the three configurations. The increments
`1/4` and `1/8` are the two draws the run makes; `3/8` is where it stops. -/
noncomputable def level : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1 / 4
  | 2 => 3 / 8

theorem level_nonneg (k : Fin 3) : 0 ≤ level k := by fin_cases k <;> norm_num [level]

theorem level_le (k : Fin 3) : level k ≤ 3 / 8 := by fin_cases k <;> norm_num [level]

/-- The same response profile and unit price as the thermal switch, so the same
conversion factor `κ = 4` is read off the same hardware. Only the occupancy
readout is new: it takes three values rather than two. -/
noncomputable def actuator : LocalActuator unitInterval Unit (Fin 3) Unit where
  occupancy z _ := level z.2
  profile _ x := 4 / 3 * (1 + (x : ℝ))
  price _ := 1

theorem storedEnergy_apply (z : Unit × Fin 3) : actuator.storedEnergy z = level z.2 := by
  simp [LocalActuator.storedEnergy, actuator]

/-! ### 29.2 The run, and the law it actually reaches -/

/-- One installation step per stage, saturating at the top level. -/
def climb : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 2

/-- The executed protocol: a prepared empty configuration and one climb per
stage. The initial law is supplied, as every initial law in this development
is. -/
noncomputable def run : FiniteProtocol Unit (Fin 3) :=
  ⟨ProbDist.dirac ((), 0), fun _ _ s => ProbDist.dirac (climb s)⟩

/-- The configuration the run has reached after `n` stages. -/
def stateAt : ℕ → Fin 3
  | 0 => 0
  | n + 1 => climb (stateAt n)

theorem stateAt_ge_two (k : ℕ) : stateAt (k + 2) = 2 := by
  induction k with
  | zero => rfl
  | succ k ih => show climb (stateAt (k + 2)) = 2; rw [ih]; rfl

/-- The run is deterministic, so its law at every horizon is a point mass. -/
theorem law_eq (n : ℕ) : run.law n = ProbDist.dirac ((), stateAt n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine ProbDist.ext ?_
    funext z
    rw [run.law_succ_apply, ih]
    obtain ⟨u, k⟩ := z
    simp only [ProbDist.dirac_apply, run, Prod.mk.injEq]
    rw [Finset.sum_eq_single (stateAt n)]
    · simp [stateAt]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem expect_law (n : ℕ) (f : Unit × Fin 3 → ℝ) :
    ∑ z, (run.law n).p z * f z = f ((), stateAt n) := by
  rw [law_eq]
  simp

/-! ### 29.3 The store, and the source behind it -/

/-- The declared source: what is left of an initial `3/8` once the run has
climbed to its current level. -/
noncomputable def reserve : Fin 3 → ℝ := fun s => 3 / 8 - level s

theorem reserve_nonneg (s : Fin 3) : 0 ≤ reserve s := by
  have := level_le s; unfold reserve; linarith

/-- **The store whose draw is the installation work.** `draw` is not a cost
assigned to an operation: it is `LocalActuator.pathWork` at this actuator, so
the work the store loses on a transition is by construction the work that
transition's installation requires. The drive is reversible, so its heat
observable is zero and the whole draw is installed energy.

The store is a pass-through: it supplies what it draws, and what falls is the
source. Nothing forces that shape here — this protocol's support is restricted,
so a falling balance and no source would carry the same bound — but it is the
shape the learner's channel does force, and §29.7 is where that is proved. -/
noncomputable def store : PathwiseStore Unit (Fin 3) where
  protocol := run
  balance := fun _ => 0
  draw := fun _ => actuator.pathWork (fun _ _ _ => 0)
  supply := fun _ _ s t => level t - level s

theorem store_ledgered : store.Ledgered := by
  intro n x s t _ _
  show (0 : ℝ) = 0 - (actuator.storedEnergy (x, t) - actuator.storedEnergy (x, s) + 0) +
    (level t - level s)
  rw [storedEnergy_apply, storedEnergy_apply]
  ring

theorem store_solvent (N : ℕ) : store.Solvent N := fun _ _ _ _ => le_rfl

theorem source_ledgered : store.SourceLedgered reserve := by
  intro n x s t _ _
  show (3 : ℝ) / 8 - level t = 3 / 8 - level s - (level t - level s)
  ring

theorem store_meanBalance_zero : store.meanBalance 0 = 0 := by
  show (∑ z, (run.law 0).p z * (0 : ℝ)) = 0
  simp

theorem initial_reserve : (∑ z, (run.law 0).p z * reserve z.2) = 3 / 8 := by
  rw [expect_law]
  norm_num [reserve, stateAt, level]

theorem initial_installedEnergy :
    (∑ z, (run.law 0).p z * actuator.storedEnergy z) = 0 := by
  rw [expect_law, storedEnergy_apply]
  norm_num [stateAt, level]

/-! ### 29.4 The arrangement the run installs -/

noncomputable def fuelled (N : ℕ) : PricedArrangement unitInterval Unit (Fin 3) Unit where
  actuator := actuator
  profile_continuous _ := continuous_const.mul (continuous_const.add continuous_subtype_val)
  law := run.law N
  volume := volume
  grid := MicroscopicCoupling.mesh
  refines := MicroscopicCoupling.mesh_refines
  couplingPerEnergy := 4
  couplingPerEnergy_pos := by norm_num
  occupancy_nonneg z _ := level_nonneg z.2
  mode_priced i := by
    show (∫ x : unitInterval, 4 / 3 * (1 + (x : ℝ))) ^ 2 ≤ 4 * (1 : ℝ)
    rw [profileMass]; norm_num

noncomputable def fuelledField (N : ℕ) : StochasticNeuralField unitInterval :=
  fieldOf (fuelled N).kernel

theorem installedEnergy_fuelled (N : ℕ) : (fuelled N).installedEnergy = level (stateAt N) := by
  show (∑ z, (run.law N).p z * actuator.storedEnergy z) = _
  rw [expect_law, storedEnergy_apply]

/-! ### 29.5 The fuel no-go -/

/--
**N10 — a source of `3/8` cannot fund the threshold, at any horizon.**

Every hypothesis of `no_coherence_of_funded_source` is discharged on the
executed run, and `hcap` reads `4 * (0 + 0 + 3/8) = 3/2 ≤ 2`. No installed
energy at stage `N` is computed anywhere in the argument: the cap comes from the
initial law, the store's initial reading and the source, and holds for every
`N` at once.

This is the fuel form of K3 and it is a no-go in the same single direction. A
larger source supplies no coherence, `κ` remains declared hardware data, and the
identification of a physical field's kernel with this arrangement's is `E56`,
untouched here. -/
theorem fuelled_no_coherence (N : ℕ) :
    ¬ exhibits_phase_transition (fuelledField N) ∧
    (∀ r : ℝ, 0 ≤ r → r = selfConsistency (mean_field_coupling (fuelledField N))
        (fuelledField N).D r → r = 0) ∧
    ¬ ∃ k : ℕ, 0 < k ∧
      0 < FokkerPlanck.incoherentRate (fuelledField N).D
        (mean_field_coupling (fuelledField N)) k := by
  refine (fuelled N).no_coherence_of_funded_source store (fuelledField N)
    (fun _ _ _ _ => (0 : ℝ)) reserve N rfl rfl rfl (fun _ => rfl) (fun k _ => ?_)
    store_ledgered source_ledgered (store_solvent N)
    (fun _ _ _ _ => reserve_nonneg _) ?_
  · simp [FiniteFeedbackStep.meanHeat]
  · show (fuelled N).couplingPerEnergy *
      ((∑ z, (run.law 0).p z * actuator.storedEnergy z) + store.meanBalance 0 +
        ∑ z, (run.law 0).p z * reserve z.2) ≤ critical_coupling (fuelledField N).D
    rw [initial_installedEnergy, store_meanBalance_zero, initial_reserve]
    show (4 : ℝ) * (0 + 0 + 3 / 8) ≤ critical_coupling 1
    rw [critical_coupling]; norm_num

/-- The cap is attained: by the second stage the source is spent and the
installed energy is exactly the `3/8` the bound allows. The run therefore does
not clear the threshold by a margin the bound invented. -/
theorem cap_attained : (fuelled 2).installedEnergy = 3 / 8 := by
  rw [installedEnergy_fuelled]
  rfl

/-- **Exhaustion does not uninstall.** From the second stage on the source holds
nothing, and the installed energy does not move: it is a functional of the
actuator and the configuration law, and `KernelArrangement.installedEnergy_congr`
says a store's reading is not among its arguments. A decay would need a stage
whose executed transitions lower the occupancies — a declared maintenance
channel, which this development does not have and this theorem does not
supply. -/
theorem spent_source_keeps_installation (k : ℕ) :
    (∑ z, (run.law (k + 2)).p z * reserve z.2) = 0 ∧
    (fuelled (k + 2)).installedEnergy = (fuelled 2).installedEnergy := by
  constructor
  · rw [expect_law, stateAt_ge_two]
    norm_num [reserve, level]
  · refine KernelArrangement.installedEnergy_congr _ _ rfl ?_
    show run.law (k + 2) = run.law 2
    rw [law_eq, law_eq, stateAt_ge_two]
    rfl

/-! ### 29.6 Rejections -/

/-- The same run and the same source, with a store that records no draw at all. -/
noncomputable def freeStore : PathwiseStore Unit (Fin 3) :=
  { store with draw := fun _ _ _ _ => 0, supply := fun _ _ _ _ => 0 }

/--
**A run that installs without drawing breaks the bound.** `freeStore` is
ledgered, solvent at every horizon and carries a source ledger; it fails exactly
one hypothesis of `installedEnergy_le_resources`, namely that its draw is the
actuator's path work. The conclusion fails with it: the run installs `3/8` out
of initial resources of zero.

The hypothesis is therefore what carries the bound. An installation whose cost
is not charged to the store is not bounded by what the store held. -/
theorem free_installation_rejected :
    freeStore.Ledgered ∧ freeStore.SourceLedgered (fun _ => 0) ∧
    (∀ N, freeStore.Solvent N) ∧
    ¬ (∀ k, freeStore.draw k = actuator.pathWork (fun _ _ _ => (0 : ℝ))) ∧
    (∑ z, (run.law 0).p z * actuator.storedEnergy z) + freeStore.meanBalance 0 +
        (∑ z, (run.law 0).p z * (0 : ℝ)) <
      ∑ z, (run.law 2).p z * actuator.storedEnergy z := by
  refine ⟨fun n x s t _ _ => by norm_num [freeStore, store],
    fun n x s t _ _ => by norm_num [freeStore, store],
    fun N k _ _ _ => le_rfl, ?_, ?_⟩
  · intro h
    have hthis := congrFun (congrFun (congrFun (h 0) ()) 0) 1
    rw [show freeStore.draw 0 () 0 1 = (0 : ℝ) from rfl,
      show actuator.pathWork (fun _ _ _ => (0 : ℝ)) () 0 1 =
        actuator.storedEnergy ((), 1) - actuator.storedEnergy ((), 0) + 0 from rfl,
      storedEnergy_apply, storedEnergy_apply] at hthis
    norm_num [level] at hthis
  · have hb : freeStore.meanBalance 0 = 0 := by
      show (∑ z, (run.law 0).p z * (0 : ℝ)) = 0
      simp
    rw [hb, initial_installedEnergy, show (∑ z, (run.law 0).p z * (0 : ℝ)) = 0 by simp,
      expect_law 2 (fun z => actuator.storedEnergy z), storedEnergy_apply]
    show (0 : ℝ) + 0 + 0 < level 2
    norm_num [level]

/-! ### 29.7 The learner takes no finite source -/

/-- The learner of §28 as a protocol: one channel, executed over and over.
`FiniteProtocol.ofStep_step` says this is the same object as the iteration the
§28 results are stated on, not a second model of it. -/
noncomputable def learnerRun : FiniteProtocol Bool Bool :=
  FiniteProtocol.ofStep ObservationalLearning.learner.step

theorem learnerRun_positive : learnerRun.Positive :=
  ⟨ObservationalLearning.positive.1, fun _ => ObservationalLearning.positive.2⟩

/-- The learner's store, with the same identification of draw and installation
work as §29.3, and the matching supply the ledger forces on it. -/
noncomputable def learnerStore : PathwiseStore Bool Bool where
  protocol := learnerRun
  balance := fun _ => 0
  draw := fun _ => hardware.pathWork ObservationalLearning.heat
  supply := fun _ => hardware.pathWork ObservationalLearning.heat

theorem learnerStore_ledgered : learnerStore.Ledgered := by
  intro n x s t _ _
  show (0 : ℝ) = 0 - hardware.pathWork ObservationalLearning.heat x s t +
    hardware.pathWork ObservationalLearning.heat x s t
  ring

/--
**A supply that matches every draw is forced, not chosen.** The learner's
composite channel has full support, so `net_draw_eq_zero_of_positive` applies to
any ledgered store on its protocol whose net draw is nowhere negative: the draw
equals the supply at every transition. A learner run off a store that falls is
not available on this channel. -/
theorem learner_net_draw_forced (B : PathwiseStore Bool Bool)
    (hproto : B.protocol = learnerRun) (hl : B.Ledgered)
    (hcost : ∀ n x s t, 0 ≤ B.draw n x s t - B.supply n x s t)
    (n : ℕ) (x s t : Bool) : B.draw n x s t = B.supply n x s t :=
  B.net_draw_eq_zero_of_positive hl (hproto ▸ learnerRun_positive) hcost n x s t

/-- The installation work of one register transition, on the §28 hardware. -/
theorem learner_pathWork (x s t : Bool) :
    hardware.pathWork ObservationalLearning.heat x s t =
      (if x = t then (1 : ℝ) else 0) - (if x = s then 1 else 0) +
        ObservationalLearning.heat x s t := by
  show hardware.storedEnergy (x, t) - hardware.storedEnergy (x, s) +
    ObservationalLearning.heat x s t = _
  rw [LearnedCoupling.storedEnergy_apply, LearnedCoupling.storedEnergy_apply]

/--
**And no finite source stands behind that supply.** `SourceLedgered` asks the
source's loss to be a function of the register alone; the learner's installation
work is not, because closing the switch costs `1 + log 3` when the register
comes to match the parameter and returns as much when it comes to differ. The
two readings of `R true - R false` differ by `2 (1 + log 3)`.

So the fuel no-go is silent about the learner, and that is the right outcome
rather than a gap: `learned_above_line` puts the learner above the threshold
from its first update onwards, and a bound whose hypotheses it satisfied would
contradict that. -/
theorem no_source_funds_learner : ¬ ∃ R : Bool → ℝ, learnerStore.SourceLedgered R := by
  rintro ⟨R, hR⟩
  have hreach : ∀ x s : Bool, learnerRun.Reachable 0 (x, s) :=
    fun x s => learnerRun.law_positive learnerRun_positive 0 (x, s)
  have hstage : ∀ x s t : Bool, 0 < (learnerRun.stage 0 x s).p t :=
    fun x s t => learnerRun_positive.2 0 x s t
  have h1 := hR 0 false false true (hreach false false) (hstage false false true)
  have h2 := hR 0 true false true (hreach true false) (hstage true false true)
  rw [show learnerStore.supply 0 false false true =
      hardware.pathWork ObservationalLearning.heat false false true from rfl,
    learner_pathWork, ObservationalLearning.heat_apply] at h1
  rw [show learnerStore.supply 0 true false true =
      hardware.pathWork ObservationalLearning.heat true false true from rfl,
    learner_pathWork, ObservationalLearning.heat_apply] at h2
  norm_num at h1 h2
  have hlog := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  linarith

/-- The two sides in one statement: a run whose fuel is declared, finite and
too small stays below the threshold at every horizon, and the learner — whose
channel admits no finite source at all — crosses it after one update. -/
theorem fuel_bounds_one_run_and_not_the_other (N n : ℕ) :
    ¬ exhibits_phase_transition (fuelledField N) ∧
    ¬ (∃ R : Bool → ℝ, learnerStore.SourceLedgered R) ∧
    critical_coupling (LearnedCoupling.learnedField (n + 1)).D <
      (LearnedCoupling.learned (n + 1)).couplingPerEnergy *
        (LearnedCoupling.learned (n + 1)).installedEnergy :=
  ⟨(fuelled_no_coherence N).1, no_source_funds_learner, LearnedCoupling.learned_above_line n⟩

#print axioms law_eq
#print axioms store_ledgered
#print axioms source_ledgered
#print axioms installedEnergy_fuelled
#print axioms fuelled_no_coherence
#print axioms cap_attained
#print axioms spent_source_keeps_installation
#print axioms free_installation_rejected
#print axioms learnerStore_ledgered
#print axioms learner_net_draw_forced
#print axioms no_source_funds_learner
#print axioms fuel_bounds_one_run_and_not_the_other

end PhysicsOfConsciousness.Examples.FundedCoupling
