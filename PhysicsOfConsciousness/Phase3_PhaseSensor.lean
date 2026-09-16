import PhysicsOfConsciousness.Phase3_ObservationalLearning

/-!
# A sensor channel derived from a phase readout

`FiniteObservationalLearner` carries the world's response to an action as free
data: `world : W → A → ProbDist O`, a postulated observation law. That is the
right shape for the thermodynamic results, and it is the wrong shape for asking
whether *coordination* supplies anything, because the answer can be written into
the postulate.

This module removes the postulate for one construction. A `PhaseSensor` is two
declared pieces of hardware — a phase law saying what configuration the
population takes at a given parameter and executed action, and a readout turning
one oscillator's phase into a finite symbol — and the observation probabilities
are *computed*: the sensor samples one oscillator uniformly and reports its
symbol, so the mass of a symbol is the fraction of the population carrying it.
Nothing is assumed about accuracy, and nothing relates coherence to accuracy.

## What the construction fixes and what it leaves open

`channel_eq_of_phase_eq` is the whole of the negative direction: the channel
sees the phase configuration and nothing else, so a phase law that does not
depend on the parameter yields observations that do not either, whatever the
population is doing. `channel_ne_iff_fiberCount_ne` is the positive direction and
names the relation a positive comparison needs — the readout's fibre counts must
actually differ between the two parameters at the executed action. That is a
condition on the phase-to-world relation, not on the order parameter: a
population can be equally coherent at both parameters and still separate them,
or be equally coherent and not separate them at all, and
`Examples/PhaseSensor.lean` §27 exhibits both.

A stationary phase law is a supplied regime. Nothing here derives the
configuration from Kuramoto dynamics, selects it, or claims that a more coherent
population learns faster. The sampling model — one oscillator, uniformly — is
declared sensor hardware in the same sense as the encoder of
`Phase5_ContentDynamics`.
-/

namespace PhysicsOfConsciousness

/-- Declared sensor hardware: the configuration the population takes at each
parameter and executed action, and the finite symbol one oscillator's phase is
read as. Bare data; no property of either map is assumed. -/
structure PhaseSensor (W A V O : Type*) where
  /-- The phase configuration, at a given parameter and executed action. -/
  phase : W → A → V → ℝ
  /-- The finite readout of a single oscillator's phase. -/
  readout : ℝ → O

namespace PhaseSensor

variable {W A V O : Type*} [Fintype V] [DecidableEq O]

/-- How many oscillators read as the symbol `o`. -/
def fiberCount (S : PhaseSensor W A V O) (w : W) (a : A) (o : O) : ℕ :=
  (Finset.univ.filter fun v => S.readout (S.phase w a v) = o).card

theorem sum_fiberCount (S : PhaseSensor W A V O) [Fintype O] (w : W) (a : A) :
    ∑ o, S.fiberCount w a o = Fintype.card V :=
  (Finset.card_eq_sum_card_fiberwise
    (f := fun v => S.readout (S.phase w a v)) fun _ _ => Finset.mem_univ _).symm

/-- **The observation law, computed rather than declared.** The sensor samples
one oscillator uniformly and reports its symbol, so a symbol's probability is
the fraction of the population carrying it. -/
noncomputable def channel (S : PhaseSensor W A V O) [Fintype O] [Nonempty V]
    (w : W) (a : A) : ProbDist O where
  p o := (S.fiberCount w a o : ℝ) / (Fintype.card V : ℝ)
  nonneg _ := by positivity
  sum_one := by
    have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Fintype.card_pos
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_fiberCount]
    exact div_self hcard.ne'

@[simp] theorem channel_apply (S : PhaseSensor W A V O) [Fintype O] [Nonempty V]
    (w : W) (a : A) (o : O) :
    (S.channel w a).p o = (S.fiberCount w a o : ℝ) / (Fintype.card V : ℝ) := rfl

/-- **The channel sees the configuration and nothing else.** Two parameters that
put the population in the same configuration are indistinguishable to the
sensor, however coherent that configuration is. -/
theorem channel_eq_of_phase_eq (S : PhaseSensor W A V O) [Fintype O] [Nonempty V]
    {w w' : W} {a : A} (h : ∀ v, S.phase w a v = S.phase w' a v) :
    S.channel w a = S.channel w' a := by
  apply ProbDist.ext
  funext o
  have hfib : S.fiberCount w a o = S.fiberCount w' a o := by
    unfold fiberCount
    have hset : (Finset.univ.filter fun v => S.readout (S.phase w a v) = o)
        = (Finset.univ.filter fun v => S.readout (S.phase w' a v) = o) := by
      apply Finset.filter_congr
      intro v _
      rw [h v]
    rw [hset]
  simp only [channel_apply, hfib]

/-- **The relation a positive comparison needs.** The sensor separates two
parameters at an executed action exactly when the readout's fibre counts differ
there. This is a condition relating the phase law to the readout, and it is what
any information or performance comparison must supply; it is not implied by, and
does not imply, any statement about the population's order parameter. -/
theorem channel_ne_iff_fiberCount_ne (S : PhaseSensor W A V O) [Fintype O] [Nonempty V]
    (w w' : W) (a : A) :
    S.channel w a ≠ S.channel w' a ↔ ∃ o, S.fiberCount w a o ≠ S.fiberCount w' a o := by
  constructor
  · intro hne
    by_contra hall
    apply hne
    apply ProbDist.ext
    funext o
    have hfib : S.fiberCount w a o = S.fiberCount w' a o := by
      by_contra hc
      exact hall ⟨o, hc⟩
    simp only [channel_apply, hfib]
  · rintro ⟨o, ho⟩ heq
    apply ho
    have h := congrArg (fun μ : ProbDist O => μ.p o) heq
    simp only [channel_apply] at h
    have hne : (Fintype.card V : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
      exact this.ne'
    rw [div_eq_div_iff hne hne] at h
    exact_mod_cast mul_right_cancel₀ hne h

/-- **A phase-independent readout observes nothing.** If every phase reads as the
same symbol, the channel is that symbol with certainty at every parameter and
every action: the sensor has no content to deliver, whatever the population
does. -/
theorem channel_eq_dirac_of_readout_const (S : PhaseSensor W A V O) [Fintype O] [Nonempty V]
    {o₀ : O} (h : ∀ x : ℝ, S.readout x = o₀) (w : W) (a : A) :
    S.channel w a = ProbDist.dirac o₀ := by
  apply ProbDist.ext
  funext o
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases ho : o = o₀
  · subst ho
    have hfull : S.fiberCount w a o = Fintype.card V := by
      unfold fiberCount
      rw [Finset.filter_true_of_mem fun v _ => h (S.phase w a v), Finset.card_univ]
    simp [channel_apply, hfull]
  · have hzero : S.fiberCount w a o = 0 := by
      unfold fiberCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v _
      rw [h (S.phase w a v)]
      exact fun hc => ho hc.symm
    simp [channel_apply, hzero, ho]

end PhaseSensor

/-- A learner whose observations are produced by a phase sensor. The parameter
enters only through `S.phase`; the update and the action readout have no access
to it, which is a property of `FiniteObservationalLearner`'s field types and not
of this constructor. -/
noncomputable def FiniteObservationalLearner.ofPhaseSensor
    {W R A O V : Type*} [Fintype W] [Fintype R] [Fintype A] [Fintype O] [DecidableEq O]
    [Fintype V] [Nonempty V]
    (prior : ProbDist (W × R)) (readout : R → A) (S : PhaseSensor W A V O)
    (update : O → R → ProbDist R) (reward : W → A → ℝ) :
    FiniteObservationalLearner W R A O :=
  ⟨prior, readout, S.channel, update, reward⟩

@[simp] theorem FiniteObservationalLearner.ofPhaseSensor_world
    {W R A O V : Type*} [Fintype W] [Fintype R] [Fintype A] [Fintype O] [DecidableEq O]
    [Fintype V] [Nonempty V]
    (prior : ProbDist (W × R)) (readout : R → A) (S : PhaseSensor W A V O)
    (update : O → R → ProbDist R) (reward : W → A → ℝ) :
    (FiniteObservationalLearner.ofPhaseSensor prior readout S update reward).world
      = S.channel := rfl

#print axioms PhaseSensor.channel
#print axioms PhaseSensor.channel_eq_of_phase_eq
#print axioms PhaseSensor.channel_ne_iff_fiberCount_ne
#print axioms PhaseSensor.channel_eq_dirac_of_readout_const

end PhysicsOfConsciousness
