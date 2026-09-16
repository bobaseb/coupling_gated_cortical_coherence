import PhysicsOfConsciousness.Phase3_AgencyThermodynamics

/-!
# Learning from experience: a register driven by observed outcomes

`FiniteControlProblem` compares fixed policies, and `FiniteFeedbackStep.iterate`
relaxes a policy register whose *energy already encodes* the expected task
values. Neither acquires task information. The structure here removes that
supply: an environmental parameter `W` is held fixed and unknown, the register
`R` is read out as the executed action, the world returns an observation of
that action's realized outcome, and the register update is a function of the
observation alone.

The two fences are type-level rather than textual. `update : O → R → ProbDist R`
has no `W` argument, so no channel can read the unknown parameter; `readout :
R → A` has no `W` argument, so no precomputed policy value can be decoded into
the action. `reward` is used only by `performance` and appears in no channel.

The composite register channel is a `FiniteFeedbackStep W R`, so the existing
path-law entropy balance, local-detailed-balance heat, first law and their
telescoped sums apply to exactly the process `performance` is read from.

`zero_work_needs_parameter_independent_heat` is the negative half and is the
reason this model is not the previous one with different names: a register
energy that makes the update a free relaxation forces its drive to carry no
information about the parameter. Learning from experience is paid for in work.

What the structure does not supply: preparation of the prior, a continuing
power source, repeated task episodes beyond the declared updates, physical
fabrication of the readout, convergence to an optimal policy, or any
identification of these variables with cortical ones.
-/

namespace PhysicsOfConsciousness

/-- Data of a finite learner that acquires task information only by observing
the outcomes of the actions it actually takes. `W` is an environmental
parameter held fixed across updates and never read by any channel. -/
structure FiniteObservationalLearner (W R A O : Type*)
    [Fintype W] [Fintype R] [Fintype A] [Fintype O] where
  /-- Joint law of the unknown parameter and the register before any update.
  Its preparation is supplied, not produced by this process. -/
  prior : ProbDist (W × R)
  /-- The register's value decodes to the executed action. -/
  readout : R → A
  /-- The world's response to the executed action, at the actual parameter. -/
  world : W → A → ProbDist O
  /-- The register update, driven by the observation alone. -/
  update : O → R → ProbDist R
  /-- The evaluation criterion. It is a modelling input and enters no channel. -/
  reward : W → A → ℝ

namespace FiniteObservationalLearner

variable {W R A O : Type*} [Fintype W] [Fintype R] [Fintype A] [Fintype O]
  (L : FiniteObservationalLearner W R A O)

/-- The outcome law of one executed action: the world's response to the action
the current register decodes to. -/
noncomputable def outcome (w : W) (r : R) : ProbDist O := L.world w (L.readout r)

/-- Act, observe, update: the composite register channel at the fixed parameter.
The intermediate observation is marginalized out of the register's law, so the
learner retains only what its update wrote. -/
noncomputable def transition (w : W) (r : R) : ProbDist R :=
  (L.outcome w r).bind fun o => L.update o r

/-- The learner as an elementary bipartite update with the parameter fixed. -/
noncomputable def step : FiniteFeedbackStep W R := ⟨L.prior, L.transition⟩

/-- The actual joint law after `n` updates. Each is the preceding final law. -/
noncomputable def law (n : ℕ) : ProbDist (W × R) := (L.step.iterate n).initial

@[simp] theorem law_zero : L.law 0 = L.prior := rfl

/-- Every actual output is the next input: no reset or independent preparation
enters the sequence. -/
@[simp] theorem law_succ (n : ℕ) : L.law (n + 1) = (L.step.iterate n).final := rfl

@[simp] theorem step_transition : L.step.transition = L.transition := rfl

/-- The next law's mass, written on the preceding law and the same channel. -/
theorem law_succ_apply (n : ℕ) (z : W × R) :
    (L.law (n + 1)).p z = ∑ r, (L.law n).p (z.1, r) * (L.transition z.1 r).p z.2 := by
  rw [law_succ]
  simp only [FiniteFeedbackStep.final, FiniteFeedbackStep.iterate_transition, step_transition]
  rfl

/-- Expectations of a path observable on the actual forward paths of update `n`. -/
theorem meanHeat_apply (q : W → R → R → ℝ) (n : ℕ) :
    (L.step.iterate n).meanHeat q =
      ∑ w, ∑ r, ∑ r', (L.law n).p (w, r) * (L.transition w r).p r' * q w r r' := by
  unfold FiniteFeedbackStep.meanHeat FiniteFeedbackStep.forward
  simp only [Fintype.sum_prod_type, FiniteFeedbackStep.iterate_transition, step_transition]
  rfl

/-- Expected reward of the action the register actually executes at update `n`,
evaluated on the same evolving law the thermodynamic balances use. -/
noncomputable def performance (n : ℕ) : ℝ :=
  ∑ z, (L.law n).p z * L.reward z.1 (L.readout z.2)

/-- Strict support of the composite channel survives every finite horizon. -/
theorem law_positive [Nonempty R] (h : L.step.Positive) (n : ℕ) (z : W × R) :
    0 < (L.law n).p z :=
  (L.step.iterate_positive h n).1 z

/-- Outward heat of one register transition in a declared local-detailed-balance
reservoir model at thermal scale `θ`. The identification is a physical
hypothesis about the drive, not a consequence of the update rule. -/
noncomputable def heat (θ : ℝ) (w : W) (r r' : R) : ℝ :=
  θ * Real.log ((L.transition w r).p r' / (L.transition w r').p r)

/-- Work into the register on one transition, in a common energy. -/
noncomputable def work (E : W × R → ℝ) (θ : ℝ) (w : W) (r r' : R) : ℝ :=
  E (w, r') - E (w, r) + L.heat θ w r r'

theorem local_balance (θ : ℝ) (n : ℕ) :
    (L.step.iterate n).LocalDetailedBalance θ (L.heat θ) := by
  intro w r r'
  rw [FiniteFeedbackStep.iterate_transition]
  rfl

/-- The first law telescopes over the actual sequence of laws. -/
theorem sum_first_law (E : W × R → ℝ) (θ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (L.step.iterate n).meanHeat (L.work E θ)) =
      (∑ z, (L.law N).p z * E z) - (∑ z, (L.law 0).p z * E z) +
        ∑ n ∈ Finset.range N, (L.step.iterate n).meanHeat (L.heat θ) :=
  L.step.sum_first_law E (L.heat θ) (L.work E θ) (fun _ _ _ => rfl) N

/-- A register whose states are energetically degenerate stores nothing, so the
whole cumulative heat is supplied from outside as work. -/
theorem cumulative_work_eq_heat (c : ℝ) (θ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (L.step.iterate n).meanHeat (L.work (fun _ => c) θ)) =
      ∑ n ∈ Finset.range N, (L.step.iterate n).meanHeat (L.heat θ) := by
  rw [L.sum_first_law (fun _ => c) θ N]
  simp only [← Finset.sum_mul, ProbDist.sum_one, one_mul]
  ring

/-- **The negative half.** Suppose a register energy makes every update a free
relaxation — zero work on every path. Because the register cannot read `W`, such
an energy is a function of the register alone, and the supposition then forces
the drive's heat to be the same at every parameter value. A drive that carries
no information about the parameter cannot teach the register anything about it.
Learning from experience therefore consumes work; it is not a relaxation. -/
theorem zero_work_needs_parameter_independent_heat (θ : ℝ) (E : R → ℝ)
    (h : ∀ w r r', E r' - E r + L.heat θ w r r' = 0) (w w' : W) (r r' : R) :
    L.heat θ w r r' = L.heat θ w' r r' := by
  have h₁ := h w r r'
  have h₂ := h w' r r'
  linarith

/-- The joint entropy the learner removes over any finite horizon is paid for
by the cumulative heat of the same process, at the declared thermal scale. -/
theorem cumulative_entropy_budget [Nonempty R] (h : L.step.Positive)
    (θ : ℝ) (hθ : 0 < θ) (N : ℕ) :
    θ * (shannon_entropy (L.law 0).p - shannon_entropy (L.law N).p) ≤
      ∑ n ∈ Finset.range N, (L.step.iterate n).meanHeat (L.heat θ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hb := (L.step.iterate N).heat_bound (L.step.iterate_positive h N) θ hθ
      (L.heat θ) (L.local_balance θ N)
    rw [Finset.sum_range_succ]
    have hinit : (L.step.iterate N).initial = L.law N := rfl
    have hfinal : (L.step.iterate N).final = L.law (N + 1) := rfl
    rw [hinit, hfinal] at hb
    nlinarith [hb, ih]

section Frozen

variable [DecidableEq R]

/-- The comparison baseline: the same task, prior, readout and world, with a
register that never changes. It executes actions and observes outcomes; it
simply does not write anything down. -/
noncomputable def frozen : FiniteObservationalLearner W R A O :=
  { L with update := fun _ r => ProbDist.dirac r }

@[simp] theorem frozen_transition (w : W) (r : R) : L.frozen.transition w r = ProbDist.dirac r :=
  ProbDist.bind_const _ _

/-- **A learner whose composite channel returns the register unchanged keeps its
prior.** The hypothesis is on the act--observe--update composite, not on the
update rule in isolation: a learner with a perfectly ordinary update rule and an
observation that never varies satisfies it. -/
theorem law_eq_prior_of_transition_dirac
    (h : ∀ w r, L.transition w r = ProbDist.dirac r) (n : ℕ) : L.law n = L.prior := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [law_succ, ← ih]
    apply ProbDist.ext
    funext z
    simp only [FiniteFeedbackStep.final, FiniteFeedbackStep.iterate_transition,
      step_transition, h, ProbDist.dirac_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Prod.mk.eta]
    rfl

/-- Such a learner's expected reward is the prior's at every horizon. -/
theorem performance_const_of_transition_dirac
    (h : ∀ w r, L.transition w r = ProbDist.dirac r) (n : ℕ) :
    L.performance n = L.performance 0 := by
  unfold performance
  rw [L.law_eq_prior_of_transition_dirac h n, L.law_eq_prior_of_transition_dirac h 0]

/-- A frozen register reproduces its own law at every horizon, so its expected
reward is the prior's and no observation can change it. -/
@[simp] theorem frozen_law (n : ℕ) : L.frozen.law n = L.prior :=
  L.frozen.law_eq_prior_of_transition_dirac (fun w r => L.frozen_transition w r) n

theorem frozen_performance (n : ℕ) : L.frozen.performance n = L.frozen.performance 0 := by
  unfold performance
  rw [frozen_law, frozen_law]

end Frozen

end FiniteObservationalLearner

end PhysicsOfConsciousness
