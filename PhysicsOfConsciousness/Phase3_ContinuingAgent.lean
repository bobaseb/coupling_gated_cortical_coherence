import PhysicsOfConsciousness.Phase3_ObservationalLearning

/-!
# One continuing agent: sequenced stages on one law, funded by a declared store

`FiniteFeedbackStep.iterate` repeats one channel, and `FiniteObservationalLearner`
gives its world no state that an action changes and an observation later reads.
A continuing agent does different things in sequence — it acts, it reads what its
action did, it clears the workspace for the next episode — and it does them out of
a supply that runs down.

`FiniteProtocol` is the first of those: an initial law and a *sequence* of
channels, each stage starting at the law the previous one produced. Every stage
is an ordinary `FiniteFeedbackStep`, so the path-law entropy balance, the first
law and the Gibbs bound hold stagewise and telescope over the run. `ofStep_step`
identifies the constant protocol with `iterate`, so the repeated case is the
same theory rather than a second one.

`ContinuingProcess` adds a common energy, a stage-indexed heat observable, one
thermal scale and `stored`: the usable work available before the first stage.
`remaining` is what is left of it, `Sustains N` says it was never overdrawn, and
the four consequences are that a sustained run has drawn at most its store, that
its reservoir heat is at most the store plus the energy the system itself gave
up, that the joint entropy reduction is bounded by that same total, and
that a store cannot fund more than `stored / c` stages each costing `c > 0`.
Sustained operation is therefore a claim about replenishment, which the store
does not make.

`ContinuingAgent` composes the agency loop into such a protocol on the joint
state `R × Env`: the register's readout drives `actuate`, which moves the
environment; `sense` reads the environment the action moved and `update` writes
the register; `reset` returns the environment to its standard state for the next
episode. The three stages run in that order on one evolving joint law, with the
unknown parameter `W` fixed. The actuator responds to `W`; the learner cannot
read it directly. The fences are signatures
again: `update` sees neither the parameter nor the action, `readout` and `sense`
do not see the parameter, and `reward` appears only in `performance`.

What this supplies is the bookkeeping of a continuing agent: one law, actual
influence of the register on the world and an executed reset preparing later
episodes. The store constrains expected cumulative work at every prefix; it
does not guarantee a nonnegative battery on every sample path. Initial-law
preparation, a microscopic store, readout/actuator fabrication and a separate
observation-memory implementation are supplied or outside the model. The
composite learning channel is assigned local detailed balance as a physical
input. Neither optimal-policy convergence nor cortical identification follows.
-/

namespace PhysicsOfConsciousness

/-! ## A time-dependent protocol on one law -/

/-- Work into the system on one path of a stage, from a common energy and that
stage's heat. The energy is shared by every stage; the heat need not be. -/
noncomputable def protocolWork {X S : Type*} (E : X × S → ℝ)
    (q : ℕ → X → S → S → ℝ) (n : ℕ) (x : X) (s t : S) : ℝ :=
  E (x, t) - E (x, s) + q n x s t

/-- An initial law and a sequence of channels on the same joint state. The
index counts executed operations, which need not be the same operation. -/
structure FiniteProtocol (X S : Type*) [Fintype X] [Fintype S] where
  /-- The law before the first stage. Its preparation is supplied, not derived. -/
  initial : ProbDist (X × S)
  /-- The channel executed at each stage, with the parameter `X` held fixed. -/
  stage : ℕ → X → S → ProbDist S

namespace FiniteProtocol

variable {X S : Type*} [Fintype X] [Fintype S] (P : FiniteProtocol X S)

/-- The actual joint law after `n` stages: every stage starts at the law the
preceding ones produced, so the whole run is one law. -/
noncomputable def law (P : FiniteProtocol X S) : ℕ → ProbDist (X × S)
  | 0 => P.initial
  | n + 1 => (⟨law P n, P.stage n⟩ : FiniteFeedbackStep X S).final

/-- Stage `n` as an elementary bipartite update, started at the law the
preceding stages actually produced. -/
noncomputable def step (n : ℕ) : FiniteFeedbackStep X S := ⟨P.law n, P.stage n⟩

@[simp] theorem law_zero : P.law 0 = P.initial := rfl

@[simp] theorem step_initial (n : ℕ) : (P.step n).initial = P.law n := rfl

@[simp] theorem step_transition (n : ℕ) : (P.step n).transition = P.stage n := rfl

/-- Every actual output is the next input: no stage is independently prepared. -/
@[simp] theorem law_succ (n : ℕ) : P.law (n + 1) = (P.step n).final := by
  rw [law, step]

/-- The next law's mass, on the preceding law and the stage actually executed. -/
theorem law_succ_apply (n : ℕ) (z : X × S) :
    (P.law (n + 1)).p z = ∑ s, (P.law n).p (z.1, s) * (P.stage n z.1 s).p z.2 := by
  rw [law_succ]
  simp only [FiniteFeedbackStep.final, step_transition, step_initial]

/-- Expectations of a stage observable on the actual forward paths of stage `n`. -/
theorem meanHeat_apply (q : X → S → S → ℝ) (n : ℕ) :
    (P.step n).meanHeat q =
      ∑ x, ∑ s, ∑ t, (P.law n).p (x, s) * (P.stage n x s).p t * q x s t := by
  unfold FiniteFeedbackStep.meanHeat FiniteFeedbackStep.forward
  simp only [Fintype.sum_prod_type, step_transition, step_initial]

/-- Strict support of the initial law and of every stage channel. -/
def Positive : Prop :=
  (∀ z, 0 < P.initial.p z) ∧ (∀ n x s t, 0 < (P.stage n x s).p t)

theorem step_positive [Nonempty S] (h : P.Positive) (n : ℕ) : (P.step n).Positive := by
  induction n with
  | zero => exact ⟨h.1, fun x s t => h.2 0 x s t⟩
  | succ n ih =>
    refine ⟨fun z => ?_, fun x s t => h.2 (n + 1) x s t⟩
    rw [step_initial, law_succ]
    exact (P.step n).final_positive ih z

theorem law_positive [Nonempty S] (h : P.Positive) (n : ℕ) (z : X × S) :
    0 < (P.law n).p z := (P.step_positive h n).1 z

/-- The stage's own outward heat in a declared local-detailed-balance reservoir
model at thermal scale `θ`. The identification is a physical hypothesis. -/
noncomputable def stageHeat (θ : ℝ) (n : ℕ) (x : X) (s t : S) : ℝ :=
  θ * Real.log ((P.stage n x s).p t / (P.stage n x t).p s)

/-- Local detailed balance for every stage, at one common thermal scale. -/
def LocalDetailedBalance (θ : ℝ) (q : ℕ → X → S → S → ℝ) : Prop :=
  ∀ n, (P.step n).LocalDetailedBalance θ (q n)

theorem local_balance (θ : ℝ) : P.LocalDetailedBalance θ (P.stageHeat θ) :=
  fun _ _ _ _ => rfl

/-- The path-law entropy balance telescopes along the actual successive laws.
The stages need not be the same operation and no stationarity is assumed. -/
theorem sum_entropy_balance [Nonempty S] (h : P.Positive) (N : ℕ) :
    (∑ k ∈ Finset.range N, (P.step k).entropyProduction) =
      shannon_entropy (P.law N).p - shannon_entropy (P.law 0).p +
        ∑ k ∈ Finset.range N, (P.step k).bathEntropy := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      (P.step N).entropy_balance (P.step_positive h N), ← P.law_succ N, step_initial]
    ring

/-- One common energy and the pathwise first law give the cumulative work of the
whole sequence from the actual endpoint energies and the cumulative heat. -/
theorem sum_first_law (E : X × S → ℝ) (q : ℕ → X → S → S → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (P.step k).meanHeat (protocolWork E q k)) =
      (∑ z, (P.law N).p z * E z) - (∑ z, (P.law 0).p z * E z) +
        ∑ k ∈ Finset.range N, (P.step k).meanHeat (q k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      (P.step N).mean_first_law E (q N) (protocolWork E q N) (fun _ _ _ => rfl),
      ← P.law_succ N, step_initial]
    ring

/-- The joint entropy the sequence removes is paid for by its cumulative heat,
at the declared thermal scale. Gibbs and local detailed balance, stage by stage. -/
theorem cumulative_entropy_budget [Nonempty S] (h : P.Positive) (θ : ℝ) (hθ : 0 < θ)
    (q : ℕ → X → S → S → ℝ) (hq : P.LocalDetailedBalance θ q) (N : ℕ) :
    θ * (shannon_entropy (P.law 0).p - shannon_entropy (P.law N).p) ≤
      ∑ k ∈ Finset.range N, (P.step k).meanHeat (q k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hb := (P.step N).heat_bound (P.step_positive h N) θ hθ (q N) (hq N)
    rw [← P.law_succ N, step_initial] at hb
    rw [Finset.sum_range_succ]
    nlinarith [hb, ih]

/-! ### The repeated case is the same theory -/

/-- The protocol that executes one channel over and over. -/
noncomputable def ofStep (M : FiniteFeedbackStep X S) : FiniteProtocol X S :=
  ⟨M.initial, fun _ => M.transition⟩

/-- A constant protocol's stages are exactly the existing repeated updates, so
nothing above replaces `FiniteFeedbackStep.iterate`; it generalizes it. -/
theorem ofStep_step (M : FiniteFeedbackStep X S) (n : ℕ) :
    (ofStep M).step n = M.iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hl : (ofStep M).law (n + 1) = (M.iterate n).final := by
      rw [law_succ, ih]
    show (⟨(ofStep M).law (n + 1), (ofStep M).stage (n + 1)⟩ :
      FiniteFeedbackStep X S) = M.iterate (n + 1)
    rw [hl]
    rfl

end FiniteProtocol

/-! ## A declared store, and what it can buy -/

/-- A protocol together with the resources that run it: one energy observable in
joint coordinates, the heat each stage delivers to its reservoir, one thermal
scale, and the usable work available before the first stage. -/
structure ContinuingProcess (X S : Type*) [Fintype X] [Fintype S] where
  /-- The sequence of operations actually executed. -/
  protocol : FiniteProtocol X S
  /-- A common energy for every stage, in joint coordinates. -/
  energy : X × S → ℝ
  /-- Outward heat of each stage, positive into that stage's reservoir. -/
  heat : ℕ → X → S → S → ℝ
  /-- The common thermal scale `k_B T` of the reservoir model. -/
  temperature : ℝ
  /-- Usable work available before the first stage. A declared supply: this
  model does not derive it from a microscopic battery. -/
  stored : ℝ

namespace ContinuingProcess

variable {X S : Type*} [Fintype X] [Fintype S] (C : ContinuingProcess X S)

/-- Work into the system on one path of stage `n`, from the common energy. -/
noncomputable def stageWork (n : ℕ) : X → S → S → ℝ :=
  protocolWork C.energy C.heat n

/-- The work the store has supplied over the first `N` executed stages. -/
noncomputable def totalWork (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (C.protocol.step k).meanHeat (C.stageWork k)

/-- The heat those same stages have delivered to their reservoirs. -/
noncomputable def totalHeat (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (C.protocol.step k).meanHeat (C.heat k)

/-- Expected remaining work allowance after `N` stages; no battery state is
carried in the protocol's sample paths. -/
noncomputable def remaining (N : ℕ) : ℝ := C.stored - C.totalWork N

/-- The expected work allowance is nonnegative at every prefix up to `N`.
This does not assert that every realization stays within a pathwise budget. -/
def Sustains (N : ℕ) : Prop := ∀ k ≤ N, 0 ≤ C.remaining k

theorem remaining_succ (n : ℕ) :
    C.remaining (n + 1) =
      C.remaining n - (C.protocol.step n).meanHeat (C.stageWork n) := by
  unfold remaining totalWork
  rw [Finset.sum_range_succ]
  ring

theorem sustains_of_le {M N : ℕ} (h : C.Sustains N) (hMN : M ≤ N) : C.Sustains M :=
  fun k hk => h k (hk.trans hMN)

/-- A sustained run has drawn at most its store. -/
theorem sustains_totalWork_le (N : ℕ) (h : C.Sustains N) : C.totalWork N ≤ C.stored := by
  have := h N le_rfl
  unfold remaining at this
  linarith

/-- The first law for the whole executed sequence: the heat delivered is the
work supplied plus the energy the system itself gave up. -/
theorem totalHeat_eq (N : ℕ) :
    C.totalHeat N = C.totalWork N + (∑ z, (C.protocol.law 0).p z * C.energy z) -
      ∑ z, (C.protocol.law N).p z * C.energy z := by
  have h := C.protocol.sum_first_law C.energy C.heat N
  unfold totalWork stageWork totalHeat
  rw [h]
  ring

/-- Over a sustained run the reservoirs receive at most the store plus the
system's own energy drop. Nothing here assumes the stages are alike. -/
theorem totalHeat_le_stored (N : ℕ) (h : C.Sustains N) :
    C.totalHeat N ≤ C.stored + (∑ z, (C.protocol.law 0).p z * C.energy z) -
      ∑ z, (C.protocol.law N).p z * C.energy z := by
  have hw := C.sustains_totalWork_le N h
  rw [C.totalHeat_eq N]
  linarith

/-- **What a store can buy.** The joint entropy a continuing process removes
over its whole run — actions, observations, updates and resets alike — is
bounded by the work its store supplied plus the energy it gave up. -/
theorem entropy_reduction_le_stored [Nonempty S] (hp : C.protocol.Positive)
    (hθ : 0 < C.temperature)
    (hq : C.protocol.LocalDetailedBalance C.temperature C.heat) (N : ℕ)
    (h : C.Sustains N) :
    C.temperature * (shannon_entropy (C.protocol.law 0).p -
        shannon_entropy (C.protocol.law N).p) ≤
      C.stored + (∑ z, (C.protocol.law 0).p z * C.energy z) -
        ∑ z, (C.protocol.law N).p z * C.energy z := by
  have hb := C.protocol.cumulative_entropy_budget hp C.temperature hθ C.heat hq N
  have hh := C.totalHeat_le_stored N h
  unfold totalHeat at hh
  linarith

/-- **No perpetual agent.** If every stage costs at least `c > 0` of work, a
store of `stored` sustains at most `stored / c` stages. Continuing operation is
a claim about replenishment, which a store does not make. -/
theorem horizon_le_of_cost (c : ℝ)
    (hcost : ∀ k, c ≤ (C.protocol.step k).meanHeat (C.stageWork k)) (N : ℕ)
    (h : C.Sustains N) : (N : ℝ) * c ≤ C.stored := by
  have hsum : (N : ℝ) * c ≤ C.totalWork N := by
    unfold totalWork
    have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range N) => hcost k)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  exact hsum.trans (C.sustains_totalWork_le N h)

theorem not_sustains_of_totalWork_gt (N : ℕ) (h : C.stored < C.totalWork N) :
    ¬ C.Sustains N := fun hs => absurd (C.sustains_totalWork_le N hs) (not_le.mpr h)

end ContinuingProcess

/-! ## The agent: action, observation, learning and preparation in sequence -/

/-- A finite agent that keeps running. `Env` is the part of the world the action
changes and the observation reads; the parameter `W` is fixed and affects the
actuator, but is not an input to the learner. `registerIdle` and `envIdle` are
the drift of whichever coordinate is
not being driven at that stage: a physical register does not hold perfectly
still while the world is being acted on. -/
structure ContinuingAgent (W R Env O A : Type*) [Fintype W] [Fintype R]
    [Fintype Env] [Fintype O] [Fintype A] where
  /-- Joint law of the unknown parameter, the register and the world before the
  first stage. Its preparation is supplied. -/
  prior : ProbDist (W × (R × Env))
  /-- The register's value decodes to the executed action. -/
  readout : R → A
  /-- What the executed action does to the world, at the actual parameter. -/
  actuate : W → A → Env → ProbDist Env
  /-- The observation: a readout of the world the action moved. It does not see
  the parameter. -/
  sense : Env → ProbDist O
  /-- The register update, driven by the observation alone. -/
  update : O → R → ProbDist R
  /-- Preparation of the next episode: the world is returned toward its
  standard state. This is an executed operation like any other. -/
  reset : Env → ProbDist Env
  /-- The register's drift while it is not being written. -/
  registerIdle : R → ProbDist R
  /-- The world's drift while it is not being acted on. -/
  envIdle : Env → ProbDist Env
  /-- The evaluation criterion. It is a modelling input and enters no channel. -/
  reward : W → A → ℝ

namespace ContinuingAgent

variable {W R Env O A : Type*} [Fintype W] [Fintype R] [Fintype Env] [Fintype O]
  [Fintype A] (G : ContinuingAgent W R Env O A)

/-- Acting: the register's readout drives the world; the register drifts. -/
noncomputable def actStage (w : W) (z : R × Env) : ProbDist (R × Env) :=
  (G.registerIdle z.1).prod (G.actuate w (G.readout z.1) z.2)

/-- Learning: the observation of the world the action moved drives the register;
the world drifts. The intermediate observation is not retained. -/
noncomputable def learnStage (_w : W) (z : R × Env) : ProbDist (R × Env) :=
  ((G.sense z.2).bind fun o => G.update o z.1).prod (G.envIdle z.2)

/-- Preparing: the world is returned toward its declared standard state; the
register drifts. Whether this improves later observations depends on the channels. -/
noncomputable def resetStage (_w : W) (z : R × Env) : ProbDist (R × Env) :=
  (G.registerIdle z.1).prod (G.reset z.2)

/-- The three operations in order, repeated. The index counts operations. -/
noncomputable def stage (n : ℕ) : W → (R × Env) → ProbDist (R × Env) :=
  if n % 3 = 0 then G.actStage else if n % 3 = 1 then G.learnStage else G.resetStage

/-- The whole run as one time-dependent protocol on one evolving joint law. -/
noncomputable def protocol : FiniteProtocol W (R × Env) := ⟨G.prior, G.stage⟩

/-- The actual joint law of parameter, register and world after `n` operations. -/
noncomputable def law (n : ℕ) : ProbDist (W × (R × Env)) := G.protocol.law n

@[simp] theorem law_zero : G.law 0 = G.prior := rfl

@[simp] theorem protocol_stage (n : ℕ) : G.protocol.stage n = G.stage n := rfl

@[simp] theorem protocol_law (n : ℕ) : G.protocol.law n = G.law n := rfl

/-- Expectations of a stage observable on the actual forward paths of the
composed run. -/
theorem meanHeat_apply (q : W → (R × Env) → (R × Env) → ℝ) (n : ℕ) :
    (G.protocol.step n).meanHeat q =
      ∑ w, ∑ s, ∑ t, (G.law n).p (w, s) * (G.stage n w s).p t * q w s t :=
  G.protocol.meanHeat_apply q n

@[simp] theorem stage_act (m : ℕ) : G.stage (3 * m) = G.actStage := by
  have h : 3 * m % 3 = 0 := by omega
  simp only [stage, h, reduceIte]

@[simp] theorem stage_learn (m : ℕ) : G.stage (3 * m + 1) = G.learnStage := by
  have h : (3 * m + 1) % 3 = 1 := by omega
  simp only [stage, h]
  norm_num

@[simp] theorem stage_reset (m : ℕ) : G.stage (3 * m + 2) = G.resetStage := by
  have h : (3 * m + 2) % 3 = 2 := by omega
  simp only [stage, h]
  norm_num

/-- Strict support of the prior and of every channel the agent executes. -/
def Positive : Prop :=
  (∀ z, 0 < G.prior.p z) ∧ (∀ w a e e', 0 < (G.actuate w a e).p e') ∧
    (∀ e o, 0 < (G.sense e).p o) ∧ (∀ o r r', 0 < (G.update o r).p r') ∧
    (∀ e e', 0 < (G.reset e).p e') ∧ (∀ r r', 0 < (G.registerIdle r).p r') ∧
    (∀ e e', 0 < (G.envIdle e).p e')

theorem protocol_positive [Nonempty O] (h : G.Positive) : G.protocol.Positive := by
  obtain ⟨hp, ha, hs, hu, hr, hri, hei⟩ := h
  refine ⟨hp, fun n w z z' => ?_⟩
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h3 | h3 | h3
  · simp only [protocol, stage, h3, reduceIte]
    exact mul_pos (hri _ _) (ha _ _ _ _)
  · simp only [protocol, stage, h3, reduceIte]
    exact mul_pos
      (ProbDist.bind_pos _ _ (fun o => hs _ o) (fun o r' => hu o _ r') _) (hei _ _)
  · simp only [protocol, stage, h3]
    exact mul_pos (hri _ _) (hr _ _)

/-- Expected reward of the action the register actually executes, read from the
same evolving law as every balance above. -/
noncomputable def performance (n : ℕ) : ℝ :=
  ∑ z, (G.law n).p z * G.reward z.1 (G.readout z.2.1)

/-- The mass recursion of the composed run. -/
theorem law_succ_apply (n : ℕ) (z : W × (R × Env)) :
    (G.law (n + 1)).p z =
      ∑ s, (G.law n).p (z.1, s) * (G.stage n z.1 s).p z.2 :=
  G.protocol.law_succ_apply n z

end ContinuingAgent

end PhysicsOfConsciousness
