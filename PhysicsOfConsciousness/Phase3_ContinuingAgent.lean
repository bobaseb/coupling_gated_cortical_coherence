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

`energyTransfer`, `sum_energyTransfer` and `reported_heat_eq` account for an
explicitly modelled subsystem of the same protocol: the stage transfers of a
declared bath energy sum to that bath's endpoint gain, with no positive support
and no thermal identification, and a reported heat ledger differs from that gain
by the transfer it omits. `Examples/RegisterBath.lean` runs them on reversible
register/bath gates, where neither positivity nor local detailed balance holds.

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

`PathwiseStore` is the store the other way round: the reading is a *coordinate
of the state*, so `Solvent` is a claim about the states the protocol reaches
rather than about an expectation over them. `solvent_of_funded` derives it from
a stagewise funding condition, with no positivity anywhere — deterministic gates
and zero masses are admitted — and `mean_balance_eq` recovers the expected
ledger from `sum_energyTransfer`, so `totalDraw_le_of_solvent` refines
`ContinuingProcess` one way only. `solvent_forall_of_replenished` and
`horizon_le_of_net_cost` are the sufficient and necessary fences on sustained
operation. `Examples/PathwiseStore.lean` exhibits a store whose expected
allowance never runs out and which a realized path overdraws, and a
spend-and-recharge cycle solvent at every horizon whose cumulative draw exceeds
any allowance.

`SourceLedgered` identifies that supply with the loss of a source coordinate
on the same transitions. `withSource` adds its energy to the store's reading,
so internal replenishment cancels. `totalDraw_le_initial_resources` and
`horizon_le_of_finite_source` bound work and positive-cost horizons by the
initial combined resources. `Examples/FiniteSupply.lean` discharges these
identities with energy-conserving gates on a source, buffer and load: available
energy does not guarantee delivery, and the unbounded charger cannot have a
nonnegative finite source satisfying the identity.

What this supplies is the bookkeeping of a continuing agent: one law, actual
influence of the register on the world and an executed reset preparing later
episodes. The finite source is a separate witness, not the supply of those
particular learning channels. Initial-law preparation, an externally refuelled
source, readout/actuator fabrication and a separate observation-memory
implementation are supplied or outside the model. The composite learning
channel is assigned local detailed balance as a physical input. Neither
optimal-policy convergence nor cortical identification follows.
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

/-- Transfer into the subsystem whose energy is `E`, on an actual transition.
For a bath coordinate this is its energy gain. Calling that gain heat assumes
the bath has no separately unaccounted work port; no thermal law is inferred. -/
noncomputable def energyTransfer (_P : FiniteProtocol X S) (E : X × S → ℝ)
    (x : X) (s t : S) : ℝ := E (x, t) - E (x, s)

/-- An explicit bath's energy ledger follows from the same evolving law: its
stage transfers sum to its endpoint energy gain. This allows deterministic
gates and zero masses and asserts no entropy/temperature identification. -/
theorem sum_energyTransfer (E : X × S → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (P.step k).meanHeat (P.energyTransfer E)) =
      (∑ z, (P.law N).p z * E z) - (∑ z, P.initial.p z * E z) := by
  have h := P.sum_first_law E (fun _ _ _ _ => 0) N
  simpa [protocolWork, energyTransfer, FiniteFeedbackStep.meanHeat] using h

/-- A reported heat ledger differs from the explicit bath's energy gain by
the expected transfer it miscounts. Equality requires this correction to
vanish; a logical register update alone supplies no such identification. -/
theorem reported_heat_eq (E : X × S → ℝ) (q : ℕ → X → S → S → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (P.step k).meanHeat (q k)) =
      (∑ z, (P.law N).p z * E z) - (∑ z, P.initial.p z * E z) +
        ∑ k ∈ Finset.range N,
          (P.step k).meanHeat (fun x s t => q k x s t - P.energyTransfer E x s t) := by
  have hd (k : ℕ) :
      (P.step k).meanHeat (fun x s t => q k x s t - P.energyTransfer E x s t) =
        (P.step k).meanHeat (q k) - (P.step k).meanHeat (P.energyTransfer E) := by
    simp only [FiniteFeedbackStep.meanHeat, mul_sub, Finset.sum_sub_distrib]
  simp_rw [hd]
  rw [Finset.sum_sub_distrib, P.sum_energyTransfer E N]
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

/-! ## Reaching a state at all -/

namespace FiniteProtocol

variable {X S : Type*} [Fintype X] [Fintype S] (P : FiniteProtocol X S)

/-- The states the protocol can actually be in after `n` stages. Everything
below quantifies over these rather than over the type, so a statement about a
store's reading is a statement about the trajectories the protocol has. -/
def Reachable (n : ℕ) (z : X × S) : Prop := 0 < (P.law n).p z

/-- Some state is always reached: the law is normalized. -/
theorem exists_reachable (n : ℕ) : ∃ z, P.Reachable n z := by
  have hsum : ∑ z, (P.law n).p z ≠ 0 := by rw [(P.law n).sum_one]; norm_num
  obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨z, lt_of_le_of_ne ((P.law n).nonneg z) (Ne.symm hz)⟩

/-- Every state the protocol reaches was reached from one it had already
reached, by a transition the stage actually executes. The parameter is fixed,
so the predecessor differs only in the system coordinate. -/
theorem exists_pred_of_reachable (n : ℕ) (x : X) (t : S)
    (h : P.Reachable (n + 1) (x, t)) :
    ∃ s, P.Reachable n (x, s) ∧ 0 < (P.stage n x s).p t := by
  have hsum : ∑ s, (P.law n).p (x, s) * (P.stage n x s).p t ≠ 0 := by
    rw [← P.law_succ_apply n (x, t)]
    exact ne_of_gt h
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨s, lt_of_le_of_ne ((P.law n).nonneg (x, s)) (Ne.symm (left_ne_zero_of_mul hs)),
    lt_of_le_of_ne ((P.stage n x s).nonneg t) (Ne.symm (right_ne_zero_of_mul hs))⟩

end FiniteProtocol

/-! ## A store carried on the trajectory -/

/-- A finite protocol whose state carries the reading of its own work store,
together with the work each executed transition draws from that store and the
work a declared supply delivers to it.

`balance` is a coordinate of the state, which is what makes this a pathwise
account: `Solvent` below is a statement about the states the protocol reaches,
not about an expectation over them. The supply is declared exactly as
`ContinuingProcess.stored` is; nothing here derives a power source, and the
draw need not be the work of any particular thermodynamic model. -/
structure PathwiseStore (X S : Type*) [Fintype X] [Fintype S] where
  /-- The operations actually executed. -/
  protocol : FiniteProtocol X S
  /-- The store's reading, a coordinate of the state the protocol evolves. -/
  balance : S → ℝ
  /-- Work drawn from the store on an executed transition of a stage. -/
  draw : ℕ → X → S → S → ℝ
  /-- Work delivered to the store on that same transition: replenishment. -/
  supply : ℕ → X → S → S → ℝ

namespace PathwiseStore

variable {X S : Type*} [Fintype X] [Fintype S] (B : PathwiseStore X S)

/-- **The reading is the ledger.** On every transition the protocol can
actually execute, the store's reading falls by the work drawn and rises by the
work supplied. Off the support nothing is required: a transition that does not
happen has no cost to record. -/
def Ledgered : Prop :=
  ∀ n x s t, B.protocol.Reachable n (x, s) → 0 < (B.protocol.stage n x s).p t →
    B.balance t = B.balance s - B.draw n x s t + B.supply n x s t

/-- Every transition stage `n` can execute is covered: the draw does not exceed
what the store holds plus what arrives with that transition. -/
def Funded (n : ℕ) : Prop :=
  ∀ x s t, B.protocol.Reachable n (x, s) → 0 < (B.protocol.stage n x s).p t →
    B.draw n x s t ≤ B.balance s + B.supply n x s t

/-- No state the protocol reaches up to `N` has a negative reading. This is the
pathwise claim `ContinuingProcess.Sustains` does not make. -/
def Solvent (N : ℕ) : Prop :=
  ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → 0 ≤ B.balance z.2

/-- Work drawn over the first `N` stages, in expectation over the actual paths. -/
noncomputable def totalDraw (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (B.protocol.step k).meanHeat (B.draw k)

/-- Work supplied over those same stages, in expectation over the actual paths. -/
noncomputable def totalSupply (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (B.protocol.step k).meanHeat (B.supply k)

/-- The mean reading after `n` stages. -/
noncomputable def meanBalance (n : ℕ) : ℝ :=
  ∑ z, (B.protocol.law n).p z * B.balance z.2

theorem solvent_of_le {M N : ℕ} (h : B.Solvent N) (hMN : M ≤ N) : B.Solvent M :=
  fun k hk => h k (hk.trans hMN)

/-- One stage of solvency. A funded stage cannot take a reachable state with a
nonnegative reading to a reachable state with a negative one. -/
theorem solvent_succ (hl : B.Ledgered) (N : ℕ) (hs : B.Solvent N)
    (hf : B.Funded N) : B.Solvent (N + 1) := by
  intro k hk z hz
  rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk' | rfl
  · exact hs k (Nat.lt_succ_iff.1 hk') z hz
  · obtain ⟨s, hsr, hst⟩ := B.protocol.exists_pred_of_reachable N z.1 z.2 hz
    have hb := hl N z.1 s z.2 hsr hst
    have hfd := hf z.1 s z.2 hsr hst
    rw [hb]
    linarith

/-- **Pathwise solvency.** A ledgered protocol that starts solvent and funds
every stage never overdraws its store on any trajectory it has. No positivity
is used: deterministic gates and zero masses are admitted, and the draw may be
random. -/
theorem solvent_of_funded (hl : B.Ledgered)
    (h0 : ∀ z, B.protocol.Reachable 0 z → 0 ≤ B.balance z.2)
    (hf : ∀ k, B.Funded k) (N : ℕ) : B.Solvent N := by
  induction N with
  | zero => intro k hk z hz; exact h0 z (Nat.le_zero.1 hk ▸ hz)
  | succ N ih => exact B.solvent_succ hl N ih (hf N)

/-- Expectations are taken over the executed paths, so two observables agreeing
on the transitions a stage can make have the same mean. -/
theorem _root_.PhysicsOfConsciousness.FiniteFeedbackStep.meanHeat_congr_support
    {X S : Type*} [Fintype X] [Fintype S] (M : FiniteFeedbackStep X S)
    {q q' : X → S → S → ℝ}
    (h : ∀ x s t, 0 < M.initial.p (x, s) → 0 < (M.transition x s).p t →
      q x s t = q' x s t) : M.meanHeat q = M.meanHeat q' := by
  unfold FiniteFeedbackStep.meanHeat
  refine Finset.sum_congr rfl fun z _ => ?_
  rcases eq_or_lt_of_le (M.forward.nonneg z) with hz | hz
  · rw [← hz, zero_mul, zero_mul]
  · have hprod : 0 < M.initial.p (z.1, z.2.1) * (M.transition z.1 z.2.1).p z.2.2 := hz
    have h1 : 0 < M.initial.p (z.1, z.2.1) := by
      rcases eq_or_lt_of_le (M.initial.nonneg (z.1, z.2.1)) with h1 | h1
      · rw [← h1, zero_mul] at hprod; exact absurd hprod (lt_irrefl 0)
      · exact h1
    have h2 : 0 < (M.transition z.1 z.2.1).p z.2.2 := by
      rcases eq_or_lt_of_le ((M.transition z.1 z.2.1).nonneg z.2.2) with h2 | h2
      · rw [← h2, mul_zero] at hprod; exact absurd hprod (lt_irrefl 0)
      · exact h2
    rw [h z.1 z.2.1 z.2.2 h1 h2]

/-- **The expected ledger is a consequence of the pathwise one.** The mean
reading falls by the work drawn and rises by the work supplied. This is the
generic bath identity applied to the store's own coordinate, not a second
calculation. -/
theorem mean_balance_eq (hl : B.Ledgered) (N : ℕ) :
    B.meanBalance N = B.meanBalance 0 - B.totalDraw N + B.totalSupply N := by
  have hE := B.protocol.sum_energyTransfer (fun z => B.balance z.2) N
  have hstage (k : ℕ) :
      (B.protocol.step k).meanHeat
          (B.protocol.energyTransfer fun z => B.balance z.2) =
        (B.protocol.step k).meanHeat (B.supply k) -
          (B.protocol.step k).meanHeat (B.draw k) := by
    rw [(B.protocol.step k).meanHeat_congr_support
      (q' := fun x s t => B.supply k x s t - B.draw k x s t) ?_]
    · simp only [FiniteFeedbackStep.meanHeat, mul_sub, Finset.sum_sub_distrib]
    · intro x s t h1 h2
      have := hl k x s t h1 h2
      simp only [FiniteProtocol.energyTransfer]
      linarith
  simp only [hstage, Finset.sum_sub_distrib] at hE
  unfold meanBalance totalDraw totalSupply
  simp only [FiniteProtocol.law_zero] at hE ⊢
  linarith

/-- A solvent run has a nonnegative mean reading: the states carrying negative
readings are exactly the ones it does not reach. -/
theorem meanBalance_nonneg_of_solvent (N : ℕ) (h : B.Solvent N) {k : ℕ} (hk : k ≤ N) :
    0 ≤ B.meanBalance k := by
  refine Finset.sum_nonneg fun z _ => ?_
  rcases eq_or_lt_of_le ((B.protocol.law k).nonneg z) with hz | hz
  · rw [← hz, zero_mul]
  · exact mul_nonneg hz.le (h k hk z hz)

/-- **The refinement, one way.** Pathwise solvency implies the expected bound
the mean ledger asserts. The converse is false: `Examples/PathwiseStore.lean`
exhibits a store whose expected allowance never runs out and whose realized
trajectory overdraws it. -/
theorem totalDraw_le_of_solvent (hl : B.Ledgered) (N : ℕ) (h : B.Solvent N) :
    B.totalDraw N ≤ B.meanBalance 0 + B.totalSupply N := by
  have hm := B.mean_balance_eq hl N
  have hn := B.meanBalance_nonneg_of_solvent N h le_rfl
  linarith

/-! ### What replenishment buys, and what it cannot -/

/-- **Sufficient.** A supply that covers each executed draw sustains every
horizon: the reading never falls, so no bound on cumulative work is needed. -/
theorem solvent_forall_of_replenished (hl : B.Ledgered)
    (h0 : ∀ z, B.protocol.Reachable 0 z → 0 ≤ B.balance z.2)
    (hr : ∀ n x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → B.draw n x s t ≤ B.supply n x s t)
    (N : ℕ) : B.Solvent N := by
  induction N with
  | zero => intro k hk z hz; exact h0 z (Nat.le_zero.1 hk ▸ hz)
  | succ N ih =>
    refine B.solvent_succ hl N ih fun x s t hsr hst => ?_
    have hb := ih N le_rfl (x, s) hsr
    have := hr N x s t hsr hst
    simp only at hb
    linarith

/-- The reading a protocol can still show after `N` stages, when each executed
transition before `N` draws at least `c` more than it supplies. The cost is
restricted to the run: a finite state space cannot sustain a uniformly
positive net draw at every natural-numbered stage. -/
theorem balance_le_of_net_cost (hl : B.Ledgered) (c b : ℝ)
    (hb : ∀ z, B.protocol.Reachable 0 z → B.balance z.2 ≤ b)
    (N : ℕ) (hc : ∀ n < N, ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → c ≤ B.draw n x s t - B.supply n x s t) :
    ∀ z, B.protocol.Reachable N z → B.balance z.2 ≤ b - N * c := by
  suffices ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → B.balance z.2 ≤ b - k * c from
    this N le_rfl
  intro k
  induction k with
  | zero => intro _ z hz; simpa using hb z hz
  | succ k ih =>
    intro hk z hz
    obtain ⟨s, hsr, hst⟩ := B.protocol.exists_pred_of_reachable k z.1 z.2 hz
    have hprev := ih ((Nat.le_succ k).trans hk) (z.1, s) hsr
    have hled := hl k z.1 s z.2 hsr hst
    have hcost := hc k (lt_of_lt_of_le (Nat.lt_succ_self k) hk) z.1 s z.2 hsr hst
    simp only at hprev
    push_cast
    rw [hled]
    linarith

/-- **Necessary.** If every executed transition before `N` draws at least
`c > 0` more than it supplies, a store that starts no higher than `b` sustains at most
`b / c` stages. This is the pathwise form of `ContinuingProcess.horizon_le_of_cost`,
and unlike that one it constrains each trajectory. Continuing operation
therefore requires a supply that keeps up; the model declares such a supply and
does not derive one. -/
theorem horizon_le_of_net_cost (hl : B.Ledgered) (c b : ℝ)
    (hb : ∀ z, B.protocol.Reachable 0 z → B.balance z.2 ≤ b)
    (N : ℕ) (hc : ∀ n < N, ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → c ≤ B.draw n x s t - B.supply n x s t)
    (h : B.Solvent N) : (N : ℝ) * c ≤ b := by
  obtain ⟨z, hz⟩ := B.protocol.exists_reachable N
  have h1 := B.balance_le_of_net_cost hl c b hb N hc z hz
  have h2 := h N le_rfl z hz
  linarith

/-! ### Closing the replenishment boundary with a finite source -/

/-- The source's usable energy falls by exactly what it supplies to the store,
on the transitions this protocol executes. This is a physical identification
to check on a model, not a consequence of the store ledger. Signed supply
permits energy to return to the source. No preparation or external refuelling
is included. -/
def SourceLedgered (R : S → ℝ) : Prop :=
  ∀ n x s t, B.protocol.Reachable n (x, s) → 0 < (B.protocol.stage n x s).p t →
    R t = R s - B.supply n x s t

/-- Enlarge the resource boundary to include the source. Transfers between
source and store are internal, so this combined store has zero external supply.
Its ledger requires both constituent transfer identities. -/
noncomputable def withSource (R : S → ℝ) : PathwiseStore X S :=
  ⟨B.protocol, fun s => B.balance s + R s, B.draw, fun _ _ _ _ => 0⟩

/-- Adding the two pathwise ledgers cancels their internal supply. The source
identity is a hypothesis; no physical source is derived for an arbitrary store. -/
theorem withSource_ledgered (R : S → ℝ) (hb : B.Ledgered)
    (hr : B.SourceLedgered R) : (B.withSource R).Ledgered := by
  intro n x s t hs ht
  have h1 := hb n x s t hs ht
  have h2 := hr n x s t hs ht
  change B.balance t + R t = B.balance s + R s - B.draw n x s t + 0
  linarith

/-- The same source's loss pays for the cumulative supply. This is first-law
bookkeeping on the actual law, with no entropy or work-extraction efficiency
claim. In particular, returned energy contributes negative supply. -/
theorem totalSupply_eq_source_loss (R : S → ℝ) (hr : B.SourceLedgered R) (N : ℕ) :
    B.totalSupply N = (∑ z, (B.protocol.law 0).p z * R z.2) -
      ∑ z, (B.protocol.law N).p z * R z.2 := by
  let source : PathwiseStore X S :=
    ⟨B.protocol, R, B.supply, fun _ _ _ _ => 0⟩
  have hl : source.Ledgered := by
    intro n x s t hs ht
    simpa only [source, add_zero] using hr n x s t hs ht
  have hm := source.mean_balance_eq hl N
  have hz : source.totalSupply N = 0 := by
    simp [totalSupply, source, FiniteFeedbackStep.meanHeat]
  rw [hz, add_zero] at hm
  change (∑ z, (B.protocol.law N).p z * R z.2) =
    (∑ z, (B.protocol.law 0).p z * R z.2) - B.totalSupply N at hm
  linarith

/-- Nonnegative store and source readings imply nonnegative combined resources.
This does not imply that energy in the source can reach a load when requested. -/
theorem withSource_solvent (R : S → ℝ) (N : ℕ) (hb : B.Solvent N)
    (hr : ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → 0 ≤ R z.2) :
    (B.withSource R).Solvent N := by
  intro k hk z hz
  exact add_nonneg (hb k hk z hz) (hr k hk z hz)

/-- **A finite source is part of the budget.** When both resources stay
nonnegative, all drawn work is bounded by their initial mean sum. This
requires the source's actual loss to equal the supply; it gives neither
delivery on demand nor a preparation mechanism for the initial resources. -/
theorem totalDraw_le_initial_resources (R : S → ℝ) (hb : B.Ledgered)
    (hr : B.SourceLedgered R) (N : ℕ) (hs : B.Solvent N)
    (hR : ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → 0 ≤ R z.2) :
    B.totalDraw N ≤ B.meanBalance 0 + ∑ z, (B.protocol.law 0).p z * R z.2 := by
  have h := (B.withSource R).totalDraw_le_of_solvent
    (B.withSource_ledgered R hb hr) N (B.withSource_solvent R N hs hR)
  simpa [withSource, totalDraw, totalSupply, meanBalance,
    FiniteFeedbackStep.meanHeat, mul_add, Finset.sum_add_distrib] using h

/-- **Moving the boundary does not create a perpetual source.** A lower bound
`c` on every executed draw before `N` and an upper bound `b` on the initial combined
resources give `N*c ≤ b`. The useful horizon bound needs `c > 0`; idling or
returning work need not exhaust a finite source. No positivity of masses is
assumed, and energy delivery remains a separate dynamical question. -/
theorem horizon_le_of_finite_source (R : S → ℝ) (hb : B.Ledgered)
    (hr : B.SourceLedgered R) (c b : ℝ)
    (h0 : ∀ z, B.protocol.Reachable 0 z → B.balance z.2 + R z.2 ≤ b)
    (N : ℕ) (hc : ∀ n < N, ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → c ≤ B.draw n x s t)
    (hs : B.Solvent N)
    (hR : ∀ k ≤ N, ∀ z, B.protocol.Reachable k z → 0 ≤ R z.2) :
    (N : ℝ) * c ≤ b := by
  apply (B.withSource R).horizon_le_of_net_cost
    (B.withSource_ledgered R hb hr) c b h0 N _ (B.withSource_solvent R N hs hR)
  intro n hn x s t hs ht
  simpa only [withSource, sub_zero] using hc n hn x s t hs ht

end PathwiseStore

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
