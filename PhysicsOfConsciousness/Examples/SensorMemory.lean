import PhysicsOfConsciousness.Phase3_SensorMemory
import PhysicsOfConsciousness.Examples.ContinuingAgent

/-!
# A sensor memory on bits, and the recurring cost of clearing it

An agent with an unknown rewarding action, a task flag its action sets, a
measurement that writes that flag into a memory bit, a register updated from the
memory alone, and a clearing operation that drives the memory toward a standard
state. Every primitive channel mass is `1/4` or `3/4`, so every heat is a
rational multiple of `log 3`.

The recurring cost is established without computing the joint law at all: the
memory's marginal after a measurement is a mixture of measurement outputs over a
world marginal that is itself a mixture of actuator outputs, and both mixtures
are bounded by the channels' own masses. What the agent has learned moves the
memory's marginal inside that interval and cannot leave it, so the floor holds
at every cycle.

The negative controls separate four things the identity would otherwise be
confused with: a blind measurement pays the same, drifting instead of clearing
pays nothing and forgets nothing, a memory already standard is free, and a
memory more ordered than the standard state draws heat out of the reservoir.
-/

namespace PhysicsOfConsciousness

namespace Examples.Sensor

/-! ## The channels -/

/-- The register's value is the action executed: it decodes no task value. -/
def readout : Bool → Bool := id

/-- The declared initial uncertainty: the rewarding action is unknown, the
register has no preference, and the memory and the flag are uniform. -/
noncomputable def prior : ProbDist (Bool × (Bool × (Bool × Bool))) where
  p _ := 1 / 16
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The actuator overwrites the flag: the rewarding action sets it three times
in four, the other action clears it three times in four. -/
noncomputable def actuate (w a : Bool) (_e : Bool) : ProbDist Bool where
  p e' := if e' = (a == w) then 3 / 4 else 1 / 4
  nonneg e' := by cases e' <;> cases a <;> cases w <;> norm_num
  sum_one := by cases a <;> cases w <;> norm_num [Fintype.sum_bool]

/-- The measurement: the memory is written from the flag the action left, right
three times in four. It does not see the unknown parameter, and it overwrites
whatever the memory held. -/
noncomputable def record (e : Bool) (_m : Bool) : ProbDist Bool where
  p m' := if m' = e then 3 / 4 else 1 / 4
  nonneg m' := by cases m' <;> cases e <;> norm_num
  sum_one := by cases e <;> norm_num [Fintype.sum_bool]

/-- Win-stay, lose-shift, driven by the memory alone. -/
noncomputable def update (m r : Bool) : ProbDist Bool where
  p r' :=
    if r' = r then (if m then 3 / 4 else 1 / 4) else (if m then 1 / 4 else 3 / 4)
  nonneg r' := by cases r' <;> cases r <;> cases m <;> norm_num
  sum_one := by cases r <;> cases m <;> norm_num [Fintype.sum_bool]

/-- The standard state the clearing operation drives toward. An exact erasure
would leave the reverse path no probability, so the memory is driven three
quarters of the way rather than all of it. -/
noncomputable def standard : ProbDist Bool where
  p b := if b then 1 / 4 else 3 / 4
  nonneg b := by cases b <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

theorem standard_pos (b : Bool) : 0 < standard.p b := by
  cases b <;> norm_num [standard]

@[simp] theorem standard_true : standard.p true = 1 / 4 := rfl

@[simp] theorem standard_false : standard.p false = 3 / 4 := rfl

/-- Clearing: the memory is driven to the standard state whatever it held. -/
noncomputable def erase (_m : Bool) : ProbDist Bool := standard

/-- Preparing the next episode's world, by the same imperfect relaxation. -/
noncomputable def reset (_e : Bool) : ProbDist Bool := standard

/-- The drift of whichever coordinate is not being driven. It is symmetric, so
it dissipates nothing, and it is positive, so no path is unreachable. -/
noncomputable def drift (x : Bool) : ProbDist Bool where
  p x' := if x' = x then 3 / 4 else 1 / 4
  nonneg x' := by cases x' <;> cases x <;> norm_num
  sum_one := by cases x <;> norm_num [Fintype.sum_bool]

/-- The evaluation criterion. It appears in no channel. -/
def reward (w a : Bool) : ℝ := if a = w then 1 else 0

/-- The agent: act, measure, learn, clear, repeat. -/
noncomputable def agent : MemoryAgent Bool Bool Bool Bool Bool :=
  ⟨prior, readout, actuate, record, update, erase, reset, drift, drift, drift, reward⟩

theorem positive : agent.Positive := by
  refine ⟨fun z => by norm_num [agent, prior], fun w a e e' => ?_, fun e m m' => ?_,
    fun m r r' => ?_, fun m m' => ?_, fun e e' => ?_, fun r r' => ?_, fun m m' => ?_,
    fun e e' => ?_⟩
  · show 0 < (actuate w a e).p e'
    cases e' <;> cases a <;> cases w <;> norm_num [actuate]
  · show 0 < (record e m).p m'
    cases m' <;> cases e <;> norm_num [record]
  · show 0 < (update m r).p r'
    cases r' <;> cases r <;> cases m <;> norm_num [update]
  · exact standard_pos m'
  · exact standard_pos e'
  · show 0 < (drift r).p r'
    cases r' <;> cases r <;> norm_num [drift]
  · show 0 < (drift m).p m'
    cases m' <;> cases m <;> norm_num [drift]
  · show 0 < (drift e).p e'
    cases e' <;> cases e <;> norm_num [drift]

theorem protocol_positive : agent.protocol.Positive := agent.protocol_positive positive

/-- The whole run is charged by the existing machinery: the joint entropy the
four operations remove is bounded by their cumulative heat. -/
theorem entropy_budget (N : ℕ) :
    (1 : ℝ) * (shannon_entropy (agent.law 0).p - shannon_entropy (agent.law N).p) ≤
      ∑ k ∈ Finset.range N,
        (agent.protocol.step k).meanHeat (agent.protocol.stageHeat 1 k) :=
  agent.protocol.cumulative_entropy_budget protocol_positive 1 one_pos _
    (agent.protocol.local_balance 1) N

/-! ## What clearing costs, on any memory law -/

/-- **The erasure's cost is fixed by the memory's marginal.** It is positive
exactly when the memory is less ordered than the standard state, and what the
memory is *about* does not enter. -/
theorem erase_cost (μ : ProbDist Bool) :
    memoryHeat 1 μ erase = (3 / 4 - μ.p false) * Real.log 3 := by
  have hsum : μ.p true + μ.p false = 1 := by
    have h := μ.sum_one
    rwa [Fintype.sum_bool] at h
  have hlog13 : Real.log ((1 : ℝ) / 3) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  show (∑ m, ∑ m', μ.p m * (erase m).p m' *
    (1 * Real.log ((erase m).p m' / (erase m').p m))) = _
  have he : ∀ m b : Bool, (erase m).p b = standard.p b := fun _ _ => rfl
  simp only [Fintype.sum_bool, he, standard]
  norm_num [hlog13]
  have hT : μ.p true = 1 - μ.p false := by linarith
  rw [hT]
  ring

/-- A symmetric drift in place of the erasure dissipates nothing, on any law. -/
theorem drift_cost (μ : ProbDist Bool) : memoryHeat 1 μ drift = 0 := by
  show (∑ m, ∑ m', μ.p m * (drift m).p m' *
    (1 * Real.log ((drift m).p m' / (drift m').p m))) = _
  simp only [Fintype.sum_bool, drift]
  norm_num

/-- A memory already at the standard state is free to clear. -/
theorem standard_free : memoryHeat 1 standard erase = 0 :=
  memoryHeat_self 1 standard standard_pos

/-- **Clearing is not dissipative by construction.** A memory more ordered than
the standard state draws heat out of the reservoir instead of delivering it. -/
theorem over_ordered_absorbs :
    memoryHeat 1 (ProbDist.dirac false) erase = -(1 / 4) * Real.log 3 := by
  rw [erase_cost]
  norm_num [ProbDist.dirac]

/-! ## The memory's marginal along the run -/

@[simp] theorem agent_erase : agent.erase = erase := rfl

@[simp] theorem agent_memoryIdle : agent.memoryIdle = drift := rfl

@[simp] theorem agent_actuate : agent.actuate = actuate := rfl

@[simp] theorem agent_readout : agent.readout = readout := rfl

/-- The mass the memory puts on a set flag after `n` operations. -/
noncomputable def memMass (n : ℕ) : ℝ := (agent.memoryLaw n).p true

/-- The mass the world puts on a set flag after `n` operations. -/
noncomputable def envMass (n : ℕ) : ℝ := (agent.envLaw n).p true

theorem memMass_sum (n : ℕ) :
    memMass n + (agent.memoryLaw n).p false = 1 := by
  have h := (agent.memoryLaw n).sum_one
  rwa [Fintype.sum_bool] at h

theorem envMass_sum (n : ℕ) : envMass n + (agent.envLaw n).p false = 1 := by
  have h := (agent.envLaw n).sum_one
  rwa [Fintype.sum_bool] at h

/-- Drifting moves the memory's mass halfway toward uniform. -/
theorem memMass_idle (n : ℕ) (h : n % 4 = 0 ∨ n % 4 = 2) :
    memMass (n + 1) = 1 / 4 + memMass n / 2 := by
  have hs := memMass_sum n
  have h1 := agent.memoryLaw_idle n h true
  unfold memMass at hs ⊢
  rw [h1]
  simp only [Fintype.sum_bool, agent_memoryIdle, drift]
  norm_num
  linarith

/-- Measuring replaces the memory's mass by the world's, seen through the
measurement channel. -/
theorem memMass_record (n : ℕ) (h : n % 4 = 1) :
    memMass (n + 1) = 1 / 4 + envMass n / 2 := by
  have hs := envMass_sum n
  have h1 := agent.memoryLaw_record n h (fun e => record e true) (fun _ _ => rfl) true
  unfold memMass envMass at hs ⊢
  rw [h1]
  simp only [Fintype.sum_bool, record]
  norm_num
  linarith

/-- **The world is never certain.** Whatever the agent has learned, the flag it
leaves is a mixture of the actuator's two masses. -/
theorem envMass_act_bounds (n : ℕ) (h : n % 4 = 0) :
    1 / 4 ≤ envMass (n + 1) ∧ envMass (n + 1) ≤ 3 / 4 := by
  constructor
  · refine agent.le_envLaw_act n h true (1 / 4) fun w b e => ?_
    show (1 : ℝ) / 4 ≤ (actuate w b e).p true
    cases b <;> cases w <;> norm_num [actuate]
  · refine agent.envLaw_act_le n h true (3 / 4) fun w a e => ?_
    show (actuate w a e).p true ≤ 3 / 4
    cases a <;> cases w <;> norm_num [actuate]

/-- **So the memory is never certain either**, at any cycle. -/
theorem memMass_clear_bounds (m : ℕ) :
    7 / 16 ≤ memMass (4 * m + 3) ∧ memMass (4 * m + 3) ≤ 9 / 16 := by
  obtain ⟨hlo, hhi⟩ := envMass_act_bounds (4 * m) (by omega)
  have hr : memMass (4 * m + 2) = 1 / 4 + envMass (4 * m + 1) / 2 :=
    memMass_record (4 * m + 1) (by omega)
  have hi : memMass (4 * m + 3) = 1 / 4 + memMass (4 * m + 2) / 2 :=
    memMass_idle (4 * m + 2) (Or.inr (by omega))
  constructor <;> linarith

/-! ## The recurring cost of clearing -/

/-- **A positive cost at every cycle, independent of what has been learned.**
The agent's own trajectories never bring the memory closer to the standard
state than this, so no amount of learning makes the measurement free. -/
theorem clear_cost_floor (m : ℕ) :
    3 / 16 * Real.log 3 ≤
      (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) := by
  rw [agent.clear_memoryHeat 1 (4 * m + 3) (by omega), agent_erase, erase_cost]
  have hs := memMass_sum (4 * m + 3)
  obtain ⟨hlo, -⟩ := memMass_clear_bounds m
  have hle : (3 : ℝ) / 16 ≤ 3 / 4 - (agent.memoryLaw (4 * m + 3)).p false := by
    unfold memMass at hs hlo; linarith
  exact mul_le_mul_of_nonneg_right hle (Real.log_nonneg (by norm_num))

/-- The same argument bounds the cost above: clearing an uncertain memory is not
arbitrarily expensive either. -/
theorem clear_cost_ceiling (m : ℕ) :
    (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) ≤
      5 / 16 * Real.log 3 := by
  rw [agent.clear_memoryHeat 1 (4 * m + 3) (by omega), agent_erase, erase_cost]
  have hs := memMass_sum (4 * m + 3)
  obtain ⟨-, hhi⟩ := memMass_clear_bounds m
  have hle : (3 : ℝ) / 4 - (agent.memoryLaw (4 * m + 3)).p false ≤ 5 / 16 := by
    unfold memMass at hs hhi; linarith
  exact mul_le_mul_of_nonneg_right hle (Real.log_nonneg (by norm_num))

/-! ## The first cycle, exactly -/

theorem envMass_one : envMass 1 = 1 / 2 := by
  have h := agent.envLaw_act 0 (by norm_num) true
  have hl : ∀ z, (agent.law 0).p z = 1 / 16 := fun _ => rfl
  unfold envMass
  rw [h]
  simp only [hl, Fintype.sum_prod_type, Fintype.sum_bool, agent_actuate, agent_readout]
  norm_num [actuate, readout]

theorem memMass_two : memMass 2 = 1 / 2 := by
  rw [memMass_record 1 (by norm_num), envMass_one]
  norm_num

theorem memMass_three : memMass 3 = 1 / 2 := by
  rw [memMass_idle 2 (Or.inr (by norm_num)), memMass_two]
  norm_num

theorem memoryLaw_three_apply (b : Bool) : (agent.memoryLaw 3).p b = 1 / 2 := by
  have h3 := memMass_three
  have hs := memMass_sum 3
  unfold memMass at h3 hs
  cases b
  · linarith
  · exact h3

/-- **The whole cost of the first clearing.** -/
theorem first_clear_cost :
    (agent.protocol.step 3).meanHeat (agent.eraseHeatObs 1) = 1 / 4 * Real.log 3 := by
  rw [agent.clear_memoryHeat 1 3 (by norm_num), agent_erase, erase_cost,
    memoryLaw_three_apply false]
  norm_num

/-- **Its Landauer term**: the entropy the clearing removes from the memory. -/
theorem first_entropy_drop :
    shannon_entropy (agent.memoryLaw 3).p - shannon_entropy standard.p =
      3 / 4 * Real.log 3 - Real.log 2 := by
  have l2 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have l4 : Real.log ((1 : ℝ) / 4) = -(2 * Real.log 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have l34 : Real.log ((3 : ℝ) / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  unfold shannon_entropy
  simp only [Fintype.sum_bool, memoryLaw_three_apply, standard_true, standard_false]
  rw [l2, l4, l34]
  ring

/-- The clearing really does remove entropy: `16 < 27`, and nothing numerical. -/
theorem first_entropy_drop_pos :
    0 < shannon_entropy (agent.memoryLaw 3).p - shannon_entropy standard.p := by
  rw [first_entropy_drop]
  have h16 : Real.log 16 < Real.log 27 := by
    refine Real.log_lt_log (by norm_num) (by norm_num)
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, show (27 : ℝ) = 3 ^ 3 by norm_num,
    Real.log_pow, Real.log_pow] at h16
  push_cast at h16
  linarith

/-- **Its irreversibility term**: how far the memory was from the state the one
fixed erasure drives it to. -/
theorem first_relative_entropy :
    KL (agent.memoryLaw 3) standard = 1 / 2 * Real.log (4 / 3) := by
  have e43 : Real.log ((4 : ℝ) / 3) = Real.log 2 + Real.log (2 / 3) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  unfold KL
  simp only [Fintype.sum_bool, memoryLaw_three_apply, standard_true, standard_false]
  rw [show (1 : ℝ) / 2 / (1 / 4) = 2 by norm_num,
    show (1 : ℝ) / 2 / (3 / 4) = 2 / 3 by norm_num, e43]
  ring

/-- The two terms are the whole cost: the identity, on the agent's own paths. -/
theorem first_cost_decomposes :
    (agent.protocol.step 3).meanHeat (agent.eraseHeatObs 1) =
      1 * (shannon_entropy (agent.memoryLaw 3).p -
        shannon_entropy (agent.memoryLaw 4).p) + 1 * KL (agent.memoryLaw 3) standard :=
  agent.clear_memoryHeat_const 1 standard standard_pos rfl 3 (by norm_num)

/-- Clearing forgets its input: the memory's law afterwards is the standard
state, whatever the measurement wrote. -/
theorem erase_memory_forgets (b : Bool) : (agent.memoryLaw 4).p b = standard.p b := by
  rw [agent.memoryLaw_clear 3 (by norm_num) b]
  have he : ∀ m : Bool, (agent.erase m).p b = standard.p b := fun _ => rfl
  simp only [he, ← Finset.sum_mul, (agent.memoryLaw 3).sum_one, one_mul]

/-! ## Negative controls -/

/-- A measurement that ignores the world. -/
noncomputable def coin : ProbDist Bool where
  p _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

noncomputable def blindRecord (_e _m : Bool) : ProbDist Bool := coin

/-- The same agent with a blind measurement, and the same clearing operation. -/
noncomputable def blind : MemoryAgent Bool Bool Bool Bool Bool :=
  ⟨prior, readout, actuate, blindRecord, update, erase, reset, drift, drift, drift,
    reward⟩

@[simp] theorem blind_erase : blind.erase = erase := rfl

/-- The informative measurement depends on the world; the blind one does not. -/
theorem record_not_constant :
    (agent.record true false).p true ≠ (agent.record false false).p true := by
  show (record true false).p true ≠ (record false false).p true
  norm_num [record]

theorem blindRecord_constant (e e' m m' : Bool) :
    blind.record e m = blind.record e' m' := rfl

theorem blind_mem_two : (blind.memoryLaw 2).p true = 1 / 2 := by
  rw [blind.memoryLaw_record 1 (by norm_num) (fun _ => coin) (fun _ _ => rfl) true]
  show (∑ e, (blind.envLaw 1).p e * (1 / 2 : ℝ)) = 1 / 2
  rw [← Finset.sum_mul, (blind.envLaw 1).sum_one, one_mul]

theorem blind_mem_three (b : Bool) : (blind.memoryLaw 3).p b = 1 / 2 := by
  have hs : (blind.memoryLaw 2).p true + (blind.memoryLaw 2).p false = 1 := by
    have h := (blind.memoryLaw 2).sum_one
    rwa [Fintype.sum_bool] at h
  have h2 := blind_mem_two
  have key : ∀ c : Bool, (blind.memoryLaw 3).p c = 1 / 2 := by
    intro c
    rw [blind.memoryLaw_idle 2 (Or.inr (by norm_num)) c]
    have hd : ∀ m : Bool, (blind.memoryIdle m).p c = (drift m).p c := fun _ => rfl
    simp only [Fintype.sum_bool, hd, drift]
    cases c <;> · norm_num; linarith
  exact key b

/-- **Clearing an uninformative memory costs exactly the same.** The blind
agent records nothing about the world and pays the identical heat, because the
cost is set by the memory's marginal and not by what the memory is about. -/
theorem blind_same_cost :
    (blind.memoryLaw 3).p false = (agent.memoryLaw 3).p false ∧
      (blind.protocol.step 3).meanHeat (blind.eraseHeatObs 1) =
        (agent.protocol.step 3).meanHeat (agent.eraseHeatObs 1) := by
  refine ⟨by rw [blind_mem_three false, memoryLaw_three_apply false], ?_⟩
  rw [blind.clear_memoryHeat 1 3 (by norm_num), blind_erase, erase_cost,
    blind_mem_three false, first_clear_cost]
  norm_num

/-- The same agent with the clearing operation replaced by the idle drift. -/
noncomputable def idler : MemoryAgent Bool Bool Bool Bool Bool :=
  ⟨prior, readout, actuate, record, update, drift, reset, drift, drift, drift, reward⟩

@[simp] theorem idler_erase : idler.erase = drift := rfl

/-- **Drifting instead of clearing costs nothing** — and, by the identity, that
is exactly because it removes no entropy and is matched to no standard state. -/
theorem idle_clear_free :
    (idler.protocol.step 3).meanHeat (idler.eraseHeatObs 1) = 0 := by
  rw [idler.clear_memoryHeat 1 3 (by norm_num), idler_erase, drift_cost]

/-- **And it forgets nothing.** Where the erasure returns the standard state
whatever the measurement wrote, the drift carries the measurement forward into
the next episode. -/
theorem idle_memory_depends :
    (idler.memoryLaw 4).p true = 1 / 4 + (idler.memoryLaw 3).p true / 2 := by
  have hs : (idler.memoryLaw 3).p true + (idler.memoryLaw 3).p false = 1 := by
    have h := (idler.memoryLaw 3).sum_one
    rwa [Fintype.sum_bool] at h
  rw [idler.memoryLaw_clear 3 (by norm_num) true]
  simp only [Fintype.sum_bool, idler_erase, drift]
  norm_num
  linarith

/-- The fence of `learn_register_independent`, on this agent. -/
theorem learn_reads_memory_only (w w' r r' m e e' : Bool) :
    (∑ y, (agent.learnStage w (r, (m, e))).p (r', y)) =
      ∑ y, (agent.learnStage w' (r, (m, e'))).p (r', y) :=
  agent.learn_register_independent w w' r r' m e e'


/-! ## Retained regression specifications

These are the specifications of `tasks/sensor_memory.md`. They were written and
run before the declarations they name existed. -/

section Specifications

variable {W R M Env A : Type*} [Fintype W] [Fintype R] [Fintype M] [Fintype Env]
  [Fintype A]

/-- The exact cost of clearing: entropy removed plus relative entropy. -/
example (θ : ℝ) (μ ν : ProbDist M) (hν : ∀ m, 0 < ν.p m) :
    memoryHeat θ μ (fun _ => ν) =
      θ * (shannon_entropy μ.p - shannon_entropy ν.p) + θ * KL μ ν :=
  memoryHeat_const θ μ ν hν

/-- Landauer's inequality as the corollary, with the gap named. -/
example (θ : ℝ) (hθ : 0 ≤ θ) (μ ν : ProbDist M) (hν : ∀ m, 0 < ν.p m) :
    θ * (shannon_entropy μ.p - shannon_entropy ν.p) ≤ memoryHeat θ μ (fun _ => ν) :=
  memoryHeat_ge_entropy_drop θ hθ μ ν hν

/-- A memory already at the standard state is free to clear. -/
example (θ : ℝ) (ν : ProbDist M) (hν : ∀ m, 0 < ν.p m) :
    memoryHeat θ ν (fun _ => ν) = 0 :=
  memoryHeat_self θ ν hν

/-- The fence, as a theorem: the register's update reads the memory alone. -/
example (G : MemoryAgent W R M Env A) (w w' : W) (r r' : R) (m : M) (e e' : Env) :
    (∑ y, (G.learnStage w (r, (m, e))).p (r', y)) =
      ∑ y, (G.learnStage w' (r, (m, e'))).p (r', y) :=
  G.learn_register_independent w w' r r' m e e'

/-- Under the clear stage the memory's marginal evolves by the erasure alone. -/
example (G : MemoryAgent W R M Env A) (n : ℕ) (h : n % 4 = 3) (m' : M) :
    (G.memoryLaw (n + 1)).p m' = ∑ m, (G.memoryLaw n).p m * (G.erase m).p m' :=
  G.memoryLaw_clear n h m'

/-- Under the record stage it does not: the world's law enters. -/
example (G : MemoryAgent W R M Env A) (n : ℕ) (h : n % 4 = 1) (ν : Env → ProbDist M)
    (hrec : ∀ e m, G.record e m = ν e) (m' : M) :
    (G.memoryLaw (n + 1)).p m' = ∑ e, (G.envLaw n).p e * (ν e).p m' :=
  G.memoryLaw_record n h ν hrec m'

/-- The memory's share of the clear stage's heat is the erasure's own cost. -/
example (G : MemoryAgent W R M Env A) (θ : ℝ) (n : ℕ) (h : n % 4 = 3) :
    (G.protocol.step n).meanHeat (G.eraseHeatObs θ) =
      memoryHeat θ (G.memoryLaw n) G.erase :=
  G.clear_memoryHeat θ n h

/-- That share is a named part of the whole stage's heat. -/
example (G : MemoryAgent W R M Env A) (hG : G.Positive) (θ : ℝ) (n : ℕ)
    (h : n % 4 = 3) (x : W) (s t : R × (M × Env)) :
    G.protocol.stageHeat θ n x s t =
      G.registerHeatObs θ x s t + G.eraseHeatObs θ x s t + G.resetHeatObs θ x s t :=
  G.clear_stageHeat_eq hG θ n h x s t

/-- The identity on an agent's own executed paths. -/
example (G : MemoryAgent W R M Env A) (θ : ℝ) (ν : ProbDist M) (hν : ∀ m, 0 < ν.p m)
    (hc : G.erase = fun _ => ν) (n : ℕ) (h : n % 4 = 3) :
    (G.protocol.step n).meanHeat (G.eraseHeatObs θ) =
      θ * (shannon_entropy (G.memoryLaw n).p -
        shannon_entropy (G.memoryLaw (n + 1)).p) + θ * KL (G.memoryLaw n) ν :=
  G.clear_memoryHeat_const θ ν hν hc n h

end Specifications

example : agent.Positive := positive

example (N : ℕ) :
    (1 : ℝ) * (shannon_entropy (agent.law 0).p - shannon_entropy (agent.law N).p) ≤
      ∑ k ∈ Finset.range N,
        (agent.protocol.step k).meanHeat (agent.protocol.stageHeat 1 k) :=
  entropy_budget N

/-- The erasure's cost is fixed by the memory's marginal. -/
example (μ : ProbDist Bool) :
    memoryHeat 1 μ erase = (3 / 4 - μ.p false) * Real.log 3 :=
  erase_cost μ

/-- At every cycle, whatever has been learned. -/
example (m : ℕ) : 7 / 16 ≤ memMass (4 * m + 3) ∧ memMass (4 * m + 3) ≤ 9 / 16 :=
  memMass_clear_bounds m

/-- A positive recurring cost, independent of what the agent has learned. -/
example (m : ℕ) :
    3 / 16 * Real.log 3 ≤
      (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) :=
  clear_cost_floor m

example (m : ℕ) :
    (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) ≤
      5 / 16 * Real.log 3 :=
  clear_cost_ceiling m

/-- The first cycle exactly, and its two terms. -/
example : memMass 3 = 1 / 2 := memMass_three

example :
    (agent.protocol.step 3).meanHeat (agent.eraseHeatObs 1) = 1 / 4 * Real.log 3 :=
  first_clear_cost

example :
    shannon_entropy (agent.memoryLaw 3).p - shannon_entropy standard.p =
      3 / 4 * Real.log 3 - Real.log 2 :=
  first_entropy_drop

example : 0 < shannon_entropy (agent.memoryLaw 3).p - shannon_entropy standard.p :=
  first_entropy_drop_pos

example : KL (agent.memoryLaw 3) standard = 1 / 2 * Real.log (4 / 3) :=
  first_relative_entropy

example :
    (agent.protocol.step 3).meanHeat (agent.eraseHeatObs 1) =
      1 * (shannon_entropy (agent.memoryLaw 3).p -
        shannon_entropy (agent.memoryLaw 4).p) + 1 * KL (agent.memoryLaw 3) standard :=
  first_cost_decomposes

/-- Clearing forgets what the measurement wrote. -/
example (b : Bool) : (agent.memoryLaw 4).p b = standard.p b := erase_memory_forgets b

/-- Clearing an uninformative memory costs exactly the same. -/
example :
    (blind.memoryLaw 3).p false = (agent.memoryLaw 3).p false ∧
      (blind.protocol.step 3).meanHeat (blind.eraseHeatObs 1) =
        (agent.protocol.step 3).meanHeat (agent.eraseHeatObs 1) :=
  blind_same_cost

example :
    (agent.record true false).p true ≠ (agent.record false false).p true :=
  record_not_constant

example (e e' m m' : Bool) : blind.record e m = blind.record e' m' :=
  blindRecord_constant e e' m m'

/-- Letting the memory drift instead of clearing it costs nothing, and carries
the measurement into the next episode. -/
example : (idler.protocol.step 3).meanHeat (idler.eraseHeatObs 1) = 0 :=
  idle_clear_free

example :
    (idler.memoryLaw 4).p true = 1 / 4 + (idler.memoryLaw 3).p true / 2 :=
  idle_memory_depends

example : memoryHeat 1 standard erase = 0 := standard_free

/-- Clearing a memory more ordered than the standard state draws heat out of
the reservoir. -/
example : memoryHeat 1 (ProbDist.dirac false) erase = -(1 / 4) * Real.log 3 :=
  over_ordered_absorbs

example (w w' r r' m e e' : Bool) :
    (∑ y, (agent.learnStage w (r, (m, e))).p (r', y)) =
      ∑ y, (agent.learnStage w' (r, (m, e'))).p (r', y) :=
  learn_reads_memory_only w w' r r' m e e'


end Examples.Sensor

#print axioms memoryHeat_const
#print axioms memoryHeat_ge_entropy_drop
#print axioms memoryHeat_self
#print axioms MemoryAgent.learn_register_independent
#print axioms MemoryAgent.memoryLaw_clear
#print axioms MemoryAgent.memoryLaw_record
#print axioms MemoryAgent.clear_stageHeat_eq
#print axioms MemoryAgent.clear_memoryHeat
#print axioms MemoryAgent.clear_memoryHeat_const
#print axioms Examples.Sensor.erase_cost
#print axioms Examples.Sensor.clear_cost_floor
#print axioms Examples.Sensor.first_clear_cost
#print axioms Examples.Sensor.first_entropy_drop_pos
#print axioms Examples.Sensor.first_cost_decomposes
#print axioms Examples.Sensor.blind_same_cost
#print axioms Examples.Sensor.idle_clear_free
#print axioms Examples.Sensor.over_ordered_absorbs


end PhysicsOfConsciousness
