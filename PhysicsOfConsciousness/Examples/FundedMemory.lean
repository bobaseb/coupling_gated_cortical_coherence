import PhysicsOfConsciousness.Examples.SensorMemory

/-!
# The source that pays for clearing, and how long it lasts

`Examples/SensorMemory.lean` prices the erasure this agent executes at every
fourth operation; `Examples/FiniteSupply.lean` runs a source, a buffer and a
load. They are two protocols. Here they are one: the world this agent acts on
carries a task flag *and* a charge, the operation that prepares the next episode
spends a unit of that charge, and the charge is the reading of a `PathwiseStore`
on the agent's own trajectory.

The memory channels are the ones already priced — `Examples.Sensor`'s
measurement, update, erasure and drift — so what the source funds is what
`memoryHeat_const` costs. Three facts fix the run: the charge never rises, every
clear stage before the sixteenth operation spends exactly one unit, and the
agent starts with three. `clearings_le_of_source` then bounds the funded
horizon at three complete cycles, and the bound is attained.

Two things the model does not do are recorded rather than repaired. The charge
floors at nothing, so from the sixteenth operation the clear stage still runs
and still costs `(3/16) log 3` at least, while the source pays nothing: an
erasure that cannot read the world cannot be conditioned on the energy it needs.
And this agent is not `Positive` — `positive_source_never_falls` says no funded
one can be, because a channel of full support makes the ledger's reading
constant.
-/

namespace PhysicsOfConsciousness

namespace Examples.Funded

open Examples.Sensor

/-! ## The charge, and the world that carries it -/

/-- Spending a unit, with nothing below empty. -/
def pred (c : Fin 5) : Fin 5 := ⟨c.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩

@[simp] theorem pred_val (c : Fin 5) : (pred c).val = c.val - 1 := rfl

/-- The world is a task flag and a charge. -/
abbrev World := Bool × Fin 5

/-- The joint state the agent evolves: register, memory, flag and charge. -/
abbrev State := Bool × (Bool × World)

/-- The action changes the flag exactly as in `Examples.Sensor` and leaves the
charge alone: acting is not what this agent pays for. -/
noncomputable def actuate (w a : Bool) (e : World) : ProbDist World :=
  (Sensor.actuate w a e.1).prod (ProbDist.dirac e.2)

/-- The measurement reads the flag. It cannot see the charge, and it does not
see the parameter. -/
noncomputable def record (e : World) (m : Bool) : ProbDist Bool := Sensor.record e.1 m

/-- Preparing the next episode: the flag relaxes as before, and the charge falls
by one. This is the world half of the clear stage, so the unit is spent in the
same operation as the erasure. -/
noncomputable def reset (e : World) : ProbDist World :=
  (Sensor.reset e.1).prod (ProbDist.dirac (pred e.2))

/-- The world's drift while it is not being acted on: the flag wanders, the
charge does not leak. -/
noncomputable def envIdle (e : World) : ProbDist World :=
  (Sensor.drift e.1).prod (ProbDist.dirac e.2)

/-- The declared initial law: the rewarding action, the register, the memory and
the flag are all uniform, and the source is full. -/
noncomputable def prior : ProbDist (Bool × State) where
  p z := if z.2.2.2.2 = 4 then 1 / 16 else 0
  nonneg z := by split <;> norm_num
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_five]
    norm_num [Fin.ext_iff]

/-- The agent: act, measure, learn, clear, repeat, out of a finite charge. -/
noncomputable def agent : MemoryAgent Bool Bool Bool World Bool :=
  ⟨prior, Sensor.readout, actuate, record, Sensor.update, Sensor.erase, reset,
    Sensor.drift, Sensor.drift, envIdle, Sensor.reward⟩

@[simp] theorem agent_erase : agent.erase = Sensor.erase := rfl

@[simp] theorem agent_memoryIdle : agent.memoryIdle = Sensor.drift := rfl

@[simp] theorem agent_actuate : agent.actuate = actuate := rfl

@[simp] theorem agent_readout : agent.readout = Sensor.readout := rfl

/-- The store's reading: the charge, counted so that an empty source is zero and
a run that clears once more than it can afford is overdrawn. -/
noncomputable def source (s : State) : ℝ := (s.2.2.2.val : ℝ) - 1

/-! ## The charge along the run -/

private theorem pos_right {a b : ℝ} (hb : 0 ≤ b) (h : 0 < a * b) : 0 < b := by
  rcases hb.lt_or_eq with h' | h'
  · exact h'
  · exact absurd h (by rw [← h']; simp)

/-- Every executed transition either keeps the charge or spends one unit, and it
spends exactly when the operation is the clearing. -/
theorem step_charge (n : ℕ) (w : Bool) (s t : State) (ht : 0 < (agent.stage n w s).p t) :
    t.2.2.2 = if n % 4 = 3 then pred s.2.2.2 else s.2.2.2 := by
  have hdirac : ∀ (P Q Sf : ProbDist Bool) (c : Fin 5),
      0 < (P.prod (Q.prod (Sf.prod (ProbDist.dirac c)))).p t → t.2.2.2 = c := by
    intro P Q Sf c hpos
    have h1 : 0 < (Q.prod (Sf.prod (ProbDist.dirac c))).p t.2 :=
      pos_right ((Q.prod (Sf.prod (ProbDist.dirac c))).nonneg _) hpos
    have h2 : 0 < (Sf.prod (ProbDist.dirac c)).p t.2.2 :=
      pos_right ((Sf.prod (ProbDist.dirac c)).nonneg _) h1
    have h3 : 0 < (ProbDist.dirac c).p t.2.2.2 :=
      pos_right ((ProbDist.dirac c).nonneg _) h2
    by_contra hne
    rw [ProbDist.dirac_apply, ite_eq_right hne] at h3
    exact lt_irrefl _ h3
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · rw [agent.stage_eq_act n h] at ht
    rw [ite_eq_right (by omega)]
    exact hdirac _ _ _ _ ht
  · rw [agent.stage_eq_record n h] at ht
    rw [ite_eq_right (by omega)]
    exact hdirac _ _ _ _ ht
  · rw [agent.stage_eq_learn n h] at ht
    rw [ite_eq_right (by omega)]
    exact hdirac _ _ _ _ ht
  · rw [agent.stage_eq_clear n h] at ht
    rw [ite_eq_left h]
    exact hdirac _ _ _ _ ht

/-- The charge after `n` operations: full, less one for each clearing executed,
and never below empty. -/
def chargeAt (n : ℕ) : Fin 5 := ⟨4 - n / 4, by omega⟩

@[simp] theorem chargeAt_val (n : ℕ) : (chargeAt n).val = 4 - n / 4 := rfl

/-- **The charge is not uncertain.** Whatever the agent has learned, every state
it can reach after `n` operations carries the same charge, because only the
clearing moves it and the clearing is deterministic there. -/
theorem charge_invariant (n : ℕ) (z : Bool × State) (h : agent.protocol.Reachable n z) :
    z.2.2.2.2 = chargeAt n := by
  induction n generalizing z with
  | zero =>
    have hz : 0 < prior.p z := h
    by_contra hne
    rw [show prior.p z = if z.2.2.2.2 = 4 then 1 / 16 else 0 from rfl,
      ite_eq_right (by simpa [chargeAt] using hne)] at hz
    exact lt_irrefl _ hz
  | succ n ih =>
    obtain ⟨s, hsr, hst⟩ := agent.protocol.exists_pred_of_reachable n z.1 z.2 h
    have hprev : s.2.2.2 = chargeAt n := ih (z.1, s) hsr
    have hstep := step_charge n z.1 s z.2 hst
    have hval : (chargeAt (n + 1)).val =
        if n % 4 = 3 then (pred (chargeAt n)).val else (chargeAt n).val := by
      split <;> simp only [chargeAt_val, pred_val] <;> omega
    apply Fin.ext
    rw [show z.2.2.2.2 = (z.2).2.2.2 from rfl, hstep, hval, hprev]
    split <;> rfl

/-! ## The ledger the agent's own operations keep -/

/-- The charge never rises on a transition the protocol can execute. -/
theorem source_nonincreasing (n : ℕ) (w : Bool) (s t : State)
    (ht : 0 < (agent.stage n w s).p t) : source t ≤ source s := by
  have h := step_charge n w s t ht
  unfold source
  rw [show t.2.2.2 = (t : State).2.2.2 from rfl, h]
  split
  · simp only [pred_val]
    have : (s.2.2.2.val : ℝ) - 1 ≤ (s.2.2.2.val : ℝ) := by linarith
    have hle : ((s.2.2.2.val - 1 : ℕ) : ℝ) ≤ (s.2.2.2.val : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    linarith
  · exact le_rfl

/-- **Every clearing the charge can pay for costs exactly one unit.** The bound
runs to the sixteenth operation, which is where the charge runs out. -/
theorem clear_spends_one (n : ℕ) (hn : n < 16) (h : n % 4 = 3) (w : Bool) (s t : State)
    (hs : agent.protocol.Reachable n (w, s)) (ht : 0 < (agent.stage n w s).p t) :
    source t ≤ source s - 1 := by
  have hc : s.2.2.2 = chargeAt n := charge_invariant n (w, s) hs
  have hpos : 1 ≤ s.2.2.2.val := by rw [hc]; simp only [chargeAt_val]; omega
  have hstep := step_charge n w s t ht
  unfold source
  rw [show t.2.2.2 = (t : State).2.2.2 from rfl, hstep, ite_eq_left h]
  simp only [pred_val]
  have hcast : ((s.2.2.2.val - 1 : ℕ) : ℝ) = (s.2.2.2.val : ℝ) - 1 := by
    push_cast [Nat.cast_sub hpos]
    ring
  rw [hcast]

/-- The run is solvent through three complete cycles. -/
theorem solvent_twelve (k : ℕ) (hk : k ≤ 12) (z : Bool × State)
    (h : agent.protocol.Reachable k z) : 0 ≤ source z.2 := by
  have hc : z.2.2.2.2 = chargeAt k := charge_invariant k z h
  have : (z.2).2.2.2 = chargeAt k := hc
  unfold source
  rw [this]
  simp only [chargeAt_val]
  have : 1 ≤ 4 - k / 4 := by omega
  have hcast : (1 : ℝ) ≤ ((4 - k / 4 : ℕ) : ℝ) := by exact_mod_cast this
  linarith

/-- **Three cycles, and the bound is attained.** The generic horizon theorem at
`c = 1` and `b = 3`, on the agent's own source coordinate. -/
theorem cycles_le_three : (3 : ℝ) * 1 ≤ 3 := by
  refine agent.clearings_le_of_source source 1 3 3 ?_ ?_ ?_ ?_
  · intro n _ w s t _ ht
    exact source_nonincreasing n w s t ht
  · intro n hn h w s t hs ht
    exact clear_spends_one n (by omega) h w s t hs ht
  · intro z hz
    have hc : (z.2).2.2.2 = chargeAt 0 := charge_invariant 0 z hz
    unfold source
    rw [hc]
    norm_num [chargeAt]
  · exact solvent_twelve

/-- **A fourth cycle is not funded.** The store the same agent carries reads
below empty at the sixteenth operation, so the run is not solvent there — which
is what `cycles_le_three` forbids and this exhibits. -/
theorem not_solvent_four : ¬ (agent.sourceStore source).Solvent 16 := by
  intro hs
  obtain ⟨z, hz⟩ := agent.protocol.exists_reachable 16
  have h := hs 16 le_rfl z hz
  have hc : (z.2).2.2.2 = chargeAt 16 := charge_invariant 16 z hz
  rw [MemoryAgent.sourceStore_balance] at h
  unfold source at h
  rw [hc] at h
  norm_num [chargeAt] at h

/-! ## What is funded is what is priced -/

/-- The clear stage's memory heat, at every cycle, on the agent's own paths. -/
theorem clear_cost (m : ℕ) :
    (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) =
      (3 / 4 - (agent.memoryLaw (4 * m + 3)).p false) * Real.log 3 := by
  rw [agent.clear_memoryHeat 1 (4 * m + 3) (by omega), agent_erase, erase_cost]

/-- The mass the memory puts on a set flag after `n` operations. -/
noncomputable def memMass (n : ℕ) : ℝ := (agent.memoryLaw n).p true

/-- The world states carrying a given flag. -/
def flagSet (b : Bool) : Finset World := Finset.univ.image (Prod.mk b)

theorem flagSet_sum (b : Bool) (g : World → ℝ) :
    (∑ e ∈ flagSet b, g e) = ∑ c, g (b, c) := by
  rw [flagSet, Finset.sum_image (by intro x _ y _ h; exact (Prod.mk.injEq _ _ _ _ ▸ h).2)]

/-- The mass the world puts on a set flag after `n` operations, charge and all. -/
noncomputable def flagMass (b : Bool) (n : ℕ) : ℝ := ∑ c, (agent.envLaw n).p (b, c)

theorem flagSet_mass (b : Bool) (n : ℕ) :
    (∑ e ∈ flagSet b, (agent.envLaw n).p e) = flagMass b n := flagSet_sum b _

theorem flagMass_sum (n : ℕ) : flagMass true n + flagMass false n = 1 := by
  have h := (agent.envLaw n).sum_one
  rw [Fintype.sum_prod_type, Fintype.sum_bool] at h
  unfold flagMass
  linarith

theorem memMass_sum (n : ℕ) : memMass n + (agent.memoryLaw n).p false = 1 := by
  have h := (agent.memoryLaw n).sum_one
  rwa [Fintype.sum_bool] at h

/-- Drifting moves the memory's mass halfway toward uniform. -/
theorem memMass_idle (n : ℕ) (h : n % 4 = 0 ∨ n % 4 = 2) :
    memMass (n + 1) = 1 / 4 + memMass n / 2 := by
  have hs := memMass_sum n
  have h1 := agent.memoryLaw_idle n h true
  unfold memMass at hs ⊢
  rw [h1]
  simp only [Fintype.sum_bool, agent_memoryIdle, Sensor.drift]
  norm_num
  linarith

/-- Measuring replaces the memory's mass by the flag's, seen through the
measurement channel. The charge the world also carries enters nowhere: the
measurement reads the flag. -/
theorem memMass_record (n : ℕ) (h : n % 4 = 1) :
    memMass (n + 1) = 1 / 4 + flagMass true n / 2 := by
  have hs := flagMass_sum n
  have h1 := agent.memoryLaw_record n h (fun e => Sensor.record e.1 true)
  have h2 : ∀ (e : World) (m : Bool), agent.record e m = Sensor.record e.1 true := by
    intro e m
    show Sensor.record e.1 m = Sensor.record e.1 true
    cases m <;> cases e.1 <;> rfl
  have h3 := h1 h2 true
  rw [memMass, h3, Fintype.sum_prod_type, Fintype.sum_bool]
  have htr : ∀ y : Fin 5, (agent.envLaw n).p (true, y) * (Sensor.record (true, y).1 true).p true
      = (agent.envLaw n).p (true, y) * (3 / 4) := by
    intro y; norm_num [Sensor.record]
  have hfa : ∀ y : Fin 5, (agent.envLaw n).p (false, y) * (Sensor.record (false, y).1 true).p true
      = (agent.envLaw n).p (false, y) * (1 / 4) := by
    intro y; norm_num [Sensor.record]
  simp_rw [htr, hfa, ← Finset.sum_mul]
  unfold flagMass at hs ⊢
  linarith

/-- **The world is never certain.** Whatever the agent has learned, the flag its
action leaves is a mixture of the actuator's two masses. -/
theorem flagMass_act_bounds (n : ℕ) (h : n % 4 = 0) :
    1 / 4 ≤ flagMass true (n + 1) ∧ flagMass true (n + 1) ≤ 3 / 4 := by
  have key : ∀ (w a : Bool) (e : World),
      (∑ e' ∈ flagSet true, (agent.actuate w a e).p e') = (Sensor.actuate w a e.1).p true := by
    intro w a e
    rw [flagSet_sum]
    have : ∀ c : Fin 5, (agent.actuate w a e).p (true, c) =
        (Sensor.actuate w a e.1).p true * (ProbDist.dirac e.2).p c := fun _ => rfl
    simp_rw [this, ← Finset.mul_sum, ProbDist.sum_one, mul_one]
  constructor
  · rw [← flagSet_mass]
    refine agent.le_envLaw_act_sum n h (flagSet true) (1 / 4) fun w b e => ?_
    rw [key]
    cases b <;> cases w <;> norm_num [Sensor.actuate]
  · rw [← flagSet_mass]
    refine agent.envLaw_act_sum_le n h (flagSet true) (3 / 4) fun w a e => ?_
    rw [key]
    cases a <;> cases w <;> norm_num [Sensor.actuate]

/-- **So the memory is never certain either**, at any cycle. -/
theorem memMass_clear_bounds (m : ℕ) :
    7 / 16 ≤ memMass (4 * m + 3) ∧ memMass (4 * m + 3) ≤ 9 / 16 := by
  obtain ⟨hlo, hhi⟩ := flagMass_act_bounds (4 * m) (by omega)
  have hr : memMass (4 * m + 2) = 1 / 4 + flagMass true (4 * m + 1) / 2 :=
    memMass_record (4 * m + 1) (by omega)
  have hi : memMass (4 * m + 3) = 1 / 4 + memMass (4 * m + 2) / 2 :=
    memMass_idle (4 * m + 2) (Or.inr (by omega))
  constructor <;> linarith

/-- **A positive recurring price, whatever has been learned and whatever the
source still holds.** -/
theorem clear_cost_floor (m : ℕ) :
    3 / 16 * Real.log 3 ≤
      (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) := by
  rw [clear_cost m]
  have hs := memMass_sum (4 * m + 3)
  obtain ⟨hlo, -⟩ := memMass_clear_bounds m
  have hle : (3 : ℝ) / 16 ≤ 3 / 4 - (agent.memoryLaw (4 * m + 3)).p false := by
    unfold memMass at hs hlo; linarith
  exact mul_le_mul_of_nonneg_right hle (Real.log_nonneg (by norm_num))

theorem clear_cost_ceiling (m : ℕ) :
    (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) ≤
      5 / 16 * Real.log 3 := by
  rw [clear_cost m]
  have hs := memMass_sum (4 * m + 3)
  obtain ⟨-, hhi⟩ := memMass_clear_bounds m
  have hle : (3 : ℝ) / 4 - (agent.memoryLaw (4 * m + 3)).p false ≤ 5 / 16 := by
    unfold memMass at hs hhi; linarith
  exact mul_le_mul_of_nonneg_right hle (Real.log_nonneg (by norm_num))

/-! ## What the model does not do -/

/-- **An empty source does not stop the clearing.** From the sixteenth operation
the clear stage draws nothing, while `clear_cost_floor` still prices it at
`(3/16) log 3` or more. `erase : M → ProbDist M` reads only the memory, so no
channel of this agent can be conditioned on the charge: the run past three
cycles is unfunded rather than halted. -/
theorem clear_unfunded (n : ℕ) (hn : 16 ≤ n) (w : Bool) (s t : State)
    (hs : agent.protocol.Reachable n (w, s)) (ht : 0 < (agent.stage n w s).p t) :
    source t = source s := by
  have hc : s.2.2.2 = chargeAt n := charge_invariant n (w, s) hs
  have hzero : s.2.2.2.val = 0 := by rw [hc]; simp only [chargeAt_val]; omega
  have hstep := step_charge n w s t ht
  unfold source
  rw [show t.2.2.2 = (t : State).2.2.2 from rfl, hstep]
  split
  · simp only [pred_val, hzero]
  · rfl

/-- **The agent cannot have full support.** A channel that can produce every
state makes the source's reading constant (`positive_source_never_falls`),
contradicting the unit spent at the first clearing. -/
theorem not_positive : ¬ agent.Positive := by
  intro hp
  obtain ⟨z, hz⟩ := agent.protocol.exists_reachable 3
  obtain ⟨t, ht⟩ : ∃ t, 0 < (agent.stage 3 z.1 z.2).p t := by
    have hsum : ∑ t, (agent.stage 3 z.1 z.2).p t ≠ 0 := by
      rw [(agent.stage 3 z.1 z.2).sum_one]; norm_num
    obtain ⟨t, _, htne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    exact ⟨t, lt_of_le_of_ne ((agent.stage 3 z.1 z.2).nonneg t) (Ne.symm htne)⟩
  have hspend := clear_spends_one 3 (by norm_num) (by norm_num) z.1 z.2 t hz ht
  have hconst := agent.positive_source_never_falls source hp
    (fun k y u v htr => source_nonincreasing k y u v htr) 3 z.1 z.2 t
  linarith


/-! ## Retained specifications

These are the regressions written before the declarations existed. They fix the
statements rather than the proofs, and they are what a later change breaks
first. -/

section Specifications

variable {X S : Type*} [Fintype X] [Fintype S]

/-- A cost function of the stage, not a constant. -/
example (B : PathwiseStore X S) (hl : B.Ledgered) (cost : ℕ → ℝ) (b : ℝ)
    (hb : ∀ z, B.protocol.Reachable 0 z → B.balance z.2 ≤ b) (N : ℕ)
    (hc : ∀ n < N, ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → cost n ≤ B.draw n x s t - B.supply n x s t)
    (z : X × S) (hz : B.protocol.Reachable N z) :
    B.balance z.2 ≤ b - ∑ n ∈ Finset.range N, cost n :=
  B.balance_le_of_stage_cost hl cost b hb N hc z hz

example (p j : ℕ) (hj : j < p) (c : ℝ) (m : ℕ) :
    (∑ n ∈ Finset.range (p * m), if n % p = j then c else 0) = m * c :=
  sum_period_indicator p j hj c m

/-- One costly stage per period bounds the number of periods. -/
example (B : PathwiseStore X S) (hl : B.Ledgered) (p j : ℕ) (hj : j < p) (c b : ℝ)
    (h0 : ∀ z, B.protocol.Reachable 0 z → B.balance z.2 ≤ b) (m : ℕ)
    (hc : ∀ n < p * m, n % p = j → ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → c ≤ B.draw n x s t - B.supply n x s t)
    (hrest : ∀ n < p * m, n % p ≠ j → ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → 0 ≤ B.draw n x s t - B.supply n x s t)
    (hs : B.Solvent (p * m)) : (m : ℝ) * c ≤ b :=
  B.horizon_le_of_periodic_cost hl p j hj c b h0 m hc hrest hs

/-- The same with the source inside the boundary. -/
example (B : PathwiseStore X S) (R : S → ℝ) (hl : B.Ledgered) (hr : B.SourceLedgered R)
    (p j : ℕ) (hj : j < p) (c b : ℝ)
    (h0 : ∀ z, B.protocol.Reachable 0 z → B.balance z.2 + R z.2 ≤ b) (m : ℕ)
    (hc : ∀ n < p * m, n % p = j → ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → c ≤ B.draw n x s t)
    (hrest : ∀ n < p * m, n % p ≠ j → ∀ x s t, B.protocol.Reachable n (x, s) →
      0 < (B.protocol.stage n x s).p t → 0 ≤ B.draw n x s t)
    (hs : B.Solvent (p * m))
    (hR : ∀ k ≤ p * m, ∀ z, B.protocol.Reachable k z → 0 ≤ R z.2) :
    (m : ℝ) * c ≤ b :=
  B.periodic_horizon_le_of_finite_source R hl hr p j hj c b h0 m hc hrest hs hR

/-- Full support admits no net draw. -/
example [Nonempty S] (B : PathwiseStore X S) (hl : B.Ledgered)
    (hp : B.protocol.Positive)
    (hcost : ∀ n x s t, 0 ≤ B.draw n x s t - B.supply n x s t)
    (n : ℕ) (x : X) (s t : S) : B.draw n x s t = B.supply n x s t :=
  B.net_draw_eq_zero_of_positive hl hp hcost n x s t

/-- The agent's own store is source-ledgered by construction. -/
example {W Reg M Env A : Type*} [Fintype W] [Fintype Reg] [Fintype M] [Fintype Env]
    [Fintype A] (G : MemoryAgent W Reg M Env A) (src : Reg × (M × Env) → ℝ) :
    (G.drawnStore src).SourceLedgered src :=
  G.drawnStore_sourceLedgered src

/-- A finite source funds finitely many clearings. -/
example {W Reg M Env A : Type*} [Fintype W] [Fintype Reg] [Fintype M] [Fintype Env]
    [Fintype A] (G : MemoryAgent W Reg M Env A) (src : Reg × (M × Env) → ℝ) (c b : ℝ)
    (m : ℕ)
    (hmono : ∀ n < 4 * m, ∀ w s t, G.protocol.Reachable n (w, s) →
      0 < (G.stage n w s).p t → src t ≤ src s)
    (hclear : ∀ n < 4 * m, n % 4 = 3 → ∀ w s t, G.protocol.Reachable n (w, s) →
      0 < (G.stage n w s).p t → src t ≤ src s - c)
    (h0 : ∀ z, G.protocol.Reachable 0 z → src z.2 ≤ b)
    (hs : ∀ k ≤ 4 * m, ∀ z, G.protocol.Reachable k z → 0 ≤ src z.2) :
    (m : ℝ) * c ≤ b :=
  G.clearings_le_of_source src c b m hmono hclear h0 hs

/-- A positive agent draws nothing. -/
example {W Reg M Env A : Type*} [Fintype W] [Fintype Reg] [Fintype M] [Fintype Env]
    [Fintype A] [Nonempty (Reg × (M × Env))] (G : MemoryAgent W Reg M Env A)
    (src : Reg × (M × Env) → ℝ) (hp : G.Positive)
    (hmono : ∀ n w s t, 0 < (G.stage n w s).p t → src t ≤ src s)
    (n : ℕ) (w : W) (s t : Reg × (M × Env)) : src t = src s :=
  G.positive_source_never_falls src hp hmono n w s t

/-- Bounds on a world marginal, not on a single world state. -/
example {W Reg M Env A : Type*} [Fintype W] [Fintype Reg] [Fintype M] [Fintype Env]
    [Fintype A] (G : MemoryAgent W Reg M Env A) (n : ℕ) (h : n % 4 = 0)
    (F : Finset Env) (b : ℝ)
    (hb : ∀ w a e, (∑ e' ∈ F, (G.actuate w a e).p e') ≤ b) :
    (∑ e' ∈ F, (G.envLaw (n + 1)).p e') ≤ b :=
  G.envLaw_act_sum_le n h F b hb

example {W Reg M Env A : Type*} [Fintype W] [Fintype Reg] [Fintype M] [Fintype Env]
    [Fintype A] (G : MemoryAgent W Reg M Env A) (n : ℕ) (h : n % 4 = 0)
    (F : Finset Env) (a : ℝ)
    (ha : ∀ w b e, a ≤ ∑ e' ∈ F, (G.actuate w b e).p e') :
    a ≤ ∑ e' ∈ F, (G.envLaw (n + 1)).p e' :=
  G.le_envLaw_act_sum n h F a ha

/-! ### The witness -/

example (n : ℕ) (w : Bool) (s t : State) (ht : 0 < (agent.stage n w s).p t) :
    source t ≤ source s := source_nonincreasing n w s t ht

example (n : ℕ) (hn : n < 16) (h : n % 4 = 3) (w : Bool) (s t : State)
    (hs : agent.protocol.Reachable n (w, s)) (ht : 0 < (agent.stage n w s).p t) :
    source t ≤ source s - 1 := clear_spends_one n hn h w s t hs ht

example : (3 : ℝ) * 1 ≤ 3 := cycles_le_three

example : ¬ (agent.sourceStore source).Solvent 16 := not_solvent_four

example : ¬ agent.Positive := not_positive

example (n : ℕ) (hn : 16 ≤ n) (w : Bool) (s t : State)
    (hs : agent.protocol.Reachable n (w, s)) (ht : 0 < (agent.stage n w s).p t) :
    source t = source s := clear_unfunded n hn w s t hs ht

example (m : ℕ) :
    (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) =
      (3 / 4 - (agent.memoryLaw (4 * m + 3)).p false) * Real.log 3 := clear_cost m

example (m : ℕ) :
    3 / 16 * Real.log 3 ≤
      (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) :=
  clear_cost_floor m

example (m : ℕ) :
    (agent.protocol.step (4 * m + 3)).meanHeat (agent.eraseHeatObs 1) ≤
      5 / 16 * Real.log 3 := clear_cost_ceiling m

end Specifications

end Examples.Funded

end PhysicsOfConsciousness
