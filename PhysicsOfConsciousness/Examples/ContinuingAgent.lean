import PhysicsOfConsciousness.Phase3_ContinuingAgent

/-!
# One continuing agent: witness and regression specifications

An agent with an unknown rewarding action, a task flag its action sets, a noisy
readout of that flag, and a preparation stage that clears the flag for the next
episode. Everything runs in sequence on one joint law. Each operation's expected
work is charged to a declared store, which funds only a finite prefix.

Every primitive channel mass is `1/4` or `3/4`, so every stage heat is a rational multiple
of `log 3` or `log (5/3)`, and the whole run's accounting is exact.
-/

namespace PhysicsOfConsciousness.Examples

namespace Continuing

/-! ## The agent -/

/-- The register's value is the action executed: it decodes no task value. -/
def readout : Bool → Bool := id

/-- The declared initial uncertainty: the rewarding action is unknown, the
register has no preference, and the flag is as likely set as clear. -/
noncomputable def prior : ProbDist (Bool × (Bool × Bool)) where
  p _ := 1 / 8
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_prod_type, Fintype.sum_bool]

/-- The actuator. A set flag stays set with probability `3/4`; a clear flag is
set with probability `3/4` by the rewarding action and `1/4` by the other. The
world keeps what the action did to it until something clears it. -/
noncomputable def actuate (w a e : Bool) : ProbDist Bool where
  p e' :=
    if e' then (if e then 3 / 4 else (if a = w then 3 / 4 else 1 / 4))
    else (if e then 1 / 4 else (if a = w then 1 / 4 else 3 / 4))
  nonneg e' := by cases e' <;> cases e <;> cases a <;> cases w <;> norm_num
  sum_one := by cases e <;> cases a <;> cases w <;> norm_num [Fintype.sum_bool]

/-- The observation: a readout of the flag that is right three times in four.
It does not see the unknown parameter. -/
noncomputable def sense (e : Bool) : ProbDist Bool where
  p o := if o = e then 3 / 4 else 1 / 4
  nonneg o := by cases o <;> cases e <;> norm_num
  sum_one := by cases e <;> norm_num [Fintype.sum_bool]

/-- Win-stay, lose-shift, driven by the observation alone: a success keeps the
register with probability `3/4`, a failure moves it with probability `3/4`. -/
noncomputable def update (o r : Bool) : ProbDist Bool where
  p r' :=
    if r' = r then (if o then 3 / 4 else 1 / 4) else (if o then 1 / 4 else 3 / 4)
  nonneg r' := by cases r' <;> cases r <;> cases o <;> norm_num
  sum_one := by cases r <;> cases o <;> norm_num [Fintype.sum_bool]

/-- Preparation of the next episode: the flag is cleared, imperfectly, whatever
it was. An exact erasure would leave the reverse path no probability. -/
noncomputable def reset (_e : Bool) : ProbDist Bool where
  p e' := if e' then 1 / 4 else 3 / 4
  nonneg e' := by cases e' <;> norm_num
  sum_one := by norm_num [Fintype.sum_bool]

/-- The drift of whichever coordinate is not being driven. It is symmetric, so
it dissipates nothing, and it is positive, so no path is unreachable. -/
noncomputable def drift (x : Bool) : ProbDist Bool where
  p x' := if x' = x then 3 / 4 else 1 / 4
  nonneg x' := by cases x' <;> cases x <;> norm_num
  sum_one := by cases x <;> norm_num [Fintype.sum_bool]

/-- The evaluation criterion: the register executed the rewarding action. It
appears in no channel. -/
def reward (w a : Bool) : ℝ := if a = w then 1 else 0

/-- The agent: act, observe and learn, prepare, repeat. -/
noncomputable def agent : ContinuingAgent Bool Bool Bool Bool Bool :=
  ⟨prior, readout, actuate, sense, update, reset, drift, drift, reward⟩

theorem positive : agent.Positive := by
  refine ⟨fun z => by norm_num [agent, prior], fun w a e e' => ?_, fun e o => ?_,
    fun o r r' => ?_, fun e e' => ?_, fun r r' => ?_, fun e e' => ?_⟩
  · show 0 < (actuate w a e).p e'
    cases e' <;> cases e <;> cases a <;> cases w <;> norm_num [actuate]
  · show 0 < (sense e).p o
    cases o <;> cases e <;> norm_num [sense]
  · show 0 < (update o r).p r'
    cases r' <;> cases r <;> cases o <;> norm_num [update]
  · show 0 < (reset e).p e'
    cases e' <;> norm_num [reset]
  · show 0 < (drift r).p r'
    cases r' <;> cases r <;> norm_num [drift]
  · show 0 < (drift e).p e'
    cases e' <;> cases e <;> norm_num [drift]

theorem protocol_positive : agent.protocol.Positive := agent.protocol_positive positive

/-! ## The three stage channels -/

theorem actStage_apply (w r e r' e' : Bool) :
    (agent.actStage w (r, e)).p (r', e') =
      (drift r).p r' * (actuate w r e).p e' := rfl

/-- The composite register channel of the learning stage: the observation is
marginalized out, so what is left is a relaxation whose direction depends on the
flag the action left behind. -/
theorem learn_register (e r r' : Bool) :
    ((sense e).bind fun o => update o r).p r' =
      if r' = r then (if e then 5 / 8 else 3 / 8) else (if e then 3 / 8 else 5 / 8) := by
  show (∑ o, (sense e).p o * (update o r).p r') = _
  cases e <;> cases r <;> cases r' <;> norm_num [sense, update, Fintype.sum_bool]

theorem learnStage_apply (w r e r' e' : Bool) :
    (agent.learnStage w (r, e)).p (r', e') =
      (if r' = r then (if e then 5 / 8 else 3 / 8) else (if e then 3 / 8 else 5 / 8)) *
        (drift e).p e' := by
  show ((sense e).bind fun o => update o r).p r' * (drift e).p e' = _
  rw [learn_register]

theorem resetStage_apply (w r e r' e' : Bool) :
    (agent.resetStage w (r, e)).p (r', e') =
      (drift r).p r' * (reset e).p e' := rfl

/-! ## The mass form, and how each stage moves it -/

/-- The joint law throughout the run has this shape: the parameter's marginal is
uniform and what varies is the four masses of agreement against flag. `aT` is
the mass of "the register holds the rewarding action and the flag is set". -/
noncomputable def masses (aT aF dT dF : ℝ) (z : Bool × Bool × Bool) : ℝ :=
  if z.2.1 = z.1 then (if z.2.2 then aT / 2 else aF / 2)
  else (if z.2.2 then dT / 2 else dF / 2)

theorem masses_congr {aT aF dT dF aT' aF' dT' dF' : ℝ} (h1 : aT = aT') (h2 : aF = aF')
    (h3 : dT = dT') (h4 : dF = dF') (z : Bool × Bool × Bool) :
    masses aT aF dT dF z = masses aT' aF' dT' dF' z := by
  rw [h1, h2, h3, h4]

theorem law_zero_masses (z : Bool × Bool × Bool) :
    (agent.law 0).p z = masses (1 / 4) (1 / 4) (1 / 4) (1 / 4) z := by
  obtain ⟨w, r, e⟩ := z
  cases w <;> cases r <;> cases e <;> norm_num [agent, prior, masses]

/-- Acting: the readout drives the flag, so agreement and flag become correlated. -/
theorem act_masses (m : ℕ) (aT aF dT dF : ℝ)
    (h : ∀ z, (agent.law (3 * m)).p z = masses aT aF dT dF z) (z : Bool × Bool × Bool) :
    (agent.law (3 * m + 1)).p z =
      masses (9 / 16 * aT + 9 / 16 * aF + 3 / 16 * dT + 1 / 16 * dF)
        (3 / 16 * aT + 3 / 16 * aF + 1 / 16 * dT + 3 / 16 * dF)
        (3 / 16 * aT + 3 / 16 * aF + 9 / 16 * dT + 3 / 16 * dF)
        (1 / 16 * aT + 1 / 16 * aF + 3 / 16 * dT + 9 / 16 * dF) z := by
  rw [agent.law_succ_apply, ContinuingAgent.stage_act]
  obtain ⟨w, r, e⟩ := z
  cases w <;> cases r <;> cases e <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, h, actStage_apply, masses,
      drift, actuate] <;>
    norm_num <;> ring

/-- Learning: the flag the action left behind decides which way the register
relaxes, so agreement changes and the correlation is consumed. -/
theorem learn_masses (m : ℕ) (aT aF dT dF : ℝ)
    (h : ∀ z, (agent.law (3 * m + 1)).p z = masses aT aF dT dF z) (z : Bool × Bool × Bool) :
    (agent.law (3 * m + 2)).p z =
      masses (15 / 32 * aT + 3 / 32 * aF + 9 / 32 * dT + 5 / 32 * dF)
        (5 / 32 * aT + 9 / 32 * aF + 3 / 32 * dT + 15 / 32 * dF)
        (9 / 32 * aT + 5 / 32 * aF + 15 / 32 * dT + 3 / 32 * dF)
        (3 / 32 * aT + 15 / 32 * aF + 5 / 32 * dT + 9 / 32 * dF) z := by
  rw [show 3 * m + 2 = (3 * m + 1) + 1 from rfl, agent.law_succ_apply,
    ContinuingAgent.stage_learn]
  obtain ⟨w, r, e⟩ := z
  cases w <;> cases r <;> cases e <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, h, learnStage_apply, masses,
      drift] <;>
    norm_num <;> ring

/-- Preparing: the flag is returned to its standard law whatever it held, so the
next episode starts uncorrelated with the last one's outcome. -/
theorem reset_masses (m : ℕ) (aT aF dT dF : ℝ)
    (h : ∀ z, (agent.law (3 * m + 2)).p z = masses aT aF dT dF z) (z : Bool × Bool × Bool) :
    (agent.law (3 * m + 3)).p z =
      masses (3 / 16 * (aT + aF) + 1 / 16 * (dT + dF))
        (9 / 16 * (aT + aF) + 3 / 16 * (dT + dF))
        (1 / 16 * (aT + aF) + 3 / 16 * (dT + dF))
        (3 / 16 * (aT + aF) + 9 / 16 * (dT + dF)) z := by
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from rfl, agent.law_succ_apply,
    ContinuingAgent.stage_reset]
  obtain ⟨w, r, e⟩ := z
  cases w <;> cases r <;> cases e <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, h, resetStage_apply, masses,
      drift, reset] <;>
    norm_num <;> ring


/-! ## The heat of each operation -/

/-- The register's drift is symmetric, so the acting stage's heat is entirely the
actuator's: driving a clear flag toward set costs `log 3` when the register holds
the rewarding action, and the reverse path pays it back. -/
theorem act_heat_apply (m : ℕ) (w r e r' e' : Bool) :
    agent.protocol.stageHeat 1 (3 * m) w (r, e) (r', e') =
      if e then (if e' then 0 else (if r' = w then -Real.log 3 else 0))
      else (if e' then (if r = w then Real.log 3 else 0)
        else (if r = w then (if r' = w then 0 else -Real.log 3)
          else (if r' = w then Real.log 3 else 0))) := by
  have h3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.log_inv]
  show 1 * Real.log ((agent.protocol.stage (3 * m) w (r, e)).p (r', e') /
      (agent.protocol.stage (3 * m) w (r', e')).p (r, e)) = _
  simp only [ContinuingAgent.protocol_stage, ContinuingAgent.stage_act, actStage_apply,
    drift, actuate]
  cases w <;> cases r <;> cases e <;> cases r' <;> cases e' <;>
    norm_num [h3]

/-- The learning stage's heat: the register relaxes toward agreement when the
flag it read was set and away when it was clear, so a path that reads one flag
and is reversed at the other is not free. -/
theorem learn_heat_apply (m : ℕ) (w r e r' e' : Bool) :
    agent.protocol.stageHeat 1 (3 * m + 1) w (r, e) (r', e') =
      if e = e' then 0
      else if e then (if r' = r then Real.log (5 / 3) else -Real.log (5 / 3))
        else (if r' = r then -Real.log (5 / 3) else Real.log (5 / 3)) := by
  have h53 : Real.log (3 / 5 : ℝ) = -Real.log (5 / 3) := by
    rw [show (3 / 5 : ℝ) = (5 / 3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  show 1 * Real.log ((agent.protocol.stage (3 * m + 1) w (r, e)).p (r', e') /
      (agent.protocol.stage (3 * m + 1) w (r', e')).p (r, e)) = _
  simp only [ContinuingAgent.protocol_stage, ContinuingAgent.stage_learn, learnStage_apply,
    drift]
  cases w <;> cases r <;> cases e <;> cases r' <;> cases e' <;>
    norm_num [h53]

/-- The preparation stage's heat is the erasure's: clearing a set flag delivers
`log 3` to the reservoir and the reverse path draws it back. -/
theorem reset_heat_apply (m : ℕ) (w r e r' e' : Bool) :
    agent.protocol.stageHeat 1 (3 * m + 2) w (r, e) (r', e') =
      if e = e' then 0 else (if e' then -Real.log 3 else Real.log 3) := by
  have h3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.log_inv]
  show 1 * Real.log ((agent.protocol.stage (3 * m + 2) w (r, e)).p (r', e') /
      (agent.protocol.stage (3 * m + 2) w (r', e')).p (r, e)) = _
  simp only [ContinuingAgent.protocol_stage, ContinuingAgent.stage_reset, resetStage_apply,
    drift, reset]
  cases w <;> cases r <;> cases e <;> cases r' <;> cases e' <;>
    norm_num [h3]

/-! ## The expected cost of each operation on the actual law -/

/-- Acting costs work whenever the register's action is the rewarding one more
often than not: the actuator is pushing the flag away from where its own
reservoir would relax it. -/
theorem act_cost (m : ℕ) (aT aF dT dF : ℝ)
    (h : ∀ z, (agent.law (3 * m)).p z = masses aT aF dT dF z) :
    (agent.protocol.step (3 * m)).meanHeat (agent.protocol.stageHeat 1 (3 * m)) =
      (-(3 / 16) * aT + 11 / 16 * aF - 1 / 16 * dT + 3 / 16 * dF) * Real.log 3 := by
  rw [agent.meanHeat_apply]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ContinuingAgent.stage_act, h,
    actStage_apply, act_heat_apply, masses, drift, actuate]
  norm_num
  ring

/-- **The learning stage costs the same whatever the agent has learned.** Its
heat is a property of the update rule and the observation channel, not of the
law they act on, so no amount of accumulated bias makes learning cheaper. -/
theorem learn_cost (m : ℕ) :
    (agent.protocol.step (3 * m + 1)).meanHeat (agent.protocol.stageHeat 1 (3 * m + 1)) =
      1 / 16 * Real.log (5 / 3) := by
  rw [agent.meanHeat_apply]
  have hsum : ∑ z, (agent.law (3 * m + 1)).p z = 1 := (agent.law (3 * m + 1)).sum_one
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ContinuingAgent.stage_learn,
    learnStage_apply, learn_heat_apply, drift] at *
  norm_num at hsum ⊢
  linear_combination (1 / 16 * Real.log (5 / 3)) * hsum

/-- Preparing costs the flag's own excess over its standard law: the more often
the action succeeded, the more the erasure has to dissipate. -/
theorem reset_cost (m : ℕ) (aT aF dT dF : ℝ)
    (h : ∀ z, (agent.law (3 * m + 2)).p z = masses aT aF dT dF z) :
    (agent.protocol.step (3 * m + 2)).meanHeat (agent.protocol.stageHeat 1 (3 * m + 2)) =
      (3 / 4 * (aT + dT) - 1 / 4 * (aF + dF)) * Real.log 3 := by
  rw [agent.meanHeat_apply]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ContinuingAgent.stage_reset, h,
    resetStage_apply, reset_heat_apply, masses, drift, reset]
  norm_num
  ring

/-! ## One cycle, exactly -/

/-- The law two stages into a cycle, from the factorized law the cycle starts
at: the action has correlated agreement with the flag and the update has
consumed that correlation. -/
theorem learn_end_masses (m : ℕ) (a t : ℝ)
    (h : ∀ z, (agent.law (3 * m)).p z =
      masses (a * t) (a * (1 - t)) ((1 - a) * t) ((1 - a) * (1 - t)) z)
    (z : Bool × Bool × Bool) :
    (agent.law (3 * m + 2)).p z =
      masses (3 / 16 + 5 * a / 32 + 3 * t / 32 - 3 * (a * t) / 32)
        (11 / 32 - 5 * a / 32 - 5 * t / 32 + 5 * (a * t) / 32)
        (3 / 16 + 3 * a / 32 + 5 * t / 32 - 5 * (a * t) / 32)
        (9 / 32 - 3 * a / 32 - 3 * t / 32 + 3 * (a * t) / 32) z := by
  have h2 := learn_masses m _ _ _ _ (act_masses m _ _ _ _ h)
  rw [h2 z]
  exact masses_congr (by ring) (by ring) (by ring) (by ring) z

/-- **The cycle map.** A cycle takes the factorized law at agreement `a` and
flag probability `t` to the factorized law at flag probability `1/4` and
agreement `33/64 - t(1-a)/32`. The flag is back where the preparation puts it;
what the cycle has kept is the agreement. -/
theorem cycle_masses (m : ℕ) (a t : ℝ)
    (h : ∀ z, (agent.law (3 * m)).p z =
      masses (a * t) (a * (1 - t)) ((1 - a) * t) ((1 - a) * (1 - t)) z)
    (z : Bool × Bool × Bool) :
    (agent.law (3 * (m + 1))).p z =
      masses ((33 / 64 - t / 32 + a * t / 32) * (1 / 4))
        ((33 / 64 - t / 32 + a * t / 32) * (1 - 1 / 4))
        ((1 - (33 / 64 - t / 32 + a * t / 32)) * (1 / 4))
        ((1 - (33 / 64 - t / 32 + a * t / 32)) * (1 - 1 / 4)) z := by
  have h3 := reset_masses m _ _ _ _ (learn_end_masses m a t h)
  rw [show 3 * (m + 1) = 3 * m + 3 by ring, h3 z]
  exact masses_congr (by ring) (by ring) (by ring) (by ring) z

/-- The register's agreement with the unknown parameter after `m + 1` complete
cycles. The prior's agreement is `1/2`; the first cycle takes it to `65/128` and
every later cycle applies the same affine map, whose fixed point is `65/127`. -/
noncomputable def agreement : ℕ → ℝ
  | 0 => 65 / 128
  | m + 1 => 65 / 128 + agreement m / 128

/-- The law at the start of every cycle after the first: the flag is standard and
independent, and the one thing carried over is the agreement. -/
theorem law_cycle (m : ℕ) (z : Bool × Bool × Bool) :
    (agent.law (3 * (m + 1))).p z =
      masses (agreement m * (1 / 4)) (agreement m * (1 - 1 / 4))
        ((1 - agreement m) * (1 / 4)) ((1 - agreement m) * (1 - 1 / 4)) z := by
  induction m generalizing z with
  | zero =>
    have h0 : ∀ z : Bool × Bool × Bool, (agent.law (3 * 0)).p z =
        masses (1 / 2 * (1 / 2)) (1 / 2 * (1 - 1 / 2)) ((1 - 1 / 2) * (1 / 2))
          ((1 - 1 / 2) * (1 - 1 / 2)) z := by
      intro z
      rw [show 3 * 0 = 0 from rfl, law_zero_masses z]
      exact masses_congr (by norm_num) (by norm_num) (by norm_num) (by norm_num) z
    rw [cycle_masses 0 (1 / 2) (1 / 2) h0 z]
    exact masses_congr (by norm_num [agreement]) (by norm_num [agreement])
      (by norm_num [agreement]) (by norm_num [agreement]) z
  | succ m ih =>
    rw [cycle_masses (m + 1) (agreement m) (1 / 4) ih z]
    refine masses_congr ?_ ?_ ?_ ?_ z <;> simp only [agreement] <;> ring

theorem agreement_mem (m : ℕ) : 0 ≤ agreement m ∧ agreement m ≤ 1 := by
  induction m with
  | zero => constructor <;> norm_num [agreement]
  | succ m ih => constructor <;> simp only [agreement] <;> linarith [ih.1, ih.2]

/-- Every cycle of the mathematical protocol has agreement above chance.
The finite store does not fund this indefinite continuation. -/
theorem agreement_gt_half (m : ℕ) : 1 / 2 < agreement m := by
  induction m with
  | zero => norm_num [agreement]
  | succ m ih => simp only [agreement]; linarith [(agreement_mem m).1]

/-- Every cycle's law is a law the agent is actually in, so the persistence
above is the persistence of the executed behaviour. -/
theorem performance_cycle (m : ℕ) : agent.performance (3 * (m + 1)) = agreement m := by
  unfold ContinuingAgent.performance
  simp only [law_cycle]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, masses, agent, reward, readout]
  norm_num
  ring

theorem performance_zero : agent.performance 0 = 1 / 2 := by
  unfold ContinuingAgent.performance
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ContinuingAgent.law_zero, agent,
    prior, reward, readout]
  norm_num

/-- The register executes the rewarding action strictly more often than the prior
does, at every completed cycle. -/
theorem performance_improves (m : ℕ) :
    agent.performance 0 < agent.performance (3 * (m + 1)) := by
  rw [performance_zero, performance_cycle]
  exact agreement_gt_half m

/-! ## The store -/

/-- The declared store: four units of `log 3` of usable work, a degenerate
register energy so that every path's heat is paid by the store, and one
reservoir temperature. Nothing replenishes it. -/
noncomputable def process : ContinuingProcess Bool (Bool × Bool) where
  protocol := agent.protocol
  energy := fun _ => 0
  heat := agent.protocol.stageHeat 1
  temperature := 1
  stored := 4 * Real.log 3

theorem stageWork_eq (n : ℕ) : process.stageWork n = agent.protocol.stageHeat 1 n := by
  funext x s t
  simp only [ContinuingProcess.stageWork, protocolWork, process, sub_zero, zero_add]

theorem totalWork_succ (n : ℕ) :
    process.totalWork (n + 1) =
      process.totalWork n + (agent.protocol.step n).meanHeat (agent.protocol.stageHeat 1 n) := by
  unfold ContinuingProcess.totalWork
  rw [Finset.sum_range_succ, stageWork_eq]
  rfl

@[simp] theorem totalWork_zero : process.totalWork 0 = 0 := by
  unfold ContinuingProcess.totalWork
  simp

/-- The work each operation of one cycle draws from the store, in the cycle's own
starting parameters. The learning stage's share does not depend on them. -/
theorem act_cycle_cost (m : ℕ) (a t : ℝ)
    (h : ∀ z, (agent.law (3 * m)).p z =
      masses (a * t) (a * (1 - t)) ((1 - a) * t) ((1 - a) * (1 - t)) z) :
    (agent.protocol.step (3 * m)).meanHeat (agent.protocol.stageHeat 1 (3 * m)) =
      (3 / 16 + a / 2 - t / 4 - 5 * (a * t) / 8) * Real.log 3 := by
  rw [act_cost m _ _ _ _ h]; ring

theorem reset_cycle_cost (m : ℕ) (a t : ℝ)
    (h : ∀ z, (agent.law (3 * m)).p z =
      masses (a * t) (a * (1 - t)) ((1 - a) * t) ((1 - a) * (1 - t)) z) :
    (agent.protocol.step (3 * m + 2)).meanHeat (agent.protocol.stageHeat 1 (3 * m + 2)) =
      (1 / 8 + a / 4 + t / 4 - a * t / 4) * Real.log 3 := by
  rw [reset_cost m _ _ _ _ (learn_end_masses m a t h)]; ring

/-- One cycle's total draw on the store. -/
theorem cycle_work (m : ℕ) (a t : ℝ)
    (h : ∀ z, (agent.law (3 * m)).p z =
      masses (a * t) (a * (1 - t)) ((1 - a) * t) ((1 - a) * (1 - t)) z) :
    process.totalWork (3 * m + 3) =
      process.totalWork (3 * m) +
        ((3 / 16 + a / 2 - t / 4 - 5 * (a * t) / 8) + (1 / 8 + a / 4 + t / 4 - a * t / 4)) *
          Real.log 3 + 1 / 16 * Real.log (5 / 3) := by
  rw [show 3 * m + 3 = (3 * m + 2) + 1 from rfl, totalWork_succ,
    show 3 * m + 2 = (3 * m + 1) + 1 from rfl, totalWork_succ, totalWork_succ,
    act_cycle_cost m a t h, learn_cost m,
    show (3 * m + 1) + 1 = 3 * m + 2 from rfl, reset_cycle_cost m a t h]
  ring

/-- The first cycle, funded exactly. -/
theorem first_cycle_work :
    process.totalWork 3 = 15 / 32 * Real.log 3 + 1 / 16 * Real.log (5 / 3) := by
  have h0 : ∀ z : Bool × Bool × Bool, (agent.law (3 * 0)).p z =
      masses (1 / 2 * (1 / 2)) (1 / 2 * (1 - 1 / 2)) ((1 - 1 / 2) * (1 / 2))
        ((1 - 1 / 2) * (1 - 1 / 2)) z := by
    intro z
    rw [show 3 * 0 = 0 from rfl, law_zero_masses z]
    exact masses_congr (by norm_num) (by norm_num) (by norm_num) (by norm_num) z
  have h := cycle_work 0 (1 / 2) (1 / 2) h0
  norm_num at h
  rw [h]

/-! ## Persistence has a positive recurring cost -/

/-- The agreement bound concerns the mathematical protocol at any cycle; the
finite store below only funds prefixes satisfying `Sustains`. -/
theorem performance_persists (m : ℕ) : 65 / 128 ≤ agent.performance (3 * (m + 1)) := by
  rw [performance_cycle]
  cases m with
  | zero => exact le_rfl
  | succ m => simp only [agreement]; linarith [(agreement_mem m).1]

theorem agreement_strict (m : ℕ) : agreement m < agreement (m + 1) := by
  induction m with
  | zero => norm_num [agreement]
  | succ m ih => simp only [agreement] at *; linarith

/-- Successive cycle laws differ, so the learner neither freezes nor resets its
register to a freshly supplied prior. This is a statement about distributions. -/
theorem successive_cycle_laws_differ (m : ℕ) :
    agent.law (3 * (m + 1)) ≠ agent.law (3 * m) := by
  intro h
  have hp : agent.performance (3 * (m + 1)) = agent.performance (3 * m) := by
    unfold ContinuingAgent.performance
    rw [h]
  cases m with
  | zero =>
    rw [performance_cycle, show 3 * 0 = 0 from rfl, performance_zero] at hp
    norm_num [agreement] at hp
  | succ m =>
    rw [performance_cycle, performance_cycle] at hp
    exact ne_of_gt (agreement_strict m) hp

theorem log_three_pos : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
theorem log_ratio_pos : 0 < Real.log (5 / 3 : ℝ) := Real.log_pos (by norm_num)
theorem log_ratio_lt : Real.log (5 / 3 : ℝ) < Real.log 3 :=
  Real.log_lt_log (by norm_num) (by norm_num)

/-- The initial law is explicitly supplied. The first executed act--learn--reset
cycle uses it without further preparation between stages. -/
theorem initial_factorized (z : Bool × Bool × Bool) :
    (agent.law (3 * 0)).p z =
      masses (1 / 2 * (1 / 2)) (1 / 2 * (1 - 1 / 2))
        ((1 - 1 / 2) * (1 / 2)) ((1 - 1 / 2) * (1 - 1 / 2)) z := by
  rw [show 3 * 0 = 0 from rfl, law_zero_masses]
  exact masses_congr (by norm_num) (by norm_num) (by norm_num) (by norm_num) z

/-- Even a factorized starting law with arbitrary agreement and flag occupancy
in the unit interval pays this cycle cost. No stationary law is used. -/
theorem cycle_work_lower (m : ℕ) (a t : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : t ≤ 1)
    (h : ∀ z, (agent.law (3 * m)).p z =
      masses (a * t) (a * (1 - t)) ((1 - a) * t) ((1 - a) * (1 - t)) z) :
    process.totalWork (3 * m) +
      (3 / 16 * Real.log 3 + 1 / 16 * Real.log (5 / 3)) ≤ process.totalWork (3 * m + 3) := by
  rw [cycle_work m a t h]
  have hc : 3 / 16 ≤
      (3 / 16 + a / 2 - t / 4 - 5 * (a * t) / 8) +
        (1 / 8 + a / 4 + t / 4 - a * t / 4) := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ht)]
  nlinarith [mul_le_mul_of_nonneg_right hc log_three_pos.le]

/-- Every complete cycle consumes a fixed positive minimum of expected work.
The bound includes the reset, and applies only to the declared reservoir model. -/
theorem totalWork_cycles_lower (m : ℕ) :
    (m : ℝ) * (3 / 16 * Real.log 3 + 1 / 16 * Real.log (5 / 3)) ≤
      process.totalWork (3 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : process.totalWork (3 * m) +
        (3 / 16 * Real.log 3 + 1 / 16 * Real.log (5 / 3)) ≤
          process.totalWork (3 * m + 3) := by
      cases m with
      | zero =>
        exact cycle_work_lower 0 (1 / 2) (1 / 2)
          (by norm_num) (by norm_num) (by norm_num) initial_factorized
      | succ m =>
        exact cycle_work_lower (m + 1) (agreement m) (1 / 4)
          (agreement_mem m).1 (agreement_mem m).2 (by norm_num) (law_cycle m)
    rw [show 3 * (m + 1) = 3 * m + 3 by ring]
    push_cast
    linarith

/-- The declared store cannot fund 22 complete cycles even in expectation;
this conservative bound is not an exact exhaustion time. -/
theorem store_exhausted : ¬ process.Sustains (3 * 22) := by
  apply process.not_sustains_of_totalWork_gt
  have h := totalWork_cycles_lower 22
  change 4 * Real.log 3 < process.totalWork (3 * 22)
  norm_num at h ⊢
  nlinarith [log_three_pos, log_ratio_pos]

/-- Every prefix of the first cycle fits the declared expected-work allowance.
This does not promise that every stochastic realization fits a battery. -/
theorem first_cycle_sustained : process.Sustains 3 := by
  have h1 : process.totalWork 1 = 5 / 32 * Real.log 3 := by
    rw [totalWork_succ, totalWork_zero, act_cost 0 _ _ _ _ law_zero_masses]
    ring
  have h2 : process.totalWork 2 = 5 / 32 * Real.log 3 + 1 / 16 * Real.log (5 / 3) := by
    rw [totalWork_succ, h1, learn_cost 0]
  intro k hk
  unfold ContinuingProcess.remaining
  change 0 ≤ 4 * Real.log 3 - process.totalWork k
  interval_cases k <;> simp only [totalWork_zero, h1, h2, first_cycle_work] <;>
    linarith [log_three_pos, log_ratio_lt]

/-- The reset dissipates at every actual cycle. It is an executed preparation
of the next flag law, not free restoration of a supplied initial condition. -/
theorem reset_cost_pos (m : ℕ) : 0 <
    (agent.protocol.step (3 * m + 2)).meanHeat (agent.protocol.stageHeat 1 (3 * m + 2)) := by
  cases m with
  | zero =>
    rw [reset_cycle_cost 0 (1 / 2) (1 / 2) initial_factorized]
    positivity
  | succ m =>
    rw [reset_cycle_cost (m + 1) (agreement m) (1 / 4) (law_cycle m)]
    apply mul_pos _ log_three_pos
    linarith [(agreement_mem m).1]

/-- The same degenerate energy pays all stage heat from work, including sensing
and reset, under local detailed balance for the three composite channels. -/
theorem totalHeat_eq_work (N : ℕ) : process.totalHeat N = process.totalWork N := by
  rw [process.totalHeat_eq]
  simp only [process, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]

/-- A concrete instance of the complete-run entropy bound. Preparation of the
uniform prior and microscopic implementations remain outside the accounting. -/
theorem entropy_budget (N : ℕ) (h : process.Sustains N) :
    shannon_entropy (agent.law 0).p - shannon_entropy (agent.law N).p ≤ 4 * Real.log 3 := by
  have hb := process.entropy_reduction_le_stored protocol_positive (by norm_num [process])
    (agent.protocol.local_balance 1) N h
  simpa only [process, one_mul, mul_zero, Finset.sum_const_zero, add_zero, sub_zero,
    ContinuingAgent.protocol_law] using hb

/-- Changing only the register changes the next physical flag transition. The
readout is an actual actuator input; hardware fabrication remains supplied. -/
theorem readout_changes_actuation :
    (agent.actuate false (agent.readout false) false).p true ≠
      (agent.actuate false (agent.readout true) false).p true := by
  norm_num [agent, readout, actuate]

/-! ## Blinding observations and omitting preparation -/

/-- An observation independent of the flag. The actuator, update, drift and
reset remain identical to those of the informative agent. -/
noncomputable def blindSense (_e : Bool) : ProbDist Bool where
  p _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

noncomputable def blind : ContinuingAgent Bool Bool Bool Bool Bool :=
  { agent with sense := blindSense }

/-- Blinding makes the composite register write uniform. This proves that the
update alone cannot insert knowledge of the hidden rewarding action. -/
theorem blind_learn_apply (w r e r' e' : Bool) :
    (blind.learnStage w (r, e)).p (r', e') = 1 / 2 * (drift e).p e' := by
  change (∑ o, (blindSense e).p o * (update o r).p r') * (drift e).p e' = _
  cases r <;> cases r' <;> norm_num [Fintype.sum_bool, blindSense, update]

/-- The blinded learning operation is symmetric, so its assigned heat is zero
on every path, independently of the input law. -/
theorem blind_heat_apply (m : ℕ) (w r e r' e' : Bool) :
    blind.protocol.stageHeat 1 (3 * m + 1) w (r, e) (r', e') = 0 := by
  unfold FiniteProtocol.stageHeat
  simp only [ContinuingAgent.protocol_stage, ContinuingAgent.stage_learn, blind_learn_apply]
  cases e <;> cases e' <;> norm_num [drift]

theorem blind_learn_cost (m : ℕ) :
    (blind.protocol.step (3 * m + 1)).meanHeat (blind.protocol.stageHeat 1 (3 * m + 1)) = 0 := by
  rw [blind.meanHeat_apply]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, blind_heat_apply, mul_zero, add_zero]

/-- After the blinded write, register values have equal mass at each fixed
parameter and flag. The argument allows arbitrary earlier laws. -/
theorem blind_learn_uniform (m : ℕ) (w r e : Bool) :
    (blind.law (3 * m + 2)).p (w, r, e) =
      (blind.law (3 * m + 2)).p (w, false, e) := by
  rw [show 3 * m + 2 = (3 * m + 1) + 1 from rfl]
  simp only [blind.law_succ_apply, ContinuingAgent.stage_learn, Fintype.sum_prod_type,
    Fintype.sum_bool, blind_learn_apply]

/-- Reset preserves the uninformed register produced by the blinded write.
No independent preparation or replacement of the preceding law is used. -/
theorem blind_cycle_uniform (m : ℕ) (w r e : Bool) :
    (blind.law (3 * (m + 1))).p (w, r, e) =
      (blind.law (3 * (m + 1))).p (w, false, e) := by
  rw [show 3 * (m + 1) = (3 * m + 2) + 1 by ring]
  rw [blind.law_succ_apply (3 * m + 2) (w, r, e),
    blind.law_succ_apply (3 * m + 2) (w, false, e)]
  simp only [ContinuingAgent.stage_reset, Fintype.sum_prod_type, Fintype.sum_bool]
  have hr (s t : Bool) :
      (blind.resetStage w (s, t)).p (r, e) = (drift s).p r * (reset t).p e := rfl
  have hf (s t : Bool) :
      (blind.resetStage w (s, t)).p (false, e) = (drift s).p false * (reset t).p e := rfl
  simp only [hr, hf, blind_learn_uniform m w true]
  cases r <;> cases e <;> norm_num [drift, reset] <;> ring

/-- Blinded observations leave chance performance at every completed cycle.
The informative comparison concerns expectations, not every trajectory. -/
theorem blind_performance (m : ℕ) : blind.performance (3 * (m + 1)) = 1 / 2 := by
  have hs := (blind.law (3 * (m + 1))).sum_one
  unfold ContinuingAgent.performance
  change (∑ z, (blind.law (3 * (m + 1))).p z * reward z.1 (readout z.2.1)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, reward, readout] at hs ⊢
  simp only [blind_cycle_uniform m false true, blind_cycle_uniform m true true] at hs ⊢
  norm_num at hs ⊢
  linarith

/-- The reset control replaces just the flag reset with symmetric drift.
It is still a noisy continuing agent, not a model of complete saturation. -/
noncomputable def noReset : ContinuingAgent Bool Bool Bool Bool Bool :=
  { agent with reset := drift }

/-- The control's first completed cycle keeps a nonstandard flag law. The
exact masses are obtained from its own three executed transitions. -/
theorem noReset_first_law (z : Bool × Bool × Bool) :
    (noReset.law 3).p z = masses (69 / 256) (61 / 256) (67 / 256) (59 / 256) z := by
  obtain ⟨w, r, e⟩ := z
  cases w <;> cases r <;> cases e <;>
    norm_num [ContinuingAgent.law, ContinuingAgent.protocol, FiniteProtocol.law,
      FiniteFeedbackStep.final, ContinuingAgent.stage, ContinuingAgent.actStage,
      ContinuingAgent.learnStage, ContinuingAgent.resetStage, noReset, agent, prior,
      readout, drift, actuate, sense, update, ProbDist.prod, ProbDist.bind,
      Fintype.sum_prod_type, Fintype.sum_bool, masses]

/-- The next cycle inherits the control's actual law. This tests the dependence
of later behaviour on reset, not only an isolated reset transition. -/
theorem noReset_second_law (z : Bool × Bool × Bool) :
    (noReset.law 6).p z = masses (2217 / 8192) (485 / 2048) (2155 / 8192) (235 / 1024) z := by
  have h4 (z : Bool × Bool × Bool) := noReset.law_succ_apply 3 z
  have h5 (z : Bool × Bool × Bool) := noReset.law_succ_apply 4 z
  have h6 (z : Bool × Bool × Bool) := noReset.law_succ_apply 5 z
  obtain ⟨w, r, e⟩ := z
  cases w <;> cases r <;> cases e <;>
    simp only [h6, h5, h4, noReset_first_law, Fintype.sum_prod_type, Fintype.sum_bool] <;>
    norm_num [ContinuingAgent.stage, ContinuingAgent.actStage, ContinuingAgent.learnStage,
      ContinuingAgent.resetStage, noReset, agent, readout, drift, actuate, sense, update,
      ProbDist.prod, ProbDist.bind, Fintype.sum_bool, masses]

/-- Omitting reset reduces the reward of the next cycle. It does not remove
all learning: the control's reward remains above chance. -/
theorem reset_changes_next_action : noReset.performance 6 < agent.performance 6 := by
  have h : noReset.performance 6 = 4157 / 8192 := by
    unfold ContinuingAgent.performance
    simp only [noReset_second_law]
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, masses, noReset, agent, reward, readout]
  rw [h, show 6 = 3 * (1 + 1) from rfl, performance_cycle]
  norm_num [agreement]

/-- Reset restores its prescribed flag law; idle drift fails to do so on the
same first episode. A flag value of one is not absorbing in either model. -/
theorem reset_changes_flag :
    (∑ w, ∑ r, (noReset.law 3).p (w, r, true)) = 17 / 32 ∧
      (∑ w, ∑ r, (agent.law 3).p (w, r, true)) = 1 / 4 := by
  constructor
  · norm_num [Fintype.sum_bool, noReset_first_law, masses]
  · norm_num [Fintype.sum_bool, law_cycle 0, masses, agreement]

end Continuing

#print axioms FiniteProtocol.sum_entropy_balance
#print axioms FiniteProtocol.sum_first_law
#print axioms FiniteProtocol.cumulative_entropy_budget
#print axioms ContinuingProcess.totalHeat_le_stored
#print axioms ContinuingProcess.entropy_reduction_le_stored
#print axioms ContinuingProcess.horizon_le_of_cost
#print axioms Continuing.performance_persists
#print axioms Continuing.totalWork_cycles_lower
#print axioms Continuing.first_cycle_sustained
#print axioms Continuing.store_exhausted
#print axioms Continuing.entropy_budget
#print axioms Continuing.readout_changes_actuation
#print axioms Continuing.blind_performance
#print axioms Continuing.blind_learn_cost
#print axioms Continuing.reset_changes_next_action
#print axioms Continuing.reset_cost_pos
#print axioms Continuing.successive_cycle_laws_differ

end PhysicsOfConsciousness.Examples
