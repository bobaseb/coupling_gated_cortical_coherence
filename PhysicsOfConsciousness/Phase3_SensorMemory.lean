import PhysicsOfConsciousness.Phase3_ContinuingAgent

/-!
# A separately implemented sensor memory, and what clearing it costs

`ContinuingAgent.learnStage` composes sensing and updating into one channel and
marginalizes the observation out between them, so no measurement outcome is ever
held in a physical register and nothing pays to clear one. This file supplies
the missing coordinate.

`memoryHeat` is the mean log-ratio heat of a memory channel on a declared memory
law, and `memoryHeat_const` is the exact cost of an erasure that lands on one
declared law `ν` whatever it is given: `θ (H(μ) − H(ν)) + θ D(μ‖ν)`, the entropy
removed plus the relative entropy of what the memory held from the state it is
driven to. Gibbs turns that identity into Landauer's inequality
(`memoryHeat_ge_entropy_drop`) with the gap named rather than hidden, and the
identity also says what the inequality does not: a memory already at `ν` is free
to clear, and one *more* ordered than `ν` draws heat out of the reservoir.
Clearing is dissipative because of what the memory holds, not by construction.

`MemoryAgent` runs the four operations on the joint state `R × (M × Env)` with
the parameter `W` fixed: **act**, the register's readout drives the world;
**record**, the memory is written from the world the action moved; **learn**, the
register is written from the memory; **clear**, the memory and the world are
prepared for the next episode. Every coordinate not being driven drifts. The
fences are signatures — neither `record`, `update` nor `erase` takes `W`, and
`update` does not take `Env` — and `learn_register_independent` states the second
of them as a theorem: what the register can learn is exactly what the memory
carries.

The protocol is an ordinary `FiniteProtocol`, so the stagewise entropy balance,
the first law and the Gibbs bound of `Phase3_ContinuingAgent` telescope over it
unchanged. What is new is the memory's own account. `memoryLaw` is its marginal;
`memoryLaw_clear` is the one stage at which that marginal is autonomous, and
`memoryLaw_record` is the stage at which it is not — the asymmetry is the point,
because the correlation recording writes is exactly what clearing destroys.
`clear_stageHeat_eq` splits the clear stage's heat into the three coordinates'
own shares and `clear_memoryHeat` identifies the memory's share with
`memoryHeat` on its marginal, so `clear_memoryHeat_const` is the erasure
identity for the agent's own executed paths.

What this supplies is one episode's measurement and its erasure, charged to the
same run that reads the memory. Preparation of the prior, fabrication of the
gates, an external supply for the work, optimal-policy convergence and any
cortical identification remain outside the model, as they are elsewhere in this
development.
-/

namespace PhysicsOfConsciousness

/-! ## What clearing a memory costs -/

/-- Mean log-ratio heat of a memory channel `c` on a declared memory law `μ`, at
thermal scale `θ`. Reading it as heat is local detailed balance at that
register's reservoir, which is a physical input here as everywhere else. -/
noncomputable def memoryHeat {M : Type*} [Fintype M] (θ : ℝ) (μ : ProbDist M)
    (c : M → ProbDist M) : ℝ :=
  ∑ m, ∑ m', μ.p m * (c m).p m' * (θ * Real.log ((c m).p m' / (c m').p m))

variable {M : Type*} [Fintype M]

/-- Splitting a relative-entropy summand needs no positivity of `μ`: a state the
memory never holds contributes nothing to either side. -/
private theorem kl_summand (μ ν : ProbDist M) (hν : ∀ m, 0 < ν.p m) (m : M) :
    μ.p m * Real.log (μ.p m / ν.p m) =
      μ.p m * Real.log (μ.p m) - μ.p m * Real.log (ν.p m) := by
  rcases eq_or_lt_of_le (μ.nonneg m) with h | h
  · rw [← h]; simp
  · rw [Real.log_div h.ne' (hν m).ne']; ring

theorem KL_eq_cross_entropy (μ ν : ProbDist M) (hν : ∀ m, 0 < ν.p m) :
    KL μ ν = -shannon_entropy μ.p - ∑ m, μ.p m * Real.log (ν.p m) := by
  unfold KL shannon_entropy
  simp_rw [kl_summand μ ν hν]
  rw [Finset.sum_sub_distrib]
  ring

/-- **The exact cost of clearing a memory.** An erasure that lands on the law
`ν` whatever it is given removes the memory's entropy and dissipates, on top of
that, the relative entropy of what the memory held from the state it is driven
to. Landauer's bound is the first term; the second is the irreversibility of
using one fixed channel on a law it was not matched to. -/
theorem memoryHeat_const (θ : ℝ) (μ ν : ProbDist M) (hν : ∀ m, 0 < ν.p m) :
    memoryHeat θ μ (fun _ => ν) =
      θ * (shannon_entropy μ.p - shannon_entropy ν.p) + θ * KL μ ν := by
  have hlog (m m' : M) : Real.log (ν.p m' / ν.p m) =
      Real.log (ν.p m') - Real.log (ν.p m) := Real.log_div (hν m').ne' (hν m).ne'
  have key (m : M) :
      (∑ m', μ.p m * ν.p m' * (θ * (Real.log (ν.p m') - Real.log (ν.p m)))) =
        θ * μ.p m * (∑ m', ν.p m' * Real.log (ν.p m')) -
          θ * μ.p m * Real.log (ν.p m) := by
    have e1 (m' : M) :
        μ.p m * ν.p m' * (θ * (Real.log (ν.p m') - Real.log (ν.p m))) =
          θ * μ.p m * (ν.p m' * Real.log (ν.p m')) -
            (θ * μ.p m * Real.log (ν.p m)) * ν.p m' := by ring
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ν.sum_one, mul_one]
  have hcross : ∑ m, (θ * μ.p m * (∑ m', ν.p m' * Real.log (ν.p m')) -
      θ * μ.p m * Real.log (ν.p m)) =
      θ * (∑ m', ν.p m' * Real.log (ν.p m')) -
        θ * ∑ m, μ.p m * Real.log (ν.p m) := by
    have e2 (m : M) : θ * μ.p m * (∑ m', ν.p m' * Real.log (ν.p m')) -
        θ * μ.p m * Real.log (ν.p m) =
        (θ * (∑ m', ν.p m' * Real.log (ν.p m'))) * μ.p m -
          θ * (μ.p m * Real.log (ν.p m)) := by ring
    simp_rw [e2]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, μ.sum_one, mul_one, ← Finset.mul_sum]
  simp only [memoryHeat]
  simp_rw [hlog]
  rw [Finset.sum_congr rfl fun m _ => key m, hcross,
    KL_eq_cross_entropy μ ν hν]
  unfold shannon_entropy
  ring

/-- **Landauer's inequality, with the gap named.** Clearing costs at least the
entropy it removes; the excess is exactly the relative entropy above. -/
theorem memoryHeat_ge_entropy_drop (θ : ℝ) (hθ : 0 ≤ θ) (μ ν : ProbDist M)
    (hν : ∀ m, 0 < ν.p m) :
    θ * (shannon_entropy μ.p - shannon_entropy ν.p) ≤ memoryHeat θ μ (fun _ => ν) := by
  rw [memoryHeat_const θ μ ν hν]
  have := KL_nonneg μ ν hν
  nlinarith

/-- A memory already at the standard state is free to clear. -/
theorem memoryHeat_self (θ : ℝ) (ν : ProbDist M) (hν : ∀ m, 0 < ν.p m) :
    memoryHeat θ ν (fun _ => ν) = 0 := by
  have hKL : KL ν ν = 0 := by
    unfold KL
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [div_self (hν m).ne', Real.log_one, mul_zero]
  rw [memoryHeat_const θ ν ν hν, hKL, sub_self]
  ring

/-! ## The agent, with the memory as a coordinate of its state -/

/-- A finite agent whose measurement outcome is held in a register of its own.
`Env` is the part of the world the action changes and the measurement reads;
`M` is the sensor memory; the parameter `W` is fixed and drives the actuator
without being an input to anything the agent computes.

The fences are the signatures. `record` does not see `W`, so the measurement
cannot read the unknown parameter; `update` sees neither `W` nor `Env`, so the
register learns only what the memory carries; `erase` sees nothing but the
memory, so clearing cannot be conditioned on the world it was measuring. The
three idle channels are the drift of whichever coordinate is not being driven:
a physical register does not hold perfectly still while another is written. -/
structure MemoryAgent (W R M Env A : Type*) [Fintype W] [Fintype R] [Fintype M]
    [Fintype Env] [Fintype A] where
  /-- Joint law of parameter, register, memory and world before the first
  operation. Its preparation is supplied, not derived. -/
  prior : ProbDist (W × (R × (M × Env)))
  /-- The register's value decodes to the executed action. -/
  readout : R → A
  /-- What the executed action does to the world, at the actual parameter. -/
  actuate : W → A → Env → ProbDist Env
  /-- The measurement: the memory is written from the world the action moved.
  It may depend on what the memory already holds, so a memory left uncleared is
  not silently overwritten. -/
  record : Env → M → ProbDist M
  /-- The register update, driven by the memory alone. -/
  update : M → R → ProbDist R
  /-- Clearing the memory: an executed operation like any other. -/
  erase : M → ProbDist M
  /-- Preparation of the next episode's world. -/
  reset : Env → ProbDist Env
  /-- The register's drift while it is not being written. -/
  registerIdle : R → ProbDist R
  /-- The memory's drift while it is not being written. -/
  memoryIdle : M → ProbDist M
  /-- The world's drift while it is not being acted on. -/
  envIdle : Env → ProbDist Env
  /-- The evaluation criterion. It is a modelling input and enters no channel. -/
  reward : W → A → ℝ

namespace MemoryAgent

variable {W R M Env A : Type*} [Fintype W] [Fintype R] [Fintype M] [Fintype Env]
  [Fintype A] (G : MemoryAgent W R M Env A)

/-- Acting: the register's readout drives the world; register and memory drift. -/
noncomputable def actStage (w : W) (z : R × (M × Env)) : ProbDist (R × (M × Env)) :=
  (G.registerIdle z.1).prod
    ((G.memoryIdle z.2.1).prod (G.actuate w (G.readout z.1) z.2.2))

/-- Measuring: the memory is written from the world the action moved; the
register and the world drift. The outcome is retained. -/
noncomputable def recordStage (_w : W) (z : R × (M × Env)) : ProbDist (R × (M × Env)) :=
  (G.registerIdle z.1).prod ((G.record z.2.2 z.2.1).prod (G.envIdle z.2.2))

/-- Learning: the register is written from the memory; memory and world drift. -/
noncomputable def learnStage (_w : W) (z : R × (M × Env)) : ProbDist (R × (M × Env)) :=
  (G.update z.2.1 z.1).prod ((G.memoryIdle z.2.1).prod (G.envIdle z.2.2))

/-- Clearing: the memory is driven toward its standard state and the world is
prepared for the next episode; the register drifts. -/
noncomputable def clearStage (_w : W) (z : R × (M × Env)) : ProbDist (R × (M × Env)) :=
  (G.registerIdle z.1).prod ((G.erase z.2.1).prod (G.reset z.2.2))

/-- The four operations in order, repeated. The index counts operations. -/
noncomputable def stage (n : ℕ) : W → (R × (M × Env)) → ProbDist (R × (M × Env)) :=
  if n % 4 = 0 then G.actStage else if n % 4 = 1 then G.recordStage
  else if n % 4 = 2 then G.learnStage else G.clearStage

/-- The whole run as one time-dependent protocol on one evolving joint law. -/
noncomputable def protocol : FiniteProtocol W (R × (M × Env)) := ⟨G.prior, G.stage⟩

/-- The actual joint law of parameter, register, memory and world after `n`
operations. -/
noncomputable def law (n : ℕ) : ProbDist (W × (R × (M × Env))) := G.protocol.law n

@[simp] theorem law_zero : G.law 0 = G.prior := rfl

@[simp] theorem protocol_stage (n : ℕ) : G.protocol.stage n = G.stage n := rfl

@[simp] theorem protocol_law (n : ℕ) : G.protocol.law n = G.law n := rfl

theorem law_succ_apply (n : ℕ) (z : W × (R × (M × Env))) :
    (G.law (n + 1)).p z = ∑ s, (G.law n).p (z.1, s) * (G.stage n z.1 s).p z.2 :=
  G.protocol.law_succ_apply n z

theorem meanHeat_apply (q : W → (R × (M × Env)) → (R × (M × Env)) → ℝ) (n : ℕ) :
    (G.protocol.step n).meanHeat q =
      ∑ w, ∑ s, ∑ t, (G.law n).p (w, s) * (G.stage n w s).p t * q w s t :=
  G.protocol.meanHeat_apply q n

@[simp] theorem stage_act (m : ℕ) : G.stage (4 * m) = G.actStage := by
  have h : 4 * m % 4 = 0 := by omega
  simp only [stage, h, reduceIte]

@[simp] theorem stage_record (m : ℕ) : G.stage (4 * m + 1) = G.recordStage := by
  have h : (4 * m + 1) % 4 = 1 := by omega
  simp only [stage, h]
  norm_num

@[simp] theorem stage_learn (m : ℕ) : G.stage (4 * m + 2) = G.learnStage := by
  have h : (4 * m + 2) % 4 = 2 := by omega
  simp only [stage, h]
  norm_num

@[simp] theorem stage_clear (m : ℕ) : G.stage (4 * m + 3) = G.clearStage := by
  have h : (4 * m + 3) % 4 = 3 := by omega
  simp only [stage, h]
  norm_num

theorem stage_eq_clear (n : ℕ) (h : n % 4 = 3) : G.stage n = G.clearStage := by
  simp only [stage, h]
  norm_num

theorem stage_eq_record (n : ℕ) (h : n % 4 = 1) : G.stage n = G.recordStage := by
  simp only [stage, h]
  norm_num

theorem stage_eq_act (n : ℕ) (h : n % 4 = 0) : G.stage n = G.actStage := by
  simp only [stage, h, reduceIte]

theorem stage_eq_learn (n : ℕ) (h : n % 4 = 2) : G.stage n = G.learnStage := by
  simp only [stage, h]
  norm_num

/-- Strict support of the prior and of every channel the agent executes. -/
def Positive : Prop :=
  (∀ z, 0 < G.prior.p z) ∧ (∀ w a e e', 0 < (G.actuate w a e).p e') ∧
    (∀ e m m', 0 < (G.record e m).p m') ∧ (∀ m r r', 0 < (G.update m r).p r') ∧
    (∀ m m', 0 < (G.erase m).p m') ∧ (∀ e e', 0 < (G.reset e).p e') ∧
    (∀ r r', 0 < (G.registerIdle r).p r') ∧ (∀ m m', 0 < (G.memoryIdle m).p m') ∧
    (∀ e e', 0 < (G.envIdle e).p e')

theorem protocol_positive (h : G.Positive) : G.protocol.Positive := by
  obtain ⟨hp, ha, hrec, hu, he, hr, hri, hmi, hei⟩ := h
  refine ⟨hp, fun n w z z' => ?_⟩
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  show 0 < (G.stage n w z).p z'
  rcases h4 with h4 | h4 | h4 | h4
  · rw [G.stage_eq_act n h4]
    exact mul_pos (hri _ _) (mul_pos (hmi _ _) (ha _ _ _ _))
  · rw [G.stage_eq_record n h4]
    exact mul_pos (hri _ _) (mul_pos (hrec _ _ _) (hei _ _))
  · rw [G.stage_eq_learn n h4]
    exact mul_pos (hu _ _ _) (mul_pos (hmi _ _) (hei _ _))
  · rw [G.stage_eq_clear n h4]
    exact mul_pos (hri _ _) (mul_pos (he _ _) (hr _ _))

/-- Expected reward of the action the register actually executes, read from the
same evolving law as every balance in `Phase3_ContinuingAgent`. -/
noncomputable def performance (n : ℕ) : ℝ :=
  ∑ z, (G.law n).p z * G.reward z.1 (G.readout z.2.1)

/-! ### The fence, as a theorem -/

/-- At the learn stage the register's transition is `update m r`: the world
enters only through the memory. -/
theorem learnStage_register (w : W) (r r' : R) (m : M) (e : Env) :
    (∑ y, (G.learnStage w (r, (m, e))).p (r', y)) = (G.update m r).p r' := by
  have hy : ∀ y : M × Env, (G.learnStage w (r, (m, e))).p (r', y) =
      (G.update m r).p r' * ((G.memoryIdle m).prod (G.envIdle e)).p y :=
    fun _ => rfl
  simp_rw [hy, ← Finset.mul_sum, ProbDist.sum_one, mul_one]

/-- **What the register can learn is what the memory carries.** Two worlds
holding the same memory drive the register identically, at every parameter. -/
theorem learn_register_independent (w w' : W) (r r' : R) (m : M) (e e' : Env) :
    (∑ y, (G.learnStage w (r, (m, e))).p (r', y)) =
      ∑ y, (G.learnStage w' (r, (m, e'))).p (r', y) := by
  rw [G.learnStage_register w r r' m e, G.learnStage_register w' r r' m e']

/-! ### The memory's own law -/

/-- Regrouping the joint state so that the memory is separated from the rest. -/
def memSplit : (M × (W × (R × Env))) ≃ (W × (R × (M × Env))) where
  toFun y := (y.2.1, (y.2.2.1, (y.1, y.2.2.2)))
  invFun z := (z.2.2.1, (z.1, (z.2.1, z.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The same regrouping for the world coordinate. -/
def envSplit : (Env × (W × (R × M))) ≃ (W × (R × (M × Env))) where
  toFun y := (y.2.1, (y.2.2.1, (y.2.2.2, y.1)))
  invFun z := (z.2.2.2, (z.1, (z.2.1, z.2.2.1)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sensor memory's marginal after `n` operations. -/
noncomputable def memoryLaw (n : ℕ) : ProbDist M where
  p m := ∑ z : W × (R × Env), (G.law n).p (z.1, (z.2.1, (m, z.2.2)))
  nonneg _ := Finset.sum_nonneg fun _ _ => (G.law n).nonneg _
  sum_one := by
    have h : ∑ y : M × (W × (R × Env)), (G.law n).p (memSplit y) = 1 := by
      rw [Equiv.sum_comp memSplit (G.law n).p]; exact (G.law n).sum_one
    rw [Fintype.sum_prod_type] at h
    exact h

/-- The world's marginal after `n` operations. -/
noncomputable def envLaw (n : ℕ) : ProbDist Env where
  p e := ∑ z : W × (R × M), (G.law n).p (z.1, (z.2.1, (z.2.2, e)))
  nonneg _ := Finset.sum_nonneg fun _ _ => (G.law n).nonneg _
  sum_one := by
    have h : ∑ y : Env × (W × (R × M)), (G.law n).p (envSplit y) = 1 := by
      rw [Equiv.sum_comp envSplit (G.law n).p]; exact (G.law n).sum_one
    rw [Fintype.sum_prod_type] at h
    exact h

/-- Expectations against the joint law regroup onto the memory's marginal. -/
theorem regroup_mem (n : ℕ) (g : M → ℝ) :
    (∑ w, ∑ s, (G.law n).p (w, s) * g s.2.1) = ∑ m, (G.memoryLaw n).p m * g m := by
  have h1 : (∑ z : W × (R × (M × Env)), (G.law n).p z * g z.2.2.1) =
      ∑ w, ∑ s, (G.law n).p (w, s) * g s.2.1 := Fintype.sum_prod_type ..
  rw [← h1, ← Equiv.sum_comp (memSplit (W := W) (R := R) (M := M) (Env := Env)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  show (∑ z : W × (R × Env), (G.law n).p (z.1, (z.2.1, (m, z.2.2))) * g m) =
    (G.memoryLaw n).p m * g m
  rw [← Finset.sum_mul]
  rfl

/-- The same regrouping onto the world's marginal. -/
theorem regroup_env (n : ℕ) (g : Env → ℝ) :
    (∑ w, ∑ s, (G.law n).p (w, s) * g s.2.2) = ∑ e, (G.envLaw n).p e * g e := by
  have h1 : (∑ z : W × (R × (M × Env)), (G.law n).p z * g z.2.2.2) =
      ∑ w, ∑ s, (G.law n).p (w, s) * g s.2.2 := Fintype.sum_prod_type ..
  rw [← h1, ← Equiv.sum_comp (envSplit (W := W) (R := R) (M := M) (Env := Env)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  show (∑ z : W × (R × M), (G.law n).p (z.1, (z.2.1, (z.2.2, e))) * g e) =
    (G.envLaw n).p e * g e
  rw [← Finset.sum_mul]
  rfl

/-- A mean over the executed paths is bounded by a bound on the observable. -/
theorem joint_le (n : ℕ) (g : W → (R × (M × Env)) → ℝ) (b : ℝ)
    (h : ∀ w s, g w s ≤ b) : (∑ w, ∑ s, (G.law n).p (w, s) * g w s) ≤ b := by
  have hone : (∑ w, ∑ s, (G.law n).p (w, s)) = 1 := by
    have := (G.law n).sum_one
    rwa [Fintype.sum_prod_type] at this
  have hle : (∑ w, ∑ s, (G.law n).p (w, s) * g w s) ≤ ∑ w, ∑ s, (G.law n).p (w, s) * b :=
    Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (h w s) ((G.law n).nonneg _)
  calc (∑ w, ∑ s, (G.law n).p (w, s) * g w s)
      ≤ ∑ w, ∑ s, (G.law n).p (w, s) * b := hle
    _ = b := by simp_rw [← Finset.sum_mul]; rw [hone, one_mul]

theorem le_joint (n : ℕ) (g : W → (R × (M × Env)) → ℝ) (a : ℝ)
    (h : ∀ w s, a ≤ g w s) : a ≤ ∑ w, ∑ s, (G.law n).p (w, s) * g w s := by
  have hone : (∑ w, ∑ s, (G.law n).p (w, s)) = 1 := by
    have := (G.law n).sum_one
    rwa [Fintype.sum_prod_type] at this
  have hle : (∑ w, ∑ s, (G.law n).p (w, s) * a) ≤ ∑ w, ∑ s, (G.law n).p (w, s) * g w s :=
    Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (h w s) ((G.law n).nonneg _)
  calc a = ∑ w, ∑ s, (G.law n).p (w, s) * a := by
        simp_rw [← Finset.sum_mul]; rw [hone, one_mul]
    _ ≤ _ := hle

/-! ### How each operation moves the memory's law -/

/-- Collapsing the two coordinates a product stage does not use. -/
private theorem prod_collapse (P : ProbDist R) (Q : ProbDist M) (S : ProbDist Env)
    (m' : M) : (∑ r', ∑ e', (P.prod (Q.prod S)).p (r', (m', e'))) = Q.p m' := by
  have h : ∀ (r' : R) (e' : Env),
      (P.prod (Q.prod S)).p (r', (m', e')) = P.p r' * (Q.p m' * S.p e') :=
    fun _ _ => rfl
  simp_rw [h, ← Finset.mul_sum, ProbDist.sum_one, mul_one, ← Finset.sum_mul,
    ProbDist.sum_one, one_mul]

private theorem prod_collapse_env (P : ProbDist R) (Q : ProbDist M) (S : ProbDist Env)
    (e' : Env) : (∑ r', ∑ m'', (P.prod (Q.prod S)).p (r', (m'', e'))) = S.p e' := by
  have h : ∀ (r' : R) (m'' : M),
      (P.prod (Q.prod S)).p (r', (m'', e')) = P.p r' * (Q.p m'' * S.p e') :=
    fun _ _ => rfl
  have inner : ∀ r' : R, (∑ m'', P.p r' * (Q.p m'' * S.p e')) = P.p r' * S.p e' := by
    intro r'
    rw [← Finset.mul_sum, ← Finset.sum_mul, Q.sum_one, one_mul]
  simp_rw [h, inner, ← Finset.sum_mul, P.sum_one, one_mul]

/-- The memory's marginal after one stage, from the memory factor of that
stage's channel. -/
private theorem memoryLaw_succ (n : ℕ) (g : W → (R × (M × Env)) → M → ℝ)
    (hcol : ∀ w s m', (∑ r', ∑ e', (G.stage n w s).p (r', (m', e'))) = g w s m')
    (m' : M) :
    (G.memoryLaw (n + 1)).p m' = ∑ w, ∑ s, (G.law n).p (w, s) * g w s m' := by
  have expand : ∀ w : W, (∑ z : R × Env, (G.law (n + 1)).p (w, (z.1, (m', z.2)))) =
      ∑ s, (G.law n).p (w, s) * g w s m' := by
    intro w
    rw [Fintype.sum_prod_type]
    have e1 : ∀ (r' : R) (e' : Env), (G.law (n + 1)).p (w, (r', (m', e'))) =
        ∑ s, (G.law n).p (w, s) * (G.stage n w s).p (r', (m', e')) :=
      fun r' e' => G.law_succ_apply n _
    simp_rw [e1]
    conv_lhs => enter [2, r']; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp_rw [← Finset.mul_sum]
    rw [hcol w s m']
  show (∑ z : W × (R × Env), (G.law (n + 1)).p (z.1, (z.2.1, (m', z.2.2)))) = _
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun w _ => expand w

/-- The world's marginal after one stage, from the world factor of that stage's
channel. -/
private theorem envLaw_succ (n : ℕ) (g : W → (R × (M × Env)) → Env → ℝ)
    (hcol : ∀ w s e', (∑ r', ∑ m'', (G.stage n w s).p (r', (m'', e'))) = g w s e')
    (e' : Env) :
    (G.envLaw (n + 1)).p e' = ∑ w, ∑ s, (G.law n).p (w, s) * g w s e' := by
  have expand : ∀ w : W, (∑ z : R × M, (G.law (n + 1)).p (w, (z.1, (z.2, e')))) =
      ∑ s, (G.law n).p (w, s) * g w s e' := by
    intro w
    rw [Fintype.sum_prod_type]
    have e1 : ∀ (r' : R) (m'' : M), (G.law (n + 1)).p (w, (r', (m'', e'))) =
        ∑ s, (G.law n).p (w, s) * (G.stage n w s).p (r', (m'', e')) :=
      fun r' m'' => G.law_succ_apply n _
    simp_rw [e1]
    conv_lhs => enter [2, r']; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp_rw [← Finset.mul_sum]
    rw [hcol w s e']
  show (∑ z : W × (R × M), (G.law (n + 1)).p (z.1, (z.2.1, (z.2.2, e')))) = _
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun w _ => expand w

/-- **The one stage at which the memory is autonomous.** Under the clear stage
its marginal evolves by the erasure alone: nothing else in the state can be
read, which is what makes the cost below a property of the memory's own law. -/
theorem memoryLaw_clear (n : ℕ) (h : n % 4 = 3) (m' : M) :
    (G.memoryLaw (n + 1)).p m' = ∑ m, (G.memoryLaw n).p m * (G.erase m).p m' := by
  rw [G.memoryLaw_succ n (fun _ s m'' => (G.erase s.2.1).p m'') ?_ m',
    G.regroup_mem n (fun m => (G.erase m).p m')]
  intro w s m''
  rw [G.stage_eq_clear n h]
  exact prod_collapse _ _ _ _

/-- Under an idle stage the memory drifts, and is autonomous for the same
reason. Both the act and the learn stage are of this kind. -/
theorem memoryLaw_idle (n : ℕ) (h : n % 4 = 0 ∨ n % 4 = 2) (m' : M) :
    (G.memoryLaw (n + 1)).p m' = ∑ m, (G.memoryLaw n).p m * (G.memoryIdle m).p m' := by
  rw [G.memoryLaw_succ n (fun _ s m'' => (G.memoryIdle s.2.1).p m'') ?_ m',
    G.regroup_mem n (fun m => (G.memoryIdle m).p m')]
  intro w s m''
  rcases h with h | h
  · rw [G.stage_eq_act n h]; exact prod_collapse _ _ _ _
  · rw [G.stage_eq_learn n h]; exact prod_collapse _ _ _ _

/-- **The stage at which it is not.** A measurement that overwrites the memory
reads the world, so the memory's new law is the world's law pushed through the
measurement channel. The correlation this writes is what the erasure destroys. -/
theorem memoryLaw_record (n : ℕ) (h : n % 4 = 1) (ν : Env → ProbDist M)
    (hrec : ∀ e m, G.record e m = ν e) (m' : M) :
    (G.memoryLaw (n + 1)).p m' = ∑ e, (G.envLaw n).p e * (ν e).p m' := by
  rw [G.memoryLaw_succ n (fun _ s m'' => (ν s.2.2).p m'') ?_ m',
    G.regroup_env n (fun e => (ν e).p m')]
  intro w s m''
  rw [G.stage_eq_record n h]
  show (∑ r', ∑ e', ((G.registerIdle s.1).prod
    ((G.record s.2.2 s.2.1).prod (G.envIdle s.2.2))).p (r', (m'', e'))) = _
  rw [hrec s.2.2 s.2.1]
  exact prod_collapse _ _ _ _

/-- The world's law after an act stage, on the paths the protocol actually has. -/
theorem envLaw_act (n : ℕ) (h : n % 4 = 0) (e' : Env) :
    (G.envLaw (n + 1)).p e' =
      ∑ w, ∑ s, (G.law n).p (w, s) * (G.actuate w (G.readout s.1) s.2.2).p e' := by
  refine G.envLaw_succ n (fun w s e'' => (G.actuate w (G.readout s.1) s.2.2).p e'') ?_ e'
  intro w s e''
  rw [G.stage_eq_act n h]
  exact prod_collapse_env _ _ _ _

/-- That law is a mixture of actuator outputs, so any bound on the actuator
bounds it — whatever the agent has learned and however the world started. -/
theorem envLaw_act_le (n : ℕ) (h : n % 4 = 0) (e' : Env) (b : ℝ)
    (hb : ∀ w a e, (G.actuate w a e).p e' ≤ b) : (G.envLaw (n + 1)).p e' ≤ b := by
  rw [G.envLaw_act n h e']
  exact G.joint_le n _ b fun w s => hb _ _ _

theorem le_envLaw_act (n : ℕ) (h : n % 4 = 0) (e' : Env) (a : ℝ)
    (ha : ∀ w b e, a ≤ (G.actuate w b e).p e') : a ≤ (G.envLaw (n + 1)).p e' := by
  rw [G.envLaw_act n h e']
  exact G.le_joint n _ a fun w s => ha _ _ _

/-! ### The clear stage's heat, and the memory's share of it -/

/-- The register's share of a stage's log-ratio heat. -/
noncomputable def registerHeatObs (θ : ℝ) :
    W → (R × (M × Env)) → (R × (M × Env)) → ℝ :=
  fun _ s t => θ * Real.log ((G.registerIdle s.1).p t.1 / (G.registerIdle t.1).p s.1)

/-- The sensor memory's share: what clearing it costs on that path. -/
noncomputable def eraseHeatObs (θ : ℝ) :
    W → (R × (M × Env)) → (R × (M × Env)) → ℝ :=
  fun _ s t => θ * Real.log ((G.erase s.2.1).p t.2.1 / (G.erase t.2.1).p s.2.1)

/-- The world's share: what preparing the next episode costs on that path. -/
noncomputable def resetHeatObs (θ : ℝ) :
    W → (R × (M × Env)) → (R × (M × Env)) → ℝ :=
  fun _ s t => θ * Real.log ((G.reset s.2.2).p t.2.2 / (G.reset t.2.2).p s.2.2)

/-- **Allocation.** The clear stage drives three coordinates at once, and its
log-ratio heat is exactly the sum of their three own shares. Clearing the memory
is therefore a named part of the operation's cost rather than a quantity
inferred from the total. -/
theorem clear_stageHeat_eq (hG : G.Positive) (θ : ℝ) (n : ℕ) (h : n % 4 = 3)
    (x : W) (s t : R × (M × Env)) :
    G.protocol.stageHeat θ n x s t =
      G.registerHeatObs θ x s t + G.eraseHeatObs θ x s t + G.resetHeatObs θ x s t := by
  obtain ⟨-, -, -, -, he, hres, hri, -, -⟩ := hG
  have hstage : ∀ u v : R × (M × Env), (G.protocol.stage n x u).p v =
      (G.registerIdle u.1).p v.1 *
        ((G.erase u.2.1).p v.2.1 * (G.reset u.2.2).p v.2.2) := by
    intro u v
    show (G.stage n x u).p v = _
    rw [G.stage_eq_clear n h]
    rfl
  show θ * Real.log ((G.protocol.stage n x s).p t / (G.protocol.stage n x t).p s) = _
  rw [hstage s t, hstage t s]
  rw [Real.log_div (mul_pos (hri _ _) (mul_pos (he _ _) (hres _ _))).ne'
        (mul_pos (hri _ _) (mul_pos (he _ _) (hres _ _))).ne',
    Real.log_mul (hri _ _).ne' (mul_pos (he _ _) (hres _ _)).ne',
    Real.log_mul (hri _ _).ne' (mul_pos (he _ _) (hres _ _)).ne',
    Real.log_mul (he _ _).ne' (hres _ _).ne',
    Real.log_mul (he _ _).ne' (hres _ _).ne']
  unfold registerHeatObs eraseHeatObs resetHeatObs
  rw [Real.log_div (hri _ _).ne' (hri _ _).ne', Real.log_div (he _ _).ne' (he _ _).ne',
    Real.log_div (hres _ _).ne' (hres _ _).ne']
  ring

/-- Collapsing a product stage against an observable of the memory alone. -/
private theorem prod_collapse_weighted (P : ProbDist R) (Q : ProbDist M)
    (S : ProbDist Env) (q : M → ℝ) :
    (∑ t : R × (M × Env), (P.prod (Q.prod S)).p t * q t.2.1) =
      ∑ m'', Q.p m'' * q m'' := by
  rw [Fintype.sum_prod_type]
  have inner : ∀ r' : R, (∑ y : M × Env, (P.prod (Q.prod S)).p (r', y) * q y.1) =
      P.p r' * ∑ m'', Q.p m'' * q m'' := by
    intro r'
    rw [Fintype.sum_prod_type]
    have e1 : ∀ (m'' : M) (e' : Env),
        (P.prod (Q.prod S)).p (r', (m'', e')) * q m'' =
          P.p r' * (Q.p m'' * q m'') * S.p e' := by
      intro m'' e'
      show P.p r' * (Q.p m'' * S.p e') * q m'' = _
      ring
    simp_rw [e1, ← Finset.mul_sum, ProbDist.sum_one, mul_one]
    rw [Finset.mul_sum]
  simp_rw [inner, ← Finset.sum_mul, ProbDist.sum_one, one_mul]

/-- **The memory's share is the erasure's own cost.** Averaged over the paths
the protocol actually takes, the memory's part of the clear stage's heat is
`memoryHeat` on the memory's own marginal: nothing in the rest of the state
enters, because the erasure reads nothing else. -/
theorem clear_memoryHeat (θ : ℝ) (n : ℕ) (h : n % 4 = 3) :
    (G.protocol.step n).meanHeat (G.eraseHeatObs θ) =
      memoryHeat θ (G.memoryLaw n) G.erase := by
  rw [G.meanHeat_apply _ n]
  have inner : ∀ (w : W) (s : R × (M × Env)),
      (∑ t, (G.law n).p (w, s) * (G.stage n w s).p t * G.eraseHeatObs θ w s t) =
        (G.law n).p (w, s) *
          ∑ m'', (G.erase s.2.1).p m'' *
            (θ * Real.log ((G.erase s.2.1).p m'' / (G.erase m'').p s.2.1)) := by
    intro w s
    have e1 : ∀ t : R × (M × Env),
        (G.law n).p (w, s) * (G.stage n w s).p t * G.eraseHeatObs θ w s t =
          (G.law n).p (w, s) * ((G.stage n w s).p t *
            (fun m'' => θ * Real.log ((G.erase s.2.1).p m'' /
              (G.erase m'').p s.2.1)) t.2.1) := by
      intro t
      show _ = _
      unfold eraseHeatObs
      ring
    simp_rw [e1, ← Finset.mul_sum]
    congr 1
    rw [G.stage_eq_clear n h]
    exact prod_collapse_weighted (G.registerIdle s.1) (G.erase s.2.1) (G.reset s.2.2)
      fun m'' => θ * Real.log ((G.erase s.2.1).p m'' / (G.erase m'').p s.2.1)
  simp_rw [inner]
  rw [G.regroup_mem n fun m => ∑ m'', (G.erase m).p m'' *
    (θ * Real.log ((G.erase m).p m'' / (G.erase m'').p m))]
  unfold memoryHeat
  simp_rw [Finset.mul_sum, ← mul_assoc]

/-- **What clearing the agent's sensor memory costs, on its own paths.** For an
erasure that lands on one declared standard state, the memory's share of the
clear stage's heat is the entropy it removes from the memory plus the relative
entropy of what the memory held from that standard state. -/
theorem clear_memoryHeat_const (θ : ℝ) (ν : ProbDist M) (hν : ∀ m, 0 < ν.p m)
    (hc : G.erase = fun _ => ν) (n : ℕ) (h : n % 4 = 3) :
    (G.protocol.step n).meanHeat (G.eraseHeatObs θ) =
      θ * (shannon_entropy (G.memoryLaw n).p -
        shannon_entropy (G.memoryLaw (n + 1)).p) + θ * KL (G.memoryLaw n) ν := by
  have hlaw : (G.memoryLaw (n + 1)).p = ν.p := by
    funext m'
    rw [G.memoryLaw_clear n h m', hc]
    simp only [← Finset.sum_mul, (G.memoryLaw n).sum_one, one_mul]
  rw [G.clear_memoryHeat θ n h, hc, memoryHeat_const θ _ ν hν, hlaw]

end MemoryAgent

end PhysicsOfConsciousness
