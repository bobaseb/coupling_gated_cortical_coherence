import PhysicsOfConsciousness.Phase3_SensorMemory

/-!
# Preparing the declared prior

Every finite agent here starts from a law its structure calls `prior`, and every
docstring carrying that field says the same thing: its preparation is supplied,
not derived. The run is charged from that law onward and nothing is charged for
reaching it.

The tool for charging it was built for the other end of the run.
`memoryHeat_const` prices a channel that lands on one declared law whatever it
is given, and a preparation is exactly such a channel: it drives the hardware to
a law without reading what the hardware held. Preparation and erasure are the
same operation, and the identity that prices one prices the other.

`ProbDist.uniform` and `KL_uniform` give the case that matters for the agents in
`Examples`: `D(μ‖uniform) = log|V| - H(μ)`, so the two terms of
`memoryHeat_const` cancel and `memoryHeat_uniform` is zero at every starting law
and every thermal scale. This is the channel's mean log-ratio heat. Interpreting
it as reservoir heat requires local detailed balance; gate construction, control
work and a funding source are not specified by this identity.

`FiniteProtocol.withPreparation` prepends the preparation as an ordinary stage,
so the telescoped entropy balance, the first law and the store bounds of
`Phase3_ContinuingAgent` cover it without a second theory, and
`withPreparation_law_succ` identifies the shifted run with the original one.
`preparation_meanHeat` is its cost.

Two fences are theorems rather than remarks. `preparation_parameter_marginal`
holds for every preparation: the channel does not touch the parameter, so the
agent's uncertainty about the world is an input. `preparation_product` says a
state-blind preparation's output is a product, so a prior correlating the
parameter with the register is not the output of one.

The entropy identity requires a target with full support. The bit preparation
family in `Examples/Preparation.lean` has unbounded mean log-ratio heat from
uniform input at thermal scale one. Its sharp endpoint fails the positivity
premise. This does not establish a cost for every sharp-state implementation:
`Real.log` and division are totalized at zero, so the real-valued expression
alone does not encode an infinite endpoint cost. Preparing the sharp charge of
`Examples/FundedMemory.lean` remains a separate problem.
-/

namespace PhysicsOfConsciousness

namespace ProbDist

/-- The uniform law on a nonempty finite type. -/
noncomputable def uniform (V : Type*) [Fintype V] [Nonempty V] : ProbDist V where
  p _ := (Fintype.card V : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

@[simp] theorem uniform_apply (V : Type*) [Fintype V] [Nonempty V] (v : V) :
    (uniform V).p v = (Fintype.card V : ℝ)⁻¹ := rfl

theorem uniform_pos (V : Type*) [Fintype V] [Nonempty V] (v : V) : 0 < (uniform V).p v :=
  inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

theorem uniform_entropy (V : Type*) [Fintype V] [Nonempty V] :
    shannon_entropy (uniform V).p = Real.log (Fintype.card V) := by
  show -∑ _v : V, (Fintype.card V : ℝ)⁻¹ * Real.log ((Fintype.card V : ℝ)⁻¹) = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_inv]
  field_simp

/-- The system marginal of a joint law. -/
noncomputable def snd {X S : Type*} [Fintype X] [Fintype S] (P : ProbDist (X × S)) :
    ProbDist S where
  p s := ∑ x, P.p (x, s)
  nonneg _ := Finset.sum_nonneg fun _ _ => P.nonneg _
  sum_one := by
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using P.sum_one

@[simp] theorem snd_apply {X S : Type*} [Fintype X] [Fintype S] (P : ProbDist (X × S))
    (s : S) : P.snd.p s = ∑ x, P.p (x, s) := rfl

end ProbDist

/-! ## Uniform preparation has zero mean log-ratio heat -/

/-- Against the uniform reference the divergence is the entropy deficit. No
positivity of `μ` is needed: a state of zero mass contributes to neither side. -/
theorem KL_uniform {V : Type*} [Fintype V] [Nonempty V] (μ : ProbDist V) :
    KL μ (ProbDist.uniform V) = Real.log (Fintype.card V) - shannon_entropy μ.p := by
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hterm (v : V) : μ.p v * Real.log (μ.p v / (ProbDist.uniform V).p v) =
      μ.p v * Real.log (μ.p v) + μ.p v * Real.log (Fintype.card V) := by
    rcases (μ.nonneg v).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [ProbDist.uniform_apply, div_eq_mul_inv, inv_inv,
        Real.log_mul h.ne' hcard.ne']
      ring
  unfold KL shannon_entropy
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_add_distrib, ← Finset.sum_mul,
    μ.sum_one, one_mul]
  ring

/-- A constant channel to the uniform law has zero mean log-ratio heat, at every
starting law and thermal scale. This does not price gate construction or control
work; its reservoir interpretation requires local detailed balance. -/
theorem memoryHeat_uniform {V : Type*} [Fintype V] [Nonempty V] (θ : ℝ) (μ : ProbDist V) :
    memoryHeat θ μ (fun _ => ProbDist.uniform V) = 0 := by
  rw [memoryHeat_const θ μ (ProbDist.uniform V) (ProbDist.uniform_pos V),
    ProbDist.uniform_entropy, KL_uniform μ]
  ring

/-! ## The preparation as a stage of the same protocol -/

namespace FiniteProtocol

variable {X S : Type*} [Fintype X] [Fintype S]

/-- Prepend a channel executed from `blank`; stage `n+1` is the original
protocol's stage `n`. This construction alone does not require the channel to
reach `P.initial`; `withPreparation_law_succ` takes that as a hypothesis. -/
noncomputable def withPreparation (P : FiniteProtocol X S) (blank : ProbDist (X × S))
    (prep : X → S → ProbDist S) : FiniteProtocol X S where
  initial := blank
  stage n := Nat.rec prep (fun k _ => P.stage k) n

@[simp] theorem withPreparation_initial (P : FiniteProtocol X S) (blank : ProbDist (X × S))
    (prep : X → S → ProbDist S) : (P.withPreparation blank prep).initial = blank := rfl

@[simp] theorem withPreparation_stage_zero (P : FiniteProtocol X S)
    (blank : ProbDist (X × S)) (prep : X → S → ProbDist S) :
    (P.withPreparation blank prep).stage 0 = prep := rfl

@[simp] theorem withPreparation_stage_succ (P : FiniteProtocol X S)
    (blank : ProbDist (X × S)) (prep : X → S → ProbDist S) (n : ℕ) :
    (P.withPreparation blank prep).stage (n + 1) = P.stage n := rfl

/-- **The shifted run is the original one.** Once the preparation has landed on
the protocol's declared initial law, every later stage sees exactly the law it
saw before, so no result about `P` is restated for the prepared protocol. -/
theorem withPreparation_law_succ (P : FiniteProtocol X S) (blank : ProbDist (X × S))
    (prep : X → S → ProbDist S)
    (h : (⟨blank, prep⟩ : FiniteFeedbackStep X S).final = P.initial) (n : ℕ) :
    (P.withPreparation blank prep).law (n + 1) = P.law n := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply ProbDist.ext
    funext z
    rw [law_succ_apply, law_succ_apply, ih, withPreparation_stage_succ]

/-- **What the preparation costs.** A state-blind preparation's stage heat,
averaged over the paths it actually takes, is `memoryHeat` of that channel on
the system marginal of whatever the hardware held. This is an identity of the
real log-ratio expressions; their thermodynamic use requires the support and
local-detailed-balance premises of the cumulative bounds. -/
theorem preparation_meanHeat (P : FiniteProtocol X S) (blank : ProbDist (X × S))
    (θ : ℝ) (ν : ProbDist S) :
    ((P.withPreparation blank fun _ _ => ν).step 0).meanHeat
        ((P.withPreparation blank fun _ _ => ν).stageHeat θ 0) =
      memoryHeat θ blank.snd (fun _ => ν) := by
  rw [meanHeat_apply]
  show (∑ x, ∑ s, ∑ t, blank.p (x, s) * ν.p t * (θ * Real.log (ν.p t / ν.p s))) = _
  rw [Finset.sum_comm]
  unfold memoryHeat
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rfl

end FiniteProtocol

/-! ## What a preparation cannot do -/

/-- **The parameter is not prepared.** A preparation channel writes the system
coordinate and leaves the parameter's marginal exactly as it found it, whatever
the channel is. The agent's uncertainty about the world is an input. -/
theorem preparation_parameter_marginal {X S : Type*} [Fintype X] [Fintype S]
    (blank : ProbDist (X × S)) (prep : X → S → ProbDist S) (x : X) :
    (∑ t, (⟨blank, prep⟩ : FiniteFeedbackStep X S).final.p (x, t)) =
      ∑ s, blank.p (x, s) := by
  show (∑ t, ∑ s, blank.p (x, s) * (prep x s).p t) = _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ProbDist.sum_one, mul_one]

/-- **A state-blind preparation writes no correlation.** Its output is the
product of the parameter marginal it found with the law it lands on, so a prior
in which the parameter and the system are correlated is not its output. -/
theorem preparation_product {X S : Type*} [Fintype X] [Fintype S]
    (blank : ProbDist (X × S)) (ν : ProbDist S) (z : X × S) :
    (⟨blank, fun _ _ => ν⟩ : FiniteFeedbackStep X S).final.p z =
      (∑ s, blank.p (z.1, s)) * ν.p z.2 := by
  show (∑ s, blank.p (z.1, s) * ν.p z.2) = _
  rw [← Finset.sum_mul]

end PhysicsOfConsciousness
