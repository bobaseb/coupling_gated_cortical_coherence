import PhysicsOfConsciousness.Phase3_Preparation
import PhysicsOfConsciousness.Examples.SensorMemory

/-!
# Preparing the sensor-memory agent's prior

The agent of `Examples/SensorMemory.lean` declares a uniform prior on four bits.
`prior_eq_uniform` identifies it with `ProbDist.uniform`, and `memoryHeat_uniform`
then gives zero mean log-ratio heat from any hardware law. The witness runs that
preparation as stage zero of the same protocol: the hardware starts in a skewed
law with full support, the preparation randomizes it, and every later stage sees
the agent's declared law. `blank_ne_prior` proves the preparation changes it.

The contrast is the point. Preparing the agent's own standard state
`(3/4, 1/4)` from uniform costs `(1/4) log 3`, by the same `erase_cost` that
prices its erasure — preparation and erasure are one operation. And the cost of
preparing a bit law biased to `ε` is `(1/2 - ε) log((1-ε)/ε)`, which exceeds any
bound within this family. The sharp endpoint fails the entropy identity's
positive-target premise (`sharp_target_not_positive`); the theorem gives no
universal cost for sharp-state preparation or for implementing these channels.
`known_parameter_not_preparable` and `correlated_not_preparable` fence the
parameter uncertainty and correlations that hardware preparation cannot supply.
-/

namespace PhysicsOfConsciousness

namespace Examples.Prep

open Examples.Sensor

/-! ## The agent's prior is the uniform law -/

theorem prior_eq_uniform : Examples.Sensor.prior = ProbDist.uniform _ := by
  apply ProbDist.ext
  funext z
  show (1 : ℝ) / 16 = (Fintype.card (Bool × (Bool × (Bool × Bool))) : ℝ)⁻¹
  norm_num [Fintype.card_prod]

/-- The system coordinate of the agent: register, memory and world. -/
abbrev Hardware := Bool × (Bool × Bool)

/-- What the hardware held before the preparation: full support, and far from
uniform, so the preparation does something. -/
noncomputable def skew : ProbDist Hardware where
  p s := if s = (false, (false, false)) then 1 / 2 else 1 / 14
  nonneg s := by split <;> norm_num
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num

theorem skew_pos (s : Hardware) : 0 < skew.p s := by
  show (0 : ℝ) < if s = (false, (false, false)) then 1 / 2 else 1 / 14
  split <;> norm_num

/-- The law the run starts from: the parameter is already uncertain, because no
preparation of the agent's own hardware can make it so. -/
noncomputable def blank : ProbDist (Bool × Hardware) where
  p z := 1 / 2 * skew.p z.2
  nonneg z := by have := skew.nonneg z.2; linarith
  sum_one := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [← Finset.mul_sum, ProbDist.sum_one]
    norm_num

@[simp] theorem blank_snd (s : Hardware) : blank.snd.p s = skew.p s := by
  show (∑ x : Bool, 1 / 2 * skew.p s) = skew.p s
  rw [Fintype.sum_bool]
  ring

theorem blank_pos (z : Bool × Hardware) : 0 < blank.p z := by
  show (0 : ℝ) < 1 / 2 * skew.p z.2
  have := skew_pos z.2
  linarith

/-- The preparation changes the witness law; it is not an idle stage appended
to hardware already at the target. This says nothing about its implementation. -/
theorem blank_ne_prior : blank ≠ Examples.Sensor.prior := by
  intro h
  have hp := congrArg (fun μ => μ.p (false, (false, (false, false)))) h
  norm_num [blank, skew, Examples.Sensor.prior] at hp

/-- The preparation: it lands on the uniform law whatever the hardware held, and
it reads neither the hardware nor the parameter. -/
noncomputable def prep : Bool → Hardware → ProbDist Hardware :=
  fun _ _ => ProbDist.uniform Hardware

theorem prep_lands : (⟨blank, prep⟩ : FiniteFeedbackStep Bool Hardware).final =
    Examples.Sensor.agent.protocol.initial := by
  apply ProbDist.ext
  funext z
  show (∑ s, blank.p (z.1, s) * (ProbDist.uniform Hardware).p z.2) = (1 : ℝ) / 16
  rw [← Finset.sum_mul]
  show (∑ s, 1 / 2 * skew.p s) * (Fintype.card Hardware : ℝ)⁻¹ = 1 / 16
  rw [← Finset.mul_sum, ProbDist.sum_one]
  norm_num [Fintype.card_prod]

/-- The whole run, with its own preparation as stage zero. -/
noncomputable def preparedRun : FiniteProtocol Bool Hardware :=
  Examples.Sensor.agent.protocol.withPreparation blank prep

/-- **After the preparation, the run is the agent's own.** -/
theorem prepared_law (n : ℕ) : preparedRun.law (n + 1) = Examples.Sensor.agent.law n :=
  Examples.Sensor.agent.protocol.withPreparation_law_succ blank prep prep_lands n

/-- Preparing this prior has zero mean log-ratio heat at every thermal scale.
Gate construction, control work and a funding source are not specified. -/
theorem preparation_free (θ : ℝ) :
    (preparedRun.step 0).meanHeat (preparedRun.stageHeat θ 0) = 0 := by
  rw [show preparedRun = Examples.Sensor.agent.protocol.withPreparation blank
      (fun _ _ => ProbDist.uniform Hardware) from rfl,
    Examples.Sensor.agent.protocol.preparation_meanHeat blank θ (ProbDist.uniform Hardware)]
  have h : blank.snd = skew := ProbDist.ext (funext blank_snd)
  rw [h]
  exact memoryHeat_uniform θ skew

theorem prepared_positive : preparedRun.Positive := by
  refine ⟨blank_pos, fun n x s t => ?_⟩
  cases n with
  | zero => exact ProbDist.uniform_pos Hardware t
  | succ n =>
    exact (Examples.Sensor.agent.protocol_positive Examples.Sensor.positive).2 n x s t

/-- The preparation is a stage like any other, so the existing cumulative bound
charges the whole run including it. -/
theorem prepared_entropy_budget (N : ℕ) :
    (1 : ℝ) * (shannon_entropy (preparedRun.law 0).p -
        shannon_entropy (preparedRun.law N).p) ≤
      ∑ k ∈ Finset.range N, (preparedRun.step k).meanHeat (preparedRun.stageHeat 1 k) :=
  preparedRun.cumulative_entropy_budget prepared_positive 1 one_pos _
    (preparedRun.local_balance 1) N

/-! ## What a definite target costs -/

/-- Preparing the agent's own standard state from uniform costs what clearing a
uniform memory to it costs: preparation and erasure are one operation. -/
theorem standard_prep_cost :
    memoryHeat 1 (ProbDist.uniform Bool) (fun _ => Examples.Sensor.standard) =
      1 / 4 * Real.log 3 := by
  have h := Examples.Sensor.erase_cost (ProbDist.uniform Bool)
  rw [show (ProbDist.uniform Bool).p false = 1 / 2 by
    show (Fintype.card Bool : ℝ)⁻¹ = 1 / 2; norm_num] at h
  rw [show (fun _ => Examples.Sensor.standard) = Examples.Sensor.erase from rfl, h]
  norm_num

/-- A bit law biased to `ε`. -/
noncomputable def biased (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) : ProbDist Bool where
  p b := if b then ε else 1 - ε
  nonneg b := by cases b <;> simp <;> linarith
  sum_one := by rw [Fintype.sum_bool]; norm_num

/-- **The cost of a biased target, exactly.** -/
theorem biased_prep_cost (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    memoryHeat 1 (ProbDist.uniform Bool) (fun _ => biased ε h0 h1) =
      (1 / 2 - ε) * Real.log ((1 - ε) / ε) := by
  have hne : (1 : ℝ) - ε ≠ 0 := by linarith
  have hhalf : (ProbDist.uniform Bool).p true = 1 / 2 := by
    show (Fintype.card Bool : ℝ)⁻¹ = 1 / 2; norm_num
  have hhalf' : (ProbDist.uniform Bool).p false = 1 / 2 := by
    show (Fintype.card Bool : ℝ)⁻¹ = 1 / 2; norm_num
  have hT : (biased ε h0 h1).p true = ε := rfl
  have hF : (biased ε h0 h1).p false = 1 - ε := rfl
  have hinv : ε / (1 - ε) = ((1 - ε) / ε)⁻¹ := by field_simp
  show (∑ m, ∑ m', (ProbDist.uniform Bool).p m * (biased ε h0 h1).p m' *
    (1 * Real.log ((biased ε h0 h1).p m' / (biased ε h0 h1).p m))) = _
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  rw [hT, hF, hhalf, hhalf', div_self h0.ne', div_self hne, Real.log_one, hinv,
    Real.log_inv]
  ring

/-- The biased bit family has no finite upper bound on its mean log-ratio heat
from uniform input at thermal scale one. The target here remains strictly
positive; this gives neither a value at `ε = 0` nor a bound for other channels. -/
theorem sharp_prep_unbounded (B : ℝ) : ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1),
    B ≤ memoryHeat 1 (ProbDist.uniform Bool) (fun _ => biased ε h0 h1) := by
  set c := max B 0 with hcdef
  have hc : 0 ≤ c := le_max_right B 0
  have hB : B ≤ c := le_max_left B 0
  have hexp : 0 < Real.exp (-(4 * c)) := Real.exp_pos _
  have hexp1 : Real.exp (-(4 * c)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  set ε := Real.exp (-(4 * c)) / 4 with hεdef
  have h0 : 0 < ε := by positivity
  have hq : ε ≤ 1 / 4 := by rw [hεdef]; linarith
  have h1 : ε < 1 := by linarith
  refine ⟨ε, h0, h1, ?_⟩
  rw [biased_prep_cost ε h0 h1]
  have hprod : Real.exp (4 * c) * ε = 1 / 4 := by
    rw [hεdef, ← mul_div_assoc, ← Real.exp_add]
    norm_num
  have hge : Real.exp (4 * c) ≤ (1 - ε) / ε := by
    rw [le_div_iff₀ h0, hprod]
    linarith
  have hlog : 4 * c ≤ Real.log ((1 - ε) / ε) := by
    calc 4 * c = Real.log (Real.exp (4 * c)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hge
  have hfac : (1 : ℝ) / 4 ≤ 1 / 2 - ε := by linarith
  have := mul_le_mul hfac hlog (by linarith) (by linarith)
  linarith

/-! ## What a preparation cannot do -/

/-- Hardware preparation cannot supply the sensor agent's parameter
uncertainty. Even a channel allowed to read the parameter leaves a certain
parameter certain. This does not restrict processes that change the parameter. -/
theorem known_parameter_not_preparable (channel : Bool → Hardware → ProbDist Hardware) :
    (⟨(ProbDist.dirac false).prod skew, channel⟩ :
      FiniteFeedbackStep Bool Hardware).final ≠ Examples.Sensor.prior := by
  intro h
  have hm := preparation_parameter_marginal ((ProbDist.dirac false).prod skew) channel true
  rw [h] at hm
  norm_num [Examples.Sensor.prior, ProbDist.prod_apply, ProbDist.dirac_apply,
    Fintype.sum_prod_type, Fintype.sum_bool] at hm

/-- The sharp bit target is outside the positive-target entropy identity.
This support obstruction assigns no infinite value to the totalized real log. -/
theorem sharp_target_not_positive :
    ¬ ∀ s t : Bool, 0 < ((fun _ => ProbDist.dirac false) s).p t := by
  intro h
  have ht := h false true
  norm_num at ht

/-- A prior in which the parameter and the hardware are correlated. -/
noncomputable def correlatedPrior : ProbDist (Bool × Bool) where
  p z := if z.1 = z.2 then 1 / 2 else 0
  nonneg z := by split <;> norm_num
  sum_one := by simp only [Fintype.sum_prod_type, Fintype.sum_bool]; norm_num

/-- **A state-blind preparation writes no correlation.** No law it could land on
produces this prior, whatever the parameter's marginal already was. -/
theorem correlated_not_preparable : ¬ ∃ ν : ProbDist Bool,
    ∀ z, correlatedPrior.p z = (∑ s, correlatedPrior.p (z.1, s)) * ν.p z.2 := by
  rintro ⟨ν, h⟩
  have hmarg : (∑ s : Bool, correlatedPrior.p (false, s)) = 1 / 2 := by
    rw [Fintype.sum_bool]
    show ((if false = true then (1 : ℝ) / 2 else 0) + if false = false then 1 / 2 else 0) = _
    norm_num
  have hoff := h (false, true)
  rw [hmarg] at hoff
  have hzero : ν.p true = 0 := by
    have : (correlatedPrior.p (false, true)) = 0 := by
      show (if false = true then (1 : ℝ) / 2 else 0) = 0
      norm_num
    rw [this] at hoff
    linarith
  have hmarg' : (∑ s : Bool, correlatedPrior.p (true, s)) = 1 / 2 := by
    rw [Fintype.sum_bool]
    show ((if true = true then (1 : ℝ) / 2 else 0) + if true = false then 1 / 2 else 0) = _
    norm_num
  have hdiag := h (true, true)
  rw [hmarg', hzero] at hdiag
  have : (correlatedPrior.p (true, true)) = 1 / 2 := by
    show (if true = true then (1 : ℝ) / 2 else 0) = 1 / 2
    norm_num
  rw [this] at hdiag
  linarith


/-! ## Retained specifications

The regressions written before the declarations existed. They fix the
statements rather than the proofs. -/

section Specifications

variable {V : Type*} [Fintype V] [Nonempty V]
variable {X S : Type*} [Fintype X] [Fintype S]

example (μ : ProbDist V) :
    KL μ (ProbDist.uniform V) = Real.log (Fintype.card V) - shannon_entropy μ.p :=
  KL_uniform μ

example (θ : ℝ) (μ : ProbDist V) :
    memoryHeat θ μ (fun _ => ProbDist.uniform V) = 0 := memoryHeat_uniform θ μ

example (P : FiniteProtocol X S) (blank : ProbDist (X × S))
    (prep : X → S → ProbDist S)
    (h : (⟨blank, prep⟩ : FiniteFeedbackStep X S).final = P.initial) (n : ℕ) :
    (P.withPreparation blank prep).law (n + 1) = P.law n :=
  P.withPreparation_law_succ blank prep h n

example (P : FiniteProtocol X S) (blank : ProbDist (X × S)) (θ : ℝ) (ν : ProbDist S) :
    ((P.withPreparation blank fun _ _ => ν).step 0).meanHeat
        ((P.withPreparation blank fun _ _ => ν).stageHeat θ 0) =
      memoryHeat θ blank.snd (fun _ => ν) :=
  P.preparation_meanHeat blank θ ν

example (blank : ProbDist (X × S)) (prep : X → S → ProbDist S) (x : X) :
    (∑ t, (⟨blank, prep⟩ : FiniteFeedbackStep X S).final.p (x, t)) =
      ∑ s, blank.p (x, s) :=
  preparation_parameter_marginal blank prep x

example (blank : ProbDist (X × S)) (ν : ProbDist S) (z : X × S) :
    (⟨blank, fun _ _ => ν⟩ : FiniteFeedbackStep X S).final.p z =
      (∑ s, blank.p (z.1, s)) * ν.p z.2 :=
  preparation_product blank ν z

example : Examples.Sensor.prior = ProbDist.uniform _ := prior_eq_uniform

example (n : ℕ) : preparedRun.law (n + 1) = Examples.Sensor.agent.law n := prepared_law n

example (θ : ℝ) : (preparedRun.step 0).meanHeat (preparedRun.stageHeat θ 0) = 0 :=
  preparation_free θ

example : memoryHeat 1 (ProbDist.uniform Bool) (fun _ => Examples.Sensor.standard)
    = 1 / 4 * Real.log 3 := standard_prep_cost

example (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1) :
    memoryHeat 1 (ProbDist.uniform Bool) (fun _ => biased ε h0 h1)
      = (1 / 2 - ε) * Real.log ((1 - ε) / ε) := biased_prep_cost ε h0 h1

example (B : ℝ) : ∃ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1),
    B ≤ memoryHeat 1 (ProbDist.uniform Bool) (fun _ => biased ε h0 h1) :=
  sharp_prep_unbounded B

example : ¬ ∃ ν : ProbDist Bool,
    ∀ z, correlatedPrior.p z = (∑ s, correlatedPrior.p (z.1, s)) * ν.p z.2 :=
  correlated_not_preparable

-- Added on resumption; each specification failed before its theorem existed.
example : blank ≠ Examples.Sensor.prior := blank_ne_prior

example (channel : Bool → Hardware → ProbDist Hardware) :
    (⟨(ProbDist.dirac false).prod skew, channel⟩ :
      FiniteFeedbackStep Bool Hardware).final ≠ Examples.Sensor.prior :=
  known_parameter_not_preparable channel

example : ¬ ∀ s t : Bool, 0 < ((fun _ => ProbDist.dirac false) s).p t :=
  sharp_target_not_positive

end Specifications

end Examples.Prep

end PhysicsOfConsciousness
