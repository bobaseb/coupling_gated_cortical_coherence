import PhysicsOfConsciousness.Phase3_Agency
import PhysicsOfConsciousness.Phase3_FiniteInformation

/-!
# Finite feedback thermodynamics

An elementary bipartite update fixes the controller `X` and updates `S` by a
channel depending on both states. Forward and reverse laws are normalized from
the same transition matrix, with the reverse started at the forward final law.
Their finite KL divergence is nonnegative. Expanding its logarithm proves the
joint entropy balance, without assuming a dissipation inequality.

Strictly positive initial masses and transition probabilities are the stated
scope: unidirectional transitions and absolute irreversibility need a different
support treatment. The identification of transition log-ratios with reservoir
heat is a local-detailed-balance hypothesis. Energies and work additionally obey
a separately stated first law. No goal or cortical dynamics is inferred.

`FiniteFeedbackCycle` composes actuation with a memory update from the swapped
post-action law. Its final distribution is proved equal to `Agency.cycle`'s
output. The substep entropy and mean-energy balances telescope at a common
thermal scale and energy observable; no stationarity is required. The budget
consequence covers these two substeps with action/observation aliases. Extra
physical registers and time-dependent control require further accounting.

`FiniteControlProblem` compares deterministic policies through these actual
cycles, with a supplied terminal reward and local-detailed-balance reservoir
model. A finite nonempty feasible set has a reward maximizer. This chooses no
biological objective and supplies neither learning nor policy-switching costs.

`FiniteFeedbackStep.iterate` evolves an autonomous channel from each preceding
final law. Finite sums of its entropy and first-law balances telescope. The
policy-register witness uses these results for objective-biased relaxation;
task execution and physical installation of the readout remain separate.

References, verified 2026-09-13: J. M. Horowitz and M. Esposito,
"Thermodynamics with Continuous Information Flow", Physical Review X 4,
031015 (2014), doi:10.1103/PhysRevX.4.031015; S. Ito and T. Sagawa,
"Information Thermodynamics on Causal Networks", Physical Review Letters 111,
180603 (2013), doi:10.1103/PhysRevLett.111.180603.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PhysicsOfConsciousness

/-- Normalized data for one environment update with the controller held fixed.
Positivity and physical reservoir properties are separate predicates. -/
structure FiniteFeedbackStep (X S : Type*) [Fintype X] [Fintype S] where
  initial : ProbDist (X × S)
  transition : X → S → ProbDist S

namespace FiniteFeedbackStep

variable {X S : Type*} [Fintype X] [Fintype S]

/-- The regime in which every forward and reverse elementary path has finite
log-likelihood ratio. This is a support restriction, not a second-law postulate. -/
def Positive (M : FiniteFeedbackStep X S) : Prop :=
  (∀ z, 0 < M.initial.p z) ∧ (∀ x s t, 0 < (M.transition x s).p t)

/-- Forward path probability on `(X, (S, S'))`. -/
noncomputable def forward (M : FiniteFeedbackStep X S) : ProbDist (X × (S × S)) where
  p z := M.initial.p (z.1, z.2.1) * (M.transition z.1 z.2.1).p z.2.2
  nonneg z := mul_nonneg (M.initial.nonneg _) ((M.transition _ _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ProbDist.sum_one, mul_one]
    simpa only [Fintype.sum_prod_type] using M.initial.sum_one

/-- Final joint distribution; the controller marginal is conserved. -/
noncomputable def final (M : FiniteFeedbackStep X S) : ProbDist (X × S) where
  p z := ∑ s, M.initial.p (z.1, s) * (M.transition z.1 s).p z.2
  nonneg z := Finset.sum_nonneg fun s _ =>
    mul_nonneg (M.initial.nonneg _) ((M.transition _ _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ProbDist.sum_one, mul_one]
    simpa only [Fintype.sum_prod_type] using M.initial.sum_one

/-- Reversed paths use the same autonomous channel, starting at the final
distribution. A time-dependent protocol would require its reversed channel. -/
noncomputable def reverse (M : FiniteFeedbackStep X S) : ProbDist (X × (S × S)) where
  p z := M.final.p (z.1, z.2.2) * (M.transition z.1 z.2.2).p z.2.1
  nonneg z := mul_nonneg (M.final.nonneg _) ((M.transition _ _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ProbDist.sum_one, mul_one]
    simpa only [Fintype.sum_prod_type] using M.final.sum_one

theorem controller_marginal (M : FiniteFeedbackStep X S) (x : X) :
    ∑ t, M.final.p (x, t) = ∑ s, M.initial.p (x, s) := by
  simp only [final]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, ProbDist.sum_one, mul_one]

theorem final_positive [Nonempty S] (M : FiniteFeedbackStep X S) (h : M.Positive)
    (z : X × S) : 0 < M.final.p z := by
  apply Finset.sum_pos
  · intro s _
    exact mul_pos (h.1 _) (h.2 _ _ _)
  · exact Finset.univ_nonempty

/-- Dimensionless entropy production, a KL divergence of actual path laws. -/
noncomputable def entropyProduction (M : FiniteFeedbackStep X S) : ℝ :=
  KL M.forward M.reverse

/-- Expected log-ratio of forward and backward transition probabilities.
Calling this reservoir entropy requires local detailed balance. -/
noncomputable def bathEntropy (M : FiniteFeedbackStep X S) : ℝ :=
  ∑ z, M.forward.p z * Real.log
    ((M.transition z.1 z.2.1).p z.2.2 / (M.transition z.1 z.2.2).p z.2.1)

/-- Gibbs' inequality supplies the second law for the path model. The
identification with thermodynamic entropy is made separately by local balance. -/
theorem entropyProduction_nonneg [Nonempty S] (M : FiniteFeedbackStep X S)
    (h : M.Positive) : 0 ≤ M.entropyProduction :=
  KL_nonneg M.forward M.reverse fun z =>
    mul_pos (M.final_positive h (z.1, z.2.2)) (h.2 z.1 z.2.2 z.2.1)

lemma forward_expect_initial (M : FiniteFeedbackStep X S) (f : X × S → ℝ) :
    ∑ z, M.forward.p z * f (z.1, z.2.1) = ∑ z, M.initial.p z * f z := by
  simp only [forward, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext x; arg 2; ext s; arg 2; ext t; rw [mul_right_comm]
  simp only [← Finset.mul_sum, ProbDist.sum_one, mul_one]

lemma forward_expect_final (M : FiniteFeedbackStep X S) (f : X × S → ℝ) :
    ∑ z, M.forward.p z * f (z.1, z.2.2) = ∑ z, M.final.p z * f z := by
  simp only [forward, final, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

/-- Expanding the path log-ratio gives the joint entropy change plus reservoir
log-ratios. Feedback is permitted throughout; no passive memory bound is used. -/
theorem entropy_balance [Nonempty S] (M : FiniteFeedbackStep X S) (h : M.Positive) :
    M.entropyProduction =
      shannon_entropy M.final.p - shannon_entropy M.initial.p + M.bathEntropy := by
  have hlog (z : X × (S × S)) :
      Real.log (M.forward.p z / M.reverse.p z) =
        Real.log (M.initial.p (z.1, z.2.1)) - Real.log (M.final.p (z.1, z.2.2)) +
          Real.log ((M.transition z.1 z.2.1).p z.2.2 /
            (M.transition z.1 z.2.2).p z.2.1) := by
    rw [forward, reverse,
      Real.log_div (mul_pos (h.1 _) (h.2 _ _ _)).ne'
        (mul_pos (M.final_positive h _) (h.2 _ _ _)).ne',
      Real.log_mul (h.1 _).ne' (h.2 _ _ _).ne',
      Real.log_mul (M.final_positive h _).ne' (h.2 _ _ _).ne',
      Real.log_div (h.2 _ _ _).ne' (h.2 _ _ _).ne']
    ring
  unfold entropyProduction KL
  simp_rw [hlog, mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    forward_expect_initial M (fun z => Real.log (M.initial.p z)),
    forward_expect_final M (fun z => Real.log (M.final.p z))]
  unfold shannon_entropy bathEntropy
  ring

/-- Mean heat delivered to a declared reservoir, positive outward. -/
noncomputable def meanHeat (M : FiniteFeedbackStep X S) (q : X → S → S → ℝ) : ℝ :=
  ∑ z, M.forward.p z * q z.1 z.2.1 z.2.2

/-- Local detailed balance identifies dimensionless transition log-ratios with
heat divided by the thermal energy `k_B T`. It is a physical hypothesis. -/
def LocalDetailedBalance (M : FiniteFeedbackStep X S) (θ : ℝ)
    (q : X → S → S → ℝ) : Prop :=
  ∀ x s t, q x s t = θ * Real.log ((M.transition x s).p t / (M.transition x t).p s)

theorem heat_eq_thermal_bathEntropy (M : FiniteFeedbackStep X S) (θ : ℝ)
    (q : X → S → S → ℝ) (h : M.LocalDetailedBalance θ q) :
    M.meanHeat q = θ * M.bathEntropy := by
  dsimp [LocalDetailedBalance] at h
  unfold meanHeat bathEntropy
  simp_rw [h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The heat bound is derived from Gibbs plus local detailed balance. It
applies to the joint controller–environment entropy, not passive wasted memory. -/
theorem heat_bound [Nonempty S] (M : FiniteFeedbackStep X S) (h : M.Positive)
    (θ : ℝ) (hθ : 0 < θ) (q : X → S → S → ℝ)
    (hldb : M.LocalDetailedBalance θ q) :
    θ * (shannon_entropy M.initial.p - shannon_entropy M.final.p) ≤ M.meanHeat q := by
  have hs := M.entropyProduction_nonneg h
  rw [M.entropy_balance h] at hs
  rw [M.heat_eq_thermal_bathEntropy θ q hldb]
  exact mul_le_mul_of_nonneg_left (by linarith) hθ.le

/-- The first law at the level of expected energies and work. Heat has already
been defined from paths; no assumption that every action costs work is made. -/
theorem mean_first_law (M : FiniteFeedbackStep X S) (E : X × S → ℝ)
    (q w : X → S → S → ℝ)
    (h : ∀ x s t, w x s t = E (x, t) - E (x, s) + q x s t) :
    M.meanHeat w = (∑ z, M.final.p z * E z) - (∑ z, M.initial.p z * E z) +
      M.meanHeat q := by
  unfold meanHeat
  simp_rw [h, mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    forward_expect_final, forward_expect_initial]

/-! ## Repeated autonomous updates with a shared law -/

/-- Repeat the same channel, carrying the actual final law into the next step.
The index counts updates, not spatial refinement or independently reset trials. -/
noncomputable def iterate (M : FiniteFeedbackStep X S) : ℕ → FiniteFeedbackStep X S
  | 0 => M
  | n + 1 => ⟨(M.iterate n).final, M.transition⟩

@[simp] theorem iterate_zero (M : FiniteFeedbackStep X S) : M.iterate 0 = M := rfl

@[simp] theorem iterate_initial_succ (M : FiniteFeedbackStep X S) (n : ℕ) :
    (M.iterate (n + 1)).initial = (M.iterate n).final := rfl

@[simp] theorem iterate_transition (M : FiniteFeedbackStep X S) (n : ℕ) :
    (M.iterate n).transition = M.transition := by
  cases n <;> rfl

/-- Strict support survives every finite update. The initial support and
channel positivity are hypotheses; no convergence or stationarity is used. -/
theorem iterate_positive [Nonempty S] (M : FiniteFeedbackStep X S)
    (h : M.Positive) (n : ℕ) : (M.iterate n).Positive := by
  induction n with
  | zero => exact h
  | succ n ih => exact ⟨(M.iterate n).final_positive ih, h.2⟩

/-- The entropy balance telescopes along the actual successive laws. Physical
heat still requires local detailed balance; the channel is autonomous. -/
theorem sum_entropy_balance [Nonempty S] (M : FiniteFeedbackStep X S)
    (h : M.Positive) (n : ℕ) :
    (∑ k ∈ Finset.range n, (M.iterate k).entropyProduction) =
      shannon_entropy (M.iterate n).initial.p - shannon_entropy M.initial.p +
        ∑ k ∈ Finset.range n, (M.iterate k).bathEntropy := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      (M.iterate n).entropy_balance (M.iterate_positive h n), iterate_initial_succ]
    ring

/-- A common energy and pathwise first law give finite cumulative work from
the same evolving process. Preparation and time-dependent protocols are absent. -/
theorem sum_first_law (M : FiniteFeedbackStep X S) (E : X × S → ℝ)
    (q w : X → S → S → ℝ)
    (h : ∀ x s t, w x s t = E (x, t) - E (x, s) + q x s t) (n : ℕ) :
    (∑ k ∈ Finset.range n, (M.iterate k).meanHeat w) =
      (∑ z, (M.iterate n).initial.p z * E z) - (∑ z, M.initial.p z * E z) +
        ∑ k ∈ Finset.range n, (M.iterate k).meanHeat q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      (M.iterate n).mean_first_law E q w h, iterate_initial_succ]
    ring

/-- With zero path work, cumulative heat is funded by the actual initial
energy decrease. This neither supplies a continuing power source nor accounts
for preparing the initial distribution. -/
theorem sum_meanHeat_eq_energy_drop (M : FiniteFeedbackStep X S)
    (E : X × S → ℝ) (q : X → S → S → ℝ)
    (h : ∀ x s t, E (x, t) - E (x, s) + q x s t = 0) (n : ℕ) :
    (∑ k ∈ Finset.range n, (M.iterate k).meanHeat q) =
      (∑ z, M.initial.p z * E z) -
        (∑ z, (M.iterate n).initial.p z * E z) := by
  have hf := M.sum_first_law E q (fun _ _ _ => 0) (fun x s t => (h x s t).symm) n
  have hz (k : ℕ) : (M.iterate k).meanHeat (fun _ _ _ => 0) = 0 := by
    simp [meanHeat]
  simp only [hz, Finset.sum_const_zero] at hf
  linarith

section Information

variable [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSingletonClass X] [MeasurableSingletonClass S]

/-- The thermodynamic forward paths, as the very same law used for information. -/
noncomputable def history (M : FiniteFeedbackStep X S) : Measure (X × (S × S)) :=
  M.forward.toMeasure

instance (M : FiniteFeedbackStep X S) : IsProbabilityMeasure M.history := by
  unfold history
  infer_instance

@[simp] theorem present_history (M : FiniteFeedbackStep X S) :
    Feedback.presentLaw M.history = M.initial.toMeasure := by
  classical
  unfold Feedback.presentLaw history evolvedJoint
  rw [Kernel.id, Kernel.deterministic_parallelComp_deterministic,
    Measure.deterministic_comp_eq_map]
  apply Measure.ext_of_singleton
  intro ⟨x, s⟩
  rw [ProbDist.map_singleton, ProbDist.toMeasure_singleton]
  simp only [Prod.map, Fintype.sum_prod_type, Prod.mk.injEq, id_eq, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (∑ t, ENNReal.ofReal (M.initial.p (x, s) * (M.transition x s).p t)) = _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ =>
    mul_nonneg (M.initial.nonneg _) ((M.transition _ _).nonneg t))]
  rw [← Finset.mul_sum, ProbDist.sum_one, mul_one]

@[simp] theorem future_history (M : FiniteFeedbackStep X S) :
    Feedback.futureLaw M.history = M.final.toMeasure := by
  classical
  unfold Feedback.futureLaw history evolvedJoint
  rw [Kernel.id, Kernel.deterministic_parallelComp_deterministic,
    Measure.deterministic_comp_eq_map]
  apply Measure.ext_of_singleton
  intro ⟨x, t⟩
  rw [ProbDist.map_singleton, ProbDist.toMeasure_singleton]
  simp only [Prod.map, Fintype.sum_prod_type, Prod.mk.injEq, id_eq, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  change (∑ s, ENNReal.ofReal (M.initial.p (x, s) * (M.transition x s).p t)) = _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ =>
    mul_nonneg (M.initial.nonneg _) ((M.transition _ _).nonneg _))]
  rfl

/-- The feedback identity is attached to the same initial and final laws as
the entropy balance. All finiteness obligations follow from the finite spaces. -/
theorem information_balance (M : FiniteFeedbackStep X S) :
    (mutualInfo M.initial.toMeasure).toReal - (mutualInfo M.final.toMeasure).toReal =
      Feedback.retained M.history - Feedback.feedback M.history := by
  have h := Feedback.information_balance M.history
  simpa only [Feedback.signedWaste, present_history, future_history] using h

theorem conditional_information_nonneg (M : FiniteFeedbackStep X S) :
    0 ≤ Feedback.retained M.history ∧ 0 ≤ Feedback.feedback M.history :=
  ⟨Feedback.retained_nonneg M.history (mutualInfo_finite M.history),
    Feedback.feedback_nonneg M.history (mutualInfo_finite M.history)⟩

/-- This step's transition becomes an actuator with action `A = X`. The
observation is the world state; the memory update is separately supplied. -/
noncomputable def toAgency (M : FiniteFeedbackStep X S)
    (u : Kernel ((X × X) × S) X) [IsMarkovKernel u] : Agency X S X S where
  policy := Kernel.id
  world := ProbDist.kernel (fun z : S × X => M.transition z.2 z.1)
  observe := Kernel.id
  update := u
  policy_markov := inferInstance
  world_markov := inferInstance
  observe_markov := inferInstance
  update_markov := inferInstance

theorem controlled_toAgency (M : FiniteFeedbackStep X S)
    (u : Kernel ((X × X) × S) X) [IsMarkovKernel u] :
    (M.toAgency u).controlled = ProbDist.kernel (fun z : X × S => M.transition z.1 z.2) := by
  unfold Agency.controlled toAgency
  rw [Kernel.id_comap, Kernel.deterministic_prod_deterministic,
    Kernel.comp_deterministic_eq_comap]
  rfl

/-- The policy-generated history equals the thermodynamic path law. This is
the bridge between the action-channel construction and the heat calculation. -/
theorem history_toAgency (M : FiniteFeedbackStep X S)
    (u : Kernel ((X × X) × S) X) [IsMarkovKernel u] :
    (M.toAgency u).history M.initial.toMeasure = M.history := by
  classical
  unfold Agency.history
  rw [controlled_toAgency]
  apply Measure.ext_of_singleton
  intro ⟨x, s, t⟩
  rw [ProbDist.comp_measure_singleton]
  simp only [Fintype.sum_prod_type, ProbDist.prod_singleton, Kernel.deterministic_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _),
    ProbDist.kernel_singleton, ProbDist.toMeasure_singleton, Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [history, ProbDist.toMeasure_singleton]
  change ENNReal.ofReal ((M.transition x s).p t) * ENNReal.ofReal (M.initial.p (x, s)) =
    ENNReal.ofReal (M.initial.p (x, s) * (M.transition x s).p t)
  rw [ENNReal.ofReal_mul (M.initial.nonneg _), mul_comm]

end Information

end FiniteFeedbackStep

/-- An actuation step followed by a memory channel. The second initial law is
constructed from the first final law, so it cannot be independently chosen.
No energy, heat bound, stationarity or learning property is a data field. -/
structure FiniteFeedbackCycle (X S : Type*) [Fintype X] [Fintype S] where
  actuation : FiniteFeedbackStep X S
  memory : S → X → ProbDist X

namespace FiniteFeedbackCycle

variable {X S : Type*} [Fintype X] [Fintype S]

/-- Fix the post-action world and update memory, using exactly the swapped
post-action joint law. This is a coordinate exchange, not a new distribution. -/
noncomputable def sensing (C : FiniteFeedbackCycle X S) : FiniteFeedbackStep S X :=
  ⟨C.actuation.final.swap, C.memory⟩

/-- Return the post-memory law in the original internal/world coordinates. -/
noncomputable def final (C : FiniteFeedbackCycle X S) : ProbDist (X × S) :=
  C.sensing.final.swap

/-- Strict positivity of the initial law and both autonomous channels. -/
def Positive (C : FiniteFeedbackCycle X S) : Prop :=
  C.actuation.Positive ∧ ∀ s x y, 0 < (C.memory s x).p y

theorem sensing_positive [Nonempty S] (C : FiniteFeedbackCycle X S) (h : C.Positive) :
    C.sensing.Positive :=
  ⟨fun z => C.actuation.final_positive h.1 z.swap, h.2⟩

/-- Any proposed pair of substeps realized by this cycle must match their
intermediate laws with the coordinate swap. This rejects unrelated second laws. -/
theorem intermediate_required (C : FiniteFeedbackCycle X S)
    (A : FiniteFeedbackStep X S) (M : FiniteFeedbackStep S X)
    (ha : C.actuation = A) (hm : C.sensing = M) : M.initial = A.final.swap := by
  rw [← ha, ← hm]
  rfl

/-- Sum of the two normalized path-law KL divergences. -/
noncomputable def entropyProduction (C : FiniteFeedbackCycle X S) : ℝ :=
  C.actuation.entropyProduction + C.sensing.entropyProduction

/-- Sum of expected substep observables; heat is positive into the bath and
work positive into the system when the supplied observables have those meanings. -/
noncomputable def meanHeat (C : FiniteFeedbackCycle X S)
    (qa : X → S → S → ℝ) (qm : S → X → X → ℝ) : ℝ :=
  C.actuation.meanHeat qa + C.sensing.meanHeat qm

/-- Gibbs' inequality applies to both actual substeps. No local balance or
stationarity hypothesis is needed for dimensionless nonnegativity. -/
theorem entropyProduction_nonneg [Nonempty X] [Nonempty S]
    (C : FiniteFeedbackCycle X S) (h : C.Positive) : 0 ≤ C.entropyProduction :=
  add_nonneg (C.actuation.entropyProduction_nonneg h.1)
    (C.sensing.entropyProduction_nonneg (C.sensing_positive h))

/-- The same intermediate entropy cancels, including its coordinate swap.
Both channels may change the law; neither final law is assumed stationary. -/
theorem entropy_balance [Nonempty X] [Nonempty S]
    (C : FiniteFeedbackCycle X S) (h : C.Positive) :
    C.entropyProduction =
      shannon_entropy C.final.p - shannon_entropy C.actuation.initial.p +
        C.actuation.bathEntropy + C.sensing.bathEntropy := by
  rw [entropyProduction, C.actuation.entropy_balance h.1,
    C.sensing.entropy_balance (C.sensing_positive h)]
  simp only [final, sensing, ProbDist.entropy_swap]
  ring

/-- Total entropy/heat balance at one common thermal scale. Local detailed
balance is the physical identification in each substep; no passive waste term
or identification of register and actuator is inferred. -/
theorem heat_balance [Nonempty X] [Nonempty S]
    (C : FiniteFeedbackCycle X S) (h : C.Positive) (θ : ℝ)
    (qa : X → S → S → ℝ) (qm : S → X → X → ℝ)
    (ha : C.actuation.LocalDetailedBalance θ qa)
    (hm : C.sensing.LocalDetailedBalance θ qm) :
    C.meanHeat qa qm = θ * (C.entropyProduction +
      shannon_entropy C.actuation.initial.p - shannon_entropy C.final.p) := by
  rw [meanHeat, C.actuation.heat_eq_thermal_bathEntropy θ qa ha,
    C.sensing.heat_eq_thermal_bathEntropy θ qm hm, C.entropy_balance h]
  ring

/-- A budget on the complete update bounds its joint entropy decrease. The
upper heat budget is supplied; the entropy lower bound follows from the two
path laws. This supplies no allocation from another physical operation. -/
theorem entropy_budget [Nonempty X] [Nonempty S]
    (C : FiniteFeedbackCycle X S) (h : C.Positive) (θ : ℝ) (hθ : 0 < θ)
    (qa : X → S → S → ℝ) (qm : S → X → X → ℝ)
    (ha : C.actuation.LocalDetailedBalance θ qa)
    (hm : C.sensing.LocalDetailedBalance θ qm) (B : ℝ)
    (hB : C.meanHeat qa qm ≤ B) :
    shannon_entropy C.actuation.initial.p - shannon_entropy C.final.p ≤ B / θ := by
  apply (le_div_iff₀ hθ).mpr
  rw [C.heat_balance h θ qa qm ha hm] at hB
  have hn := mul_nonneg hθ.le (C.entropyProduction_nonneg h)
  nlinarith

/-- Both first laws use one energy observable in internal/world coordinates.
Relabelling its expectation cancels the same intermediate energy. Work and heat
conventions are explicit substep hypotheses, not consequences of information. -/
theorem mean_first_law (C : FiniteFeedbackCycle X S) (E : X × S → ℝ)
    (qa wa : X → S → S → ℝ) (qm wm : S → X → X → ℝ)
    (ha : ∀ x s t, wa x s t = E (x, t) - E (x, s) + qa x s t)
    (hm : ∀ s x y, wm s x y = E (y, s) - E (x, s) + qm s x y) :
    C.meanHeat wa wm = (∑ z, C.final.p z * E z) -
      (∑ z, C.actuation.initial.p z * E z) + C.meanHeat qa qm := by
  have hma := C.actuation.mean_first_law E qa wa ha
  have hmm := C.sensing.mean_first_law (fun z => E z.swap) qm wm hm
  simp only [sensing, ProbDist.expect_swap, Prod.swap_swap] at hmm
  simp only [meanHeat, final, ProbDist.expect_swap, sensing]
  linarith

section Channels

variable [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSingletonClass X] [MeasurableSingletonClass S]

/-- Memory channel with action and observation aliases, retaining the old memory
and observing the new world. There is no extra physical storage register. -/
noncomputable def memoryUpdate (C : FiniteFeedbackCycle X S) : Kernel ((X × X) × S) X :=
  ProbDist.kernel (fun z => C.memory z.2 z.1.1)

instance (C : FiniteFeedbackCycle X S) : IsMarkovKernel C.memoryUpdate := by
  unfold memoryUpdate
  infer_instance

/-- The existing policy/world/observation/update construction for these two
finite channels. The action is the old internal state, the observation the world. -/
noncomputable def toAgency (C : FiniteFeedbackCycle X S) : Agency X S X S :=
  C.actuation.toAgency C.memoryUpdate

/-- The full policy/actuation/observation/memory composition has precisely this
two-channel transition probability. The alias model samples no extra register. -/
theorem cycle_transition (C : FiniteFeedbackCycle X S) (x y : X) (s t : S) :
    C.toAgency.cycle (x, s) {(y, t)} =
      ENNReal.ofReal ((C.actuation.transition x s).p t) *
        ENNReal.ofReal ((C.memory t x).p y) := by
  classical
  simp only [Agency.cycle, Agency.sense, Agency.act, Agency.select, toAgency,
    FiniteFeedbackStep.toAgency, memoryUpdate, Kernel.id]
  simp only [Kernel.comap_apply, ProbDist.comp_singleton, Fintype.sum_prod_type,
    ProbDist.prod_singleton, Kernel.deterministic_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _), ProbDist.kernel_singleton,
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, id_eq, Prod.mk.injEq,
    ite_and, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_mul, zero_mul]
  exact mul_comm _ _

/-- The thermodynamic final law is the output of the composed perception–action
channels on the actual initial law. This identification needs no positivity,
local detailed balance, energy or equilibrium assumption. -/
theorem cycle_law (C : FiniteFeedbackCycle X S) :
    C.toAgency.cycle ∘ₘ C.actuation.initial.toMeasure = C.final.toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro ⟨y, t⟩
  rw [ProbDist.comp_measure_singleton]
  simp only [Fintype.sum_prod_type, cycle_transition, ProbDist.toMeasure_singleton]
  apply (ENNReal.toReal_eq_toReal_iff' (by
    apply ENNReal.sum_ne_top.mpr
    intro x _
    apply ENNReal.sum_ne_top.mpr
    intro s _
    finiteness) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_sum (by
    intro x _
    apply ENNReal.sum_ne_top.mpr
    intro s _
    finiteness)]
  conv_lhs =>
    arg 2; ext x
    rw [ENNReal.toReal_sum (by intro s _; finiteness)]
  simp only [ENNReal.toReal_mul]
  simp only [ENNReal.toReal_ofReal (C.final.nonneg _),
    ENNReal.toReal_ofReal (C.actuation.initial.nonneg _),
    ENNReal.toReal_ofReal ((C.actuation.transition _ _).nonneg _),
    ENNReal.toReal_ofReal ((C.memory _ _).nonneg _)]
  simp only [final, sensing, ProbDist.swap, FiniteFeedbackStep.final,
    Finset.sum_mul, Prod.swap_prod_mk]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  ring

end Channels

end FiniteFeedbackCycle

/-! ## Finite deterministic control under an actual-cycle heat budget -/

/-- Shared task data for comparing fixed deterministic policies `X → A`.
The reward is a modelling input. No success, feasibility or optimality property
is a field. Actions are functions of existing memory, not extra physical
registers; policy installation, switching and learning are outside this model. -/
structure FiniteControlProblem (X S A : Type*) [Fintype X] [Fintype S] [Fintype A] where
  initial : ProbDist (X × S)
  world : A → S → ProbDist S
  memory : S → X → ProbDist X
  reward : X × S → ℝ

namespace FiniteControlProblem

variable {X S A : Type*} [Fintype X] [Fintype S] [Fintype A]

/-- The policy changes only the action supplied to the common world channel.
The L1 construction fixes the sensing input to the swapped post-action law. -/
noncomputable def cycle (P : FiniteControlProblem X S A) (π : X → A) :
    FiniteFeedbackCycle X S := ⟨⟨P.initial, fun x => P.world (π x)⟩, P.memory⟩

/-- Expected terminal reward, evaluated on the complete update's actual law. -/
noncomputable def performance (P : FiniteControlProblem X S A) (π : X → A) : ℝ :=
  ∑ z, (P.cycle π).final.p z * P.reward z

/-- Strict support of the common initial law and both channels. -/
def Positive (P : FiniteControlProblem X S A) : Prop :=
  (∀ z, 0 < P.initial.p z) ∧ (∀ a s t, 0 < (P.world a s).p t) ∧
    ∀ s x y, 0 < (P.memory s x).p y

theorem cycle_positive (P : FiniteControlProblem X S A) (h : P.Positive) (π : X → A) :
    (P.cycle π).Positive := ⟨⟨h.1, fun x => h.2.1 (π x)⟩, h.2.2⟩

/-- Outward actuation heat in the declared local-detailed-balance model.
Its thermal interpretation is a physical choice, not inferred from optimization. -/
noncomputable def actuationHeat (P : FiniteControlProblem X S A) (θ : ℝ)
    (π : X → A) (x : X) (s t : S) : ℝ :=
  θ * Real.log ((P.world (π x) s).p t / (P.world (π x) t).p s)

/-- Memory heat uses the same reservoir scale and the actual memory channel. -/
noncomputable def memoryHeat (P : FiniteControlProblem X S A) (θ : ℝ)
    (s : S) (x y : X) : ℝ :=
  θ * Real.log ((P.memory s x).p y / (P.memory s y).p x)

/-- Total expected heat of both actual substeps, not an assigned policy cost. -/
noncomputable def heat (P : FiniteControlProblem X S A) (θ : ℝ) (π : X → A) : ℝ :=
  (P.cycle π).meanHeat (P.actuationHeat θ π) (P.memoryHeat θ)

/-- Work into the system on each actuation path, using a common energy. -/
noncomputable def actuationWork (P : FiniteControlProblem X S A) (E : X × S → ℝ)
    (θ : ℝ) (π : X → A) (x : X) (s t : S) : ℝ :=
  E (x, t) - E (x, s) + P.actuationHeat θ π x s t

/-- Work into the system on each memory path, in the same energy coordinates. -/
noncomputable def memoryWork (P : FiniteControlProblem X S A) (E : X × S → ℝ)
    (θ : ℝ) (s : S) (x y : X) : ℝ :=
  E (y, s) - E (x, s) + P.memoryHeat θ s x y

/-- Total expected work of the specified fixed-policy update. -/
noncomputable def work (P : FiniteControlProblem X S A) (E : X × S → ℝ)
    (θ : ℝ) (π : X → A) : ℝ :=
  (P.cycle π).meanHeat (P.actuationWork E θ π) (P.memoryWork E θ)

/-- The common initial/intermediate/final energies telescope for every policy.
This accounts for the declared transition work, not policy-switching costs. -/
theorem first_law (P : FiniteControlProblem X S A) (E : X × S → ℝ)
    (θ : ℝ) (π : X → A) :
    P.work E θ π = (∑ z, (P.cycle π).final.p z * E z) -
      (∑ z, P.initial.p z * E z) + P.heat θ π :=
  (P.cycle π).mean_first_law E _ _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- Feasibility supplies the upper heat allocation; the whole-update entropy
bound follows from the L1 theorem in the declared reservoir model. No task
performance or physical source of the budget follows from this inequality. -/
theorem entropy_budget [Nonempty X] [Nonempty S]
    (P : FiniteControlProblem X S A) (π : X → A) (h : P.Positive)
    (θ : ℝ) (hθ : 0 < θ) (B : ℝ) (hB : P.heat θ π ≤ B) :
    shannon_entropy P.initial.p - shannon_entropy (P.cycle π).final.p ≤ B / θ :=
  (P.cycle π).entropy_budget (P.cycle_positive h π) θ hθ _ _
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) B hB

/-- A nonempty finite feasible set has a reward maximizer. The objective and
permitted policies are supplied; strict improvement requires an actual better
feasible policy, and no learning algorithm or computation cost is inferred. -/
theorem exists_optimal (P : FiniteControlProblem X S A) (θ B : ℝ)
    (allowed : Finset (X → A)) (π₀ : X → A) (hmem : π₀ ∈ allowed)
    (hbudget : P.heat θ π₀ ≤ B) :
    ∃ π ∈ allowed, P.heat θ π ≤ B ∧
      ∀ ρ ∈ allowed, P.heat θ ρ ≤ B → P.performance ρ ≤ P.performance π := by
  classical
  obtain ⟨π, hπ, hmax⟩ :=
    (allowed.filter (fun π => P.heat θ π ≤ B)).exists_max_image P.performance
      ⟨π₀, Finset.mem_filter.mpr ⟨hmem, hbudget⟩⟩
  exact ⟨π, (Finset.mem_filter.mp hπ).1, (Finset.mem_filter.mp hπ).2,
    fun ρ hρ hB => hmax ρ (Finset.mem_filter.mpr ⟨hρ, hB⟩)⟩

section Channels

variable [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace A]
  [MeasurableSingletonClass X] [MeasurableSingletonClass S] [MeasurableSingletonClass A]

noncomputable def memoryUpdate (P : FiniteControlProblem X S A) :
    Kernel ((X × A) × S) X := ProbDist.kernel (fun z => P.memory z.2 z.1.1)

instance (P : FiniteControlProblem X S A) : IsMarkovKernel P.memoryUpdate := by
  unfold memoryUpdate
  infer_instance

/-- Explicit deterministic policy, shared world, exact observation and common
memory update. The action is an alias, so no stochastic action is marginalized
out before calculating heat. Such hidden paths would require extra accounting. -/
noncomputable def toAgency (P : FiniteControlProblem X S A) (π : X → A) : Agency X S A S where
  policy := Kernel.deterministic π (measurable_of_finite π)
  world := ProbDist.kernel (fun z => P.world z.2 z.1)
  observe := Kernel.id
  update := P.memoryUpdate
  policy_markov := inferInstance
  world_markov := inferInstance
  observe_markov := inferInstance
  update_markov := inferInstance

/-- Policy selection and the actual two thermal substeps have the same path
probabilities; varying the policy leaves world and memory channels fixed. -/
theorem cycle_transition (P : FiniteControlProblem X S A) (π : X → A)
    (x y : X) (s t : S) :
    (P.toAgency π).cycle (x, s) {(y, t)} =
      ENNReal.ofReal ((P.world (π x) s).p t) * ENNReal.ofReal ((P.memory t x).p y) := by
  classical
  simp only [Agency.cycle, Agency.sense, Agency.act, Agency.select, toAgency,
    memoryUpdate, Kernel.id]
  simp only [Kernel.comap_apply, ProbDist.comp_singleton, Fintype.sum_prod_type,
    ProbDist.prod_singleton, Kernel.deterministic_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _), ProbDist.kernel_singleton,
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, id_eq, Prod.mk.injEq,
    ite_and, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_mul, zero_mul]
  exact mul_comm _ _

/-- The explicit policy's full channel output equals the L1 law used for both
reward and cost. This is process identification, not a thermodynamic assumption. -/
theorem cycle_law (P : FiniteControlProblem X S A) (π : X → A) :
    (P.toAgency π).cycle ∘ₘ P.initial.toMeasure = (P.cycle π).final.toMeasure := by
  have heq : (P.toAgency π).cycle = (P.cycle π).toAgency.cycle := by
    ext z : 1
    apply Measure.ext_of_singleton
    intro ⟨y, t⟩
    rw [P.cycle_transition π z.1 y z.2 t, (P.cycle π).cycle_transition z.1 y z.2 t]
    rfl
  rw [heq]
  exact (P.cycle π).cycle_law

end Channels

end FiniteControlProblem
end PhysicsOfConsciousness
