import PhysicsOfConsciousness.Phase3_PredictiveThermodynamics

/-!
# Agency: a perception–action loop and its information balance

The policy, world, observation and memory update are separate stochastic
channels. Their composition allows the internal state to influence the next
environment through an action. No objective or learning rule is inferred from
these channels. Finite-state examples live in `Examples/Agency.lean`; the kernel
construction also works on measurable spaces.

For the law of `(X, (S, S'))`, conditional mutual information is defined by its
standard chain-rule expression, using the existing KL-based mutual information.
Data processing proves its nonnegativity when the joint information is finite.
The signed difference `I(X;S) - I(X;S')` is a real number, not truncated ENNReal
subtraction. Its decomposition is informational, not a heat/work inequality.
The passive constructor recovers the existing signal dynamics exactly.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PhysicsOfConsciousness

namespace Feedback

variable {X S S' : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace S']

/-- The marginal law of memory and the present environment. -/
noncomputable def presentLaw (μ : Measure (X × (S × S'))) : Measure (X × S) :=
  evolvedJoint μ (Kernel.deterministic Prod.fst measurable_fst)

/-- The marginal law of memory and the future environment. -/
noncomputable def futureLaw (μ : Measure (X × (S × S'))) : Measure (X × S') :=
  evolvedJoint μ (Kernel.deterministic Prod.snd measurable_snd)

/-- `I(X;S | S')`, by the mutual-information chain rule. The real expression
has its usual meaning when `I(X;(S,S'))` is finite. -/
noncomputable def retained (μ : Measure (X × (S × S'))) : ℝ :=
  (mutualInfo μ).toReal - (mutualInfo (futureLaw μ)).toReal

/-- `I(X;S' | S)`. Causal interpretation requires a sufficient environmental
state and a specified feedback mechanism; conditional dependence alone is not
an intervention. Finiteness has the same role as in `retained`. -/
noncomputable def feedback (μ : Measure (X × (S × S'))) : ℝ :=
  (mutualInfo μ).toReal - (mutualInfo (presentLaw μ)).toReal

/-- Signed memory minus prediction. Unlike passive `nonpredictiveInfo`, this
can be negative, and never truncates a negative difference to zero. -/
noncomputable def signedWaste (μ : Measure (X × (S × S'))) : ℝ :=
  (mutualInfo (presentLaw μ)).toReal - (mutualInfo (futureLaw μ)).toReal

theorem present_info_le (μ : Measure (X × (S × S'))) [IsProbabilityMeasure μ] :
    mutualInfo (presentLaw μ) ≤ mutualInfo μ :=
  predictiveInfo_le_mutualInfo μ _

theorem future_info_le (μ : Measure (X × (S × S'))) [IsProbabilityMeasure μ] :
    mutualInfo (futureLaw μ) ≤ mutualInfo μ :=
  predictiveInfo_le_mutualInfo μ _

/-- Conditional information is nonnegative by data processing. Finite joint
information excludes the `∞.toReal = 0` convention; no thermodynamics is used. -/
theorem retained_nonneg (μ : Measure (X × (S × S'))) [IsProbabilityMeasure μ]
    (h : mutualInfo μ ≠ ∞) : 0 ≤ retained μ :=
  sub_nonneg.mpr (ENNReal.toReal_mono h (future_info_le μ))

/-- Feedback information is nonnegative under the same finiteness condition.
Its positivity alone does not identify a causal mechanism. -/
theorem feedback_nonneg (μ : Measure (X × (S × S'))) [IsProbabilityMeasure μ]
    (h : mutualInfo μ ≠ ∞) : 0 ≤ feedback μ :=
  sub_nonneg.mpr (ENNReal.toReal_mono h (present_info_le μ))

/-- The chain-rule information balance, with signed subtraction. Its
information-theoretic reading requires finite joint information; this algebraic
equality itself does not supply a thermodynamic bound. -/
theorem information_balance (μ : Measure (X × (S × S'))) :
    signedWaste μ = retained μ - feedback μ := by
  unfold signedWaste retained feedback
  ring

/-- The amount by which prediction can exceed memory is bounded by feedback
information. No cost of creating that information follows from this theorem. -/
theorem prediction_le_memory_add_feedback (μ : Measure (X × (S × S')))
    [IsProbabilityMeasure μ] (h : mutualInfo μ ≠ ∞) :
    (mutualInfo (futureLaw μ)).toReal ≤
      (mutualInfo (presentLaw μ)).toReal + feedback μ := by
  have hn := retained_nonneg μ h
  have hb := information_balance μ
  unfold signedWaste at hb
  linarith

/-- Signal evolution with the present signal retained in the output. This is
the passive joint law of `(X, (S, S'))`, not a feedback approximation. -/
noncomputable def passiveLaw (μ : Measure (X × S)) (κ : Kernel S S') :
    Measure (X × (S × S')) := evolvedJoint μ (Kernel.id ×ₖ κ)

lemma evolvedJoint_comp {T : Type*} [MeasurableSpace T]
    (μ : Measure (X × S)) (κ : Kernel S S') [IsSFiniteKernel κ]
    (η : Kernel S' T) [IsSFiniteKernel η] :
    evolvedJoint (evolvedJoint μ κ) η = evolvedJoint μ (η ∘ₖ κ) := by
  unfold evolvedJoint
  rw [Measure.comp_assoc, Kernel.parallelComp_comp_parallelComp, Kernel.id_comp]

@[simp] theorem present_passiveLaw (μ : Measure (X × S)) (κ : Kernel S S')
    [IsMarkovKernel κ] : presentLaw (passiveLaw μ κ) = μ := by
  unfold presentLaw passiveLaw
  rw [evolvedJoint_comp, Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq,
    Kernel.fst_prod]
  simp [evolvedJoint, Kernel.id_parallelComp_id]

@[simp] theorem future_passiveLaw (μ : Measure (X × S)) (κ : Kernel S S')
    [IsMarkovKernel κ] : futureLaw (passiveLaw μ κ) = evolvedJoint μ κ := by
  unfold futureLaw passiveLaw
  rw [evolvedJoint_comp, Kernel.deterministic_comp_eq_map, ← Kernel.snd_eq,
    Kernel.snd_prod]

/-- Retaining a passively evolved signal adds no information about memory
beyond its present signal. This follows from data processing in both directions. -/
theorem passive_info_eq (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (κ : Kernel S S') [IsMarkovKernel κ] :
    mutualInfo (passiveLaw μ κ) = mutualInfo μ := by
  apply le_antisymm (predictiveInfo_le_mutualInfo μ (Kernel.id ×ₖ κ))
  have : IsProbabilityMeasure (passiveLaw μ κ) := by
    unfold passiveLaw evolvedJoint
    infer_instance
  change mutualInfo μ ≤ mutualInfo (passiveLaw μ κ)
  simpa using present_info_le (passiveLaw μ κ)

/-- No-feedback recovery is proved for the actual passive constructor, not
assumed as an extra conditional-information hypothesis. -/
theorem passive_feedback_zero (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (κ : Kernel S S') [IsMarkovKernel κ] :
    feedback (passiveLaw μ κ) = 0 := by
  simp [feedback, passive_info_eq]

/-- The passive signed difference is the existing nonpredictive information.
The finite-memory condition is essential to converting ENNReal subtraction. -/
theorem passive_signedWaste (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (κ : Kernel S S') [IsMarkovKernel κ] (h : mutualInfo μ ≠ ∞) :
    signedWaste (passiveLaw μ κ) = (nonpredictiveInfo μ κ).toReal := by
  simp only [signedWaste, present_passiveLaw, future_passiveLaw]
  exact (ENNReal.toReal_sub_of_le (predictiveInfo_le_mutualInfo μ κ) h).symm

end Feedback

/-- Data of a perception–action loop. Channel normalization is structural;
there is no optimality, thermodynamic inequality, or cortical identification
among its fields. Those require separately stated physical hypotheses. -/
structure Agency (X S A O : Type*) [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace O] where
  policy : Kernel X A
  world : Kernel (S × A) S
  observe : Kernel S O
  update : Kernel ((X × A) × O) X
  policy_markov : IsMarkovKernel policy
  world_markov : IsMarkovKernel world
  observe_markov : IsMarkovKernel observe
  update_markov : IsMarkovKernel update

attribute [instance] Agency.policy_markov Agency.world_markov
  Agency.observe_markov Agency.update_markov

namespace Agency

variable {X S A O : Type*} [MeasurableSpace X] [MeasurableSpace S]
  [MeasurableSpace A] [MeasurableSpace O]

/-- World evolution after sampling the action from the internal state. -/
noncomputable def controlled (M : Agency X S A O) : Kernel (X × S) S :=
  M.world ∘ₖ (Kernel.deterministic Prod.snd measurable_snd ×ₖ
    M.policy.comap Prod.fst measurable_fst)

instance (M : Agency X S A O) : IsMarkovKernel M.controlled := by
  unfold controlled
  infer_instance

/-- The law used for the feedback identity holds `X_t` fixed while recording
both environmental states. The later memory update has its own place in `cycle`. -/
noncomputable def history (M : Agency X S A O) (μ : Measure (X × S)) :
    Measure (X × (S × S)) :=
  (Kernel.deterministic Prod.fst measurable_fst ×ₖ
    (Kernel.deterministic Prod.snd measurable_snd ×ₖ M.controlled)) ∘ₘ μ

instance (M : Agency X S A O) (μ : Measure (X × S)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (M.history μ) := by
  unfold history
  infer_instance

/-- The recorded present is exactly the input law, so the information balance
compares prediction with the actual pre-action memory. -/
@[simp] theorem present_history (M : Agency X S A O) (μ : Measure (X × S)) :
    Feedback.presentLaw (M.history μ) = μ := by
  unfold Feedback.presentLaw evolvedJoint history
  rw [Measure.comp_assoc, Kernel.parallelComp_comp_prod, Kernel.id_comp,
    Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq, Kernel.fst_prod,
    Kernel.deterministic_prod_deterministic]
  change Kernel.id ∘ₘ μ = μ
  exact Measure.id_comp

/-- The recorded future is the post-action world paired with the old memory.
The subsequent memory update is deliberately excluded from predictive information. -/
@[simp] theorem future_history (M : Agency X S A O) (μ : Measure (X × S)) :
    Feedback.futureLaw (M.history μ) =
      (Kernel.deterministic Prod.fst measurable_fst ×ₖ M.controlled) ∘ₘ μ := by
  unfold Feedback.futureLaw evolvedJoint history
  rw [Measure.comp_assoc, Kernel.parallelComp_comp_prod, Kernel.id_comp,
    Kernel.deterministic_comp_eq_map, ← Kernel.snd_eq, Kernel.snd_prod]

/-- Select an action while retaining the current state. -/
noncomputable def select (M : Agency X S A O) : Kernel (X × S) ((X × S) × A) :=
  Kernel.id ×ₖ M.policy.comap Prod.fst measurable_fst

/-- Execute the selected action, keeping it available to the memory update. -/
noncomputable def act (M : Agency X S A O) : Kernel ((X × S) × A) ((X × A) × S) :=
  Kernel.deterministic (fun z => (z.1.1, z.2)) (by fun_prop) ×ₖ
    M.world.comap (fun z => (z.1.2, z.2)) (by fun_prop)

/-- Sense the new environment and update memory; the world is fixed during
this substep. Sensor noise is sampled once and supplied to `update`. -/
noncomputable def sense (M : Agency X S A O) : Kernel ((X × A) × S) (X × S) :=
  (M.update.comap (fun z => (z.1.1, z.2)) (by fun_prop) ×ₖ
    Kernel.deterministic (fun z => z.1.2) (by fun_prop)) ∘ₖ
      (Kernel.id ×ₖ M.observe.comap Prod.snd measurable_snd)

/-- One complete perception–action cycle, preserving the sampled action
through actuation and memory update. This specifies behaviour, not learning. -/
noncomputable def cycle (M : Agency X S A O) : Kernel (X × S) (X × S) :=
  M.sense ∘ₖ M.act ∘ₖ M.select

instance (M : Agency X S A O) : IsMarkovKernel M.cycle := by
  unfold cycle sense act select
  infer_instance

end Agency
end PhysicsOfConsciousness
