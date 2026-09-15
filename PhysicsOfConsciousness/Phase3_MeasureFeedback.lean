import PhysicsOfConsciousness.Phase3_SupportedThermodynamics

/-!
# Feedback thermodynamics on an arbitrary measurable state space

`Phase3_AgencyThermodynamics` fixes a `Fintype` state and computes with finite
sums. `Phase3_ResourceFoundations` removed the finite-state assumption from the
*resource ledger*, but those are trajectory identities: there is no probability
law on the unbounded space, so nothing there discharges an integrability or
existence assumption. This file carries the path law itself to an arbitrary
measurable space.

The vehicle is Mathlib's `InformationTheory.klDiv`, valued in `ℝ≥0∞`. Three
things follow from that choice rather than from any work here, and all three are
the discipline the finite development had to impose by hand:

* **nonnegativity is free**, because the codomain has no negative elements;
* **absolute irreversibility is `⊤`**, by `klDiv_of_not_ac`, so no unsupported
  forward path is silently priced at a finite number;
* **integrability is a stated side condition** on the real-valued form
  (`toReal_klDiv`), not an implicit assumption of a sum that happens to be finite.

`ProbDist.extendedKL` was built to keep those properties on finite spaces. The
bridge `extendedKL_eq_klDiv` below proves the two agree wherever both are
defined, including at `⊤`, so the finite development is a special case rather
than a parallel theory.

## Scope

What is generalized: the path law, its divergence, the chain-rule split of that
divergence into a state term and a channel term, data-processing monotonicity,
the second law in divergence form, and the existence of an optimal policy over a
state space carrying no finiteness assumption at all.

What is **not** generalized: the *Shannon-entropy* form of the balance,
`entropyProduction = H(final) - H(initial) + bathEntropy`. That identity needs a
reference measure and densities against it, and differential entropy relative to
Lebesgue measure is not entropy — it is not even nonnegative. The divergence
form below is the statement that survives the generalization; the entropy form
remains finite-state, and `path_divergence_splits` is what replaces it.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace PhysicsOfConsciousness

/-- One update of a state law by a channel, on any measurable space. No
`Fintype`, no positivity, no density: the space carries only the σ-algebra it
needs to support a kernel. -/
structure MeasureFeedbackStep (Ω : Type*) [MeasurableSpace Ω] where
  initial : Measure Ω
  transition : Kernel Ω Ω
  initial_prob : IsProbabilityMeasure initial
  transition_markov : IsMarkovKernel transition

namespace MeasureFeedbackStep

variable {Ω : Type*} [MeasurableSpace Ω]

instance (M : MeasureFeedbackStep Ω) : IsProbabilityMeasure M.initial := M.initial_prob
instance (M : MeasureFeedbackStep Ω) : IsMarkovKernel M.transition := M.transition_markov

/-- The forward path law on ordered pairs (before, after). -/
noncomputable def forward (M : MeasureFeedbackStep Ω) : Measure (Ω × Ω) :=
  M.initial ⊗ₘ M.transition

instance (M : MeasureFeedbackStep Ω) : IsProbabilityMeasure M.forward := by
  unfold forward; infer_instance

/-- The law the step actually produces. -/
noncomputable def final (M : MeasureFeedbackStep Ω) : Measure Ω := M.forward.snd

instance (M : MeasureFeedbackStep Ω) : IsProbabilityMeasure M.final := by
  unfold final; infer_instance

theorem forward_fst (M : MeasureFeedbackStep Ω) : M.forward.fst = M.initial := by
  unfold forward
  exact Measure.fst_compProd _ _

/-- The reverse process's own path law, in its own time order: it starts at the
law the forward step ended on and runs the declared reverse channel `η`. -/
noncomputable def reversePath (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω)
    [IsMarkovKernel η] : Measure (Ω × Ω) :=
  M.final ⊗ₘ η

/-- The same law read in forward time order, which is what the forward path law
must be compared against. The swap is the whole content of "time reversal" here;
without it the two measures live on differently ordered pairs. -/
noncomputable def reverse (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω)
    [IsMarkovKernel η] : Measure (Ω × Ω) :=
  (M.reversePath η).map Prod.swap

instance (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω) [IsMarkovKernel η] :
    IsProbabilityMeasure (M.reversePath η) := by
  unfold reversePath; infer_instance

instance (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω) [IsMarkovKernel η] :
    IsProbabilityMeasure (M.reverse η) := by
  unfold reverse
  exact (Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).mpr inferInstance

/-- Dimensionless entropy production against a declared reverse channel. Valued
in `ℝ≥0∞`, so it is nonnegative by construction and `⊤` exactly when the forward
law is not absolutely continuous with respect to the reversed one. -/
noncomputable def entropyProduction (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω)
    [IsMarkovKernel η] : ℝ≥0∞ :=
  klDiv M.forward (M.reverse η)

/-- The second law, with nothing to prove: on an arbitrary measurable space the
production is nonnegative because it is an extended nonnegative real. The finite
development had to derive this from Gibbs' inequality because its `KL` was
real-valued. -/
theorem entropyProduction_nonneg (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω)
    [IsMarkovKernel η] : 0 ≤ M.entropyProduction η := zero_le

/-- **Absolute irreversibility is retained, not priced.** A forward path law
with no reverse support has infinite production on any measurable space, with no
finiteness or positivity hypothesis anywhere. -/
theorem entropyProduction_eq_top (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω)
    [IsMarkovKernel η] (h : ¬ M.forward ≪ M.reverse η) :
    M.entropyProduction η = ⊤ := klDiv_of_not_ac h

/-- Zero production is exactly path reversibility. `IsFiniteMeasure` on both
sides is supplied by the Markov hypotheses. -/
theorem entropyProduction_eq_zero_iff (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω)
    [IsMarkovKernel η] :
    M.entropyProduction η = 0 ↔ M.forward = M.reverse η := klDiv_eq_zero_iff

/-- **The general balance: the path divergence splits into a state term and a
channel term.** Comparing the forward path law with any reference process
`(ν, η)`, the chain rule gives

  `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`

— the first summand depending only on the two initial laws and the second only
on the channels, compared on the forward law's own initial distribution.

This is what replaces `entropy_balance` off finite spaces. It is *not* that
identity in disguise: the finite one splits against a same-channel reversed law
into `H(final) - H(initial) + bathEntropy`, and that split needs densities. This
one needs nothing, holds in `ℝ≥0∞`, and stays true when either term is `⊤`. -/
theorem path_divergence_splits (M : MeasureFeedbackStep Ω) (ν : Measure Ω)
    [IsFiniteMeasure ν] (η : Kernel Ω Ω) [IsMarkovKernel η] :
    klDiv M.forward (ν ⊗ₘ η) =
      klDiv M.initial ν + klDiv M.forward (M.initial ⊗ₘ η) := by
  unfold forward
  exact klDiv_compProd_eq_add _ _ _ _

/-- **Coarse-graining cannot increase entropy production**, on an arbitrary
measurable space and for an arbitrary measurable observable. The finite
development has no statement of this shape; it follows here from Mathlib's data
processing inequality applied to the path laws. -/
theorem entropyProduction_map_le {Ω' : Type*} [MeasurableSpace Ω']
    (M : MeasureFeedbackStep Ω) (η : Kernel Ω Ω) [IsMarkovKernel η]
    (g : Ω × Ω → Ω') (hg : Measurable g) :
    klDiv (M.forward.map g) ((M.reverse η).map g) ≤ M.entropyProduction η :=
  klDiv_map_le _ _ hg

/-- **The second law in divergence form.** The divergence between where the step
actually started and where the reverse process ends is bounded by the entropy
production. This is the general-space replacement for
`entropy_reduction_le_bathEntropy`: it compares laws rather than entropies, so
it needs no reference measure. -/
theorem initial_divergence_le_entropyProduction (M : MeasureFeedbackStep Ω)
    (η : Kernel Ω Ω) [IsMarkovKernel η] :
    klDiv M.initial ((M.reversePath η).snd) ≤ M.entropyProduction η := by
  have h := M.entropyProduction_map_le η Prod.fst measurable_fst
  have hf : M.forward.map Prod.fst = M.initial := M.forward_fst
  have hr : (M.reverse η).map Prod.fst = (M.reversePath η).snd := by
    unfold reverse
    exact Measure.fst_map_swap
  rwa [hf, hr] at h

/-- A stationary step compared against its own channel produces nothing. This is
the sanity check that `entropyProduction` is not measuring the arrow of time by
accident: reversibility is exactly the zero of the scale. -/
theorem entropyProduction_self (M : MeasureFeedbackStep Ω)
    (h : M.reverse M.transition = M.forward) :
    M.entropyProduction M.transition = 0 := by
  unfold entropyProduction
  rw [h]
  exact klDiv_self _

end MeasureFeedbackStep

/-! ## The finite theory is a special case

`ProbDist.extendedKL` keeps `⊤` for a missing reverse atom and applies `toReal`
only under support inclusion. `klDiv` does the same on general spaces. They
agree, so the finite development is this one restricted, and the recorded gap
"equality with Mathlib's measure divergence" is discharged for both branches of
the definition rather than only the finite one. -/

namespace ProbDist

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Support inclusion is absolute continuity of the induced measures. -/
theorem toMeasure_ac_of_support (P Q : ProbDist V) (h : P.SupportIncluded Q) :
    P.toMeasure ≪ Q.toMeasure := by
  intro s hs
  rw [toMeasure_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases hv : v ∈ s
  · have hqz : Q.p v = 0 := by
      by_contra hne
      have hqpos : 0 < Q.p v := lt_of_le_of_ne (Q.nonneg v) (Ne.symm hne)
      have hle : Q.toMeasure {v} ≤ Q.toMeasure s :=
        measure_mono (Set.singleton_subset_iff.mpr hv)
      rw [hs, le_zero_iff, toMeasure_singleton, ENNReal.ofReal_eq_zero] at hle
      linarith
    have hpz : P.p v = 0 := by
      by_contra hne
      have hpos := h v (lt_of_le_of_ne (P.nonneg v) (Ne.symm hne))
      rw [hqz] at hpos
      exact lt_irrefl 0 hpos
    simp [hv, hpz]
  · simp [hv]

/-- **The bridge, including the infinite branch.** Where support is included the
extended divergence is Mathlib's, and where it is not both are `⊤`. -/
theorem extendedKL_eq_klDiv (P Q : ProbDist V) (hQ : ∀ v, 0 < Q.p v) :
    P.extendedKL Q = klDiv P.toMeasure Q.toMeasure := by
  have hsupp : P.SupportIncluded Q := fun v _ => hQ v
  have hint : Integrable (llr P.toMeasure Q.toMeasure) P.toMeasure := Integrable.of_finite
  have hac : P.toMeasure ≪ Q.toMeasure := P.toMeasure_ac Q hQ
  have hfin : klDiv P.toMeasure Q.toMeasure ≠ ⊤ := klDiv_ne_top hac hint
  simp only [extendedKL, ite_eq_left hsupp]
  rw [P.KL_eq_klDiv Q hQ, ENNReal.ofReal_toReal hfin]

/-- A missing reverse atom is `⊤` on both sides. -/
theorem extendedKL_eq_klDiv_of_missing (P Q : ProbDist V) (v : V)
    (hp : 0 < P.p v) (hq : Q.p v = 0) :
    P.extendedKL Q = klDiv P.toMeasure Q.toMeasure := by
  rw [P.extendedKL_top_of_missing Q v hp hq]
  refine (klDiv_of_not_ac ?_).symm
  intro hac
  have hz : Q.toMeasure {v} = 0 := by rw [toMeasure_singleton, hq]; simp
  have hpz := hac hz
  rw [toMeasure_singleton, ENNReal.ofReal_eq_zero] at hpz
  exact absurd hpz (not_le.mpr hp)

end ProbDist

/-! ## Control without a finite state space

`FiniteControlProblem.exists_optimal` selects a maximizing policy from a
`Finset` of policies. Its `Fintype` assumptions on the state are not what makes
that argument work — they are there because `ProbDist` needs them. Stated on a
measure-theoretic problem, the same selection goes through with **no finiteness
assumption on the state space at all**, which is the sense in which the control
result was previously finite-state.

Two existence results are given, because the two hypotheses are different
physics: a finite permitted policy set, and a compact one with continuous
performance. The second is the one that discharges an existence assumption
rather than assuming its way past it. -/

/-- A control problem whose state space carries only a σ-algebra. -/
structure MeasureControlProblem (Ω A : Type*) [MeasurableSpace Ω] where
  initial : Measure Ω
  world : A → Kernel Ω Ω
  reward : Ω → ℝ
  cost : A → ℝ
  initial_prob : IsProbabilityMeasure initial
  world_markov : ∀ a, IsMarkovKernel (world a)

namespace MeasureControlProblem

variable {Ω A : Type*} [MeasurableSpace Ω]

instance (P : MeasureControlProblem Ω A) : IsProbabilityMeasure P.initial := P.initial_prob
instance (P : MeasureControlProblem Ω A) (a : A) : IsMarkovKernel (P.world a) :=
  P.world_markov a

/-- The law the chosen action actually produces. -/
noncomputable def final (P : MeasureControlProblem Ω A) (a : A) : Measure Ω :=
  (P.initial ⊗ₘ P.world a).snd

/-- Expected terminal reward on that actual law. The integral may fail to
converge; where it does, `integral` is zero, and the maximizer below is then a
maximizer of the convention rather than of the physics. That is a real
limitation of stating performance as a Bochner integral and it is not hidden by
a finiteness assumption elsewhere. -/
noncomputable def performance (P : MeasureControlProblem Ω A) (a : A) : ℝ :=
  ∫ x, P.reward x ∂(P.final a)

/-- **A maximizer over a finite permitted set, on an unrestricted state space.**
The proof is the finite-state one; what has gone is every `Fintype` on `Ω`. -/
theorem exists_optimal (P : MeasureControlProblem Ω A) (B : ℝ)
    (allowed : Finset A) (a₀ : A) (hmem : a₀ ∈ allowed) (hbudget : P.cost a₀ ≤ B) :
    ∃ a ∈ allowed, P.cost a ≤ B ∧
      ∀ b ∈ allowed, P.cost b ≤ B → P.performance b ≤ P.performance a := by
  classical
  obtain ⟨a, ha, hmax⟩ :=
    (allowed.filter (fun a => P.cost a ≤ B)).exists_max_image P.performance
      ⟨a₀, Finset.mem_filter.mpr ⟨hmem, hbudget⟩⟩
  exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2,
    fun b hb hB => hmax b (Finset.mem_filter.mpr ⟨hb, hB⟩)⟩

/-- **A maximizer over a compact permitted set.** Continuity of performance and
of cost are the existence assumptions, stated rather than assumed away, and the
feasible set is closed because the budget constraint is. This is the result the
finite version cannot state: `Finset` is not a topological hypothesis. -/
theorem exists_optimal_compact [TopologicalSpace A] (P : MeasureControlProblem Ω A)
    (B : ℝ) (allowed : Set A) (hcompact : IsCompact allowed)
    (hcost : Continuous P.cost) (hperf : Continuous P.performance)
    (a₀ : A) (hmem : a₀ ∈ allowed) (hbudget : P.cost a₀ ≤ B) :
    ∃ a ∈ allowed, P.cost a ≤ B ∧
      ∀ b ∈ allowed, P.cost b ≤ B → P.performance b ≤ P.performance a := by
  have hfeas : IsCompact (allowed ∩ {a | P.cost a ≤ B}) :=
    hcompact.inter_right (isClosed_le hcost continuous_const)
  have hne : (allowed ∩ {a | P.cost a ≤ B}).Nonempty := ⟨a₀, hmem, hbudget⟩
  obtain ⟨a, ha, hmax⟩ := hfeas.exists_isMaxOn hne hperf.continuousOn
  exact ⟨a, ha.1, ha.2, fun b hb hB => hmax ⟨hb, hB⟩⟩

end MeasureControlProblem

#print axioms MeasureFeedbackStep.path_divergence_splits
#print axioms MeasureFeedbackStep.initial_divergence_le_entropyProduction
#print axioms MeasureFeedbackStep.entropyProduction_map_le
#print axioms ProbDist.extendedKL_eq_klDiv
#print axioms MeasureControlProblem.exists_optimal_compact

end PhysicsOfConsciousness
