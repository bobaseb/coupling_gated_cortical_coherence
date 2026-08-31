import Mathlib
import PhysicsOfConsciousness.Phase3_KLBound

/-!
# Phase 3 — The thermodynamics of prediction

This module replaces Derivation 3's inference, which was invalid.

## What was wrong

Derivation 3 read: entropy production obeys `σ ≥ D_KL(P_ext ‖ Q_int)/Δt`
(`Phase3_KLBound.structural_resonance_bound`), therefore a system descending on
`σ` drives `D_KL → 0`, therefore the internal model comes to match the
environment. The rearranged bound `D_KL ≤ Δt · σ` is true, and descending on `σ`
does lower the *bound*; what does not follow is the limit. A driven system
relaxes to a non-equilibrium steady state at strictly positive `σ`, so the bound
delivers `D_KL ≤ Δt · σ_NESS`, a positive number, and never zero. The conclusion
that buys the framework predictive processing was read off an inequality that
does not support it.

## What replaces it

Still, Sivak, Bell and Crooks, *Thermodynamics of Prediction*, Phys. Rev. Lett.
**109** (2012) 120604. For a system `X` driven by an environmental signal `S`,

```
  W_diss  ≥  k_B T · [ I(X_t ; S_t) − I(X_t ; S_{t+1}) ]
                       \___ memory ___/   \_ prediction _/
```

The bracket is the *nonpredictive* information: what the system remembers about
the signal's present that says nothing about the signal's future. Dissipation is
bounded below by it. Memory that does not predict is thermodynamic waste.

Two things make this a replacement rather than a restatement.

1. **The bracket is provably non-negative**, and that is a theorem of this file,
   not a postulate: `predictiveInfo_le_mutualInfo`. If the system does not drive
   the signal — if `X_t → S_t → S_{t+1}` is a Markov chain — then the data
   processing inequality says the system cannot know more about `S_{t+1}` than
   it knows about `S_t`. So the lower bound on dissipation is a bound by a
   quantity that is always ≥ 0, and the second law follows
   (`PredictiveDissipation.dissipatedWork_nonneg`) instead of being assumed.
2. **The inference now runs the right way.** `nonpredictiveInfo` sits on the
   *small* side of the inequality, so a bound on dissipation *is* a bound on it
   (`PredictiveDissipation.nonpredictive_le_dissipation`), and zero dissipation forces
   every retained bit to be predictive
   (`PredictiveDissipation.predictive_eq_of_no_dissipation`). No limit is claimed and none
   is needed.

## What this does *not* establish

* It is **not** the Free Energy Principle. Still's bound says prediction is
  thermodynamically favoured. It says nothing about hierarchical generative
  models, variational free energy, or Bayesian inference, and this file claims
  none of them.
* Still's bound itself is **a postulate here**, carried as a class field
  (`PredictiveDissipation.still_bound`) exactly as `StructuralResonance.kl_bound`
  was. Deriving it needs a stochastic thermodynamics — a path measure, a
  time-reversal involution, and Crooks' fluctuation theorem — none of which is in
  Mathlib. What is *derived* here is everything downstream of it.
* Mutual information is defined here, not imported: Mathlib has `klDiv` but no
  `mutualInfo`. The definition used, `I(X;S) = D_KL(joint ‖ product of
  marginals)`, is the standard one and is what makes Mathlib's data processing
  and chain-rule lemmas apply directly.
* Nothing here connects to the Kuramoto dynamics of Phase 4 or to the continuous
  field of Phase 8. The signal `S` is abstract.

Witness: `Examples.lean` §18.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace PhysicsOfConsciousness

variable {X S S' : Type*} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace S']

/-! ## 1. Mutual information

Mathlib carries `klDiv` but no mutual information, no conditional entropy and no
measure entropy (checked by `grep` against the pinned revision). The definition
below is the standard one — the divergence of the joint law from the product of
its marginals — chosen because every lemma in
`Mathlib/InformationTheory/KullbackLeibler/` then applies to it unchanged. -/

/-- **Mutual information** of a joint law on `X × S`, as the Kullback–Leibler
divergence of the joint from the product of its marginals.

Valued in `ℝ≥0∞`, so non-negativity is definitional rather than a theorem; the
content of Gibbs' inequality is discharged by Mathlib's construction of `klDiv`.
It is `⊤` exactly when the joint is not absolutely continuous with respect to the
product, or the log-likelihood ratio fails to be integrable. -/
noncomputable def mutualInfo (μ : Measure (X × S)) : ℝ≥0∞ :=
  klDiv μ (μ.fst.prod μ.snd)

/-- Mutual information is non-negative. Definitional in `ℝ≥0∞`; stated so that
the appeal to Gibbs' inequality is visible at the point of use. -/
lemma mutualInfo_nonneg (μ : Measure (X × S)) : 0 ≤ mutualInfo μ := zero_le

/-- **Converse Gibbs, specialised:** mutual information vanishes exactly on
independent pairs. This is what makes `mutualInfo` a measure of dependence
rather than an arbitrary non-negative functional, and it is what a witness must
fire to show its memory is not vacuous. -/
lemma mutualInfo_eq_zero_iff (μ : Measure (X × S)) [IsFiniteMeasure μ]
    [IsFiniteMeasure (μ.fst.prod μ.snd)] :
    mutualInfo μ = 0 ↔ μ = μ.fst.prod μ.snd :=
  klDiv_eq_zero_iff

/-- An independent pair carries no mutual information. -/
@[simp] lemma mutualInfo_prod (μ : Measure X) (ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    mutualInfo (μ.prod ν) = 0 := by
  rw [mutualInfo, Measure.fst_prod, Measure.snd_prod, klDiv_self]

/-! ## 2. One step of the signal, and the two informations

The physical setting is a system state `X_t` and a signal `S_t` with a joint law,
and a signal dynamics `κ : Kernel S S'` carrying `S_t` to `S_{t+1}`. The crucial
modelling assumption — that the *system does not drive the signal* — is built
into the shape of the evolution rather than assumed as a hypothesis: the kernel
applied to the pair is `Kernel.id ∥ₖ κ`, which acts as the identity on `X` and as
`κ` on `S`, and therefore cannot let `X_t` influence `S_{t+1}`. That is exactly
the Markov chain `X_t → S_t → S_{t+1}` of Still et al. -/

/-- The joint law of `(X_t, S_{t+1})`, obtained from the joint law of
`(X_t, S_t)` by running the signal dynamics `κ` and leaving the system state
untouched.

`Kernel.id ∥ₖ κ` is a Markov kernel `X × S → X × S'` whose first component is a
Dirac mass and whose second is `κ` applied to the *signal* coordinate only. The
system therefore has no channel through which to influence the signal's next
value: this is where the Markov-chain hypothesis `X_t → S_t → S_{t+1}` lives. -/
noncomputable def evolvedJoint (μ : Measure (X × S)) (κ : Kernel S S') :
    Measure (X × S') :=
  ((Kernel.id : Kernel X X) ∥ₖ κ) ∘ₘ μ

/-- The system's marginal is untouched by the signal's evolution. -/
lemma evolvedJoint_fst (μ : Measure (X × S)) [SFinite μ]
    (κ : Kernel S S') [IsMarkovKernel κ] :
    (evolvedJoint μ κ).fst = μ.fst := by
  have hfst : Kernel.fst ((Kernel.id : Kernel X X) ∥ₖ κ)
      = Kernel.deterministic Prod.fst measurable_fst := by
    ext x s hs
    have h : ((Kernel.id : Kernel X X) ∥ₖ κ) x = (Measure.dirac x.1).prod (κ x.2) := by
      rw [Kernel.parallelComp_apply, Kernel.id_apply]
    rw [Kernel.fst_apply, h, ← Measure.fst, Measure.fst_prod, Kernel.deterministic_apply]
  rw [evolvedJoint, Measure.fst, Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq, hfst,
    Measure.deterministic_comp_eq_map]
  rfl

/-- The signal's marginal is pushed forward by the signal's own dynamics, with
no reference to the system. -/
lemma evolvedJoint_snd (μ : Measure (X × S)) [SFinite μ]
    (κ : Kernel S S') [IsMarkovKernel κ] :
    (evolvedJoint μ κ).snd = κ ∘ₘ μ.snd := by
  have hsnd : Kernel.snd ((Kernel.id : Kernel X X) ∥ₖ κ)
      = Kernel.comap κ Prod.snd measurable_snd := by
    ext x s hs
    have h : ((Kernel.id : Kernel X X) ∥ₖ κ) x = (Measure.dirac x.1).prod (κ x.2) := by
      rw [Kernel.parallelComp_apply, Kernel.id_apply]
    rw [Kernel.snd_apply, h, ← Measure.snd, Measure.snd_prod, Kernel.comap_apply]
  rw [evolvedJoint, Measure.snd, Measure.map_comp _ _ measurable_snd, ← Kernel.snd_eq, hsnd,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  rfl

/-- **Instantaneous memory**, `I(X_t ; S_t)`: what the system's present state
says about the signal's present value. -/
noncomputable abbrev memoryInfo (μ : Measure (X × S)) : ℝ≥0∞ := mutualInfo μ

/-- **Predictive information**, `I(X_t ; S_{t+1})`: what the system's present
state says about the signal's *next* value. -/
noncomputable def predictiveInfo (μ : Measure (X × S)) (κ : Kernel S S') : ℝ≥0∞ :=
  mutualInfo (evolvedJoint μ κ)

/--
**The system cannot predict the signal better than it remembers it.**

`I(X_t ; S_{t+1}) ≤ I(X_t ; S_t)`.

This is the data processing inequality for the Markov chain
`X_t → S_t → S_{t+1}`, and it is the mathematical fact that makes Still's bound
a statement about waste rather than an arbitrary inequality: the bracket
`I_mem − I_pred` it bounds dissipation by is guaranteed non-negative.

The proof is three rewrites. The evolved joint is `(id ∥ₖ κ) ∘ₘ μ`; its
marginals are `μ.fst` and `κ ∘ₘ μ.snd` (`evolvedJoint_fst`, `evolvedJoint_snd`);
and the product of *those* is `(id ∥ₖ κ)` applied to the product of the original
marginals (`Measure.prod_comp_right`) — the parallel kernel maps a product law to
a product law, which is the formal content of "the channel cannot create
dependence". Mathlib's `klDiv_comp_right_le` then applies to both arguments at
once.

Note where the hypothesis sits. Nothing is assumed about `κ` beyond its being a
Markov kernel on the *signal alone*. Had the system been allowed to act on its
environment — a kernel `X × S → X × S'` not of the form `id ∥ₖ κ` — the
inequality would be false, and rightly so: an agent that steers its environment
can know more about the environment's future than about its present.
-/
theorem predictiveInfo_le_mutualInfo (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (κ : Kernel S S') [IsMarkovKernel κ] :
    predictiveInfo μ κ ≤ mutualInfo μ := by
  rw [predictiveInfo, mutualInfo, evolvedJoint_fst, evolvedJoint_snd, Measure.prod_comp_right]
  exact klDiv_comp_right_le _ _ _

/-- **Nonpredictive information**: the memory the system holds that is silent
about the future. In `ℝ≥0∞` the subtraction is truncated, and
`predictiveInfo_le_mutualInfo` is what guarantees the truncation never bites —
see `predictiveInfo_add_nonpredictiveInfo`. -/
noncomputable def nonpredictiveInfo (μ : Measure (X × S)) (κ : Kernel S S') : ℝ≥0∞ :=
  mutualInfo μ - predictiveInfo μ κ

/-- Memory splits exactly into a predictive and a nonpredictive part. The
truncated subtraction of `ℝ≥0∞` is faithful here precisely because of the data
processing inequality. -/
theorem predictiveInfo_add_nonpredictiveInfo (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (κ : Kernel S S') [IsMarkovKernel κ] :
    predictiveInfo μ κ + nonpredictiveInfo μ κ = mutualInfo μ := by
  rw [nonpredictiveInfo, add_tsub_cancel_of_le (predictiveInfo_le_mutualInfo μ κ)]

/-- All retained information is predictive exactly when none of it is wasted. -/
theorem nonpredictiveInfo_eq_zero_iff (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (κ : Kernel S S') [IsMarkovKernel κ] :
    nonpredictiveInfo μ κ = 0 ↔ predictiveInfo μ κ = mutualInfo μ := by
  constructor
  · intro h
    have := predictiveInfo_add_nonpredictiveInfo μ κ
    rwa [h, add_zero] at this
  · intro h
    rw [nonpredictiveInfo, h, tsub_self]

/-! ### Two extreme regimes, both proved rather than asserted -/

/-- **A frozen signal is perfectly predicted.** If the signal does not change,
every remembered bit is a predictive bit and the nonpredictive information — and
so, by Still's bound, the dissipation it forces — is zero. -/
@[simp] theorem predictiveInfo_id (μ : Measure (X × S)) :
    predictiveInfo μ (Kernel.id : Kernel S S) = mutualInfo μ := by
  rw [predictiveInfo, evolvedJoint, Kernel.id_parallelComp_id, Measure.id_comp]

/-- **A signal that forgets its own past can predict nothing.** If `S_{t+1}` is
drawn from a fixed law `ν` regardless of `S_t`, the system's memory of `S_t`
carries no information about `S_{t+1}` at all.

The proof computes the evolved joint outright: pushing `μ` through
`id ∥ₖ const ν` gives the product `μ.fst ⊗ ν`, whose mutual information is zero
by `mutualInfo_prod`. Combined with `nonpredictiveInfo_const` below, this is the
sharp form of "memory that does not predict is waste": the *entire* memory is
charged against dissipation. -/
theorem evolvedJoint_const (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (ν : Measure S') [IsProbabilityMeasure ν] :
    evolvedJoint μ (Kernel.const S ν) = μ.fst.prod ν := by
  ext s hs
  have hm : Measurable fun x : X => ν (Prod.mk x ⁻¹' s) := measurable_measure_prodMk_left hs
  rw [evolvedJoint, Measure.bind_apply hs (Kernel.aemeasurable _), Measure.prod_apply hs,
    Measure.fst, lintegral_map hm measurable_fst]
  refine lintegral_congr fun p => ?_
  rw [Kernel.parallelComp_apply, Kernel.id_apply, Kernel.const_apply, Measure.prod_apply hs,
    lintegral_dirac' _ hm]

@[simp] theorem predictiveInfo_const (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (ν : Measure S') [IsProbabilityMeasure ν] :
    predictiveInfo μ (Kernel.const S ν) = 0 := by
  rw [predictiveInfo, evolvedJoint_const, mutualInfo_prod]

/-- When the signal's future is independent of its present, *every* bit the
system holds about the signal is nonpredictive. -/
theorem nonpredictiveInfo_const (μ : Measure (X × S)) [IsProbabilityMeasure μ]
    (ν : Measure S') [IsProbabilityMeasure ν] :
    nonpredictiveInfo μ (Kernel.const S ν) = mutualInfo μ := by
  rw [nonpredictiveInfo, predictiveInfo_const, tsub_zero]

/-! ## 3. Still's bound as an instance obligation

Standing rule: a physical postulate mentioning a class field is a field of that
class, never a free-standing `axiom` quantified over all instances. The reason is
recorded at `Phase3_KLBound.StructuralResonance` and applies verbatim here. The
`axiom` form

    axiom still_bound_axiom (μ : Measure (X × S)) (κ : Kernel S S') :
      thermalEnergy * (nonpredictiveInfo μ κ).toReal ≤ dissipatedWork

would be inconsistent for the same reason its predecessor was: `dissipatedWork`
is one real number fixed by a class field, while `nonpredictiveInfo μ κ` ranges
over an unbounded set as `μ` and `κ` vary, so an instance with
`dissipatedWork := 0` together with any correlated `μ` and a constant `κ` (for
which `nonpredictiveInfo_const` computes the left-hand side to be the full
mutual information) yields `False`. Bundling `μ`, `κ`, `k_B T` and `W_diss` as
data of *one* system constrains only that system. -/

/--
**The thermodynamics of prediction, as an instance obligation.**
[IRREDUCIBLE PHYSICAL POSTULATE]

Still, Sivak, Bell and Crooks (2012), Phys. Rev. Lett. **109** 120604:

```
  W_diss  ≥  k_B T · [ I(X_t ; S_t) − I(X_t ; S_{t+1}) ]
```

Every field is the data of a single physical system: its joint law over state
and signal, the signal's own dynamics, its thermal energy scale, and the work it
dissipates over one step. `still_bound` constrains exactly that system.

`memory_ne_top` is a genuine physical restriction and not bookkeeping: a system
whose state and signal are perfectly correlated over a continuum carries infinite
mutual information, and Still's bound then says only that infinite dissipation is
bounded by infinite dissipation. Requiring finite memory is what makes the real
number `dissipatedWork` say anything. By `predictiveInfo_le_mutualInfo` it also
makes the predictive information finite, so it is the *only* finiteness
hypothesis needed.
-/
class PredictiveDissipation (X S S' : Type*)
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace S'] where
  /-- The joint law of system state and signal at time `t`. -/
  joint : Measure (X × S)
  joint_isProb : IsProbabilityMeasure joint
  /-- The signal's own dynamics, `S_t ↦ S_{t+1}`. The system does not appear:
  that is the Markov-chain assumption, and it is what `evolvedJoint` encodes. -/
  signal : Kernel S S'
  signal_isMarkov : IsMarkovKernel signal
  /-- The system's memory of the signal is finite. -/
  memory_ne_top : mutualInfo joint ≠ ⊤
  /-- The thermal energy scale `k_B T`. -/
  thermalEnergy : ℝ
  thermalEnergy_pos : 0 < thermalEnergy
  /-- Work dissipated over one step of the drive, `W − ΔF`. -/
  dissipatedWork : ℝ
  /-- **The postulate.** Dissipation is at least the thermal cost of the memory
  that fails to predict. -/
  still_bound :
    thermalEnergy * (mutualInfo joint - predictiveInfo joint signal).toReal ≤ dissipatedWork

namespace PredictiveDissipation

variable (R : PredictiveDissipation X S S')

/-- The predictive information carried by an instance, `I(X_t ; S_{t+1})`. -/
noncomputable abbrev predictive : ℝ≥0∞ := predictiveInfo R.joint R.signal

/-- The nonpredictive information carried by an instance, `I_mem − I_pred`. -/
noncomputable abbrev nonpredictive : ℝ≥0∞ := nonpredictiveInfo R.joint R.signal

/-- Still's bound, restated with `nonpredictive` in place of the unfolded
subtraction. This is the class field and nothing more. -/
theorem still_bound' :
    R.thermalEnergy * (R.nonpredictive).toReal ≤ R.dissipatedWork := R.still_bound

/-- Predictive information is finite, as a consequence of the finite-memory field
and the data processing inequality. Nothing further is assumed. -/
lemma predictive_ne_top : R.predictive ≠ ⊤ := by
  have := R.joint_isProb
  have := R.signal_isMarkov
  exact ne_top_of_le_ne_top R.memory_ne_top (predictiveInfo_le_mutualInfo _ _)

lemma nonpredictive_ne_top : R.nonpredictive ≠ ⊤ :=
  ne_top_of_le_ne_top R.memory_ne_top tsub_le_self

/--
**The second law, derived.**

`0 ≤ W_diss`.

This is the exact analogue of `Phase3_KLBound.discrete_entropy_rate_nonneg`, and
the analogy is the point: there, Gibbs' inequality supplied a non-negative lower
bound for the entropy production rate; here the *data processing inequality*
supplies a non-negative lower bound for dissipated work. In neither case is
non-negativity assumed. The difference is that Gibbs' inequality compares a
system to an arbitrary reference distribution, whereas the bound below compares
the system to its own future — which is why the quantity it bounds is one a
physical system can be selected to reduce.
-/
theorem dissipatedWork_nonneg : 0 ≤ R.dissipatedWork :=
  le_trans (mul_nonneg R.thermalEnergy_pos.le ENNReal.toReal_nonneg) R.still_bound

/--
**The inference Derivation 3 needed, running in the valid direction.**

`I_mem − I_pred ≤ W_diss / k_B T`.

Contrast the old step. There the quantity of interest, `D_KL(P_ext ‖ Q_int)`, was
bounded above by `Δt · σ`, and the argument then required `σ → 0` — which is
false for a driven system in a non-equilibrium steady state. Here the quantity of
interest is bounded above by `W_diss / k_B T`, and no limit is required: *any*
bound on the dissipation is immediately a bound on the nonpredictive memory. A
system held to a dissipation budget is thereby held to a prediction standard.

This is weaker than what Derivation 3 used to claim, and it is what is true.
-/
theorem nonpredictive_le_dissipation :
    (R.nonpredictive).toReal ≤ R.dissipatedWork / R.thermalEnergy := by
  rw [le_div_iff₀ R.thermalEnergy_pos, mul_comm]
  exact R.still_bound

/-- A dissipation budget is a prediction standard: a system dissipating no more
than `ε` per step wastes at most `ε / k_B T` nats of memory. -/
theorem nonpredictive_le_of_dissipatedWork_le {ε : ℝ} (h : R.dissipatedWork ≤ ε) :
    (R.nonpredictive).toReal ≤ ε / R.thermalEnergy :=
  le_trans R.nonpredictive_le_dissipation
    (div_le_div_of_nonneg_right h R.thermalEnergy_pos.le)

/--
**A system that dissipates nothing remembers only what it can predict.**

`W_diss = 0 → I(X_t ; S_{t+1}) = I(X_t ; S_t)`.

This is the replacement for "gradient descent on `σ` drives `D_KL → 0`". It is an
implication rather than a limit, its hypothesis is a physically meaningful
idealisation (a quasi-static drive), and its conclusion is an equality between
two informations rather than the vanishing of a model mismatch.

What it does *not* say: that the system's internal model equals the
environment's statistics. Predictive information being maximal is compatible with
the system storing a lossy, encrypted or otherwise unrecognisable function of the
signal. Symbol grounding does not follow, and the manuscript no longer claims it
does.
-/
theorem predictive_eq_of_no_dissipation (h : R.dissipatedWork = 0) :
    R.predictive = mutualInfo R.joint := by
  have := R.joint_isProb
  have := R.signal_isMarkov
  have h_le : (R.nonpredictive).toReal ≤ 0 := by
    simpa [h] using R.nonpredictive_le_dissipation
  have h_zero : R.nonpredictive = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h_le ENNReal.toReal_nonneg) with h' | h'
    · exact h'
    · exact absurd h' R.nonpredictive_ne_top
  exact (nonpredictiveInfo_eq_zero_iff R.joint R.signal).1 h_zero

end PredictiveDissipation

/-! ## 4. The equality the loose bound was gesturing at

Kawai, Parrondo and Van den Broeck, *Dissipation: the phase-space perspective*,
Phys. Rev. Lett. **98** (2007) 080602:

```
  ⟨W_diss⟩  =  k_B T · D_KL( forward path ensemble ‖ time-reversed ensemble )
```

An *equality*, where Derivation 3 had a one-sided bound it could not tighten. It
is carried here as a predicate on an instance rather than as a further class
field, following the `IsRestrictionResonance` pattern of `Phase8_SelfConsistency`:
it is a property some systems have, the theorems that consume it say so in their
hypotheses, and a system whose path ensembles are not defined is not thereby
excluded from `PredictiveDissipation`. -/

/-- **Kawai–Parrondo–Van den Broeck dissipation.** The system's dissipated work is
`k_B T` times the divergence between its forward and time-reversed path ensembles
on a trajectory space `Ω`. -/
def IsKPVDissipation {Ω : Type*} [MeasurableSpace Ω]
    (R : PredictiveDissipation X S S') (forward reverse : Measure Ω) : Prop :=
  R.dissipatedWork = R.thermalEnergy * (klDiv forward reverse).toReal

/--
**The arrow of time bounds the wasted memory.**

`I_mem − I_pred ≤ D_KL(forward ‖ reverse)`.

Both sides are dimensionless informations. The right-hand side is measurable — it
is the statistical distinguishability of a film of the system from the same film
run backwards — and the left-hand side is a property of what the system knows.
The inequality says the irreversibility of the dynamics is at least the amount of
memory that fails to earn its keep.

This has no independent mathematical content: it is `still_bound` and
`IsKPVDissipation` divided by `k_B T`, in the same way that
`Phase3_KLBound.structural_resonance_bound` was its postulate multiplied by `Δt`.
What it buys is that the abstract `dissipatedWork` field is replaced by a
quantity an experiment can estimate.
-/
theorem nonpredictive_le_arrow {Ω : Type*} [MeasurableSpace Ω]
    (R : PredictiveDissipation X S S') (forward reverse : Measure Ω)
    (h : IsKPVDissipation R forward reverse) :
    (R.nonpredictive).toReal ≤ (klDiv forward reverse).toReal := by
  have h1 := R.nonpredictive_le_dissipation
  rw [h, mul_div_cancel_left₀ _ R.thermalEnergy_pos.ne'] at h1
  exact h1

end PhysicsOfConsciousness
