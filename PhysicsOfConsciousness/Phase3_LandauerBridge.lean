import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_MeasureThermodynamics
import PhysicsOfConsciousness.Phase3_PredictiveThermodynamics
import PhysicsOfConsciousness.Phase1_PhaseSpaceCapacity

/-!
# Phase 3 — Landauer's heat as Still's budget

Two accounts of dissipation live in this development and until now nothing
related them.

* `Phase3_CombinatorialThermodynamics` charges a *finite* system for destroying
  information: a many-to-one update shrinks the reachable set, the bath takes up
  the difference, and `landauer_bound` says the heat is at least
  `T · (S(id) − S(t))`.
* `Phase3_PredictiveThermodynamics` charges a system for *keeping* information it
  cannot use: Still's bound says the dissipated work over one drive step is at
  least `k_B T` times the memory that fails to predict.

They are two accounts of one physical quantity, and the chain's n3 → n4 edge is
exactly the assertion that a system paying the first bill is a system subject to
the second. This module makes that assertion a construction instead of a
transfer of vocabulary: `PredictiveDissipation.ofLandauer` builds a predictive
structure **whose `dissipatedWork` is the Landauer heat of a named update and
whose `thermalEnergy` is that system's own temperature**, and whose
`still_bound` field — the irreducible postulate of the predictive file — is
*derived* from `landauer_bound` rather than assumed again.

## What has to be supplied, and why it is not bookkeeping

One hypothesis carries the whole physical content:

```
  (nonpredictiveInfo μ κ).toReal  ≤  erasedEntropy t
```

*the memory that fails to predict is no larger than the entropy the update
destroys.* This is the identification. It says the wasted bits and the erased
bits are the same bits — that the register is cleared of exactly what it could
not use — and no theorem here or elsewhere derives it, because `μ`, `κ` and `t`
are otherwise unrelated objects.

What the module does establish is that *given* the identification, Still's bound
is not an extra postulate: Landauer's heat already pays for it. That is one
postulate removed from the composite, not zero, and it is why the constructor
takes an inequality rather than a `PredictiveDissipation`.

## The fence

`nonpredictive_eq_zero_of_injective` is what stops the identification from being
free. On a *reversible* update the erased entropy is zero, so the hypothesis
forces the wasted memory to be zero too: an injective register cannot pay for a
single wasted bit, and `ofLandauer` cannot be used to pretend otherwise. This is
the same distinction `Examples.lean` §19 draws with `keepRecord_injective` — heat
attaches to refreshing a register, not to the passage of time — arriving here
from the informational side.

## A third account, and why it is the same one

`Phase3_MeasureThermodynamics` states Landauer for a *measure* space: a map that
shrinks the volume of a region forces positive heat. It had no consumer, and
§3 below gives it one by specialising it: at counting measure on a finite type
its `continuous_entropy` **is** `boltzmann_entropy`, its `is_dissipative` is
non-injectivity, and its `landauer_heat_bound` is `T · erasedEntropy`. The two
statements of Derivation 2 are one statement at two levels of generality, which
is worth a theorem rather than a remark.

## One functional, two ways of evaluating it

§4 counts the distinction `Phase1_PhaseSpaceCapacity` §3 draws one step at a
time. Two maps compute the same sum over `N` sites: `recordingSum` keeps the
site array and is injective, so it destroys nothing; `clearingSum` clears it and
destroys `N log |Val|`, which Landauer's bound prices at temperature times that.
The comparison is between two evaluations of one functional on one finite phase
space, and it prices nothing until the decomposition into site values is
declared. `erasedEntropy_ge_of_card_image_le` then removes the exhibited pair
from the statement: *any* evaluation whose results fit in a register space of
`m` states destroys at least `log (|sys| / m)`, so the charge follows from a
memory budget rather than from an implementation's choice to clear. It is a
trade and not a barrier — memory enough to keep every intermediate pays zero.

Witness: `Examples.lean` §18.5.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace PhysicsOfConsciousness

variable {sys : Type*} [Fintype sys] [DecidableEq sys]

/-- **The entropy an update destroys**: the Boltzmann entropy of the whole phase
space less that of the reachable set, `S(id) − S(t)`. This is the quantity
Landauer's bound charges for, written as one name so that the informational
hypothesis of `ofLandauer` can be stated against it. -/
noncomputable def erasedEntropy (t : sys → sys) : ℝ :=
  entropy (id : sys → sys) - entropy t

/-- An update destroys no *negative* amount of entropy: the reachable set is a
subset of the phase space. -/
theorem erasedEntropy_nonneg [Nonempty sys] (t : sys → sys) : 0 ≤ erasedEntropy t := by
  have h_le : (Finset.image t Finset.univ).card ≤ (Finset.univ : Finset sys).card :=
    Finset.card_image_le
  have h_pos : 0 < (Finset.image t Finset.univ).card :=
    Finset.card_pos.mpr ⟨t (Classical.arbitrary sys),
      Finset.mem_image.mpr ⟨Classical.arbitrary sys, Finset.mem_univ _, rfl⟩⟩
  have h_id : entropy (id : sys → sys) = boltzmann_entropy (Finset.univ : Finset sys) := by
    unfold entropy
    rw [Finset.image_id]
  rw [erasedEntropy, h_id, sub_nonneg]
  exact Real.log_le_log (by exact_mod_cast h_pos) (by exact_mod_cast h_le)

/-- **A reversible update destroys nothing.** An injective map on a finite phase
space is a bijection, so the reachable set is the whole space and the erased
entropy is exactly zero. This is the fence's arithmetic half. -/
theorem erasedEntropy_eq_zero_of_injective {t : sys → sys} (h : Function.Injective t) :
    erasedEntropy t = 0 := by
  have himg : Finset.image t Finset.univ = Finset.univ :=
    Finset.eq_univ_of_card _ (Finset.card_image_of_injective _ h)
  simp [erasedEntropy, entropy, himg, Finset.image_id]

/-- An erasure destroys a strictly positive amount, which is what makes the
budget below non-empty. -/
theorem erasedEntropy_pos_of_erasure [Nonempty sys] {t : sys → sys} (h : is_erasure t) :
    0 < erasedEntropy t :=
  sub_pos.mpr (erasure_decreases_entropy t h)

/-- **Landauer's bound, in the notation the bridge uses.** The heat is at least
the temperature times the entropy destroyed. This is `landauer_bound` and
nothing more; it is restated so that the constructor's chain of inequalities
reads in one vocabulary. -/
theorem temperature_mul_erasedEntropy_le_heat [Nonempty sys] [StatisticalMechanics sys]
    (t : sys → sys) :
    Thermodynamics.temperature (sys := sys) * erasedEntropy t ≤ heat_dissipation t :=
  landauer_bound t

section Bridge

variable {Xs Sg Sg' : Type*} [MeasurableSpace Xs] [MeasurableSpace Sg] [MeasurableSpace Sg']

/--
**Landauer's heat pays Still's bill.**

Given a finite system whose update `t` destroys `erasedEntropy t` of entropy,
and a joint law and signal dynamics whose *wasted* memory is no larger than
that, this is the predictive structure of that very system: its thermal scale is
the system's temperature, its dissipated work is the system's Landauer heat, and
`still_bound` is proved rather than assumed.

**What the hypotheses are.**

* `h_fin` is `PredictiveDissipation.memory_ne_top`, unchanged: a memory of
  infinite mutual information makes the real number `dissipatedWork` say nothing.
* `h_waste` is the identification, and it is the physics. See the module
  docstring; `nonpredictive_eq_zero_of_injective` below is the check that it is
  not free.

**What this does not establish.** Not that any physical register satisfies
`h_waste` — nothing here relates `μ` and `κ` to `t` except that inequality. Not
Still's bound in general: the postulate remains a class field, and what is shown
is that *this* instance discharges it from Landauer's, so the composite of the
two derivations carries one irreducible postulate at this joint rather than two.
-/
@[instance_reducible]
noncomputable def PredictiveDissipation.ofLandauer [Nonempty sys] [StatisticalMechanics sys]
    (t : sys → sys)
    (μ : Measure (Xs × Sg)) [IsProbabilityMeasure μ]
    (κ : Kernel Sg Sg') [IsMarkovKernel κ]
    (h_fin : mutualInfo μ ≠ ⊤)
    (h_waste : (nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t) :
    PredictiveDissipation Xs Sg Sg' where
  joint := μ
  joint_isProb := inferInstance
  signal := κ
  signal_isMarkov := inferInstance
  memory_ne_top := h_fin
  thermalEnergy := Thermodynamics.temperature (sys := sys)
  thermalEnergy_pos := Thermodynamics.temperature_pos
  dissipatedWork := heat_dissipation t
  still_bound := by
    refine le_trans ?_ (temperature_mul_erasedEntropy_le_heat (sys := sys) t)
    exact mul_le_mul_of_nonneg_left h_waste Thermodynamics.temperature_pos.le

@[simp] theorem PredictiveDissipation.ofLandauer_thermalEnergy [Nonempty sys]
    [StatisticalMechanics sys] (t : sys → sys) (μ : Measure (Xs × Sg)) [IsProbabilityMeasure μ]
    (κ : Kernel Sg Sg') [IsMarkovKernel κ] (h_fin : mutualInfo μ ≠ ⊤)
    (h_waste : (nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t) :
    (PredictiveDissipation.ofLandauer (sys := sys) t μ κ h_fin h_waste).thermalEnergy
      = Thermodynamics.temperature (sys := sys) := rfl

@[simp] theorem PredictiveDissipation.ofLandauer_dissipatedWork [Nonempty sys]
    [StatisticalMechanics sys] (t : sys → sys) (μ : Measure (Xs × Sg)) [IsProbabilityMeasure μ]
    (κ : Kernel Sg Sg') [IsMarkovKernel κ] (h_fin : mutualInfo μ ≠ ⊤)
    (h_waste : (nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t) :
    (PredictiveDissipation.ofLandauer (sys := sys) t μ κ h_fin h_waste).dissipatedWork
      = heat_dissipation t := rfl

@[simp] theorem PredictiveDissipation.ofLandauer_nonpredictive [Nonempty sys]
    [StatisticalMechanics sys] (t : sys → sys) (μ : Measure (Xs × Sg)) [IsProbabilityMeasure μ]
    (κ : Kernel Sg Sg') [IsMarkovKernel κ] (h_fin : mutualInfo μ ≠ ⊤)
    (h_waste : (nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t) :
    (PredictiveDissipation.ofLandauer (sys := sys) t μ κ h_fin h_waste).nonpredictive
      = nonpredictiveInfo μ κ := rfl

/--
**The fence: a reversible register pays for nothing.**

If the update is injective it destroys no entropy, so the identification
`h_waste` — the hypothesis of `ofLandauer` — forces the wasted memory to vanish
outright. A system that keeps a record rather than clearing one cannot be given a
Landauer budget for wasted memory, at any size.

This is what keeps the constructor honest. Without it `h_waste` would look like a
bookkeeping side condition; with it, `h_waste` is visibly a claim that the
register is *cleared*, and the manuscript's Norton–Shenker paragraph — heat
attaches to refreshing a register, not to the collision of histories — has a
theorem behind it on the informational side as well as the combinatorial one.
-/
theorem nonpredictive_eq_zero_of_injective {t : sys → sys} (hinj : Function.Injective t)
    {μ : Measure (Xs × Sg)} [IsProbabilityMeasure μ] {κ : Kernel Sg Sg'} [IsMarkovKernel κ]
    (h_fin : mutualInfo μ ≠ ⊤)
    (h_waste : (nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t) :
    nonpredictiveInfo μ κ = 0 := by
  rw [erasedEntropy_eq_zero_of_injective hinj] at h_waste
  have h_ne_top : nonpredictiveInfo μ κ ≠ ⊤ := ne_top_of_le_ne_top h_fin tsub_le_self
  rcases (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h_waste ENNReal.toReal_nonneg) with h | h
  · exact h
  · exact absurd h h_ne_top

end Bridge

/-! ## 3. The measure-theoretic restatement, specialised

`Phase3_MeasureThermodynamics` is Derivation 2 over a measure space. Nothing
consumed it, and a module whose theorems nothing consumes is the defect
`simulations/check_leaves.py` exists to catch. The three results below consume it
by identifying it with the combinatorial account on a finite register — the case
the chain actually runs on, since n1 supplies a *finite* phase space and
`Examples.lean` §19's `succ_is_not_an_erasure` fences what happens without
finiteness. -/

section MeasureRestatement

variable {sys : Type*} [Fintype sys] [DecidableEq sys] [MeasurableSpace sys]
  [MeasurableSingletonClass sys]

omit [Fintype sys] [DecidableEq sys] in
theorem count_finset_toReal (S : Finset sys) :
    ((Measure.count : Measure sys) (↑S : Set sys)).toReal = S.card := by
  rw [Measure.count_apply_finset]; simp

omit [Fintype sys] [DecidableEq sys] in
theorem count_finset_ne_top (S : Finset sys) :
    (Measure.count : Measure sys) (↑S : Set sys) ≠ ⊤ := by
  rw [Measure.count_apply_finset]; simp

omit [MeasurableSpace sys] [MeasurableSingletonClass sys] in
theorem image_univ_coe (t : sys → sys) :
    t '' (Set.univ : Set sys) = ↑(Finset.image t Finset.univ) := by simp

omit [Fintype sys] in
/-- **Boltzmann's entropy is the measure-theoretic one at counting measure.**
`log (vol S)` with `vol` counting is `log |S|`. -/
theorem continuous_entropy_count_eq_boltzmann (S : Finset sys) :
    continuous_entropy (Measure.count : Measure sys) (↑S : Set sys) = boltzmann_entropy S := by
  unfold continuous_entropy boltzmann_entropy
  rw [Measure.count_apply_finset]
  simp

/-- **Volume contraction is non-injectivity**, on a finite register at counting
measure: the image of a map that identifies two states is a strictly smaller
set. -/
theorem is_dissipative_count_of_not_injective {t : sys → sys} (h : ¬ Function.Injective t) :
    is_dissipative (Measure.count : Measure sys) t Set.univ MeasurableSet.univ := by
  unfold is_dissipative
  rw [image_univ_coe, ← Finset.coe_univ (α := sys), Measure.count_apply_finset,
    Measure.count_apply_finset]
  exact_mod_cast not_injective_image_card_lt t h

/-- **The two heat bounds are one bound.** `Phase3_MeasureThermodynamics`'s
`landauer_heat_bound`, at counting measure on a finite register, is `T` times
the entropy the update erases. -/
theorem landauer_heat_bound_count_eq (t : sys → sys) (T : ℝ) :
    landauer_heat_bound (Measure.count : Measure sys) T Set.univ (t '' Set.univ)
      = T * erasedEntropy t := by
  unfold landauer_heat_bound erasedEntropy entropy
  rw [image_univ_coe, ← Finset.coe_univ (α := sys), continuous_entropy_count_eq_boltzmann,
    continuous_entropy_count_eq_boltzmann]
  simp [Finset.image_id]

/-- **The measure-theoretic theorem, fired on a finite register.**
`dissipative_implies_heat` — the continuum statement — applied at counting
measure to an erasure, which is the configuration Derivation 2 is about. With
`landauer_heat_bound_count_eq` this reproduces `erasedEntropy_pos_of_erasure`
from the other file's theorem rather than from `erasure_decreases_entropy`, so
the two accounts are checked against each other rather than merely coexisting. -/
theorem measure_heat_pos_of_erasure [Nonempty sys] {t : sys → sys} (h : is_erasure t)
    {T : ℝ} (hT : 0 < T) :
    0 < landauer_heat_bound (Measure.count : Measure sys) T Set.univ (t '' Set.univ) := by
  have hpos : 0 < ((Measure.count : Measure sys) (Set.univ : Set sys)).toReal := by
    rw [← Finset.coe_univ (α := sys), count_finset_toReal]
    exact_mod_cast Finset.card_pos.mpr Finset.univ_nonempty
  have hfin : (Measure.count : Measure sys) (Set.univ : Set sys) ≠ ⊤ := by
    rw [← Finset.coe_univ (α := sys)]; exact count_finset_ne_top _
  have himgpos : 0 < ((Measure.count : Measure sys) (t '' (Set.univ : Set sys))).toReal := by
    rw [image_univ_coe, count_finset_toReal]
    have : 0 < (Finset.image t Finset.univ).card :=
      Finset.card_pos.mpr ⟨t (Classical.arbitrary sys),
        Finset.mem_image.mpr ⟨Classical.arbitrary sys, Finset.mem_univ _, rfl⟩⟩
    exact_mod_cast this
  exact dissipative_implies_heat (vol := (Measure.count : Measure sys)) t Set.univ
    MeasurableSet.univ (is_dissipative_count_of_not_injective h) hpos hfin himgpos T hT

/-- The two derivations of the same positivity agree, which is the point of the
specialisation: the measure-theoretic bound at counting measure is exactly
`T · erasedEntropy t`, and both routes make it positive on an erasure. -/
theorem measure_heat_eq_temperature_mul_erasedEntropy [Nonempty sys] {t : sys → sys}
    (h : is_erasure t) {T : ℝ} (hT : 0 < T) : 0 < T * erasedEntropy t := by
  have := measure_heat_pos_of_erasure (sys := sys) h hT
  rwa [landauer_heat_bound_count_eq] at this

end MeasureRestatement

/-! ## 4. One functional, two ways of evaluating it

`Phase1_PhaseSpaceCapacity` §3 is careful about where heat appears: not at
losing history, but at *erasure*. The joint map that keeps the incoming record
is injective and dissipates nothing; `absorbStep`, which refreshes the incoming
slot instead, is not and does. That distinction has been stated one step at a
time. This section counts it over `N` of them.

The functional is a sum over sites — the reduction a mean-field kernel performs,
in the only form a finite phase space can carry it. Two evaluations:

* `recordingSum` accumulates the site values into the register and *leaves the
  site array standing*. It is injective (`recordingSum_injective`), so the
  entropy it destroys is exactly zero and Landauer's bound charges it nothing.
* `clearingSum` computes the same register value and clears the array. Its image
  is one array's worth of states, so it destroys `N log |Val|`
  (`erasedEntropy_clearingSum`) and the heat is at least the temperature times
  that (`temperature_mul_le_heat_clearingSum`) — `Ω(N)`, linear in the number of
  sites reduced, with a coefficient set by the alphabet each site is read to.

This is the analog energy-per-operation argument with the hand-waving removed,
and what it prices is not what it is usually said to price.

**Scope, and it is the whole of the result's reach.**

The comparison is between two ways of *evaluating one functional*, not between
two ways of being conscious, and not between two substrates. `recordingSum` is
a map on a finite phase space like any other; nothing here says a continuous
medium performs it, that a digital machine cannot, or that either is easier to
build. What is proved is that the record-keeping evaluation carries no Landauer
charge and the clearing one carries a charge growing linearly in `N`.

The bound on the clearing route is a *lower* bound on heat, and the zero on the
recording route is a lower bound too — it is the absence of a charge, not the
achievement of free computation. A reversible implementation still pays for the
noise floor it runs above, which is the diffusion `D` of
`Phase8_FokkerPlanck` and not this section's subject.

And the count is in bits of the site alphabet, `N log |Val|`, so it prices
nothing until the decomposition of the field into site values is declared. That
is the same `κ` problem the installed-coupling argument has, in the same place:
a quantity linear in `N` with an undetermined coefficient is a scaling law and
not an energy. -/

/-! ### The budget charges, not the implementation

`erasedEntropy_clearingSum` computes a charge for one map, and that map erases
because it is *defined* to clear. The obvious reply is that the implementation
chose to clear, and `recordingSum` is the proof that it did not have to. The
lemmas below close the reply by quantifying over implementations instead of
exhibiting two.

`erasedEntropy_ge_of_card_image_le` is the general form, and it is extraction
rather than new mathematics: `erasedEntropy_clearingSum` already performs this
computation at one image cardinality, through `card_image_clearingSum`. Any
evaluation whose reachable set fits in a register space of `m` states destroys
at least `log (|sys| / m)`, by pigeonhole — the phase space has not moved, and
everything the update fails to reach is entropy it removed. Below the size of
the phase space the map is not surjective, hence not injective on a finite
space, hence an erasure (`is_erasure_of_card_image_lt`), and
`temperature_mul_log_le_heat_of_card_image_le` prices it.

So the claim upgrades from *one implementation pays* to *every implementation
within a memory budget pays*, at a stated exchange rate.

**And it is a trade, not a barrier**, which is the whole of its content. Memory
sufficient to retain every intermediate costs zero, which is exactly
`recordingSum_injective`; the theorem prices the exchange between memory and
dissipation and closes neither end of it. It also still prices nothing in watts
until the decomposition of the field into site values is declared — the same `κ`
problem, in the same place, as the comparison above and as the
installed-coupling argument. -/

/-- **The entropy a memory budget forces.** An update whose reachable set has at
most `m` states destroys at least `log (|sys| / m)`, whatever the update is.

The hypothesis is a *budget*: it says where the evaluation may put its results
and nothing about how it computes them. What the quantifier buys over
`erasedEntropy_clearingSum` is that no map has to be exhibited — a map that
reaches few states is charged for the states it does not reach. -/
theorem erasedEntropy_ge_of_card_image_le [Nonempty sys] {t : sys → sys} {m : ℕ}
    (hm : 0 < m) (h : (Finset.image t Finset.univ).card ≤ m) :
    Real.log ((Fintype.card sys : ℝ) / m) ≤ erasedEntropy t := by
  have hN : (0 : ℝ) < Fintype.card sys := by exact_mod_cast Fintype.card_pos (α := sys)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have himg : 0 < (Finset.image t Finset.univ).card :=
    Finset.card_pos.mpr ⟨t (Classical.arbitrary sys),
      Finset.mem_image.mpr ⟨Classical.arbitrary sys, Finset.mem_univ _, rfl⟩⟩
  have hid : entropy (id : sys → sys) = Real.log (Fintype.card sys) := by
    unfold entropy boltzmann_entropy
    rw [Finset.image_id, Finset.card_univ]
  have hlog : Real.log ((Finset.image t Finset.univ).card : ℝ) ≤ Real.log m :=
    Real.log_le_log (by exact_mod_cast himg) (by exact_mod_cast h)
  rw [erasedEntropy, hid, Real.log_div (ne_of_gt hN) (ne_of_gt hm')]
  unfold entropy boltzmann_entropy
  linarith

/-- **A budget below the phase space is an erasure.** An update that reaches
fewer states than the space holds is not surjective, hence — on a finite phase
space, and only there — not injective, which is what `is_erasure` is. The step
is `is_erasure_of_not_surjective`, where finiteness does the work. -/
theorem is_erasure_of_card_image_lt {t : sys → sys}
    (h : (Finset.image t Finset.univ).card < Fintype.card sys) : is_erasure t := by
  refine is_erasure_of_not_surjective t fun hsurj => ?_
  have himg : Finset.image t Finset.univ = Finset.univ :=
    Finset.eq_univ_of_forall fun y => by
      obtain ⟨x, hx⟩ := hsurj y
      exact Finset.mem_image.2 ⟨x, Finset.mem_univ x, hx⟩
  rw [himg, Finset.card_univ] at h
  exact lt_irrefl _ h

/-- **Landauer's bill for a memory budget.** Temperature times
`log (|sys| / m)`, for any evaluation that puts its results in `m` states.

This is the exchange rate between memory and dissipation, and it closes neither
end: enlarging `m` to the whole phase space sends the bound to zero, which is
the reversible route and not a failure of the theorem. -/
theorem temperature_mul_log_le_heat_of_card_image_le [Nonempty sys] [StatisticalMechanics sys]
    {t : sys → sys} {m : ℕ} (hm : 0 < m) (h : (Finset.image t Finset.univ).card ≤ m) :
    Thermodynamics.temperature (sys := sys) * Real.log ((Fintype.card sys : ℝ) / m)
      ≤ heat_dissipation t := by
  refine le_trans ?_ (temperature_mul_erasedEntropy_le_heat (sys := sys) t)
  exact mul_le_mul_of_nonneg_left (erasedEntropy_ge_of_card_image_le hm h)
    (le_of_lt Thermodynamics.temperature_pos)

section Reduction

variable {Reg Val : Type*} [Fintype Reg] [DecidableEq Reg] [AddCommGroup Reg]
  [Fintype Val] [DecidableEq Val]

/-- The reduction performed digitally: the `N` site values are accumulated into
the register and the site array is cleared to `val₀`. Clearing is what a working
register does; keeping every input is the alternative below. -/
def clearingSum {N : ℕ} (site : Val → Reg) (val₀ : Val) :
    Reg × (Fin N → Val) → Reg × (Fin N → Val) :=
  fun rv => (rv.1 + ∑ k, site (rv.2 k), fun _ => val₀)

/-- The same reduction with the record kept: the register carries the sum and
the site array is left where it was. -/
def recordingSum {N : ℕ} (site : Val → Reg) :
    Reg × (Fin N → Val) → Reg × (Fin N → Val) :=
  fun rv => (rv.1 + ∑ k, site (rv.2 k), rv.2)

omit [Fintype Reg] [DecidableEq Reg] [Fintype Val] [DecidableEq Val] in
/-- **Keeping the record is reversible.** The array is read straight off the
output and the register's old value is the sum subtracted back. -/
theorem recordingSum_injective {N : ℕ} (site : Val → Reg) :
    Function.Injective (recordingSum (N := N) site) := by
  rintro ⟨r, v⟩ ⟨r', v'⟩ h
  simp only [recordingSum, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h2
  simpa using h1

/-- **So it destroys nothing.** The reduction itself carries no Landauer charge:
`erasedEntropy` is exactly zero, and `temperature_mul_erasedEntropy_le_heat`
bounds the heat below by zero and no more. -/
theorem erasedEntropy_recordingSum {N : ℕ} (site : Val → Reg) :
    erasedEntropy (recordingSum (N := N) site) = 0 :=
  erasedEntropy_eq_zero_of_injective (recordingSum_injective site)

/-- The clearing evaluation reaches exactly one array: the cleared one. -/
theorem image_clearingSum {N : ℕ} (site : Val → Reg) (val₀ : Val) :
    Finset.image (clearingSum (N := N) site val₀) Finset.univ
      = Finset.image (fun r : Reg => (r, (fun _ => val₀ : Fin N → Val))) Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨rv, rfl⟩
    exact ⟨rv.1 + ∑ k, site (rv.2 k), rfl⟩
  · rintro ⟨r, rfl⟩
    refine ⟨(r - ∑ _k : Fin N, site val₀, fun _ => val₀), ?_⟩
    simp [clearingSum]

theorem card_image_clearingSum {N : ℕ} (site : Val → Reg) (val₀ : Val) :
    (Finset.image (clearingSum (N := N) site val₀) Finset.univ).card = Fintype.card Reg := by
  rw [image_clearingSum,
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.injEq _ _ _ _ ▸ h).1),
    Finset.card_univ]

/-- **`Ω(N)`, exactly.** Clearing the site array after the reduction destroys
`N log |Val|` of entropy: the reachable set has shrunk from the whole phase
space to one register's worth of states, and the factor lost is the array. -/
theorem erasedEntropy_clearingSum [Nonempty Reg] [Nonempty Val] {N : ℕ}
    (site : Val → Reg) (val₀ : Val) :
    erasedEntropy (clearingSum (N := N) site val₀) = N * Real.log (Fintype.card Val) := by
  have hReg : (0 : ℝ) < Fintype.card Reg := by exact_mod_cast Fintype.card_pos (α := Reg)
  have hVal : (0 : ℝ) < Fintype.card Val := by exact_mod_cast Fintype.card_pos (α := Val)
  have hcard : Fintype.card (Reg × (Fin N → Val)) = Fintype.card Reg * Fintype.card Val ^ N := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [erasedEntropy, entropy, entropy, Finset.image_id, boltzmann_entropy, boltzmann_entropy,
    Finset.card_univ, card_image_clearingSum, hcard]
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (ne_of_gt hReg) (by positivity), Real.log_pow]
  ring

omit [Fintype Reg] [DecidableEq Reg] [Fintype Val] [DecidableEq Val] in
/-- A cleared array is unreachable from any state whose array is not cleared, so
long as there is another letter and at least one site. -/
theorem clearingSum_not_surjective [Nonempty Reg] {N : ℕ} (hN : 0 < N)
    (site : Val → Reg) {val₀ val₁ : Val} (hne : val₁ ≠ val₀) :
    ¬ Function.Surjective (clearingSum (N := N) site val₀) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (Classical.arbitrary Reg,
    Function.update (fun _ => val₀) ⟨0, hN⟩ val₁)
  have hval := congrFun (congrArg Prod.snd hx) ⟨0, hN⟩
  simp [clearingSum] at hval
  exact hne hval.symm

omit [DecidableEq Reg] [DecidableEq Val] in
/-- Hence it is an erasure, by `is_erasure_of_not_surjective` — the step where
finiteness of the phase space does the work. -/
theorem clearingSum_is_erasure [Nonempty Reg] {N : ℕ} (hN : 0 < N)
    (site : Val → Reg) {val₀ val₁ : Val} (hne : val₁ ≠ val₀) :
    is_erasure (clearingSum (N := N) site val₀) :=
  is_erasure_of_not_surjective _ (clearingSum_not_surjective hN site hne)

theorem erasedEntropy_clearingSum_pos [Nonempty Reg] [Nonempty Val] {N : ℕ} (hN : 0 < N)
    (site : Val → Reg) {val₀ val₁ : Val} (hne : val₁ ≠ val₀) :
    0 < erasedEntropy (clearingSum (N := N) site val₀) := by
  rw [erasedEntropy_clearingSum]
  have h2 : (2 : ℝ) ≤ Fintype.card Val := by
    have hcard : 2 ≤ Fintype.card Val := Fintype.one_lt_card_iff.2 ⟨val₁, val₀, hne⟩
    exact_mod_cast hcard
  have hlog : 0 < Real.log (Fintype.card Val) := Real.log_pos (by linarith)
  positivity

/-- **The reduction costs no erasure; clearing the record costs `N` times a
letter.** The one-line form of the comparison: two maps computing the same
register value, one charged nothing and the other charged a quantity linear in
the number of sites reduced. -/
theorem erasedEntropy_recordingSum_lt_clearingSum [Nonempty Reg] [Nonempty Val] {N : ℕ}
    (hN : 0 < N) (site : Val → Reg) {val₀ val₁ : Val} (hne : val₁ ≠ val₀) :
    erasedEntropy (recordingSum (N := N) site)
      < erasedEntropy (clearingSum (N := N) site val₀) := by
  rw [erasedEntropy_recordingSum]
  exact erasedEntropy_clearingSum_pos hN site hne

/-- **Landauer's bill for the clearing evaluation.** Temperature times
`N log |Val|`, and no smaller, for a system whose thermodynamics is declared.

The temperature is the phase space's own, as everywhere in this file; what the
`StatisticalMechanics` instance supplies is `heat_eq`, and the bound is
`landauer_bound` specialized to the entropy this map destroys. -/
theorem temperature_mul_le_heat_clearingSum [Nonempty Reg] [Nonempty Val] {N : ℕ}
    [StatisticalMechanics (Reg × (Fin N → Val))] (site : Val → Reg) (val₀ : Val) :
    Thermodynamics.temperature (sys := Reg × (Fin N → Val)) * (N * Real.log (Fintype.card Val))
      ≤ heat_dissipation (clearingSum (N := N) site val₀) := by
  have hbound := temperature_mul_erasedEntropy_le_heat (sys := Reg × (Fin N → Val))
    (clearingSum (N := N) site val₀)
  rwa [erasedEntropy_clearingSum] at hbound

omit [DecidableEq Reg] [AddCommGroup Reg] [DecidableEq Val] in
/-- The budget the clearing evaluation keeps to: one register's worth of states
out of `|Reg| · |Val|^N`, so the ratio the general bound charges for is exactly
`|Val|^N`. -/
theorem log_card_div_card_reg [Nonempty Reg] [Nonempty Val] {N : ℕ} :
    Real.log ((Fintype.card (Reg × (Fin N → Val)) : ℝ) / Fintype.card Reg)
      = N * Real.log (Fintype.card Val) := by
  have hReg : (0 : ℝ) < Fintype.card Reg := by exact_mod_cast Fintype.card_pos (α := Reg)
  have hcard : Fintype.card (Reg × (Fin N → Val)) = Fintype.card Reg * Fintype.card Val ^ N := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  push_cast
  rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hReg), mul_one, Real.log_pow]

/-- **The budget bound is tight here.** Charged only for the states it fails to
reach, the clearing evaluation still owes `N log |Val|` — the quantity
`erasedEntropy_clearingSum` computes from the map's definition. The general
lemma therefore loses nothing on the instance it generalizes, which is what
makes it a replacement for the exhibited comparison rather than a weaker
statement beside it. -/
theorem erasedEntropy_clearingSum_of_budget [Nonempty Reg] [Nonempty Val] {N : ℕ}
    (site : Val → Reg) (val₀ : Val) :
    (N : ℝ) * Real.log (Fintype.card Val)
      ≤ erasedEntropy (clearingSum (N := N) site val₀) := by
  have h := erasedEntropy_ge_of_card_image_le
    (sys := Reg × (Fin N → Val)) (t := clearingSum (N := N) site val₀)
    (m := Fintype.card Reg) Fintype.card_pos
    (le_of_eq (card_image_clearingSum site val₀))
  rwa [log_card_div_card_reg] at h

end Reduction

#print axioms recordingSum_injective
#print axioms erasedEntropy_recordingSum
#print axioms erasedEntropy_clearingSum
#print axioms erasedEntropy_recordingSum_lt_clearingSum
#print axioms temperature_mul_le_heat_clearingSum
#print axioms erasedEntropy_ge_of_card_image_le
#print axioms is_erasure_of_card_image_lt
#print axioms temperature_mul_log_le_heat_of_card_image_le
#print axioms erasedEntropy_clearingSum_of_budget

end PhysicsOfConsciousness
