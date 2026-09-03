import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase3_MeasureThermodynamics
import PhysicsOfConsciousness.Phase3_PredictiveThermodynamics

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

end PhysicsOfConsciousness
