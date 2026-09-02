import Mathlib
import PhysicsOfConsciousness.Phase8_ContinuousField

/-!
# Phase 9 — EM field identification predicate

The identification of the posited continuum coupling kernel with the cortical
endogenous EM field is the framework's central empirical commitment. Currently it
lives entirely in prose. This module makes it a formal `Prop` whose fields are
the necessary mathematical conditions the kernel must satisfy:

1. **Joint continuity** — the kernel is a continuous function `M × M → ℝ`, which
   is what the continuum theorems (`fieldCorrelation`, `structural_resonance`,
   etc.) need for the integration and differentiation steps.
2. **Domain of positive measure** — the field is defined on a spatially extended
   region; a null set carries no coupling energy.
3. **Coupling non-negative** — `K ≥ 0`, matching the mean-field convention.
4. **Noise positive** — `D > 0`, so the phase noise defines a von Mises density.

The predicate remains uninhabited by a cortical witness — that is the empirical
question. What it makes formal is the list of conditions a future model must
satisfy to claim ``the kernel is the EM field''. The toy witness on ℝ shows
the non-cortical conditions (continuity, positive measure, non-negativity) are
jointly satisfiable.

## What this does not establish

* Not that cortex satisfies any of the conditions.
* Not that the mean-field coupling constant `K` is the integrated kernel — the
  relation `L = K` (from `FieldRealizes` in `Chain.lean`) is a separate
  numerical identification between the coarse-graining limit and the coupling
  constant, and this predicate does not derive it.
* Not that continuity on ℝ is sufficient for the analysis theorems on a compact
  cortical manifold. The predicate is deliberately modest and can be strengthened
  as the formalization demands.
-/

open Set MeasureTheory Topology

namespace PhysicsOfConsciousness

variable {M : Type*} [MeasureSpace M] [TopologicalSpace M]

/-- The necessary mathematical conditions the continuum coupling kernel must
satisfy if it is to be identified with the endogenous EM field.

The four fields below are the *formal* part of the empirical commitment. The
first two are mathematical (continuity, positive domain measure). The third
and fourth are the sign conditions `Chain.lean`'s `FieldRealizes` already
carries. Unlike `FieldRealizes`, this predicate is stated about a concrete
`ContinuousNeuralField M` rather than about the abstract scalar `K`. -/
structure IsEMFieldCoupling (sys : ContinuousNeuralField M) (K D : ℝ) : Prop where
  /-- The kernel `sys.K : M → M → ℝ` is jointly continuous. -/
  kernel_continuous : Continuous (Function.uncurry sys.K)
  /-- The domain carries positive measure (the field is spatially extended). -/
  domain_positive_measure : 0 < (volume : Measure M) (Set.univ)
  /-- The mean-field coupling constant is non-negative. -/
  coupling_nonneg : 0 ≤ K
  /-- The phase noise is positive (a von Mises density exists). -/
  noise_pos : 0 < D

/-! ## Witness: ℝ with a constant kernel -/

/-- A constant kernel on ℝ with a constant drift satisfies all four
non-cortical conditions of `IsEMFieldCoupling`.

The kernel `fun _ _ => 1` is constant hence continuous. The real line with
Lebesgue measure has positive (indeed infinite) volume. The coupling constant
`K = 1` is non-negative and `D = 1` is positive.

This is a *mathematical* witness: it shows the predicate is not vacuous. It
says nothing about cortex. -/
theorem em_constant_kernel_is_em_field_coupling :
    IsEMFieldCoupling (M := ℝ)
    (ContinuousNeuralField.mk (fun _ : ℝ => (0 : ℝ)) (fun _ _ => (1 : ℝ)) (1 : ℝ))
    (1 : ℝ) (1 : ℝ) := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · -- kernel_continuous: constant kernel on ℝ × ℝ is continuous
    have h : (Function.uncurry fun (_ _ : ℝ) => (1 : ℝ)) = fun _ : ℝ × ℝ => (1 : ℝ) := by
      ext ⟨x, y⟩; rfl
    rw [h]
    exact continuous_const
  · -- domain_positive_measure: ℝ has positive (infinite) Lebesgue measure
    -- The interval [0,1] has Lebesgue measure 1 > 0, and [0,1] ⊆ ℝ, so volume(ℝ) ≥ 1 > 0.
    have hIcc_vol : (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) = (1 : ENNReal) := by
      simp [Real.volume_Icc, ENNReal.ofReal_one]
    have hpos : (0 : ENNReal) < (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) := by
      rw [hIcc_vol]
      exact by norm_num
    have h_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.univ := Set.subset_univ _
    have h_mono : (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) ≤ (volume : Measure ℝ) (Set.univ : Set ℝ) :=
      measure_mono h_sub
    exact lt_of_lt_of_le hpos h_mono

end PhysicsOfConsciousness