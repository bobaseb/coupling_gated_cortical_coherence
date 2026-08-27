import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finset.Basic

open scoped BigOperators

noncomputable def kuramoto_potential {N : Type} [Fintype N] (K : ℝ) (θ : N → ℝ) : ℝ :=
  - (K / 2) * ∑ i, ∑ j, Real.cos (θ i - θ j)
