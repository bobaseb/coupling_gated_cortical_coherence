import Mathlib
open BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma test_deriv (theta : ℝ → V → ℝ) (t : ℝ) (i j : V) (A : ℝ)
  (h_diff : ∀ i, DifferentiableAt ℝ (fun t => theta t i) t) :
  deriv (fun t => A * Real.cos (theta t i - theta t j)) t = 
  A * (- Real.sin (theta t i - theta t j)) * (deriv (fun t => theta t i) t - deriv (fun t => theta t j) t) := by
  have h_diff_sub : DifferentiableAt ℝ (fun t => theta t i - theta t j) t := DifferentiableAt.sub (h_diff i) (h_diff j)
  have H : deriv (fun t => A * Real.cos (theta t i - theta t j)) t = A * deriv (fun t => Real.cos (theta t i - theta t j)) t := by
    exact deriv_const_mul A (DifferentiableAt.cos h_diff_sub)
  rw [H]
  have H2 : deriv (fun t => Real.cos (theta t i - theta t j)) t = - Real.sin (theta t i - theta t j) * deriv (fun t => theta t i - theta t j) t := by
    exact deriv_cos h_diff_sub
  rw [H2]
  have H3 : deriv (fun t => theta t i - theta t j) t = deriv (fun t => theta t i) t - deriv (fun t => theta t j) t := by
    exact deriv_sub (h_diff i) (h_diff j)
  rw [H3]
  ring
