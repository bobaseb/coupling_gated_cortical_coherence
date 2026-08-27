import Mathlib
open BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

structure KuramotoSystem (V : Type*) where
  omega : V → ℝ
  A : V → V → ℝ
  symm : ∀ i j, A i j = A j i

noncomputable def kuramoto_potential (sys : KuramotoSystem V) (theta : V → ℝ) : ℝ :=
  - (1/2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta i - theta j) - ∑ i, sys.omega i * theta i

noncomputable def kuramoto_velocity (sys : KuramotoSystem V) (theta : V → ℝ) (i : V) : ℝ :=
  sys.omega i + ∑ j, sys.A i j * Real.sin (theta j - theta i)

lemma dV_dt_le_zero (sys : KuramotoSystem V) (theta : ℝ → V → ℝ) (t : ℝ) 
  (h_diff : ∀ i, DifferentiableAt ℝ (fun t => theta t i) t)
  (h_dyn : ∀ i, deriv (fun t => theta t i) t = kuramoto_velocity sys (theta t) i) :
  deriv (fun t => kuramoto_potential sys (theta t)) t = - ∑ i, (kuramoto_velocity sys (theta t) i)^2 := by
  have h_diff_cos (i j : V) : DifferentiableAt ℝ (fun t => sys.A i j * Real.cos (theta t i - theta t j)) t := by
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.cos
    apply DifferentiableAt.sub (h_diff i) (h_diff j)
  have h_diff_sum_only : DifferentiableAt ℝ (fun t => ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) t := by
    have H : (fun (t : ℝ) => ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) = ∑ i, (fun (t : ℝ) => ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) := by ext; simp
    rw [H]
    apply DifferentiableAt.sum
    intro i _
    have H2 : (fun (t : ℝ) => ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) = ∑ j, (fun (t : ℝ) => sys.A i j * Real.cos (theta t i - theta t j)) := by ext; simp
    rw [H2]
    apply DifferentiableAt.sum
    intro j _
    exact h_diff_cos i j
  have h_diff_sum1 : DifferentiableAt ℝ (fun t => - (1/2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) t := by
    apply DifferentiableAt.const_mul
    exact h_diff_sum_only
  have h_diff_sum2 : DifferentiableAt ℝ (fun t => ∑ i, sys.omega i * theta t i) t := by
    have H : (fun (t : ℝ) => ∑ i, sys.omega i * theta t i) = ∑ i, (fun (t : ℝ) => sys.omega i * theta t i) := by ext; simp
    rw [H]
    apply DifferentiableAt.sum
    intro i _
    apply DifferentiableAt.const_mul
    exact h_diff i
  dsimp [kuramoto_potential]
  have H_sub : (fun t => - (1/2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j) - ∑ i, sys.omega i * theta t i) = 
    (fun t => - (1/2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) - (fun t => ∑ i, sys.omega i * theta t i) := rfl
  rw [H_sub, deriv_sub h_diff_sum1 h_diff_sum2]
  have H_const : deriv (fun t => -(1 / 2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) t = 
    -(1 / 2) * deriv (fun t => ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) t := by
    apply deriv_const_mul
  rw [H_const]
  
  have H_sum1 : (fun (t : ℝ) => ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) = ∑ i, (fun (t : ℝ) => ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) := by ext; simp
  rw [H_sum1]
  rw [deriv_sum]
  swap
  · intro i _
    have H2 : (fun (t : ℝ) => ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) = ∑ j, (fun (t : ℝ) => sys.A i j * Real.cos (theta t i - theta t j)) := by ext; simp
    rw [H2]
    apply DifferentiableAt.sum
    intro j _
    exact h_diff_cos i j
  
  sorry
