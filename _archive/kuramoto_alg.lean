import Mathlib
open BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

structure KuramotoSystem (V : Type*) where
  omega : V → ℝ
  A : V → V → ℝ
  symm : ∀ i j, A i j = A j i

lemma kuramoto_alg (sys : KuramotoSystem V) (theta : V → ℝ) (v : V → ℝ) 
  (h_dyn : ∀ i, v i = sys.omega i + ∑ j, sys.A i j * Real.sin (theta j - theta i)) :
  -(1/2) * ∑ i, ∑ j, sys.A i j * (- Real.sin (theta i - theta j)) * (v i - v j) - ∑ i, sys.omega i * v i = - ∑ i, (v i)^2 := by
  have H_sin (i j : V) : Real.sin (theta i - theta j) = - Real.sin (theta j - theta i) := by
    have : theta i - theta j = - (theta j - theta i) := by ring
    rw [this, Real.sin_neg]
  have H_term (i j : V) : sys.A i j * (- Real.sin (theta i - theta j)) * (v i - v j) =
    sys.A i j * Real.sin (theta j - theta i) * v i - sys.A i j * Real.sin (theta j - theta i) * v j := by
    rw [H_sin i j]
    ring
  have H_sum1 : (∑ i, ∑ j, sys.A i j * (- Real.sin (theta i - theta j)) * (v i - v j)) = 
    (∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v i) - (∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v j) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => H_term i j))]
    simp only [Finset.sum_sub_distrib]
  rw [H_sum1]
  
  have H_swap : (∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v j) = - (∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v i) := by
    rw [Finset.sum_comm]
    have H_rename : (∑ j, ∑ i, sys.A i j * Real.sin (theta j - theta i) * v j) = ∑ i, ∑ j, sys.A j i * Real.sin (theta i - theta j) * v i := rfl
    rw [H_rename]
    have H_inner_neg (i j : V) : sys.A j i * Real.sin (theta i - theta j) * v i = - (sys.A i j * Real.sin (theta j - theta i) * v i) := by
      rw [sys.symm j i, H_sin i j]
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => H_inner_neg i j))]
    simp only [Finset.sum_neg_distrib]
  rw [H_swap]
  have H_combine : ((∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v i) - -∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v i) = 
    2 * (∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v i) := by ring
  rw [H_combine]
  
  have H_factor : -(1 / 2) * (2 * ∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v i) =
    - ∑ i, (∑ j, sys.A i j * Real.sin (theta j - theta i)) * v i := by
    have : -(1 / 2) * (2 * ∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v i) = - (∑ i, ∑ j, sys.A i j * Real.sin (theta j - theta i) * v i) := by ring
    rw [this]
    apply congr_arg Neg.neg
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_mul]
    
  rw [H_factor]
  
  have H_final : -∑ i, (∑ j, sys.A i j * Real.sin (theta j - theta i)) * v i - ∑ i, sys.omega i * v i = - ∑ i, (v i)^2 := by
    have : -∑ i, (∑ j, sys.A i j * Real.sin (theta j - theta i)) * v i - ∑ i, sys.omega i * v i = 
      - (∑ i, (∑ j, sys.A i j * Real.sin (theta j - theta i)) * v i + ∑ i, sys.omega i * v i) := by ring
    rw [this]
    rw [← Finset.sum_add_distrib]
    apply congr_arg Neg.neg
    apply Finset.sum_congr rfl; intro i _
    have H_dyn_i := h_dyn i
    have : (∑ j, sys.A i j * Real.sin (theta j - theta i)) * v i + sys.omega i * v i = (sys.omega i + ∑ j, sys.A i j * Real.sin (theta j - theta i)) * v i := by ring
    rw [this, ← H_dyn_i]
    ring
  exact H_final
