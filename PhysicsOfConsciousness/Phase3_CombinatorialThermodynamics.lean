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
    exact DifferentiableAt.const_mul h_diff_sum_only (-(1/2))
  have h_diff_sum2 : DifferentiableAt ℝ (fun t => ∑ i, sys.omega i * theta t i) t := by
    have H : (fun (t : ℝ) => ∑ i, sys.omega i * theta t i) = ∑ i, (fun (t : ℝ) => sys.omega i * theta t i) := by ext; simp
    rw [H]
    apply DifferentiableAt.sum
    intro i _
    exact DifferentiableAt.const_mul (h_diff i) (sys.omega i)

  dsimp [kuramoto_potential]
  have H_sub : (fun t => - (1/2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j) - ∑ i, sys.omega i * theta t i) = 
    (fun t => - (1/2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) - (fun t => ∑ i, sys.omega i * theta t i) := rfl
  rw [H_sub, deriv_sub h_diff_sum1 h_diff_sum2]
  
  have H_const : deriv (fun t => -(1 / 2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) t = 
    -(1 / 2) * deriv (fun t => ∑ i, ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) t := by
    exact deriv_const_mul (-(1/2)) h_diff_sum_only
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
  
  have H_sum_inner : (∑ i, deriv (fun t => ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) t) =
    ∑ i, ∑ j, deriv (fun t => sys.A i j * Real.cos (theta t i - theta t j)) t := by
    apply Finset.sum_congr rfl
    intro i _
    have H2 : (fun (t : ℝ) => ∑ j, sys.A i j * Real.cos (theta t i - theta t j)) = ∑ j, (fun (t : ℝ) => sys.A i j * Real.cos (theta t i - theta t j)) := by ext; simp
    rw [H2]
    rw [deriv_sum]
    intro j _
    exact h_diff_cos i j
  rw [H_sum_inner]
  
  have H_deriv_cos : (∑ i, ∑ j, deriv (fun t => sys.A i j * Real.cos (theta t i - theta t j)) t) =
    ∑ i, ∑ j, sys.A i j * (- Real.sin (theta t i - theta t j)) * (deriv (fun t => theta t i) t - deriv (fun t => theta t j) t) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have h_diff_sub : DifferentiableAt ℝ (fun t => theta t i - theta t j) t := DifferentiableAt.sub (h_diff i) (h_diff j)
    have H1 : deriv (fun t => sys.A i j * Real.cos (theta t i - theta t j)) t = sys.A i j * deriv (fun t => Real.cos (theta t i - theta t j)) t := by
      exact deriv_const_mul (sys.A i j) (DifferentiableAt.cos h_diff_sub)
    rw [H1]
    have H2 : deriv (fun t => Real.cos (theta t i - theta t j)) t = - Real.sin (theta t i - theta t j) * deriv (fun t => theta t i - theta t j) t := by
      exact deriv_cos h_diff_sub
    rw [H2]
    have H3 : deriv (fun t => theta t i - theta t j) t = deriv (fun t => theta t i) t - deriv (fun t => theta t j) t := by
      exact deriv_sub (h_diff i) (h_diff j)
    rw [H3]
    ring
  rw [H_deriv_cos]
  
  have H_sum2 : (fun (t : ℝ) => ∑ i, sys.omega i * theta t i) = ∑ i, (fun (t : ℝ) => sys.omega i * theta t i) := by ext; simp
  rw [H_sum2]
  rw [deriv_sum]
  swap
  · intro i _
    exact DifferentiableAt.const_mul (h_diff i) (sys.omega i)
    
  have H_omega : (∑ i, deriv (fun t => sys.omega i * theta t i) t) = ∑ i, sys.omega i * deriv (fun t => theta t i) t := by
    apply Finset.sum_congr rfl
    intro i _
    exact deriv_const_mul (sys.omega i) (h_diff i)
  rw [H_omega]
  
  have H_sin (i j : V) : Real.sin (theta t i - theta t j) = - Real.sin (theta t j - theta t i) := by
    have : theta t i - theta t j = - (theta t j - theta t i) := by ring
    rw [this, Real.sin_neg]
  have H_term (i j : V) : sys.A i j * (- Real.sin (theta t i - theta t j)) * (deriv (fun t => theta t i) t - deriv (fun t => theta t j) t) =
    sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t - sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t j) t := by
    rw [H_sin i j]
    ring
  have H_sum_split : (∑ i, ∑ j, sys.A i j * (- Real.sin (theta t i - theta t j)) * (deriv (fun t => theta t i) t - deriv (fun t => theta t j) t)) = 
    (∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) - (∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t j) t) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => H_term i j))]
    simp only [Finset.sum_sub_distrib]
  rw [H_sum_split]
  
  have H_swap : (∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t j) t) = - (∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) := by
    rw [Finset.sum_comm]
    have H_rename : (∑ j, ∑ i, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t j) t) = ∑ i, ∑ j, sys.A j i * Real.sin (theta t i - theta t j) * deriv (fun t => theta t i) t := rfl
    rw [H_rename]
    have H_inner_neg (i j : V) : sys.A j i * Real.sin (theta t i - theta t j) * deriv (fun t => theta t i) t = - (sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) := by
      rw [sys.symm j i, H_sin i j]
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => H_inner_neg i j))]
    simp only [Finset.sum_neg_distrib]
  rw [H_swap]
  have H_combine : ((∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) - -∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) = 
    2 * (∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) := by ring
  rw [H_combine]
  
  have H_factor : -(1 / 2) * (2 * ∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) =
    - ∑ i, (∑ j, sys.A i j * Real.sin (theta t j - theta t i)) * deriv (fun t => theta t i) t := by
    have : -(1 / 2) * (2 * ∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) = - (∑ i, ∑ j, sys.A i j * Real.sin (theta t j - theta t i) * deriv (fun t => theta t i) t) := by ring
    rw [this]
    apply congr_arg Neg.neg
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_mul]
    
  rw [H_factor]
  
  have H_final : -∑ i, (∑ j, sys.A i j * Real.sin (theta t j - theta t i)) * deriv (fun t => theta t i) t - ∑ i, sys.omega i * deriv (fun t => theta t i) t = - ∑ i, (kuramoto_velocity sys (theta t) i)^2 := by
    have : -∑ i, (∑ j, sys.A i j * Real.sin (theta t j - theta t i)) * deriv (fun t => theta t i) t - ∑ i, sys.omega i * deriv (fun t => theta t i) t = 
      - (∑ i, (∑ j, sys.A i j * Real.sin (theta t j - theta t i)) * deriv (fun t => theta t i) t + ∑ i, sys.omega i * deriv (fun t => theta t i) t) := by ring
    rw [this]
    rw [← Finset.sum_add_distrib]
    apply congr_arg Neg.neg
    apply Finset.sum_congr rfl; intro i _
    have H_dyn_i := h_dyn i
    have : (∑ j, sys.A i j * Real.sin (theta t j - theta t i)) * deriv (fun t => theta t i) t + sys.omega i * deriv (fun t => theta t i) t = (sys.omega i + ∑ j, sys.A i j * Real.sin (theta t j - theta t i)) * deriv (fun t => theta t i) t := by ring
    rw [this]
    have H_vel : sys.omega i + ∑ j, sys.A i j * Real.sin (theta t j - theta t i) = kuramoto_velocity sys (theta t) i := rfl
    rw [H_vel, ← H_dyn_i]
    ring
  exact H_final

noncomputable def boltzmann_entropy {sys : Type*} [DecidableEq sys] (states : Finset sys) : ℝ :=
  Real.log (states.card : ℝ)

noncomputable def entropy {sys : Type*} [Fintype sys] [DecidableEq sys] (t : sys → sys) : ℝ :=
  boltzmann_entropy (Finset.image t Finset.univ)

lemma entropy_decrease {sys : Type*} [Fintype sys] [DecidableEq sys] (t : sys → sys)
  (h_nonempty : Nonempty sys) (h_not_inj : ¬ Function.Injective t) :
  entropy t < boltzmann_entropy (Finset.univ : Finset sys) := by
  dsimp [entropy, boltzmann_entropy]
  apply Real.log_lt_log
  · exact Nat.cast_pos.mpr (by
      obtain ⟨x⟩ := h_nonempty
      exact Finset.card_pos.mpr ⟨t x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩)
  · apply Nat.cast_lt.mpr
    have le : (Finset.image t Finset.univ).card ≤ (Finset.univ : Finset sys).card := Finset.card_image_le
    apply lt_of_le_of_ne le
    intro h_eq
    have h_inj : Set.InjOn t ↑(Finset.univ : Finset sys) := by
      rwa [Finset.card_image_iff] at h_eq
    apply h_not_inj
    intro x y hxy
    exact h_inj (Finset.mem_univ x) (Finset.mem_univ y) hxy
