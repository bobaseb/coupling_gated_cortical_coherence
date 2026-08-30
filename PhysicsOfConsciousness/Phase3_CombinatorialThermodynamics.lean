import Mathlib

open BigOperators

namespace PhysicsOfConsciousness

variable {V : Type*} [Fintype V] [DecidableEq V]

structure KuramotoSystem (V : Type*) where
  omega : V → ℝ
  A : V → V → ℝ
  symm : ∀ i j, A i j = A j i

/--
The full Kuramoto potential, including the natural-frequency term.

**Two different potentials live in this development, and they are now chained.**
`dV_dt_le_zero` below proves Lyapunov descent for *this* function, while
`phase_locked_minimizes_potential` (in `Phase4_KuramotoDynamics.lean`) and
everything downstream of it (Phase 5's `ThermodynamicCover`) characterise the
minimum of `kuramoto_potential_dynamic`, which drops the `- ∑ ωᵢ θᵢ` term.

The difference is substantive, not cosmetic: `kuramoto_potential_unbounded_below`
proves that whenever some `ωᵢ ≠ 0` this potential is *unbounded below* — walk `θ`
out along `ω` and the bounded cosine term cannot compensate — so it has no
minimum for phase-locking to attain. The manuscript's phrase "the phase-locked
state minimises the Lyapunov potential of the system" is therefore true of
`kuramoto_potential_dynamic` and false of this one.

`Phase4_RotatingFrame.lean` closes the gap by the standard reduction to the
rotating frame (θᵢ ↦ θᵢ - Ω t). For *identical* natural frequencies `ω ≡ Ω`,
`is_kuramoto_trajectory_rotate` sends a trajectory of this system to a trajectory
of the zero-frequency system `sys.reduced`, on which the two potentials coincide
(`kuramoto_potential_reduced`); `dynamic_potential_descent` then transports the
descent proved here onto `kuramoto_potential_dynamic`, and `rotating_frame_chain`
runs the whole chain through to phase-locking and `r² = 1`. The reduction is
exact only for identical frequencies; a genuine spread leaves residual detunings,
and phase-locking then requires a critical coupling `K_c` that this file does not
formalize. For what is proved about `K_c` — one direction, from an assumed
stationary density — see `Phase8_SelfConsistency.lean`.
-/
noncomputable def kuramoto_potential (sys : KuramotoSystem V) (theta : V → ℝ) : ℝ :=
  - (1/2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta i - theta j) - ∑ i, sys.omega i * theta i

noncomputable def kuramoto_velocity (sys : KuramotoSystem V) (theta : V → ℝ) (i : V) : ℝ :=
  sys.omega i + ∑ j, sys.A i j * Real.sin (theta j - theta i)

/-- The Kuramoto vector field as a self-map of the state space `V → ℝ`, which is
what the ODE theorems in `Mathlib.Analysis.ODE` want. Pointwise it is
`kuramoto_velocity`; the only difference is that the index is bundled. -/
noncomputable def kuramotoField (sys : KuramotoSystem V) (theta : V → ℝ) : V → ℝ :=
  fun i => kuramoto_velocity sys theta i

omit [DecidableEq V] in
/-- **The Kuramoto field is globally Lipschitz**, with constant `2 ∑ᵢⱼ |Aᵢⱼ|`.

Two facts make this hold with no smallness or locality caveat: `sin` is
`1`-Lipschitz, and `V` is finite so the sum over `j` is finite. The natural
frequencies drop out — they are an additive constant in `θ` — so the bound sees
only the coupling matrix. The state space carries the sup metric, which is why
the row sum rather than the whole matrix would suffice; `∑ᵢⱼ |Aᵢⱼ|` is used
because it dominates every row and needs no `max`.

This is what makes the Kuramoto ODE well-posed in the strong sense: uniqueness
of solutions holds on all of `ℝ`, not just locally. See
`is_kuramoto_trajectory_unique` in `Phase4_KuramotoDynamics.lean`, and the scope
note there for what is *not* proved (global existence). -/
lemma kuramotoField_lipschitz (sys : KuramotoSystem V) :
    LipschitzWith (Real.toNNReal (2 * ∑ i, ∑ j, |sys.A i j|)) (kuramotoField sys) := by
  set C : ℝ := ∑ i, ∑ j, |sys.A i j| with hC
  have hC0 : 0 ≤ C := by
    apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _; positivity
  have hrow : ∀ i, ∑ j, |sys.A i j| ≤ C := by
    intro i
    exact Finset.single_le_sum (f := fun i => ∑ j, |sys.A i j|)
      (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hK : ((Real.toNNReal (2 * C) : NNReal) : ℝ) = 2 * C := Real.coe_toNNReal _ (by positivity)
  rw [hK, dist_pi_le_iff (by positivity)]
  intro i
  have hsin : ∀ a b : ℝ, |Real.sin a - Real.sin b| ≤ |a - b| := by
    intro a b
    have := Real.lipschitzWith_sin.dist_le_mul a b
    simpa [Real.dist_eq] using this
  have hstep : |kuramotoField sys x i - kuramotoField sys y i|
      ≤ ∑ j, |sys.A i j| * (2 * dist x y) := by
    have hexp : kuramotoField sys x i - kuramotoField sys y i
        = ∑ j, sys.A i j * (Real.sin (x j - x i) - Real.sin (y j - y i)) := by
      simp [kuramotoField, kuramoto_velocity, Finset.sum_sub_distrib, mul_sub]
    rw [hexp]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (hsin _ _).trans ?_
    have h1 : |x j - y j| ≤ dist x y := by
      simpa [Real.dist_eq] using dist_le_pi_dist x y j
    have h2 : |x i - y i| ≤ dist x y := by
      simpa [Real.dist_eq] using dist_le_pi_dist x y i
    have h3 : |(x j - x i) - (y j - y i)| ≤ |x j - y j| + |x i - y i| := by
      have he : (x j - x i) - (y j - y i) = (x j - y j) - (x i - y i) := by ring
      rw [he]
      exact abs_sub _ _
    linarith
  calc dist (kuramotoField sys x i) (kuramotoField sys y i)
      = |kuramotoField sys x i - kuramotoField sys y i| := Real.dist_eq _ _
    _ ≤ ∑ j, |sys.A i j| * (2 * dist x y) := hstep
    _ = (∑ j, |sys.A i j|) * (2 * dist x y) := by rw [← Finset.sum_mul]
    _ ≤ C * (2 * dist x y) := by
        apply mul_le_mul_of_nonneg_right (hrow i)
        positivity
    _ = 2 * C * dist x y := by ring

omit [DecidableEq V] in
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

structure StochasticMatrix (n : Type*) [Fintype n] [DecidableEq n] where
  P : Matrix n n ℝ
  nonneg : ∀ i j, 0 ≤ P i j
  sum_eq_one : ∀ i, ∑ j, P i j = 1

def is_prob_dist {n : Type*} [Fintype n] (p : n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

noncomputable def shannon_entropy {n : Type*} [Fintype n] (p : n → ℝ) : ℝ :=
  - ∑ i, p i * Real.log (p i)

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
def is_erasure {sys : Type*} (t : sys → sys) : Prop :=
  ¬ Function.Injective t

theorem landauer_from_reversibility
  {S B : Type*} [DecidableEq S] [DecidableEq B]
  (X : Finset S) (Y : Finset B) (U : S × B → S × B)
  (h_inj : Function.Injective U)
  (X_final : Finset S) (B_final : Finset B)
  (h_evolve : Finset.image U (X ×ˢ Y) ⊆ X_final ×ˢ B_final)
  (hX : X.Nonempty) (hY : Y.Nonempty) :
  boltzmann_entropy B_final - boltzmann_entropy Y ≥ boltzmann_entropy X - boltzmann_entropy X_final := by
  have card_prod : (X ×ˢ Y).card = X.card * Y.card := Finset.card_product X Y
  have card_prod_final : (X_final ×ˢ B_final).card = X_final.card * B_final.card := Finset.card_product X_final B_final
  have card_image : (Finset.image U (X ×ˢ Y)).card = (X ×ˢ Y).card := Finset.card_image_of_injective (X ×ˢ Y) h_inj
  have card_le : (Finset.image U (X ×ˢ Y)).card ≤ (X_final ×ˢ B_final).card := Finset.card_le_card h_evolve
  rw [card_image, card_prod, card_prod_final] at card_le
  have hX_pos : X.card > 0 := Finset.card_pos.mpr hX
  have hY_pos : Y.card > 0 := Finset.card_pos.mpr hY
  have h_prod_pos : X.card * Y.card > 0 := mul_pos hX_pos hY_pos
  have h_final_pos : X_final.card * B_final.card > 0 := lt_of_lt_of_le h_prod_pos card_le
  have hXf_pos : X_final.card > 0 := Nat.pos_of_mul_pos_right h_final_pos
  have hBf_pos : B_final.card > 0 := Nat.pos_of_mul_pos_left h_final_pos
  
  have real_le : (X.card : ℝ) * (Y.card : ℝ) ≤ (X_final.card : ℝ) * (B_final.card : ℝ) := by
    exact_mod_cast card_le
    
  have h_log_le : Real.log ((X.card : ℝ) * (Y.card : ℝ)) ≤ Real.log ((X_final.card : ℝ) * (B_final.card : ℝ)) := by
    apply Real.log_le_log
    · exact mul_pos (Nat.cast_pos.mpr hX_pos) (Nat.cast_pos.mpr hY_pos)
    · exact real_le
    
  rw [Real.log_mul (ne_of_gt (Nat.cast_pos.mpr hX_pos)) (ne_of_gt (Nat.cast_pos.mpr hY_pos))] at h_log_le
  rw [Real.log_mul (ne_of_gt (Nat.cast_pos.mpr hXf_pos)) (ne_of_gt (Nat.cast_pos.mpr hBf_pos))] at h_log_le
  
  unfold boltzmann_entropy
  linarith

class BipartiteEnvironment (sys : Type*) [Fintype sys] [DecidableEq sys] where
  bath : Type*
  dec_bath : DecidableEq bath
  U : (sys → sys) → sys × bath → sys × bath
  U_inj : ∀ t, Function.Injective (U t)
  initial_bath : (sys → sys) → Finset bath
  final_bath : (sys → sys) → Finset bath
  h_evolve : ∀ t, Finset.image (U t) (Finset.univ ×ˢ initial_bath t) ⊆ (Finset.image t Finset.univ) ×ˢ final_bath t
  h_bath_nonempty : ∀ t, (initial_bath t).Nonempty

instance instDecidableEqBath {sys : Type*} [Fintype sys] [DecidableEq sys] [BipartiteEnvironment sys] : 
  DecidableEq (BipartiteEnvironment.bath sys) := BipartiteEnvironment.dec_bath

class Thermodynamics (sys : Type*) where
  heat_dissipation : (sys → sys) → ℝ
  temperature : ℝ
  temperature_pos : temperature > 0

/--
Bundles the thermodynamic and bipartite-environment structure of a finite system.

The field `heat_eq` is **Landauer's heat equation** — heat dissipated equals
temperature times the change in Boltzmann entropy of the bath. It is an
irreducible physical postulate.

**Why it is a class field and not an `axiom`.** An earlier version declared

    axiom landauer_heat_eq (t : sys → sys) :
      Thermodynamics.heat_dissipation t
        = Thermodynamics.temperature * (boltzmann_entropy (final_bath t)
                                        - boltzmann_entropy (initial_bath t))

Because `heat_dissipation`, `temperature`, `initial_bath` and `final_bath` are
all *free fields* of their classes, that axiom pinned them for **every**
instance, including instances that contradict it. Taking `sys := Unit` with
`heat_dissipation := fun _ => 0`, `temperature := 1`, `initial_bath := {false}`
and `final_bath := Finset.univ : Finset Bool` yields `0 = log 2`, hence `False`.

As a class field the postulate becomes an obligation each instance must
discharge, which is what a physical assumption should be. See `Examples.lean`
for an instance witnessing that the class is inhabited.
-/
class StatisticalMechanics (sys : Type*) [Fintype sys] [DecidableEq sys]
    extends Thermodynamics sys, BipartiteEnvironment sys where
  heat_eq : ∀ t : sys → sys,
    Thermodynamics.heat_dissipation t =
      Thermodynamics.temperature (sys := sys) *
        (boltzmann_entropy (BipartiteEnvironment.final_bath t) -
         boltzmann_entropy (BipartiteEnvironment.initial_bath t))

theorem second_law {sys : Type*} [Fintype sys] [DecidableEq sys] [StatisticalMechanics sys] [Nonempty sys] (t : sys → sys) :
  (boltzmann_entropy (BipartiteEnvironment.final_bath t) - boltzmann_entropy (BipartiteEnvironment.initial_bath t)) + 
  (entropy t - entropy (id : sys → sys)) ≥ 0 := by
  have hX : (Finset.univ : Finset sys).Nonempty := Finset.univ_nonempty
  have hY : (BipartiteEnvironment.initial_bath t).Nonempty := BipartiteEnvironment.h_bath_nonempty t
  have bound := landauer_from_reversibility 
    (Finset.univ : Finset sys) (BipartiteEnvironment.initial_bath t) (BipartiteEnvironment.U t) (BipartiteEnvironment.U_inj t)
    (Finset.image t Finset.univ) (BipartiteEnvironment.final_bath t) (BipartiteEnvironment.h_evolve t) hX hY
  have h_id_card : (Finset.image id (Finset.univ : Finset sys)).card = (Finset.univ : Finset sys).card := by
    rw [Finset.image_id]
  have eq_id : entropy (id : sys → sys) = boltzmann_entropy (Finset.univ : Finset sys) := by
    unfold entropy boltzmann_entropy
    rw [h_id_card]
  have eq_t : entropy t = boltzmann_entropy (Finset.image t Finset.univ) := rfl
  rw [eq_id, eq_t]
  linarith

theorem landauer_bound {sys : Type*} [Fintype sys] [DecidableEq sys] [StatisticalMechanics sys] [Nonempty sys] :
  ∀ (t : sys → sys), Thermodynamics.heat_dissipation (sys := sys) t ≥ Thermodynamics.temperature (sys := sys) * (entropy (id : sys → sys) - entropy t) := by
  intro t
  rw [StatisticalMechanics.heat_eq t]
  have h2 : Thermodynamics.temperature (sys := sys) > 0 := Thermodynamics.temperature_pos
  have h_sec := second_law (sys := sys) t
  nlinarith

def heat_dissipation {sys : Type*} [Thermodynamics sys] (t : sys → sys) : ℝ :=
  Thermodynamics.heat_dissipation t

lemma not_injective_image_card_lt {sys : Type*} [Fintype sys] [DecidableEq sys] (t : sys → sys) (h : ¬ Function.Injective t) : 
  (Finset.image t Finset.univ).card < Fintype.card sys := by
  have h1 : (Finset.image t Finset.univ).card ≤ Fintype.card sys := Finset.card_image_le
  by_contra hc
  have heq : (Finset.image t Finset.univ).card = Fintype.card sys := le_antisymm h1 (not_lt.mp hc)
  have hsurj : Function.Surjective t := by
    have himage_eq_univ : Finset.image t Finset.univ = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le
      · intro x _ ; exact Finset.mem_univ x
      · rw [heq] ; rfl
    intro y
    have hy : y ∈ Finset.univ := Finset.mem_univ y
    rw [← himage_eq_univ] at hy
    rcases Finset.mem_image.mp hy with ⟨x, _, hx_eq⟩
    exact ⟨x, hx_eq⟩
  have hinj : Function.Injective t := Finite.injective_iff_surjective.mpr hsurj
  exact h hinj

theorem erasure_decreases_entropy {sys : Type*} [Fintype sys] [DecidableEq sys] [Nonempty sys] (t : sys → sys) (h : is_erasure t) :
  entropy (id : sys → sys) > entropy t := by
  unfold entropy boltzmann_entropy
  have h_id_card : (Finset.image id (Finset.univ : Finset sys)).card = Fintype.card sys := by
    have himage : Finset.image id (Finset.univ : Finset sys) = Finset.univ := Finset.image_id
    rw [himage]
    rfl
  rw [h_id_card]
  have h_lt : (Finset.image t Finset.univ).card < Fintype.card sys := not_injective_image_card_lt t h
  have h_pos1 : (0 : ℝ) < ((Finset.image t Finset.univ).card : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    have ⟨x⟩ := ‹Nonempty sys›
    exact ⟨t x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  have h_pos2 : (0 : ℝ) < (Fintype.card sys : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Fintype.card_pos
  exact Real.strictMonoOn_log h_pos1 h_pos2 (Nat.cast_lt.mpr h_lt)

theorem entropy_decrease_implies_heat {sys : Type*} [Fintype sys] [DecidableEq sys] [StatisticalMechanics sys] [Nonempty sys] (t : sys → sys) 
  (h : entropy (id : sys → sys) > entropy t) : heat_dissipation t > 0 := by
  have bound := landauer_bound (sys := sys) t
  have diff_pos : entropy (id : sys → sys) - entropy t > 0 := sub_pos.mpr h
  have rhs_pos : Thermodynamics.temperature (sys := sys) * (entropy (id : sys → sys) - entropy t) > 0 :=
    mul_pos (Thermodynamics.temperature_pos) diff_pos
  exact lt_of_lt_of_le rhs_pos bound

theorem landauers_principle {sys : Type*} [Fintype sys] [DecidableEq sys] [Nonempty sys] [StatisticalMechanics sys] (t : sys → sys) :
  is_erasure t → heat_dissipation t > 0 := by
  intro h_erasure
  have h_entropy := erasure_decreases_entropy t h_erasure
  exact entropy_decrease_implies_heat t h_entropy

def is_dissipative_structure {sys : Type*} [Thermodynamics sys] (t : sys → sys) : Prop :=
  heat_dissipation t > 0

theorem boundary_is_dissipative {sys : Type*} [Fintype sys] [DecidableEq sys] [Nonempty sys] [StatisticalMechanics sys] (t : sys → sys) (h : is_erasure t) :
  is_dissipative_structure t := by
  exact landauers_principle t h

end PhysicsOfConsciousness
