import Mathlib
import PhysicsOfConsciousness.Phase4_KuramotoDynamics

/-!
# The rotating-frame reduction

This file closes the gap flagged on `kuramoto_potential` in
`Phase3_CombinatorialThermodynamics.lean`: the development carries *two*
Kuramoto potentials, and until now nothing connected them.

* `kuramoto_potential` — with the natural-frequency term `- ∑ ωᵢ θᵢ`. This is
  the function `dV_dt_le_zero` proves Lyapunov descent for.
* `kuramoto_potential_dynamic` — without it. This is the function whose minimum
  `phase_locked_minimizes_potential` and `potential_min_implies_phase_locked`
  characterise, and the one Phase 5's `ThermodynamicCover` assumes minimised.

The two are genuinely different functionals, and the difference is not cosmetic:
`kuramoto_potential_unbounded_below` proves that as soon as one `ωᵢ ≠ 0` the
first has *no* minimum at all, so "the phase-locked state minimises the Lyapunov
potential" is simply false of it. The physics literature closes this by passing
to the frame rotating with the natural frequency; this file formalizes that step
for the case the reduction actually holds in — identical natural frequencies.

The chain established here is:

  trajectory of `sys` (ω ≡ Ω)
    → `rotate Ω θ` is a trajectory of `sys.reduced` (ω ≡ 0)   [`is_kuramoto_trajectory_rotate`]
    → its `kuramoto_potential` *is* `kuramoto_potential_dynamic`  [`kuramoto_potential_reduced`]
    → so `dV_dt_le_zero` gives descent of the dynamic potential  [`dynamic_potential_descent`]
    → whose minimisers are exactly the phase-locked states       [Phase 4]
    → and phase-locking, the order parameter, and the potential are
      all frame-independent                                      [`is_phase_locked_rotate`, …]

## Scope

The reduction is exact only for identical natural frequencies. For a spread of
frequencies the change of variables `θᵢ ↦ θᵢ - Ω t` leaves residual detunings
`ωᵢ - Ω` in the reduced system, `kuramoto_potential_unbounded_below` still
applies to it, and phase-locking exists only above a critical coupling `K_c`.
`K_c` appears nowhere in *this* file. `Phase8_SelfConsistency.lean` proves one
direction of it — below `K_c = 2D` the incoherent state is the unique
non-negative solution of the mean-field self-consistency equation — from an
assumed stationary density, and the supercritical branch remains numerical
(`simulations/kuramoto.py`). Nothing here should be read as formalizing the
synchronization transition; what is formalized is the reduction that makes the
*zero-frequency* system used by Phase 5 the honest reduced description of a
uniform-frequency one.
-/

open Finset Complex

namespace PhysicsOfConsciousness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The two potentials differ exactly by the frequency term -/

omit [DecidableEq V] in
/-- `kuramoto_potential` is `kuramoto_potential_dynamic` minus the frequency
term. The cosine halves agree because `cos` is even and the two definitions
write the phase difference in opposite orders. -/
theorem kuramoto_potential_eq_dynamic_sub (sys : KuramotoSystem V) (theta : V → ℝ) :
    kuramoto_potential sys theta
      = kuramoto_potential_dynamic sys theta - ∑ i, sys.omega i * theta i := by
  unfold kuramoto_potential kuramoto_potential_dynamic
  congr 2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show theta i - theta j = -(theta j - theta i) by ring, Real.cos_neg]

/-- The system with the same coupling and all natural frequencies set to zero —
the form Phase 5's `ThermodynamicCover` already works with. -/
def KuramotoSystem.reduced (sys : KuramotoSystem V) : KuramotoSystem V :=
  ⟨fun _ => 0, sys.A, sys.symm⟩

omit [Fintype V] [DecidableEq V] in
@[simp] lemma KuramotoSystem.reduced_omega (sys : KuramotoSystem V) (i : V) :
    sys.reduced.omega i = 0 := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] lemma KuramotoSystem.reduced_A (sys : KuramotoSystem V) (i j : V) :
    sys.reduced.A i j = sys.A i j := rfl

omit [DecidableEq V] in
/-- **The two potentials coincide on the reduced system.** This is the identity
that lets `dV_dt_le_zero` speak about the functional Phase 4 and Phase 5 use. -/
@[simp] theorem kuramoto_potential_reduced (sys : KuramotoSystem V) (theta : V → ℝ) :
    kuramoto_potential sys.reduced theta = kuramoto_potential_dynamic sys theta := by
  rw [kuramoto_potential_eq_dynamic_sub]
  simp [kuramoto_potential_dynamic]

/-! ## 2. Why the frequency term has to go: no minimum exists

The claim in the doc-string of `kuramoto_potential` — that the potential is
unbounded below whenever some `ωᵢ ≠ 0` — is proved here rather than asserted.
Walking `θ` out along `ω` drives `- ∑ ωᵢ θᵢ` to `-∞` while the cosine sum stays
inside `± ½ ∑ᵢⱼ |Aᵢⱼ|`. -/

omit [DecidableEq V] in
private lemma cos_sum_le_abs_sum (sys : KuramotoSystem V) (theta : V → ℝ) :
    -(1/2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta i - theta j)
      ≤ (1/2) * ∑ i, ∑ j, |sys.A i j| := by
  have hterm : ∀ i ∈ (univ : Finset V), ∀ j ∈ (univ : Finset V),
      -|sys.A i j| ≤ sys.A i j * Real.cos (theta i - theta j) := by
    intro i _ j _
    refine neg_le_of_abs_le ?_
    rw [abs_mul]
    calc |sys.A i j| * |Real.cos (theta i - theta j)|
        ≤ |sys.A i j| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |sys.A i j| := mul_one _
  have hsum : -∑ i, ∑ j, |sys.A i j|
      ≤ ∑ i, ∑ j, sys.A i j * Real.cos (theta i - theta j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j hj => hterm i hi j hj
  linarith

omit [DecidableEq V] in
/-- **The full Kuramoto potential has no minimum when the frequencies are not
all zero.** For every bound `C` there is a phase configuration below it. -/
theorem kuramoto_potential_unbounded_below (sys : KuramotoSystem V)
    (h_omega : ∃ i, sys.omega i ≠ 0) (C : ℝ) :
    ∃ theta : V → ℝ, kuramoto_potential sys theta < C := by
  obtain ⟨i0, hi0⟩ := h_omega
  set B : ℝ := (1/2) * ∑ i, ∑ j, |sys.A i j| with hB
  set S : ℝ := ∑ i, sys.omega i ^ 2 with hS
  have hS_pos : 0 < S := by
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i0, mem_univ i0, ?_⟩
    exact pow_pos (abs_pos.mpr hi0) 2 |>.trans_le (le_of_eq (sq_abs _))
  set c : ℝ := (B - C + 1) / S with hc
  refine ⟨fun i => c * sys.omega i, ?_⟩
  have hlin : ∑ i, sys.omega i * (c * sys.omega i) = c * S := by
    rw [hS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcS : c * S = B - C + 1 := by
    rw [hc, div_mul_cancel₀ _ (ne_of_gt hS_pos)]
  rw [kuramoto_potential, hlin, hcS]
  have := cos_sum_le_abs_sum sys (fun i => c * sys.omega i)
  rw [← hB] at this
  linarith

/-! ## 3. The rotating frame -/

/-- The change of variables `θᵢ(t) ↦ θᵢ(t) - Ω t`. -/
def rotate (Ω : ℝ) (theta : ℝ → V → ℝ) : ℝ → V → ℝ :=
  fun t i => theta t i - Ω * t

omit [Fintype V] [DecidableEq V] in
@[simp] lemma rotate_sub (Ω : ℝ) (theta : ℝ → V → ℝ) (t : ℝ) (i j : V) :
    rotate Ω theta t i - rotate Ω theta t j = theta t i - theta t j := by
  simp [rotate]

omit [DecidableEq V] in
/-- **The reduction.** In the frame rotating at the common natural frequency,
a trajectory of a uniform-frequency Kuramoto system is a trajectory of the
zero-frequency system with the same coupling. -/
theorem is_kuramoto_trajectory_rotate (sys : KuramotoSystem V) (Ω : ℝ)
    (h_omega : ∀ i, sys.omega i = Ω)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) :
    is_kuramoto_trajectory sys.reduced (rotate Ω theta) := by
  intro i t
  have hlin : HasDerivAt (fun t : ℝ => Ω * t) Ω t := by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hd := (h_traj i t).sub hlin
  have hsum : ∑ j, sys.A i j * Real.sin (theta t j - theta t i)
      = ∑ j, sys.reduced.A i j
          * Real.sin (rotate Ω theta t j - rotate Ω theta t i) :=
    Finset.sum_congr rfl fun j _ => by rw [rotate_sub, KuramotoSystem.reduced_A]
  have hval : sys.omega i + ∑ j, sys.A i j * Real.sin (theta t j - theta t i) - Ω
      = sys.reduced.omega i
        + ∑ j, sys.reduced.A i j
            * Real.sin (rotate Ω theta t j - rotate Ω theta t i) := by
    rw [h_omega i, hsum, KuramotoSystem.reduced_omega]
    ring
  rw [hval] at hd
  exact hd

/-! ## 4. What the frame change does not move -/

omit [Fintype V] [DecidableEq V] in
@[simp] lemma is_phase_locked_rotate (Ω : ℝ) (theta : ℝ → V → ℝ) (t : ℝ) :
    is_phase_locked (rotate Ω theta t) ↔ is_phase_locked (theta t) := by
  unfold is_phase_locked
  constructor <;> intro h i j
  · rw [← rotate_sub Ω theta t i j]; exact h i j
  · rw [rotate_sub]; exact h i j

omit [DecidableEq V] in
lemma order_parameter_complex_shift (theta : V → ℝ) (c : ℝ) :
    order_parameter_complex (fun i => theta i - c)
      = Complex.exp (-(I * (c : ℂ))) * order_parameter_complex theta := by
  unfold order_parameter_complex
  have h : ∀ j : V, Complex.exp (I * ((theta j - c : ℝ) : ℂ))
      = Complex.exp (-(I * (c : ℂ))) * Complex.exp (I * (theta j : ℂ)) := by
    intro j
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [h, ← Finset.mul_sum]
  ring

omit [DecidableEq V] in
/-- The magnitude of the macroscopic order parameter is frame-independent: the
observable Phase 4 uses does not see the rotation. -/
theorem order_parameter_r_sq_shift (theta : V → ℝ) (c : ℝ) :
    order_parameter_r_sq (fun i => theta i - c) = order_parameter_r_sq theta := by
  unfold order_parameter_r_sq
  rw [order_parameter_complex_shift, Complex.normSq_mul]
  have h1 : Complex.normSq (Complex.exp (-(I * (c : ℂ)))) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have : (-(I * (c : ℂ))) = ((-c : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [h1, one_mul]

omit [DecidableEq V] in
@[simp] theorem order_parameter_r_sq_rotate (Ω : ℝ) (theta : ℝ → V → ℝ) (t : ℝ) :
    order_parameter_r_sq (rotate Ω theta t) = order_parameter_r_sq (theta t) :=
  order_parameter_r_sq_shift (theta t) (Ω * t)

/-! ## 5. The chain -/

omit [DecidableEq V] in
/-- **Descent of the dynamic potential along a trajectory.** `dV_dt_le_zero`
proves Lyapunov descent for `kuramoto_potential`; transported through the
rotating frame it becomes descent for `kuramoto_potential_dynamic`, the
functional Phase 4 and Phase 5 actually use. -/
theorem dynamic_potential_descent (sys : KuramotoSystem V) (Ω : ℝ)
    (h_omega : ∀ i, sys.omega i = Ω)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) (t : ℝ) :
    deriv (fun t => kuramoto_potential_dynamic sys (rotate Ω theta t)) t
      = - ∑ i, (kuramoto_velocity sys.reduced (rotate Ω theta t) i) ^ 2 := by
  have h_red := is_kuramoto_trajectory_rotate sys Ω h_omega theta h_traj
  have h_diff : ∀ i, DifferentiableAt ℝ (fun t => rotate Ω theta t i) t :=
    fun i => (h_red i t).differentiableAt
  have h_dyn : ∀ i, deriv (fun t => rotate Ω theta t i) t
      = kuramoto_velocity sys.reduced (rotate Ω theta t) i :=
    fun i => (h_red i t).deriv
  have hfun : (fun t => kuramoto_potential_dynamic sys (rotate Ω theta t))
      = fun t => kuramoto_potential sys.reduced (rotate Ω theta t) := by
    funext t; rw [kuramoto_potential_reduced]
  rw [hfun]
  exact dV_dt_le_zero sys.reduced (rotate Ω theta) t h_diff h_dyn

omit [DecidableEq V] in
/-- The dynamic potential is non-increasing along trajectories of a
uniform-frequency system, read in the rotating frame. -/
theorem dynamic_potential_deriv_nonpos (sys : KuramotoSystem V) (Ω : ℝ)
    (h_omega : ∀ i, sys.omega i = Ω)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) (t : ℝ) :
    deriv (fun t => kuramoto_potential_dynamic sys (rotate Ω theta t)) t ≤ 0 := by
  rw [dynamic_potential_descent sys Ω h_omega theta h_traj t]
  simp only [neg_nonpos]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

omit [DecidableEq V] in
/-- **The chain, end to end.** For a uniform-frequency Kuramoto system with
positive couplings: passing to the rotating frame produces a trajectory of the
zero-frequency system Phase 5 works with; along it the dynamic potential
descends; if the rotated configuration at time `t` attains the global minimum of
that potential then it is phase-locked, and so is the original trajectory, and
the order parameter of both is `1`. -/
theorem rotating_frame_chain [Nonempty V] (sys : KuramotoSystem V) (Ω : ℝ)
    (h_omega : ∀ i, sys.omega i = Ω) (h_pos : ∀ i j, sys.A i j > 0)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) (t : ℝ)
    (h_min : ∀ phi, kuramoto_potential_dynamic sys (rotate Ω theta t)
                      ≤ kuramoto_potential_dynamic sys phi) :
    is_kuramoto_trajectory sys.reduced (rotate Ω theta)
      ∧ deriv (fun t => kuramoto_potential_dynamic sys (rotate Ω theta t)) t ≤ 0
      ∧ is_phase_locked (theta t)
      ∧ order_parameter_r_sq (theta t) = 1 := by
  refine ⟨is_kuramoto_trajectory_rotate sys Ω h_omega theta h_traj,
          dynamic_potential_deriv_nonpos sys Ω h_omega theta h_traj t, ?_, ?_⟩
  · have h_locked : is_phase_locked (rotate Ω theta t) :=
      potential_min_implies_phase_locked sys h_pos (rotate Ω theta t) h_min
    exact (is_phase_locked_rotate Ω theta t).mp h_locked
  · refine phase_locked_implies_r_sq_eq_one (theta t) ?_
    have h_locked : is_phase_locked (rotate Ω theta t) :=
      potential_min_implies_phase_locked sys h_pos (rotate Ω theta t) h_min
    exact (is_phase_locked_rotate Ω theta t).mp h_locked

end PhysicsOfConsciousness
