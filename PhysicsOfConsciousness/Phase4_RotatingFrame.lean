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

/-! ## 5. Dissipation: the potential converges, and only finitely much is dissipated

`dynamic_potential_deriv_nonpos` says the potential does not increase at any one
instant. That is a statement about each `t` separately, and on its own it does
not say the trajectory settles: a function can decrease forever without
converging. The results here close that gap for the two claims that do not need
a LaSalle principle.

Both are stated for a system whose natural frequencies vanish, which by §1 is
exactly the case in which `kuramoto_potential` and `kuramoto_potential_dynamic`
agree — and, by `kuramoto_potential_unbounded_below`, the only case in which
either is bounded below. `rotating_frame_dissipation` transports them to a
uniform-frequency system through the reduction of §3.
-/

open Filter Topology MeasureTheory

section Dissipation

variable (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta)

omit [DecidableEq V] in
include hw in
/-- With zero natural frequencies the two potentials are the same function. -/
lemma kuramoto_potential_eq_dynamic_of_zero_freq (phi : V → ℝ) :
    kuramoto_potential sys phi = kuramoto_potential_dynamic sys phi := by
  rw [kuramoto_potential_eq_dynamic_sub]
  simp [hw]

omit [DecidableEq V] in
include h_traj in
lemma dynamic_potential_differentiableAt (t : ℝ) :
    DifferentiableAt ℝ (fun t => kuramoto_potential_dynamic sys (theta t)) t := by
  have h_diff : ∀ i, DifferentiableAt ℝ (fun t => theta t i) t :=
    fun i => (h_traj i t).differentiableAt
  have hsum : DifferentiableAt ℝ
      (fun t => ∑ i, ∑ j, sys.A i j * Real.cos (theta t j - theta t i)) t := by
    have H : (fun (t : ℝ) => ∑ i, ∑ j, sys.A i j * Real.cos (theta t j - theta t i))
        = ∑ i, (fun (t : ℝ) => ∑ j, sys.A i j * Real.cos (theta t j - theta t i)) := by
      ext; simp
    rw [H]
    refine DifferentiableAt.sum fun i _ => ?_
    have H2 : (fun (t : ℝ) => ∑ j, sys.A i j * Real.cos (theta t j - theta t i))
        = ∑ j, (fun (t : ℝ) => sys.A i j * Real.cos (theta t j - theta t i)) := by
      ext; simp
    rw [H2]
    exact DifferentiableAt.sum fun j _ => ((h_diff j).sub (h_diff i)).cos.const_mul _
  unfold kuramoto_potential_dynamic
  exact hsum.const_mul _

omit [DecidableEq V] in
include hw h_traj in
/-- **The Lyapunov identity, in `HasDerivAt` form.** `dV_dt_le_zero` computes
`deriv`, which carries no differentiability information and so cannot be fed to
the fundamental theorem of calculus; this restates it as a `HasDerivAt`, which
can. The differentiability it needs is `dynamic_potential_differentiableAt`, and
the value of the derivative is `dV_dt_le_zero` transported across
`kuramoto_potential_eq_dynamic_of_zero_freq`. -/
theorem dynamic_potential_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t => kuramoto_potential_dynamic sys (theta t))
      (- ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2) t := by
  have hdiff := dynamic_potential_differentiableAt sys theta h_traj t
  have hkey : deriv (fun t => kuramoto_potential_dynamic sys (theta t)) t
      = - ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2 := by
    have hfun : (fun t => kuramoto_potential_dynamic sys (theta t))
        = fun t => kuramoto_potential sys (theta t) := by
      funext s; rw [kuramoto_potential_eq_dynamic_of_zero_freq sys hw]
    rw [hfun]
    exact dV_dt_le_zero sys theta t (fun i => (h_traj i t).differentiableAt)
      (fun i => (h_traj i t).deriv)
  exact hkey ▸ hdiff.hasDerivAt

omit [DecidableEq V] in
/-- **The dynamic potential is bounded below**, by `-½ ∑ᵢⱼ |Aᵢⱼ|`, uniformly
over configurations. This is the half of the Lyapunov argument that the full
`kuramoto_potential` does not have: by `kuramoto_potential_unbounded_below` no
such bound exists once a natural frequency is non-zero, which is why the
convergence result below is stated for the reduced system. -/
lemma dynamic_potential_bounded_below (phi : V → ℝ) :
    -(1/2) * ∑ i, ∑ j, |sys.A i j| ≤ kuramoto_potential_dynamic sys phi := by
  unfold kuramoto_potential_dynamic
  have hle : ∑ i, ∑ j, sys.A i j * Real.cos (phi j - phi i) ≤ ∑ i, ∑ j, |sys.A i j| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    calc sys.A i j * Real.cos (phi j - phi i)
        ≤ |sys.A i j * Real.cos (phi j - phi i)| := le_abs_self _
      _ = |sys.A i j| * |Real.cos (phi j - phi i)| := abs_mul _ _
      _ ≤ |sys.A i j| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |sys.A i j| := mul_one _
  linarith

omit [DecidableEq V] in
include hw h_traj in
/-- **The dynamic potential is non-increasing along a trajectory**, as a function
of time rather than instant by instant. This is the global statement
`dynamic_potential_deriv_nonpos` does not make. -/
theorem dynamic_potential_antitone :
    Antitone (fun t => kuramoto_potential_dynamic sys (theta t)) := by
  apply antitone_of_deriv_nonpos
  · exact fun t => (dynamic_potential_hasDerivAt sys hw theta h_traj t).differentiableAt
  · intro t
    rw [(dynamic_potential_hasDerivAt sys hw theta h_traj t).deriv]
    simp only [neg_nonpos]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _

omit [DecidableEq V] in
include hw h_traj in
/-- **O20(b): the potential converges along *every* trajectory**, and its limit
is a lower bound for it. Monotone convergence: antitone by
`dynamic_potential_antitone`, bounded below by `dynamic_potential_bounded_below`.

`Examples.lean` §15 computes this limit for one trajectory by evaluating it; this
theorem needs no formula for the limit and holds for every system and every
initial condition.

**What it does not establish.** That the limit is the *global minimum* of the
potential, which is what `thermodynamic_equilibrium` assumes and what
`potential_min_iff_phase_locked` would then convert into phase-locking. A
trajectory sitting at a splay or twisted equilibrium converges too, to a value
that is not the minimum. -/
theorem dynamic_potential_tendsto :
    ∃ L : ℝ, Tendsto (fun t => kuramoto_potential_dynamic sys (theta t)) atTop (𝓝 L)
      ∧ ∀ t, L ≤ kuramoto_potential_dynamic sys (theta t) := by
  have hanti := dynamic_potential_antitone sys hw theta h_traj
  have hbdd : BddBelow (Set.range fun t => kuramoto_potential_dynamic sys (theta t)) :=
    ⟨-(1/2) * ∑ i, ∑ j, |sys.A i j|, by
      rintro x ⟨t, rfl⟩; exact dynamic_potential_bounded_below sys (theta t)⟩
  exact ⟨_, tendsto_atTop_ciInf hanti hbdd, fun t => ciInf_le hbdd t⟩

omit [DecidableEq V] in
include h_traj in
/-- The instantaneous dissipation rate `∑ᵢ θ̇ᵢ²` is continuous in time — needed
to integrate it. -/
lemma velocity_sq_continuous :
    Continuous (fun t => ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2) := by
  have hth : ∀ i, Continuous (fun t => theta t i) := fun i =>
    Differentiable.continuous (fun t => (h_traj i t).differentiableAt)
  have hsin : ∀ i j, Continuous (fun t => Real.sin (theta t j - theta t i)) := fun i j =>
    Real.continuous_sin.comp ((hth j).sub (hth i))
  refine continuous_finsetSum _ fun i _ => Continuous.pow ?_ 2
  simp only [kuramoto_velocity]
  exact continuous_const.add
    (continuous_finsetSum _ fun j _ => continuous_const.mul (hsin i j))

omit [DecidableEq V] in
include hw h_traj in
/-- **Energy dissipated equals potential dropped.** The integrated form of the
Lyapunov identity, by the fundamental theorem of calculus. -/
theorem dissipation_integral_eq (T : ℝ) :
    ∫ t in (0:ℝ)..T, ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2
      = kuramoto_potential_dynamic sys (theta 0)
        - kuramoto_potential_dynamic sys (theta T) := by
  have hcont := velocity_sq_continuous sys theta h_traj
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => kuramoto_potential_dynamic sys (theta t))
    (f' := fun t => - ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2)
    (fun x _ => dynamic_potential_hasDerivAt sys hw theta h_traj x)
    (hcont.neg.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg] at h
  linarith

omit [DecidableEq V] in
include hw h_traj in
/-- **O20(c): a trajectory dissipates only finitely much.** The improper integral
`∫₀^∞ ∑ᵢ θ̇ᵢ² dt` converges, to the total drop `V(0) - L` of the potential, and
every partial integral is bounded by that same number.

This is the quantitative form of "the motion stops": the total squared speed
accumulated over all of time is finite, so the trajectory cannot keep moving at
a rate bounded away from zero.

**What it does not establish, and what would.** Finiteness of the integral does
*not* by itself give `∑ᵢ θ̇ᵢ² → 0` — an integrable function can spike forever, on
ever narrower intervals. The classical bridge is Barbalat's lemma: an integrable
uniformly continuous function tends to zero. The dissipation rate here *is*
uniformly continuous (it is bounded, and so is its derivative, since
`kuramotoField_norm_le` bounds the velocities and the coupling bounds the
accelerations), so Barbalat would give `θ̇ → 0` — but Mathlib does not have
Barbalat's lemma, and this development does not prove it. Note that this is a
strictly weaker requirement than the LaSalle principle that O20(d) needs:
velocity tending to zero does not locate the limit, and locating it needs a
compact invariant set the state space `V → ℝ` does not supply. -/
theorem dissipation_integral_tendsto :
    ∃ L : ℝ, Tendsto (fun t => kuramoto_potential_dynamic sys (theta t)) atTop (𝓝 L)
      ∧ Tendsto (fun T => ∫ t in (0:ℝ)..T, ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2)
          atTop (𝓝 (kuramoto_potential_dynamic sys (theta 0) - L))
      ∧ ∀ T, ∫ t in (0:ℝ)..T, ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2
              ≤ kuramoto_potential_dynamic sys (theta 0) - L := by
  obtain ⟨L, hL, hLle⟩ := dynamic_potential_tendsto sys hw theta h_traj
  refine ⟨L, hL, ?_, fun T => ?_⟩
  · have hsub : Tendsto (fun T => kuramoto_potential_dynamic sys (theta 0)
        - kuramoto_potential_dynamic sys (theta T)) atTop
        (𝓝 (kuramoto_potential_dynamic sys (theta 0) - L)) := tendsto_const_nhds.sub hL
    exact hsub.congr fun T => (dissipation_integral_eq sys hw theta h_traj T).symm
  · rw [dissipation_integral_eq sys hw theta h_traj T]
    linarith [hLle T]

end Dissipation

omit [DecidableEq V] in
/-- **The dissipation results in the rotating frame.** For a system of identical
natural frequencies, read in the frame rotating with them, the dynamic potential
converges and the total dissipation is finite.

The hypothesis `∀ i, sys.omega i = Ω` is the same one §3 needs, and for the same
reason: with a genuine spread of frequencies no change of frame makes the
potential bounded below, so nothing here applies. -/
theorem rotating_frame_dissipation (sys : KuramotoSystem V) (Ω : ℝ)
    (h_omega : ∀ i, sys.omega i = Ω)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) :
    ∃ L : ℝ,
      Tendsto (fun t => kuramoto_potential_dynamic sys (rotate Ω theta t)) atTop (𝓝 L)
      ∧ Tendsto (fun T => ∫ t in (0:ℝ)..T,
            ∑ i, (kuramoto_velocity sys.reduced (rotate Ω theta t) i) ^ 2)
          atTop (𝓝 (kuramoto_potential_dynamic sys (rotate Ω theta 0) - L))
      ∧ ∀ T, ∫ t in (0:ℝ)..T,
            ∑ i, (kuramoto_velocity sys.reduced (rotate Ω theta t) i) ^ 2
              ≤ kuramoto_potential_dynamic sys (rotate Ω theta 0) - L :=
  dissipation_integral_tendsto sys.reduced (fun _ => rfl) (rotate Ω theta)
    (is_kuramoto_trajectory_rotate sys Ω h_omega theta h_traj)

end PhysicsOfConsciousness
