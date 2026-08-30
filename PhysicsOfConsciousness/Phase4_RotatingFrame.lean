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

§5 and §6 then run a dynamics into that potential — it converges, the dissipation
is finite, and the motion stops — and §7 locates the limit: for initial data
within a quarter turn and below an energy threshold, the trajectory converges to
a global minimiser, so `ThermodynamicCover`'s standing hypothesis is discharged
rather than assumed.

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
that is not the minimum — so no hypothesis-free strengthening of this theorem is
possible. §7 supplies the hypotheses under which the limit *is* the minimum. -/
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

**What it does not establish on its own.** Finiteness of the integral does *not*
by itself give `∑ᵢ θ̇ᵢ² → 0` — an integrable function can spike forever, on ever
narrower intervals. The classical bridge is Barbalat's lemma, which Mathlib does
not have; §6 proves it (`tendsto_zero_of_lipschitz_of_integral_le`), checks its
Lipschitz hypothesis for the dissipation rate, and concludes `θ̇ → 0`
(`velocity_sq_tendsto_zero`). Velocity tending to zero still does not locate the
limit; §7 does that, for initial data near consensus, by a Łojasiewicz estimate
rather than by the LaSalle principle Mathlib lacks. -/
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

/-! ## 6. Barbalat's lemma: the motion stops

§5 leaves a specific gap. `dissipation_integral_tendsto` says `∫₀^∞ ∑ᵢ θ̇ᵢ² dt`
is finite, and finiteness of an integral does **not** imply that the integrand
tends to zero — an integrable function can spike to height `1` forever, on
intervals of width `2⁻ⁿ`. The classical repair is Barbalat's lemma: an
integrable function that is *uniformly* continuous cannot do that, because a
spike of height `ε` drags a whole window of fixed width `δ` up with it, and only
finitely many such windows fit under a finite integral.

Mathlib does not have Barbalat's lemma, so `tendsto_zero_of_lipschitz_of_integral_le`
proves it here, in the Lipschitz form the dissipation rate satisfies. The rest of
the section checks that hypothesis for the Kuramoto dissipation rate — it is
Lipschitz because the velocities are bounded (`kuramotoField_norm_le`), the field
is Lipschitz in the configuration (`kuramotoField_lipschitz`), and the trajectory
is Lipschitz in time because its derivative *is* the bounded field — and concludes
`∑ᵢ θ̇ᵢ² → 0`.

**What this is not.** `θ̇ → 0` says the motion stops; it does not say *where*.
§7 locates the limit, but only for initial data near consensus, so the two
results are incomparable rather than ordered: this section holds for an
*arbitrary* trajectory of an *arbitrary* system — the first such statement in the
development, and the first that is not about the one witness of `Examples.lean`
§15 — while §7 is conditional on the initial configuration.
-/

section Barbalat

/-- **Barbalat's lemma**, in Lipschitz form: a non-negative Lipschitz function
whose integrals `∫₀^T g` are bounded above tends to zero at infinity.

Not in Mathlib, and not a consequence of integrability alone: `g` could be a
sequence of ever narrower unit spikes, whose integral converges while `g` does
not. Uniform continuity is what forbids that, and Lipschitz is the form of it
available here.

The proof is the standard window argument. `F T = ∫₀^T g` is monotone (`g ≥ 0`)
and bounded, so it converges to its supremum, and hence `∫ₜ^{t+δ} g` is small
for all large `t`. If `g t ≥ ε` at some large `t`, the Lipschitz bound keeps
`g ≥ ε/2` across a window of width `δ ≈ ε/2K` that does not depend on `t`, so
that same integral is at least `εδ/2` — a contradiction once `δ` is chosen to
make `εδ/2` exceed the tolerance. -/
theorem tendsto_zero_of_lipschitz_of_integral_le
    {g : ℝ → ℝ} {K M : ℝ}
    (hg_cont : Continuous g)
    (hg_nonneg : ∀ t, 0 ≤ g t)
    (hg_lip : ∀ s t, |g s - g t| ≤ K * |s - t|)
    (hbdd : ∀ T, ∫ t in (0:ℝ)..T, g t ≤ M) :
    Tendsto g atTop (𝓝 0) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hg_cont.intervalIntegrable a b
  set F : ℝ → ℝ := fun T => ∫ t in (0:ℝ)..T, g t with hFdef
  have hFmono : Monotone F := by
    intro a b hab
    have hadd : F a + ∫ t in a..b, g t = F b :=
      intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b)
    have hnn : 0 ≤ ∫ t in a..b, g t :=
      intervalIntegral.integral_nonneg hab (fun x _ => hg_nonneg x)
    linarith
  have hbddA : BddAbove (Set.range F) := ⟨M, by rintro x ⟨T, rfl⟩; exact hbdd T⟩
  have hFL : Tendsto F atTop (𝓝 (⨆ T, F T)) := tendsto_atTop_ciSup hFmono hbddA
  have hFle : ∀ T, F T ≤ ⨆ T, F T := fun T => le_ciSup hbddA T
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (by simpa using hg_lip 0 1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- `K'` replaces `K` by a strictly positive constant, so that `δ` is well defined
  -- even for a constant `g`.
  obtain ⟨K', hK'pos, hKK'⟩ : ∃ K' : ℝ, 0 < K' ∧ K ≤ K' := ⟨K + 1, by linarith, by linarith⟩
  obtain ⟨δ, hδpos, hKδ⟩ : ∃ δ : ℝ, 0 < δ ∧ K' * δ = ε / 2 :=
    ⟨ε / (2 * K'), by positivity, by field_simp⟩
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.1 hFL) (ε * δ / 4) (by positivity)
  refine ⟨T₀, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg_nonneg t)]
  by_contra hcon
  rw [not_lt] at hcon
  -- A spike at `t` drags the whole window `[t, t+δ]` up to `ε/2`.
  have hlow : ∀ s ∈ Set.Icc t (t + δ), ε / 2 ≤ g s := by
    intro s hs
    have h1 : |g t - g s| ≤ K * |t - s| := hg_lip t s
    have h2 : |t - s| ≤ δ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]
      linarith [hs.2]
    have h3 : g t - g s ≤ K * δ := le_trans (le_trans (le_abs_self _) h1)
      (mul_le_mul_of_nonneg_left h2 hK0)
    have h4 : K * δ ≤ K' * δ := mul_le_mul_of_nonneg_right hKK' hδpos.le
    linarith
  have hIlow : ε / 2 * δ ≤ ∫ s in t..(t + δ), g s := by
    have hc : ∫ _ in t..(t + δ), (ε / 2 : ℝ) = ε / 2 * δ := by
      rw [intervalIntegral.integral_const]; simp; ring
    rw [← hc]
    exact intervalIntegral.integral_mono_on (by linarith)
      (intervalIntegrable_const) (hint _ _) hlow
  -- But the tail of a convergent monotone integral carries no such mass.
  have hIup : ∫ s in t..(t + δ), g s < ε * δ / 4 := by
    have hadd : F t + ∫ s in t..(t + δ), g s = F (t + δ) :=
      intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + δ))
    have h1 : |F t - ⨆ T, F T| < ε * δ / 4 := by
      simpa [Real.dist_eq] using hT₀ t ht
    have h3 : (⨆ T, F T) - ε * δ / 4 < F t := by
      have := (abs_lt.1 h1).1; linarith
    have h2 : F (t + δ) ≤ ⨆ T, F T := hFle _
    linarith
  nlinarith [mul_pos hε hδpos]

end Barbalat

section MotionStops

omit [DecidableEq V] in
/-- Each individual velocity is bounded by the field bound of
`kuramotoField_norm_le`, uniformly in the configuration. The sup norm on
`V → ℝ` is what turns the bound on the field into a bound on each component. -/
lemma velocity_abs_le (sys : KuramotoSystem V) (phi : V → ℝ) (i : V) :
    |kuramoto_velocity sys phi i| ≤ (∑ i, |sys.omega i|) + ∑ i, ∑ j, |sys.A i j| := by
  calc |kuramoto_velocity sys phi i| = ‖kuramotoField sys phi i‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ‖kuramotoField sys phi‖ := norm_le_pi_norm _ i
    _ ≤ _ := kuramotoField_norm_le sys phi

omit [DecidableEq V] in
/-- **A trajectory is Lipschitz in time**, with the field bound as constant.
This is the mean value theorem applied to `theta`, whose derivative *is* the
field, and the field is bounded on the whole state space — so unlike the usual
ODE estimate this needs no invariant region. -/
lemma trajectory_dist_le (sys : KuramotoSystem V) (theta : ℝ → V → ℝ)
    (h_traj : is_kuramoto_trajectory sys theta) (s t : ℝ) :
    dist (theta s) (theta t)
      ≤ ((∑ i, |sys.omega i|) + ∑ i, ∑ j, |sys.A i j|) * dist s t := by
  set C : ℝ := (∑ i, |sys.omega i|) + ∑ i, ∑ j, |sys.A i j| with hC
  have hC0 : 0 ≤ C := by
    have h1 : (0:ℝ) ≤ ∑ i, |sys.omega i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h2 : (0:ℝ) ≤ ∑ i, ∑ j, |sys.A i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    rw [hC]; linarith
  have hd : ∀ u, HasDerivAt theta (kuramotoField sys (theta u)) u :=
    (is_kuramoto_trajectory_iff sys theta).1 h_traj
  have hlip : LipschitzWith (Real.toNNReal C) theta := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun u => (hd u).differentiableAt) fun u => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hC0, (hd u).deriv]
    exact kuramotoField_norm_le sys (theta u)
  have h := hlip.dist_le_mul s t
  rwa [Real.coe_toNNReal _ hC0] at h

omit [DecidableEq V] in
/-- **The dissipation rate is Lipschitz in time.** This is the hypothesis
Barbalat's lemma needs, and the constant is explicit: with
`C = ∑ᵢ|ωᵢ| + ∑ᵢⱼ|Aᵢⱼ|` it is `|V| · 4C³`.

Three bounds compose. The velocities are bounded by `C` (`velocity_abs_le`), so
`x ↦ x²` is `2C`-Lipschitz where it is evaluated; the field is `2∑ᵢⱼ|Aᵢⱼ|`-Lipschitz
in the configuration (`kuramotoField_lipschitz`); and the configuration is
`C`-Lipschitz in time (`trajectory_dist_le`). No derivative of the dissipation
rate is ever computed. -/
lemma velocity_sq_lipschitz (sys : KuramotoSystem V) (theta : ℝ → V → ℝ)
    (h_traj : is_kuramoto_trajectory sys theta) (s t : ℝ) :
    |(∑ i, (kuramoto_velocity sys (theta s) i) ^ 2)
        - ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2|
      ≤ (Fintype.card V * (4 * ((∑ i, |sys.omega i|) + ∑ i, ∑ j, |sys.A i j|) ^ 3)) * |s - t| := by
  set C : ℝ := (∑ i, |sys.omega i|) + ∑ i, ∑ j, |sys.A i j| with hC
  have hw0 : (0:ℝ) ≤ ∑ i, |sys.omega i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hSA0 : (0:ℝ) ≤ ∑ i, ∑ j, |sys.A i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hC0 : 0 ≤ C := by rw [hC]; linarith
  have hSA : ∑ i, ∑ j, |sys.A i j| ≤ C := by rw [hC]; linarith
  have hD0 : (0:ℝ) ≤ dist (theta s) (theta t) := dist_nonneg
  have hD := trajectory_dist_le sys theta h_traj s t
  rw [Real.dist_eq] at hD
  have hfield := (kuramotoField_lipschitz sys).dist_le_mul (theta s) (theta t)
  rw [Real.coe_toNNReal _ (by positivity)] at hfield
  have hvdiff : ∀ i, |kuramoto_velocity sys (theta s) i - kuramoto_velocity sys (theta t) i|
      ≤ 2 * C * (C * |s - t|) := by
    intro i
    calc |kuramoto_velocity sys (theta s) i - kuramoto_velocity sys (theta t) i|
        = dist (kuramotoField sys (theta s) i) (kuramotoField sys (theta t) i) := by
          rw [Real.dist_eq]; rfl
      _ ≤ dist (kuramotoField sys (theta s)) (kuramotoField sys (theta t)) :=
          dist_le_pi_dist _ _ i
      _ ≤ 2 * (∑ i, ∑ j, |sys.A i j|) * dist (theta s) (theta t) := hfield
      _ ≤ 2 * C * (C * |s - t|) := by nlinarith
  have hterm : ∀ i, |(kuramoto_velocity sys (theta s) i) ^ 2
      - (kuramoto_velocity sys (theta t) i) ^ 2| ≤ 4 * C ^ 3 * |s - t| := by
    intro i
    have hfac : (kuramoto_velocity sys (theta s) i) ^ 2
        - (kuramoto_velocity sys (theta t) i) ^ 2
        = (kuramoto_velocity sys (theta s) i + kuramoto_velocity sys (theta t) i)
          * (kuramoto_velocity sys (theta s) i - kuramoto_velocity sys (theta t) i) := by ring
    have hsum : |kuramoto_velocity sys (theta s) i + kuramoto_velocity sys (theta t) i|
        ≤ 2 * C := by
      calc |kuramoto_velocity sys (theta s) i + kuramoto_velocity sys (theta t) i|
          ≤ |kuramoto_velocity sys (theta s) i| + |kuramoto_velocity sys (theta t) i| :=
            abs_add_le _ _
        _ ≤ C + C := add_le_add (velocity_abs_le sys _ i) (velocity_abs_le sys _ i)
        _ = 2 * C := by ring
    rw [hfac, abs_mul]
    calc |kuramoto_velocity sys (theta s) i + kuramoto_velocity sys (theta t) i|
          * |kuramoto_velocity sys (theta s) i - kuramoto_velocity sys (theta t) i|
        ≤ (2 * C) * (2 * C * (C * |s - t|)) :=
          mul_le_mul hsum (hvdiff i) (abs_nonneg _) (by positivity)
      _ = 4 * C ^ 3 * |s - t| := by ring
  calc |(∑ i, (kuramoto_velocity sys (theta s) i) ^ 2)
          - ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2|
      = |∑ i, ((kuramoto_velocity sys (theta s) i) ^ 2
          - (kuramoto_velocity sys (theta t) i) ^ 2)| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |(kuramoto_velocity sys (theta s) i) ^ 2
          - (kuramoto_velocity sys (theta t) i) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : V, 4 * C ^ 3 * |s - t| := Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card V * (4 * C ^ 3)) * |s - t| := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

omit [DecidableEq V] in
/-- **O22: the dissipation rate tends to zero along every trajectory.**
`∑ᵢ θ̇ᵢ² → 0` as `t → ∞`, for every zero-frequency system and every initial
condition.

This is Barbalat's lemma applied to the two halves proved above: the integral
bound is `dissipation_integral_tendsto` and the Lipschitz hypothesis is
`velocity_sq_lipschitz`. It is the first asymptotic statement in this development
about an arbitrary trajectory rather than about a single witness.

**It does not locate the limit.** The motion stops, but "stops where" is O20(d),
and the trajectory may stop at a splay or twisted equilibrium rather than at the
phase-locked minimum. -/
theorem velocity_sq_tendsto_zero (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) :
    Tendsto (fun t => ∑ i, (kuramoto_velocity sys (theta t) i) ^ 2) atTop (𝓝 0) := by
  obtain ⟨L, _, _, hle⟩ := dissipation_integral_tendsto sys hw theta h_traj
  exact tendsto_zero_of_lipschitz_of_integral_le
    (velocity_sq_continuous sys theta h_traj)
    (fun t => Finset.sum_nonneg fun i _ => sq_nonneg _)
    (velocity_sq_lipschitz sys theta h_traj) hle

omit [DecidableEq V] in
/-- Each oscillator's velocity tends to zero: the sum of squares dominates each
square, so squeezing gives `θ̇ᵢ² → 0`, and the square root is continuous. -/
theorem velocity_tendsto_zero (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) (i : V) :
    Tendsto (fun t => kuramoto_velocity sys (theta t) i) atTop (𝓝 0) := by
  have hsum := velocity_sq_tendsto_zero sys hw theta h_traj
  have hsq : Tendsto (fun t => (kuramoto_velocity sys (theta t) i) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun t => sq_nonneg _)
      (fun t => Finset.single_le_sum
        (f := fun j => (kuramoto_velocity sys (theta t) j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)) hsum
  have h1 : Tendsto (fun t => Real.sqrt ((kuramoto_velocity sys (theta t) i) ^ 2)) atTop
      (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at h1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using h1

omit [DecidableEq V] in
/-- **The trajectory approaches the equilibrium set**, in the sense that the
vector field evaluated along it tends to `0` in the state space. Equivalently:
the distance from `theta t` to the zero set of `kuramotoField` — the set of
equilibria — tends to zero in the field's own scale. It does *not* follow that
`theta t` converges, and it does not follow that any particular equilibrium is
approached. -/
theorem kuramotoField_tendsto_zero (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) :
    Tendsto (fun t => kuramotoField sys (theta t)) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i
  have hz : (0 : V → ℝ) i = 0 := rfl
  rw [hz]
  exact velocity_tendsto_zero sys hw theta h_traj i

omit [DecidableEq V] in
/-- The same statement read off the trajectory rather than the field: every
phase's time derivative tends to zero. This is the literal reading of "the
motion stops". -/
theorem phase_deriv_tendsto_zero (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) (i : V) :
    Tendsto (fun t => deriv (fun u => theta u i) t) atTop (𝓝 0) := by
  have heq : (fun t => deriv (fun u => theta u i) t)
      = fun t => kuramoto_velocity sys (theta t) i := by
    funext t; exact (h_traj i t).deriv
  rw [heq]
  exact velocity_tendsto_zero sys hw theta h_traj i

omit [DecidableEq V] in
/-- **The motion stops in the rotating frame.** For a system of identical natural
frequencies, read in the frame rotating with them, the dissipation rate tends to
zero. In the original frame the phases keep turning at rate `Ω` forever; what
this says is that the *relative* motion stops. -/
theorem rotating_frame_velocity_tendsto_zero (sys : KuramotoSystem V) (Ω : ℝ)
    (h_omega : ∀ i, sys.omega i = Ω)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta) :
    Tendsto (fun t => ∑ i, (kuramoto_velocity sys.reduced (rotate Ω theta t) i) ^ 2)
      atTop (𝓝 0) :=
  velocity_sq_tendsto_zero sys.reduced (fun _ => rfl) (rotate Ω theta)
    (is_kuramoto_trajectory_rotate sys Ω h_omega theta h_traj)

end MotionStops

/-! ## 7. O20(d) and (e): the trajectory reaches the minimum

§5 and §6 leave the item this development most needs and had recorded as blocked:
`ThermodynamicCover.thermodynamic_equilibrium` *assumes* the cover sits at the
minimum of the potential, and nothing showed a trajectory ever gets there.
`velocity_sq_tendsto_zero` says the motion stops but not where.

The blocker recorded for that step was the LaSalle invariance principle, which
Mathlib does not have, together with the observation that the state space
`V → ℝ` carries no compact invariant set. **That is the wrong tool.** LaSalle is
what one reaches for when a system has a decreasing functional and nothing else.
This system has more, and §5 already proved most of it:

* the flow is a **gradient flow** — `∇ᵢ kuramoto_potential_dynamic` is exactly
  `-kuramoto_velocity` at zero natural frequencies, which is why
  `dynamic_potential_hasDerivAt` gives `V̇ = -∑ᵢ θ̇ᵢ²` as an *identity*;
* the potential's minimisers are known exactly
  (`potential_min_iff_phase_locked`);
* and, proved here, a **Polyak–Łojasiewicz estimate** `‖∇W‖² ≥ cW` holds on the
  region where the phases stay within a quarter turn (`lojasiewicz_estimate`).

Those three give convergence *with a rate*, which is strictly more than LaSalle
would supply. The compactness objection dissolves as well: the invariant region
is produced by the Lyapunov function itself rather than assumed
(`spread_le_of_small`), so no quotient by the phase-shift symmetry and no torus
is needed.

The chain is

  `W` decreasing (§5) + `‖∇W‖² ≥ cW`   →  `W(t) ≤ W(0)e^{-ct}`  [`excess_decay`]
    →  `|θ̇ᵢ(t)| ≤ Be^{-ct/2}`                      [`velocity_abs_le_exp`]
    →  `θ̇ᵢ` integrable on `[0, ∞)`, so `θ` converges [`phase_tendsto`]
    →  the limit has `W = 0`, hence is phase-locked and a global minimiser
                                        [`kuramoto_tendsto_global_minimum`]

## Scope

The two hypotheses are on the initial data and both are necessary. `h_init` puts
the initial phases within a quarter turn of each other; `h_small` puts the
initial excess below `a/2`, where `a` is a positive lower bound for the coupling.
Neither can be dropped: splay and twisted configurations are equilibria of the
same flow, so "every trajectory converges to the phase-locked state" is **false**,
and the hypotheses here are the standard arc condition under which the true
statement holds. This is the version the manuscript's causal chain needs, and it
is conditional on initial data — which the prose now says.
-/

section Lojasiewicz

/-- The total coupling weight `∑ᵢⱼ Aᵢⱼ`. -/
noncomputable def couplingTotal (sys : KuramotoSystem V) : ℝ := ∑ i, ∑ j, sys.A i j

/-- How far a configuration sits above the phase-locked minimum. -/
noncomputable def potentialExcess (sys : KuramotoSystem V) (phi : V → ℝ) : ℝ :=
  kuramoto_potential_dynamic sys phi - kuramoto_potential_dynamic sys (fun _ => 0)

omit [DecidableEq V] in
lemma potentialExcess_eq (sys : KuramotoSystem V) (phi : V → ℝ) :
    potentialExcess sys phi
      = (1/2) * ∑ i, ∑ j, sys.A i j * (1 - Real.cos (phi j - phi i)) := by
  unfold potentialExcess kuramoto_potential_dynamic
  have h0 : ∑ i, ∑ j, sys.A i j * Real.cos ((0:ℝ) - 0) = ∑ i, ∑ j, sys.A i j := by simp
  have key : ∑ i, ∑ j, sys.A i j * (1 - Real.cos (phi j - phi i))
      = (∑ i, ∑ j, sys.A i j) - ∑ i, ∑ j, sys.A i j * Real.cos (phi j - phi i) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  simp only [h0, key]
  ring

omit [DecidableEq V] in
lemma one_sub_cos_nonneg (x : ℝ) : (0:ℝ) ≤ 1 - Real.cos x := by
  linarith [Real.cos_le_one x]

omit [Fintype V] [DecidableEq V] in
lemma potentialExcess_term_nonneg (sys : KuramotoSystem V) (hA : ∀ i j, (0:ℝ) ≤ sys.A i j)
    (phi : V → ℝ) (i j : V) : (0:ℝ) ≤ sys.A i j * (1 - Real.cos (phi j - phi i)) :=
  mul_nonneg (hA i j) (one_sub_cos_nonneg _)

omit [DecidableEq V] in
lemma potentialExcess_nonneg (sys : KuramotoSystem V) (hA : ∀ i j, (0:ℝ) ≤ sys.A i j)
    (phi : V → ℝ) : 0 ≤ potentialExcess sys phi := by
  rw [potentialExcess_eq]
  have : (0:ℝ) ≤ ∑ i, ∑ j, sys.A i j * (1 - Real.cos (phi j - phi i)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      potentialExcess_term_nonneg sys hA phi i j
  linarith

omit [DecidableEq V] in
/-- **A single pair is controlled by the excess.** Every term of the double sum is
non-negative, so the `(i, j)` term alone is a lower bound. -/
lemma pair_le_potentialExcess (sys : KuramotoSystem V) {a : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i j, a ≤ sys.A i j) (phi : V → ℝ) (i j : V) :
    (1/2) * (a * (1 - Real.cos (phi j - phi i))) ≤ potentialExcess sys phi := by
  have hA0 : ∀ i j, (0:ℝ) ≤ sys.A i j := fun i j => le_trans ha (hA i j)
  rw [potentialExcess_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc a * (1 - Real.cos (phi j - phi i))
      ≤ sys.A i j * (1 - Real.cos (phi j - phi i)) :=
        mul_le_mul_of_nonneg_right (hA i j) (one_sub_cos_nonneg _)
    _ ≤ ∑ j', sys.A i j' * (1 - Real.cos (phi j' - phi i)) :=
        Finset.single_le_sum (f := fun j' => sys.A i j' * (1 - Real.cos (phi j' - phi i)))
          (fun j' _ => potentialExcess_term_nonneg sys hA0 phi i j') (mem_univ j)
    _ ≤ ∑ i', ∑ j', sys.A i' j' * (1 - Real.cos (phi j' - phi i')) :=
        Finset.single_le_sum
          (f := fun i' => ∑ j', sys.A i' j' * (1 - Real.cos (phi j' - phi i')))
          (fun i' _ => Finset.sum_nonneg fun j' _ => potentialExcess_term_nonneg sys hA0 phi i' j')
          (mem_univ i)

omit [DecidableEq V] in
/-- **A uniform bound on the pairwise cosines bounds the excess.** -/
lemma potentialExcess_le (sys : KuramotoSystem V) (hA : ∀ i j, (0:ℝ) ≤ sys.A i j)
    (phi : V → ℝ) {e : ℝ} (he : ∀ i j, 1 - Real.cos (phi j - phi i) ≤ e) :
    potentialExcess sys phi ≤ (1/2) * (couplingTotal sys * e) := by
  rw [potentialExcess_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  unfold couplingTotal
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (he i j) (hA i j)


omit [DecidableEq V] in
/-- `sin` is non-positive on `[-π/2, 0]`. -/
lemma sin_nonpos_of_le_zero {x : ℝ} (h1 : -(Real.pi/2) ≤ x) (h2 : x ≤ 0) :
    Real.sin x ≤ 0 := by
  have h : 0 ≤ Real.sin (-x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_neg] at h
  linarith

omit [DecidableEq V] in
/-- **The extremal site has a definite velocity.** At a site `m` carrying the
largest phase, every coupling term pulls backwards, and the term coming from a
site `n` carrying the smallest phase pulls back by at least `a·sin D`, where `D`
is the spread. This is the whole content of the Łojasiewicz estimate below: no
spectral gap, no convexity, one extremal index. -/
lemma velocity_max_le (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    {a : ℝ} (ha : 0 ≤ a) (hA : ∀ i j, a ≤ sys.A i j) (phi : V → ℝ) {m n : V}
    (hm : ∀ j, phi j ≤ phi m) (hn : ∀ j, phi n ≤ phi j)
    (hD : phi m - phi n ≤ Real.pi/2) :
    kuramoto_velocity sys phi m ≤ - (a * Real.sin (phi m - phi n)) := by
  classical
  have hDnn : 0 ≤ phi m - phi n := by linarith [hm n]
  have hsinD : 0 ≤ Real.sin (phi m - phi n) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hDnn (by linarith [Real.pi_pos])
  have hneg : ∀ j, Real.sin (phi j - phi m) ≤ 0 := fun j =>
    sin_nonpos_of_le_zero (by linarith [hn j, hm n]) (by linarith [hm j])
  have hsplit : ∑ j, sys.A m j * Real.sin (phi j - phi m)
      = (∑ j ∈ Finset.univ.erase n, sys.A m j * Real.sin (phi j - phi m))
        + sys.A m n * Real.sin (phi n - phi m) :=
    (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ n)).symm
  have hrest : (∑ j ∈ Finset.univ.erase n, sys.A m j * Real.sin (phi j - phi m)) ≤ 0 :=
    Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (le_trans ha (hA m j)) (hneg j)
  have hlast : sys.A m n * Real.sin (phi n - phi m) ≤ - (a * Real.sin (phi m - phi n)) := by
    have hflip : phi n - phi m = -(phi m - phi n) := by ring
    rw [hflip, Real.sin_neg]
    have : a * Real.sin (phi m - phi n) ≤ sys.A m n * Real.sin (phi m - phi n) :=
      mul_le_mul_of_nonneg_right (hA m n) hsinD
    linarith
  simp only [kuramoto_velocity, hw m, zero_add]
  rw [hsplit]
  linarith


omit [DecidableEq V] in
/-- **The Łojasiewicz estimate.** On the region where every pair of phases is
within a quarter turn, the squared velocity dominates the potential excess:

  `2a²·W(φ) ≤ (∑ᵢⱼ Aᵢⱼ)·∑ᵢ (θ̇ᵢ)²`.

This is a Polyak–Łojasiewicz inequality for the Kuramoto potential, and it is
what replaces the LaSalle principle Mathlib does not have. Its proof is two
extremal indices and the identity `sin²D = (1 - cos D)(1 + cos D)`: the site with
the largest phase moves backwards at rate at least `a·sin D`
(`velocity_max_le`), while the excess is at most `½·(∑ᵢⱼ Aᵢⱼ)·(1 - cos D)`.
The quarter-turn hypothesis enters exactly once, to give `cos D ≥ 0`, hence
`1 + cos D ≥ 1`. -/
theorem lojasiewicz_estimate [Nonempty V] (sys : KuramotoSystem V)
    (hw : ∀ i, sys.omega i = 0) {a : ℝ} (ha : 0 ≤ a) (hA : ∀ i j, a ≤ sys.A i j)
    (phi : V → ℝ) (hspread : ∀ i j, |phi i - phi j| ≤ Real.pi/2) :
    2 * a^2 * potentialExcess sys phi
      ≤ couplingTotal sys * ∑ i, (kuramoto_velocity sys phi i)^2 := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset V) phi Finset.univ_nonempty
  obtain ⟨n, -, hn⟩ := Finset.exists_min_image (Finset.univ : Finset V) phi Finset.univ_nonempty
  have hm' : ∀ j, phi j ≤ phi m := fun j => hm j (Finset.mem_univ j)
  have hn' : ∀ j, phi n ≤ phi j := fun j => hn j (Finset.mem_univ j)
  have hA0 : ∀ i j, (0:ℝ) ≤ sys.A i j := fun i j => le_trans ha (hA i j)
  set D : ℝ := phi m - phi n with hDdef
  have hDnn : 0 ≤ D := by simp only [hDdef]; linarith [hm' n]
  have hDle : D ≤ Real.pi/2 := le_trans (le_abs_self _) (hspread m n)
  have hcnn : 0 ≤ Real.cos D :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hDle⟩
  have hone : (0:ℝ) ≤ 1 - Real.cos D := one_sub_cos_nonneg D
  -- the excess is controlled by the spread
  have hexc : potentialExcess sys phi ≤ (1/2) * (couplingTotal sys * (1 - Real.cos D)) := by
    refine potentialExcess_le sys hA0 phi ?_
    intro i j
    have habs : |phi j - phi i| ≤ D := by
      rw [hDdef]
      exact abs_le.mpr ⟨by linarith [hn' j, hm' i], by linarith [hm' j, hn' i]⟩
    have : Real.cos D ≤ Real.cos |phi j - phi i| :=
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) habs
    rw [Real.cos_abs] at this
    linarith
  -- the extremal velocity is large
  have hvm : kuramoto_velocity sys phi m ≤ - (a * Real.sin D) :=
    velocity_max_le sys hw ha hA phi hm' hn' hDle
  have hsinD : 0 ≤ Real.sin D :=
    Real.sin_nonneg_of_nonneg_of_le_pi hDnn (by linarith [Real.pi_pos])
  have hpyth : Real.sin D ^ 2 + Real.cos D ^ 2 = 1 := Real.sin_sq_add_cos_sq D
  have e1 : (a * Real.sin D)^2 ≤ (kuramoto_velocity sys phi m)^2 := by
    nlinarith [mul_nonneg ha hsinD, hvm]
  have e2 : a^2 * (1 - Real.cos D) ≤ (a * Real.sin D)^2 := by
    nlinarith [sq_nonneg a, hone, hcnn, hpyth]
  have e3 : (kuramoto_velocity sys phi m)^2 ≤ ∑ i, (kuramoto_velocity sys phi i)^2 :=
    Finset.single_le_sum (f := fun i => (kuramoto_velocity sys phi i)^2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ m)
  have hS : 0 ≤ couplingTotal sys :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA0 i j
  have hkey : a^2 * (1 - Real.cos D) ≤ ∑ i, (kuramoto_velocity sys phi i)^2 := by linarith
  calc 2 * a^2 * potentialExcess sys phi
      = a^2 * (2 * potentialExcess sys phi) := by ring
    _ ≤ a^2 * (couplingTotal sys * (1 - Real.cos D)) := by nlinarith [sq_nonneg a]
    _ = couplingTotal sys * (a^2 * (1 - Real.cos D)) := by ring
    _ ≤ couplingTotal sys * ∑ i, (kuramoto_velocity sys phi i)^2 :=
        mul_le_mul_of_nonneg_left hkey hS


section Confinement

variable (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    {a : ℝ} (ha : 0 < a) (hA : ∀ i j, a ≤ sys.A i j)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta)

omit [DecidableEq V] in
include h_traj in
lemma theta_continuous (i : V) : Continuous (fun t => theta t i) :=
  Differentiable.continuous (fun t => (h_traj i t).differentiableAt)

omit [DecidableEq V] in
include hw h_traj in
/-- The excess above the minimum is non-increasing along a trajectory: the
Lyapunov statement, shifted by a constant. -/
lemma potentialExcess_antitone : Antitone (fun t => potentialExcess sys (theta t)) := by
  intro s t hst
  have := dynamic_potential_antitone sys hw theta h_traj hst
  simp only [potentialExcess]
  linarith

omit [DecidableEq V] in
include hw h_traj ha hA in
/-- **Every pairwise phase difference keeps a positive cosine.** The Lyapunov
function confines the trajectory on its own: a single pair contributes
`½a(1 - cos)` to the excess, so an excess below `a/2` forces every cosine
positive, and the excess never grows. No compactness of the state space and no
invariant region put in by hand. -/
lemma cos_pos_of_small (h_small : 2 * potentialExcess sys (theta 0) < a)
    {t : ℝ} (ht : 0 ≤ t) (i j : V) : 0 < Real.cos (theta t j - theta t i) := by
  have h1 : (1/2) * (a * (1 - Real.cos (theta t j - theta t i))) ≤ potentialExcess sys (theta t) :=
    pair_le_potentialExcess sys ha.le hA (theta t) i j
  have h2 : potentialExcess sys (theta t) ≤ potentialExcess sys (theta 0) :=
    potentialExcess_antitone sys hw theta h_traj ht
  nlinarith [h1, h2, h_small, ha]

omit [DecidableEq V] in
include hw h_traj ha hA in
/-- **The quarter-turn region is forward invariant.** This is the branch-pinning
step. `cos_pos_of_small` says the difference of any two phases stays away from
`±π/2` modulo `2π` for all time; continuity of the trajectory on the connected
half-line then says it cannot change branch, so a difference that starts inside
`[-π/2, π/2]` stays inside it. The intermediate value theorem does the work: an
escape would have to cross `π/2` in absolute value, and there the cosine
vanishes. -/
theorem spread_le_of_small (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi/2)
    {t : ℝ} (ht : 0 ≤ t) (i j : V) : |theta t i - theta t j| ≤ Real.pi/2 := by
  -- a difference whose absolute value is `π/2` has vanishing cosine, which
  -- `cos_pos_of_small` forbids at every non-negative time
  have hcross : ∀ u : ℝ, 0 ≤ u → |theta u i - theta u j| ≠ Real.pi/2 := by
    intro u hu heq
    have hc := cos_pos_of_small sys hw ha hA theta h_traj h_small hu j i
    have : Real.cos (theta u i - theta u j) = 0 := by
      rw [← Real.cos_abs, heq, Real.cos_pi_div_two]
    linarith
  by_cases hcon : Real.pi/2 < |theta t i - theta t j|
  swap
  · exact not_lt.mp hcon
  exfalso
  have hfc : Continuous (fun u => |theta u i - theta u j|) :=
    (((theta_continuous sys theta h_traj i).sub (theta_continuous sys theta h_traj j)).abs)
  have h0 : |theta 0 i - theta 0 j| < Real.pi/2 :=
    lt_of_le_of_ne (h_init i j) (hcross 0 le_rfl)
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc ht hfc.continuousOn
    (Set.mem_Icc.mpr ⟨h0.le, hcon.le⟩)
  exact hcross s hs.1 hfs

omit [DecidableEq V] in
lemma couplingTotal_pos [Nonempty V] (ha : 0 < a) (hA : ∀ i j, a ≤ sys.A i j) :
    0 < couplingTotal sys := by
  obtain ⟨i0⟩ := ‹Nonempty V›
  have hA0 : ∀ i j, (0:ℝ) ≤ sys.A i j := fun i j => le_trans ha.le (hA i j)
  have h1 : sys.A i0 i0 ≤ ∑ j, sys.A i0 j :=
    Finset.single_le_sum (f := fun j => sys.A i0 j) (fun j _ => hA0 i0 j) (Finset.mem_univ i0)
  have h2 : (∑ j, sys.A i0 j) ≤ couplingTotal sys :=
    Finset.single_le_sum (f := fun i => ∑ j, sys.A i j)
      (fun i _ => Finset.sum_nonneg fun j _ => hA0 i j) (Finset.mem_univ i0)
  linarith [hA i0 i0]

omit [DecidableEq V] in
include hw h_traj ha hA in
/-- **The excess decays exponentially.** `lojasiewicz_estimate` turns the exact
Lyapunov identity `Ẇ = -∑ᵢ θ̇ᵢ²` into the differential inequality `Ẇ ≤ -cW` with
`c = 2a²/∑ᵢⱼ Aᵢⱼ`, and Grönwall — here in the elementary form "`W(t)e^{ct}` has
non-positive derivative" — integrates it.

This is the step LaSalle would otherwise be needed for, and it gives more than
LaSalle would: a rate, rather than convergence to an unlocated limit set. -/
theorem excess_decay [Nonempty V] (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi/2) {t : ℝ} (ht : 0 ≤ t) :
    potentialExcess sys (theta t)
      ≤ potentialExcess sys (theta 0) * Real.exp (-(2*a^2/couplingTotal sys) * t) := by
  have hS : 0 < couplingTotal sys := couplingTotal_pos sys ha hA
  set c : ℝ := 2*a^2/couplingTotal sys with hc
  set g : ℝ → ℝ := fun u => potentialExcess sys (theta u) with hg
  have hgd : ∀ u, HasDerivAt g (- ∑ i, (kuramoto_velocity sys (theta u) i)^2) u := by
    intro u
    simpa only [hg, potentialExcess] using
      (dynamic_potential_hasDerivAt sys hw theta h_traj u).sub_const _
  set F : ℝ → ℝ := fun u => g u * Real.exp (c * u) with hF
  have hFd : ∀ u, HasDerivAt F
      ((- ∑ i, (kuramoto_velocity sys (theta u) i)^2) * Real.exp (c * u)
        + g u * (Real.exp (c * u) * c)) u := by
    intro u
    have hexpd : HasDerivAt (fun v : ℝ => Real.exp (c * v)) (Real.exp (c * u) * c) u := by
      simpa using ((hasDerivAt_id u).const_mul c).exp
    exact (hgd u).mul hexpd
  have hFdiff : Differentiable ℝ F := fun u => (hFd u).differentiableAt
  have hnonpos : ∀ u ∈ interior (Set.Ici (0:ℝ)), deriv F u ≤ 0 := by
    intro u hu
    rw [interior_Ici] at hu
    have hu0 : (0:ℝ) ≤ u := le_of_lt hu
    have hspread : ∀ i j, |theta u i - theta u j| ≤ Real.pi/2 :=
      fun i j => spread_le_of_small sys hw ha hA theta h_traj h_small h_init hu0 i j
    have hloj := lojasiewicz_estimate sys hw ha.le hA (theta u) hspread
    have hcg : c * g u ≤ ∑ i, (kuramoto_velocity sys (theta u) i)^2 := by
      rw [hc, div_mul_eq_mul_div, div_le_iff₀ hS]
      nlinarith [hloj]
    rw [(hFd u).deriv]
    have hexp : 0 < Real.exp (c * u) := Real.exp_pos _
    nlinarith [hcg, hexp]
  have hanti : AntitoneOn F (Set.Ici (0:ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hFdiff.continuous.continuousOn
      hFdiff.differentiableOn hnonpos
  have hle : F t ≤ F 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [hF, mul_zero, Real.exp_zero, mul_one] at hle
  have hexp : 0 < Real.exp (c * t) := Real.exp_pos _
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexp]
  exact hle

omit [Fintype V] [DecidableEq V] in
/-- `|sin d| ≤ √(2e)` whenever `1 - cos d ≤ e`. The identity is
`sin²d = (1 - cos d)(1 + cos d)` and the second factor is at most `2`. -/
lemma abs_sin_le_sqrt {d e : ℝ} (hd : 1 - Real.cos d ≤ e) (he : 0 ≤ e) :
    |Real.sin d| ≤ Real.sqrt (2 * e) := by
  have hpyth : Real.sin d ^ 2 + Real.cos d ^ 2 = 1 := Real.sin_sq_add_cos_sq d
  have hc1 : Real.cos d ≤ 1 := Real.cos_le_one d
  have hc2 : -1 ≤ Real.cos d := Real.neg_one_le_cos d
  have hsq : Real.sin d ^ 2 ≤ 2 * e := by nlinarith
  calc |Real.sin d| = Real.sqrt (Real.sin d ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * e) := Real.sqrt_le_sqrt hsq

omit [DecidableEq V] in
/-- **A uniform bound on the pairwise cosines bounds the velocity.** -/
lemma velocity_abs_le_sqrt (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    (hA0 : ∀ i j, (0:ℝ) ≤ sys.A i j) (phi : V → ℝ) (i : V) {e : ℝ} (he : 0 ≤ e)
    (hcos : ∀ j, 1 - Real.cos (phi j - phi i) ≤ e) :
    |kuramoto_velocity sys phi i| ≤ couplingTotal sys * Real.sqrt (2 * e) := by
  have hrow : (∑ j, sys.A i j) ≤ couplingTotal sys :=
    Finset.single_le_sum (f := fun i' => ∑ j, sys.A i' j)
      (fun i' _ => Finset.sum_nonneg fun j _ => hA0 i' j) (Finset.mem_univ i)
  have hsr : 0 ≤ Real.sqrt (2 * e) := Real.sqrt_nonneg _
  calc |kuramoto_velocity sys phi i|
      = |∑ j, sys.A i j * Real.sin (phi j - phi i)| := by
        simp only [kuramoto_velocity, hw i, zero_add]
    _ ≤ ∑ j, |sys.A i j * Real.sin (phi j - phi i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, sys.A i j * Real.sqrt (2 * e) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hA0 i j)]
        exact mul_le_mul_of_nonneg_left (abs_sin_le_sqrt (hcos j) he) (hA0 i j)
    _ = (∑ j, sys.A i j) * Real.sqrt (2 * e) := by rw [Finset.sum_mul]
    _ ≤ couplingTotal sys * Real.sqrt (2 * e) := mul_le_mul_of_nonneg_right hrow hsr

omit [DecidableEq V] in
include hw h_traj ha hA in
/-- **The velocity decays exponentially.** Combining `excess_decay` with the
elementary bound `|sin d| ≤ √(2(1 - cos d))`, every component of the velocity is
dominated by `B·e^{-(a²/∑Aᵢⱼ)t}`. This is what makes the trajectory itself — not
just its potential — converge: an exponentially small velocity is integrable, and
a trajectory with integrable velocity has a limit. -/
theorem velocity_abs_le_exp [Nonempty V] (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi/2) {t : ℝ} (ht : 0 ≤ t) (i : V) :
    |kuramoto_velocity sys (theta t) i|
      ≤ (couplingTotal sys * Real.sqrt (4 * potentialExcess sys (theta 0) / a))
          * Real.exp (-(a^2/couplingTotal sys) * t) := by
  have hS : 0 < couplingTotal sys := couplingTotal_pos sys ha hA
  have hA0 : ∀ i j, (0:ℝ) ≤ sys.A i j := fun i j => le_trans ha.le (hA i j)
  set c : ℝ := 2*a^2/couplingTotal sys with hc
  set W0 : ℝ := potentialExcess sys (theta 0) with hW0
  have hW0nn : 0 ≤ W0 := potentialExcess_nonneg sys hA0 _
  have hWt : 0 ≤ potentialExcess sys (theta t) := potentialExcess_nonneg sys hA0 _
  -- pairwise cosines are controlled by the excess
  have hcos : ∀ j, 1 - Real.cos (theta t j - theta t i) ≤ 2 * potentialExcess sys (theta t) / a := by
    intro j
    have := pair_le_potentialExcess sys ha.le hA (theta t) i j
    rw [le_div_iff₀ ha]
    linarith
  have he : (0:ℝ) ≤ 2 * potentialExcess sys (theta t) / a := by positivity
  have hstep := velocity_abs_le_sqrt sys hw hA0 (theta t) i he hcos
  -- and the excess decays
  have hdec : potentialExcess sys (theta t) ≤ W0 * Real.exp (-c * t) := by
    have := excess_decay sys hw ha hA theta h_traj h_small h_init ht
    simpa only [hc, neg_mul] using this
  have hmono : 2 * (2 * potentialExcess sys (theta t) / a) ≤ (4 * W0 / a) * Real.exp (-c * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    have h4 : 2 * (2 * potentialExcess sys (theta t) / a) * a
        = 4 * potentialExcess sys (theta t) := by field_simp; ring
    rw [h4]
    linarith [hdec]
  have hsqrt : Real.sqrt (2 * (2 * potentialExcess sys (theta t) / a))
      ≤ Real.sqrt (4 * W0 / a) * Real.exp (-(a^2/couplingTotal sys) * t) := by
    have hexpsq : Real.exp (-(a^2/couplingTotal sys) * t) ^ 2 = Real.exp (-c * t) := by
      rw [sq, ← Real.exp_add, hc]
      ring_nf
    calc Real.sqrt (2 * (2 * potentialExcess sys (theta t) / a))
        ≤ Real.sqrt ((4 * W0 / a) * Real.exp (-c * t)) := Real.sqrt_le_sqrt hmono
      _ = Real.sqrt (4 * W0 / a) * Real.sqrt (Real.exp (-c * t)) :=
          Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (4 * W0 / a) * Real.exp (-(a^2/couplingTotal sys) * t) := by
          rw [← hexpsq, Real.sqrt_sq (Real.exp_nonneg _)]
  calc |kuramoto_velocity sys (theta t) i|
      ≤ couplingTotal sys * Real.sqrt (2 * (2 * potentialExcess sys (theta t) / a)) := hstep
    _ ≤ couplingTotal sys * (Real.sqrt (4 * W0 / a)
          * Real.exp (-(a^2/couplingTotal sys) * t)) :=
        mul_le_mul_of_nonneg_left hsqrt hS.le
    _ = (couplingTotal sys * Real.sqrt (4 * W0 / a))
          * Real.exp (-(a^2/couplingTotal sys) * t) := by ring

omit [DecidableEq V] in
include h_traj in
lemma velocity_continuous (i : V) :
    Continuous (fun t => kuramoto_velocity sys (theta t) i) := by
  have hth : ∀ j, Continuous (fun t => theta t j) := theta_continuous sys theta h_traj
  simp only [kuramoto_velocity]
  exact continuous_const.add (continuous_finsetSum _ fun j _ =>
    continuous_const.mul (Real.continuous_sin.comp ((hth j).sub (hth i))))

omit [DecidableEq V] in
include hw h_traj ha hA in
/-- **The trajectory converges.** An exponentially decaying velocity is
integrable on `[0, ∞)`, and a trajectory with integrable velocity is the integral
of that velocity, hence has a limit. Concretely the limit is
`θᵢ(0) + ∫₀^∞ θ̇ᵢ`. -/
theorem phase_tendsto [Nonempty V] (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi/2) (i : V) :
    Filter.Tendsto (fun t => theta t i) Filter.atTop
      (nhds (theta 0 i + ∫ u in Set.Ioi (0:ℝ), kuramoto_velocity sys (theta u) i)) := by
  have hS : 0 < couplingTotal sys := couplingTotal_pos sys ha hA
  have hlam0 : 0 < a^2/couplingTotal sys := div_pos (pow_pos ha 2) hS
  have hcont := velocity_continuous sys theta h_traj i
  have hdom : MeasureTheory.IntegrableOn
      (fun u : ℝ => (couplingTotal sys * Real.sqrt (4 * potentialExcess sys (theta 0) / a))
        * Real.exp (-(a^2/couplingTotal sys) * u)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hlam0).const_mul _
  have hint : MeasureTheory.IntegrableOn
      (fun u => kuramoto_velocity sys (theta u) i) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono' hdom hcont.aestronglyMeasurable.restrict ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    simpa only [Real.norm_eq_abs] using
      velocity_abs_le_exp sys hw ha hA theta h_traj h_small h_init (le_of_lt hu) i
  have hFTC : ∀ T : ℝ, ∫ u in (0:ℝ)..T, kuramoto_velocity sys (theta u) i
      = theta T i - theta 0 i := fun T =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => h_traj i x)
      (hcont.intervalIntegrable 0 T)
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0:ℝ) hint
    (Filter.tendsto_id (x := (Filter.atTop : Filter ℝ)))
  have hlim2 : Filter.Tendsto (fun T => theta T i - theta 0 i) Filter.atTop
      (nhds (∫ u in Set.Ioi (0:ℝ), kuramoto_velocity sys (theta u) i)) :=
    hlim.congr hFTC
  have := hlim2.const_add (theta 0 i)
  exact this.congr (fun T => by ring)

omit [DecidableEq V] in
include hw h_traj ha hA in
/-- **The excess vanishes in the limit**: the trajectory reaches the *global*
minimum of the potential, not merely some critical value. -/
theorem excess_tendsto_zero [Nonempty V] (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi/2) :
    Filter.Tendsto (fun t => potentialExcess sys (theta t)) Filter.atTop (nhds 0) := by
  have hS : 0 < couplingTotal sys := couplingTotal_pos sys ha hA
  have hA0 : ∀ i j, (0:ℝ) ≤ sys.A i j := fun i j => le_trans ha.le (hA i j)
  have hc0 : 0 < 2*a^2/couplingTotal sys := div_pos (by positivity) hS
  have h1 : Filter.Tendsto (fun t : ℝ => -(2*a^2/couplingTotal sys) * t)
      Filter.atTop Filter.atBot :=
    Filter.tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 hc0)
  have hexp0 : Filter.Tendsto (fun t : ℝ => Real.exp (-(2*a^2/couplingTotal sys) * t))
      Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp h1
  have hlim : Filter.Tendsto
      (fun t => potentialExcess sys (theta 0) * Real.exp (-(2*a^2/couplingTotal sys) * t))
      Filter.atTop (nhds 0) := by
    simpa using hexp0.const_mul (potentialExcess sys (theta 0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun t => potentialExcess_nonneg sys hA0 _) ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
  exact excess_decay sys hw ha hA theta h_traj h_small h_init ht

omit [DecidableEq V] in
include hw h_traj ha hA in
/-- **O20(d) and O20(e): the trajectory converges to a global minimiser of the
potential.**

Initial data within a quarter turn and below the energy threshold `a/2` — the two
hypotheses `h_init` and `h_small` — is carried by the flow to a phase-locked
configuration, which by `potential_min_iff_phase_locked` is a global minimum of
`kuramoto_potential_dynamic`, the configuration `ThermodynamicCover`'s
`thermodynamic_equilibrium` field assumes.

No LaSalle principle and no compact invariant set appear: the Lyapunov function
confines the trajectory itself (`spread_le_of_small`), the Łojasiewicz estimate
turns descent into an exponential rate (`excess_decay`), and the rate makes the
velocity integrable, which is what produces the limit.

**What it does not establish.** Anything for initial data outside the threshold.
Splay and twisted configurations are equilibria of the same flow, so no theorem
of the form "every trajectory reaches the phase-locked state" is true; the
hypotheses here are exactly the arc condition under which the statement holds. -/
theorem kuramoto_tendsto_global_minimum [Nonempty V]
    (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi/2) :
    ∃ thetaInf : V → ℝ,
      (∀ i, Filter.Tendsto (fun t => theta t i) Filter.atTop (nhds (thetaInf i)))
      ∧ is_phase_locked thetaInf
      ∧ (∀ phi, kuramoto_potential_dynamic sys thetaInf
            ≤ kuramoto_potential_dynamic sys phi)
      ∧ order_parameter_r_sq thetaInf = 1 := by
  have hpos : ∀ i j, sys.A i j > 0 := fun i j => lt_of_lt_of_le ha (hA i j)
  set thetaInf : V → ℝ :=
    fun i => theta 0 i + ∫ u in Set.Ioi (0:ℝ), kuramoto_velocity sys (theta u) i with hInf
  have hconv : ∀ i, Filter.Tendsto (fun t => theta t i) Filter.atTop (nhds (thetaInf i)) :=
    fun i => phase_tendsto sys hw ha hA theta h_traj h_small h_init i
  have hzero := excess_tendsto_zero sys hw ha hA theta h_traj h_small h_init
  have hlock : is_phase_locked thetaInf := by
    intro i j
    have hcoslim := (Real.continuous_cos.tendsto _).comp ((hconv i).sub (hconv j))
    have hcos1 : Filter.Tendsto (fun t => Real.cos (theta t i - theta t j))
        Filter.atTop (nhds 1) := by
      have hlowlim : Filter.Tendsto
          (fun t => 1 - 2 * potentialExcess sys (theta t) / a) Filter.atTop (nhds 1) := by
        simpa using tendsto_const_nhds.sub ((hzero.const_mul 2).div_const a)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim tendsto_const_nhds ?_
        (Filter.Eventually.of_forall fun t => Real.cos_le_one _)
      refine Filter.Eventually.of_forall fun t => ?_
      have hW := pair_le_potentialExcess sys ha.le hA (theta t) j i
      have h2 : 1 - Real.cos (theta t i - theta t j)
          ≤ 2 * potentialExcess sys (theta t) / a := by
        rw [le_div_iff₀ ha]; nlinarith [hW]
      linarith
    exact tendsto_nhds_unique hcoslim hcos1
  exact ⟨thetaInf, hconv, hlock,
    fun phi => phase_locked_minimizes_potential' sys hpos thetaInf hlock phi,
    phase_locked_implies_r_sq_eq_one thetaInf hlock⟩

end Confinement

end Lojasiewicz

omit [DecidableEq V] in
/-- **The rotating-frame form.** For a system of identical natural frequencies,
read in the frame rotating with them, a trajectory starting near consensus
converges to a phase-locked configuration, which is a global minimiser of the
reduced potential.

In the original frame the phases keep turning at rate `Ω` forever; what converges
is the *relative* configuration, which is what `is_phase_locked` and the order
parameter see. -/
theorem rotating_frame_tendsto_global_minimum [Nonempty V] (sys : KuramotoSystem V) (Ω : ℝ)
    (h_omega : ∀ i, sys.omega i = Ω) {a : ℝ} (ha : 0 < a) (hA : ∀ i j, a ≤ sys.A i j)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta)
    (h_small : 2 * potentialExcess sys.reduced (rotate Ω theta 0) < a)
    (h_init : ∀ i j, |rotate Ω theta 0 i - rotate Ω theta 0 j| ≤ Real.pi/2) :
    ∃ thetaInf : V → ℝ,
      (∀ i, Tendsto (fun t => rotate Ω theta t i) atTop (𝓝 (thetaInf i)))
      ∧ is_phase_locked thetaInf
      ∧ (∀ phi, kuramoto_potential_dynamic sys thetaInf
            ≤ kuramoto_potential_dynamic sys phi)
      ∧ order_parameter_r_sq thetaInf = 1 :=
  kuramoto_tendsto_global_minimum sys.reduced (fun _ => rfl) ha hA (rotate Ω theta)
    (is_kuramoto_trajectory_rotate sys Ω h_omega theta h_traj) h_small h_init


end PhysicsOfConsciousness
