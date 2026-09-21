/-
  Examples/Phase4.lean — oscillators that run

  §7 runs the rotating-frame reduction end to end on two oscillators with a
  common natural frequency, every hypothesis discharged, and exhibits a system
  whose full Kuramoto potential provably has no minimum. §15 is a trajectory
  with a closed form that runs into that minimum, on the two-site substrate of
  `Examples/Phase8.lean` §5; §16 is the one-way coupling that beats its own
  phase-locked state, which is why the symmetric-kernel result needs its
  hypothesis. §17 reaches the minimum on three sites, where no closed form
  exists and the trajectory comes from the existence theorem instead. §32 is
  about covers rather than trajectories: two sites in antiphase, two legal
  uniform covers of them, and the reported patch agreement zero on one and one
  on the other.
-/

import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics
import PhysicsOfConsciousness.Phase4_RotatingFrame
import PhysicsOfConsciousness.Phase8_ContinuousField
import PhysicsOfConsciousness.Phase8_SelfConsistency
import PhysicsOfConsciousness.Examples.Phase8

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 7. The rotating-frame reduction on a two-oscillator system

`Phase4_RotatingFrame` chains the two Kuramoto potentials, but only for systems
whose natural frequencies are identical, and only at configurations that
minimise the dynamic potential. Both are real restrictions, so the chain is
worth nothing unless something satisfies them. This section exhibits a system
that does, and — on the other side — a system for which the full potential
provably has no minimum at all, which is what forced the reduction in the first
place. -/

/-- Two oscillators, unit coupling, common natural frequency `Ω`. -/
noncomputable def pairSystem (Ω : ℝ) : KuramotoSystem Bool where
  omega := fun _ => Ω
  A := fun _ _ => 1
  symm := fun _ _ => rfl

/-- The fully synchronized trajectory: both phases advance at the common
frequency. -/
noncomputable def pairTrajectory (Ω : ℝ) : ℝ → Bool → ℝ := fun t _ => Ω * t

theorem pairTrajectory_is_trajectory (Ω : ℝ) :
    is_kuramoto_trajectory (pairSystem Ω) (pairTrajectory Ω) := by
  intro i t
  have h : HasDerivAt (fun t : ℝ => Ω * t) Ω t := by
    simpa using (hasDerivAt_id t).const_mul Ω
  have hval : (pairSystem Ω).omega i
      + ∑ j, (pairSystem Ω).A i j
          * Real.sin (pairTrajectory Ω t j - pairTrajectory Ω t i) = Ω := by
    simp [pairSystem, pairTrajectory]
  rw [hval]
  exact h

/-- In the rotating frame the trajectory sits at the origin — where
`phase_locked_minimizes_potential` says the dynamic potential is minimised. -/
theorem rotate_pairTrajectory (Ω : ℝ) (t : ℝ) :
    rotate Ω (pairTrajectory Ω) t = fun _ => 0 := by
  funext i
  simp [rotate, pairTrajectory]

/-- **The chain fires.** Every hypothesis of `rotating_frame_chain` is
discharged concretely: the rotated trajectory solves the zero-frequency
equations, the dynamic potential is non-increasing along it, the original
phases are locked, and the order parameter is `1`. -/
theorem pair_rotating_frame_chain (Ω : ℝ) (t : ℝ) :
    is_kuramoto_trajectory (pairSystem Ω).reduced (rotate Ω (pairTrajectory Ω))
      ∧ deriv (fun t => kuramoto_potential_dynamic (pairSystem Ω)
            (rotate Ω (pairTrajectory Ω) t)) t ≤ 0
      ∧ is_phase_locked (pairTrajectory Ω t)
      ∧ order_parameter_r_sq (pairTrajectory Ω t) = 1 := by
  refine rotating_frame_chain (pairSystem Ω) Ω (fun _ => rfl) (fun _ _ => by
    simp [pairSystem]) (pairTrajectory Ω) (pairTrajectory_is_trajectory Ω) t ?_
  intro phi
  rw [rotate_pairTrajectory]
  exact phase_locked_minimizes_potential (pairSystem Ω) (fun _ _ => by
    simp [pairSystem]) phi

/-- The full potential really is non-constant along the reduction: at the
synchronized configuration it differs from its value at the origin exactly by
the frequency term. -/
example (Ω : ℝ) (t : ℝ) :
    kuramoto_potential (pairSystem Ω) (pairTrajectory Ω t)
      = kuramoto_potential_dynamic (pairSystem Ω) (rotate Ω (pairTrajectory Ω) t)
        - 2 * Ω * (Ω * t) := by
  rw [kuramoto_potential_eq_dynamic_sub, rotate_pairTrajectory]
  simp [kuramoto_potential_dynamic, pairSystem, pairTrajectory]
  ring

/-- **The other side.** With a non-zero natural frequency the full Kuramoto
potential is unbounded below, so "the phase-locked state minimises the Lyapunov
potential" is false of it — there is no minimum to attain. The hypothesis of
`kuramoto_potential_unbounded_below` is satisfiable. -/
example (C : ℝ) : ∃ theta : Bool → ℝ, kuramoto_potential (pairSystem 1) theta < C :=
  kuramoto_potential_unbounded_below (pairSystem 1) ⟨true, by simp [pairSystem]⟩ C

/-! ## 15. A trajectory that runs into the minimum

  Open item **O20** records that nothing in this development runs a dynamics.
  Every Derivation 5 result is conditional on `thermodynamic_equilibrium` — the
  cover is *assumed* to sit at the potential minimum — and until now the only
  trajectory anywhere in the development was §7's rigid rotation
  `pairTrajectory Ω t = Ω·t`, which starts synchronised and therefore never
  converges to anything. `is_kuramoto_trajectory` was a predicate whose one
  inhabitant began at its own limit.

  This section exhibits a trajectory that does not. On two oscillators with unit
  coupling and zero natural frequency, the phase difference `Δ = θ₁ - θ₀` obeys
  the scalar equation `Δ̇ = -2 sin Δ`, which is integrable: `Δ(t) = 2 arctan(c
  e^{-2t})`. Splitting it symmetrically gives an exact solution of the full
  Kuramoto system (`pairRelax_is_trajectory`), defined on all of `ℝ`, and
  everything downstream is a statement about it:

  * it is **not** phase-locked at time zero — at `c = 1` the phases start a
    quarter turn apart (`pairRelax_not_locked_at_zero`);
  * the cosine of the phase difference tends to `1`
    (`pairRelax_tendsto_locked`), which is the value `is_phase_locked` demands;
  * the order parameter tends to `1` (`pairRelax_order_parameter_tendsto`), via
    the two-oscillator identity `r² = (1 + cos Δ)/2`;
  * and the dynamic potential tends to its **global minimum**
    (`pairRelax_potential_tendsto_min`) — the value
    `phase_locked_minimizes_potential` names.

  **What this settles and what it does not.** It settles the vacuity worry:
  the phrase "a thermodynamic phase transition into unity" now has one instance
  in Lean where a trajectory genuinely runs from a non-synchronised state into
  the minimiser, rather than being placed there by hypothesis. Combined with
  `is_kuramoto_trajectory_unique` this is the *only* trajectory through its
  initial state, so it is not one solution among many.

  It does not settle O20 by itself. `is_kuramoto_trajectory_exists` (O20(a))
  gives every system a solution on all of `ℝ`; `dynamic_potential_tendsto`
  (O20(b)) makes every trajectory's potential converge; `velocity_sq_tendsto_zero`
  (O22) makes every trajectory's velocity tend to zero, and
  `pairRelax_velocity_sq_tendsto_zero` below is that theorem fired on this
  trajectory. What none of them gives is *where* the motion stops.

  That is O20(d), and it is now proved — `kuramoto_tendsto_global_minimum` in
  `Phase4_RotatingFrame.lean` §7 — but conditionally, and by a Łojasiewicz
  estimate rather than the LaSalle principle this note used to name as the
  blocker. The general statement of O20(e) is genuinely **false**: splay and
  twisted configurations are equilibria too, so no theorem of the form "every
  trajectory reaches the phase-locked state" can be proved. The arc condition
  that makes it true is satisfied here for every `c`, since `2 arctan` lands in
  `(-π, π)`, which is why this witness converges and a general trajectory need
  not. §17 runs the general theorem on three sites, where no closed form of the
  kind this section relies on exists.
-/

section RunningDynamics

/-- `sin(2 arctan u) = 2u/(1+u²)`. -/
lemma sin_two_arctan (u : ℝ) : Real.sin (2 * Real.arctan u) = 2 * u / (1 + u ^ 2) := by
  have h1 : (0:ℝ) < 1 + u ^ 2 := by positivity
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have hs : Real.sqrt (1 + u ^ 2) * Real.sqrt (1 + u ^ 2) = 1 + u ^ 2 :=
    Real.mul_self_sqrt h1.le
  have hne : Real.sqrt (1 + u ^ 2) ≠ 0 := by positivity
  have hsq : Real.sqrt (1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt h1.le
  field_simp
  rw [hsq]

/-- The relaxing gap: `c e^{-2t}`, the tangent of half the phase difference. -/
noncomputable def relaxU (c : ℝ) (t : ℝ) : ℝ := c * Real.exp (-2 * t)

/-- Half the phase difference along the relaxing trajectory. -/
noncomputable def relaxAngle (c : ℝ) (t : ℝ) : ℝ := Real.arctan (relaxU c t)

/-- The relaxing two-oscillator trajectory: the phases approach each other. -/
noncomputable def pairRelax (c : ℝ) : ℝ → Bool → ℝ :=
  fun t i => if i then relaxAngle c t else -relaxAngle c t

lemma hasDerivAt_relaxU (c t : ℝ) : HasDerivAt (relaxU c) (-2 * relaxU c t) t := by
  have hin : HasDerivAt (fun t : ℝ => -2 * t) (-2 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 : ℝ)
  have h : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t :=
    (Real.hasDerivAt_exp (-2 * t)).comp t hin
  have h2 := h.const_mul c
  refine h2.congr_deriv ?_
  simp [relaxU]
  ring

lemma hasDerivAt_relaxAngle (c t : ℝ) :
    HasDerivAt (relaxAngle c) (-2 * relaxU c t / (1 + relaxU c t ^ 2)) t := by
  have := (hasDerivAt_relaxU c t).arctan
  refine this.congr_deriv ?_
  field_simp

/-- **A trajectory that runs into synchrony.** The relaxing pair solves the
zero-frequency Kuramoto equations exactly. -/
theorem pairRelax_is_trajectory (c : ℝ) :
    is_kuramoto_trajectory (pairSystem 0) (pairRelax c) := by
  intro i t
  have hsin := sin_two_arctan (relaxU c t)
  cases i
  · have hval : (pairSystem 0).omega false
        + ∑ j, (pairSystem 0).A false j * Real.sin (pairRelax c t j - pairRelax c t false)
        = -(-2 * relaxU c t / (1 + relaxU c t ^ 2)) := by
      simp only [pairSystem, pairRelax, relaxAngle, Fintype.sum_bool]
      norm_num
      rw [show Real.arctan (relaxU c t) + Real.arctan (relaxU c t)
          = 2 * Real.arctan (relaxU c t) by ring, hsin]
      ring
    rw [hval]
    have hfun : (fun t : ℝ => pairRelax c t false) = fun t => -relaxAngle c t := by
      funext s; simp [pairRelax]
    rw [hfun]
    exact (hasDerivAt_relaxAngle c t).neg
  · have hval : (pairSystem 0).omega true
        + ∑ j, (pairSystem 0).A true j * Real.sin (pairRelax c t j - pairRelax c t true)
        = -2 * relaxU c t / (1 + relaxU c t ^ 2) := by
      simp only [pairSystem, pairRelax, relaxAngle, Fintype.sum_bool]
      norm_num
      rw [show -Real.arctan (relaxU c t) - Real.arctan (relaxU c t)
          = -(2 * Real.arctan (relaxU c t)) by ring, Real.sin_neg, hsin]
      ring
    rw [hval]
    have hfun : (fun t : ℝ => pairRelax c t true) = fun t => relaxAngle c t := by
      funext s; simp [pairRelax]
    rw [hfun]
    exact hasDerivAt_relaxAngle c t

/-! ### It converges, and it does not start where it ends -/

lemma relaxU_tendsto (c : ℝ) : Tendsto (relaxU c) atTop (𝓝 0) := by
  have hb : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
    have h2 : Tendsto (fun t : ℝ => (2 : ℝ) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
    have : (fun t : ℝ => -2 * t) = fun t : ℝ => -((2 : ℝ) * t) := by funext t; ring
    rw [this]
    exact tendsto_neg_atBot_iff.2 h2
  have he : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hb
  have h3 := he.const_mul c
  have heq : relaxU c = fun t : ℝ => c * Real.exp (-2 * t) := by funext t; rfl
  rw [heq]
  simpa using h3

lemma relaxAngle_tendsto (c : ℝ) : Tendsto (relaxAngle c) atTop (𝓝 0) := by
  have h := (Real.continuous_arctan.tendsto 0).comp (relaxU_tendsto c)
  rw [Real.arctan_zero] at h
  exact h

/-- The phase difference along the relaxing trajectory. -/
lemma pairRelax_gap (c t : ℝ) :
    pairRelax c t true - pairRelax c t false = 2 * relaxAngle c t := by
  simp [pairRelax]; ring

/-- **The trajectory synchronises.** The cosine of the phase difference tends to
`1` — the value `is_phase_locked` demands. -/
theorem pairRelax_tendsto_locked (c : ℝ) :
    Tendsto (fun t => Real.cos (pairRelax c t true - pairRelax c t false)) atTop (𝓝 1) := by
  have h : Tendsto (fun t => 2 * relaxAngle c t) atTop (𝓝 0) := by
    simpa using (relaxAngle_tendsto c).const_mul 2
  have h2 := (Real.continuous_cos.tendsto 0).comp h
  rw [Real.cos_zero] at h2
  have : (fun t => Real.cos (pairRelax c t true - pairRelax c t false))
      = Real.cos ∘ fun t => 2 * relaxAngle c t := by
    funext t; simp [Function.comp, pairRelax_gap]
  rw [this]
  exact h2

/-- With `c = 1` the trajectory starts at a phase difference of `π/2`: it is
*not* phase-locked at time zero, so it has somewhere to go. -/
theorem pairRelax_not_locked_at_zero : ¬ is_phase_locked (pairRelax 1 0) := by
  intro h
  have h1 := h true false
  rw [pairRelax_gap] at h1
  have hu : relaxU 1 0 = 1 := by simp [relaxU]
  rw [relaxAngle, hu, Real.arctan_one] at h1
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two] at h1
  norm_num at h1

/-! ### The potential falls to its minimum -/

/-- The dynamic potential along the relaxing trajectory, in closed form. -/
lemma pairRelax_potential (c t : ℝ) :
    kuramoto_potential_dynamic (pairSystem 0) (pairRelax c t)
      = -(1 + Real.cos (2 * relaxAngle c t)) := by
  simp only [kuramoto_potential_dynamic, pairSystem, Fintype.sum_bool, pairRelax]
  norm_num
  rw [show -relaxAngle c t - relaxAngle c t = -(2 * relaxAngle c t) by ring,
    show relaxAngle c t + relaxAngle c t = 2 * relaxAngle c t by ring, Real.cos_neg]
  ring

/-- The minimum value of the dynamic potential on this system. -/
lemma pairSystem_potential_min : kuramoto_potential_dynamic (pairSystem 0) (fun _ => 0) = -2 := by
  simp [kuramoto_potential_dynamic, pairSystem]

/-- **The potential falls to its global minimum along the trajectory.** -/
theorem pairRelax_potential_tendsto_min (c : ℝ) :
    Tendsto (fun t => kuramoto_potential_dynamic (pairSystem 0) (pairRelax c t)) atTop
      (𝓝 (kuramoto_potential_dynamic (pairSystem 0) (fun _ => 0))) := by
  rw [pairSystem_potential_min]
  have h : Tendsto (fun t => 2 * relaxAngle c t) atTop (𝓝 0) := by
    simpa using (relaxAngle_tendsto c).const_mul 2
  have h2 := (Real.continuous_cos.tendsto 0).comp h
  rw [Real.cos_zero] at h2
  have h3 : Tendsto (fun t => -(1 + Real.cos (2 * relaxAngle c t))) atTop (𝓝 (-(1 + 1))) := by
    exact (h2.const_add 1).neg
  have heq : (fun t => kuramoto_potential_dynamic (pairSystem 0) (pairRelax c t))
      = fun t => -(1 + Real.cos (2 * relaxAngle c t)) := by
    funext t; exact pairRelax_potential c t
  rw [heq]
  have : (-(1 + 1) : ℝ) = -2 := by norm_num
  rw [← this]
  exact h3

/-! ### The order parameter -/

/-- On two oscillators the squared order parameter is `(1 + cos Δ)/2`. -/
lemma pair_order_parameter (theta : Bool → ℝ) :
    order_parameter_r_sq theta = (1 + Real.cos (theta true - theta false)) / 2 := by
  simp only [order_parameter_r_sq, order_parameter_complex, Fintype.sum_bool]
  rw [Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  rw [mul_comm Complex.I _, mul_comm Complex.I _, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Real.cos_sub]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq (theta true), Real.sin_sq_add_cos_sq (theta false)]

/-- **The static order-parameter link: incoherent state.**
`order_parameter_complex` (discrete, empirical average over finitely many sites)
and `circularOrderParameter` (continuum integral against a density) agree on the
incoherent state: both are zero.

For the discrete side, opposite phases on two sites — `θ(false)=0`, `θ(true)=π` —
give `order_parameter_complex = 0`. For the continuum side, the uniform density
(von Mises at concentration zero) gives `circularOrderParameter = 0`.  This
isolates the mean-field limit (propagation of chaos) as the only remaining gap
between the two order-parameter notions. -/
theorem incoherent_orderParameters_agree :
    let theta : Bool → ℝ := fun b => if b then Real.pi else 0
    order_parameter_complex theta = 0 ∧
    circularOrderParameter (vonMisesDensity 0) = 0 :=
by
  intro theta
  constructor
  · unfold order_parameter_complex
    simp [theta, Complex.exp_zero]
    have h2 : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
      simpa [mul_comm] using Complex.exp_pi_mul_I
    simp [h2]
  · rw [circularOrderParameter_vonMises, besselRatio_zero]
    norm_num

/-- **The order parameter tends to 1 along the trajectory.** -/
theorem pairRelax_order_parameter_tendsto (c : ℝ) :
    Tendsto (fun t => order_parameter_r_sq (pairRelax c t)) atTop (𝓝 1) := by
  have heq : (fun t => order_parameter_r_sq (pairRelax c t))
      = fun t => (1 + Real.cos (pairRelax c t true - pairRelax c t false)) / 2 := by
    funext t; exact pair_order_parameter _
  rw [heq]
  have h := ((pairRelax_tendsto_locked c).const_add 1).div_const 2
  simpa using h

/-! ### The motion stops -/

/-- The velocity of the upper oscillator along the relaxing trajectory, in closed
form: it is exactly the derivative `hasDerivAt_relaxAngle` computes, which is
what makes `pairRelax` a solution in the first place. -/
lemma pairRelax_velocity (c t : ℝ) :
    kuramoto_velocity (pairSystem 0) (pairRelax c t) true
      = -2 * relaxU c t / (1 + relaxU c t ^ 2) := by
  have hsin := sin_two_arctan (relaxU c t)
  simp only [kuramoto_velocity, pairSystem, pairRelax, relaxAngle, Fintype.sum_bool]
  norm_num
  rw [show -Real.arctan (relaxU c t) - Real.arctan (relaxU c t)
      = -(2 * Real.arctan (relaxU c t)) by ring, Real.sin_neg, hsin]
  ring

/-- **The witness is not already at rest.** With `c = 1` the upper oscillator
moves at speed `1` at time zero, so the convergence below is a statement about a
trajectory that has somewhere to go. -/
theorem pairRelax_velocity_at_zero :
    kuramoto_velocity (pairSystem 0) (pairRelax 1 0) true = -1 := by
  rw [pairRelax_velocity]
  have hu : relaxU 1 0 = 1 := by simp [relaxU]
  rw [hu]; norm_num

/-- **O22 on the witness.** `velocity_sq_tendsto_zero` is a statement about an
arbitrary trajectory of an arbitrary zero-frequency system; here it fires on the
one trajectory this development writes down, whose velocity starts at `-1`
(`pairRelax_velocity_at_zero`) and is therefore genuinely decaying rather than
identically zero. -/
theorem pairRelax_velocity_sq_tendsto_zero (c : ℝ) :
    Tendsto (fun t => ∑ i, (kuramoto_velocity (pairSystem 0) (pairRelax c t) i) ^ 2)
      atTop (𝓝 0) :=
  velocity_sq_tendsto_zero (pairSystem 0) (fun _ => rfl) (pairRelax c)
    (pairRelax_is_trajectory c)

/-- **Uniqueness applied to the witness.** The relaxing trajectory is the *only*
solution through its initial state — so the convergence above is not a property
of a lucky choice among many solutions. -/
theorem pairRelax_unique (c : ℝ) (psi : ℝ → Bool → ℝ)
    (hpsi : is_kuramoto_trajectory (pairSystem 0) psi)
    (h0 : psi 0 = pairRelax c 0) : psi = pairRelax c :=
  is_kuramoto_trajectory_unique (pairSystem 0) psi (pairRelax c) hpsi
    (pairRelax_is_trajectory c) 0 h0

end RunningDynamics

/-!
## §16 — A symmetric kernel, and a one-way one that breaks the theorem

Open item **O11** asked whether `phase_locked_achieves_minimum_entropy`'s
`h_mean` hypothesis could be removed. It can, for symmetric kernels, and
`Phase8_ContinuousField` §2a proves it. This section discharges that theorem's
integrability hypotheses on a concrete substrate and then answers the question
the theorem itself cannot: whether the symmetry hypothesis that replaced
`h_mean` is doing work.

It is, and the check is a counterexample rather than a remark. `asymSys` is the
same two sites with a **one-way** coupling — `a` feels `b`, `b` does not feel
`a` — and there the phase-locked field is *strictly beaten*
(`asymSys_locked_not_minimal`): moving `b` to `−π/2` cancels `a`'s natural drift
without adding any drift at `b`, halving the entropy production. So
"phase-locking minimizes entropy production" is **false** for general kernels and
true for reciprocal ones, which is the physically intended case and the one
`ThermodynamicCover.A_symm` already imposes in Derivation 5.

Both systems live on the `Duo` substrate of §5, whose `volume` is counting
measure; `Integrable.of_finite` discharges every integrability hypothesis there,
including the one on the product measure that Fubini needs.
-/

section SymmetricKernel

/-- Counting measure on two sites is finite, which the variance bound needs. -/
instance : IsFiniteMeasure (volume : Measure Duo) := by
  constructor
  show (Measure.count : Measure Duo) Set.univ < ⊤
  rw [Measure.count_univ]; simp

/-- Entropy production on `Duo`, written out. Both integrals are sums against
counting measure, so the functional is four `sin` evaluations. -/
lemma duo_entropy (sys : StochasticNeuralField Duo) (theta : Duo → ℝ) :
    entropy_production_rate sys theta
      = (1/sys.D) * (sys.omega Duo.a + (sys.K Duo.a Duo.a * Real.sin (theta Duo.a - theta Duo.a)
          + sys.K Duo.a Duo.b * Real.sin (theta Duo.b - theta Duo.a)))^2
      + (1/sys.D) * (sys.omega Duo.b + (sys.K Duo.b Duo.a * Real.sin (theta Duo.a - theta Duo.b)
          + sys.K Duo.b Duo.b * Real.sin (theta Duo.b - theta Duo.b)))^2 := by
  unfold entropy_production_rate
  simp only [duo_volume, integral_count, duo_sum]

/-- Reciprocal coupling: every pair of sites influences the other equally. -/
noncomputable def symmSys : StochasticNeuralField Duo where
  omega := fun _ => 0
  K := fun _ _ => 1
  tau := 1
  D := 2
  h_D_pos := by norm_num
  Omega_avg := 0

theorem symmSys_symm : ∀ x y, symmSys.K x y = symmSys.K y x := fun _ _ => rfl

theorem symmSys_locked : is_dynamically_phase_locked symmSys (fun _ => 0) := by
  intro x
  show (0:ℝ) + ∫ y : Duo, (1:ℝ) * Real.sin (0 - 0) = 0
  simp

/-- **The unrestricted minimality theorem fires.** No `h_mean`: the conclusion
holds against *every* competitor field, with only integrability of its squared
drift assumed — and that is discharged here too, by finiteness. -/
theorem symmSys_minimizes :
    ∀ (t : Duo → ℝ) (_hf2 : Integrable
        (fun x => (symmSys.omega x + ∫ y : Duo, symmSys.K x y * Real.sin (t y - t x)) ^ 2)),
      entropy_production_rate symmSys (fun _ => 0) ≤ entropy_production_rate symmSys t :=
  (phase_locked_minimizes_entropy_of_symm symmSys (fun _ => 0) symmSys_symm symmSys_locked
    Integrable.of_finite (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite)).2

theorem symmSys_locked_entropy : entropy_production_rate symmSys (fun _ => 0) = 0 := by
  rw [duo_entropy]; norm_num [symmSys]

theorem symmSys_competitor_entropy : entropy_production_rate symmSys duoTheta = 1 := by
  rw [duo_entropy]
  norm_num [symmSys, duoTheta, Real.sin_pi_div_two]

/-- **The minimum is attained strictly.** `duoTheta` produces entropy `1` where
the locked field produces `0`, so `symmSys_minimizes` is not the observation that
every field is equally good. -/
theorem symmSys_gap :
    entropy_production_rate symmSys (fun _ => 0) < entropy_production_rate symmSys duoTheta := by
  rw [symmSys_locked_entropy, symmSys_competitor_entropy]; norm_num

/-- A **one-way** coupling: `a` feels `b`, `b` does not feel `a`. Physically this
is a directed synapse rather than a reciprocal field. -/
noncomputable def asymSys : StochasticNeuralField Duo where
  omega := fun _ => 1
  K := fun x y => if x = Duo.a ∧ y = Duo.b then 1 else 0
  tau := 1
  D := 2
  h_D_pos := by norm_num
  Omega_avg := 1

theorem asymSys_not_symm : ¬ ∀ x y, asymSys.K x y = asymSys.K y x := by
  intro h
  have hab := h Duo.a Duo.b
  simp [asymSys] at hab

theorem asymSys_locked : is_dynamically_phase_locked asymSys (fun _ => 0) := by
  intro x
  show (1:ℝ) + ∫ y : Duo, asymSys.K x y * Real.sin (0 - 0) = 1
  simp

/-- Phases `0` and `−π/2`. The one-way coupling subtracts exactly `a`'s natural
drift and adds nothing at `b`, which is what a reciprocal kernel cannot do. -/
noncomputable def asymTheta : Duo → ℝ
  | Duo.a => 0
  | Duo.b => -(Real.pi / 2)

theorem asymSys_locked_entropy : entropy_production_rate asymSys (fun _ => 0) = 1 := by
  rw [duo_entropy]; norm_num [asymSys]

theorem asymSys_competitor_entropy : entropy_production_rate asymSys asymTheta = 1/2 := by
  rw [duo_entropy]
  norm_num [asymSys, asymTheta, Real.sin_neg, Real.sin_pi_div_two]
  exact Or.inl (by decide)

/-- **Symmetry is necessary, not decorative.** Drop it and the theorem is false:
here a phase-locked field is strictly beaten by a competitor, so no amount of
extra work could remove `hK` from `phase_locked_minimizes_entropy_of_symm`.

This is the same kind of result as `contracting_implies_const` in §10 and
`ThermodynamicCover.phase_locked` in §13 — a proof that a hypothesis is as weak
as it can be made, rather than a hope that it is. -/
theorem asymSys_locked_not_minimal :
    entropy_production_rate asymSys asymTheta
      < entropy_production_rate asymSys (fun _ => 0) := by
  rw [asymSys_locked_entropy, asymSys_competitor_entropy]; norm_num

/-- The mechanism of the counterexample, isolated: for the one-way kernel the
total drift is *not* conserved, so `h_mean` fails and the variance bound has
nothing to stand on. Compare `total_drift_eq_of_symm`. -/
theorem asymSys_mean_drift_fails :
    (∫ x : Duo, (asymSys.omega x + ∫ y : Duo, asymSys.K x y
        * Real.sin (asymTheta y - asymTheta x)))
      ≠ asymSys.Omega_avg * (volume (Set.univ : Set Duo)).toReal := by
  have hlhs : (∫ x : Duo, (asymSys.omega x + ∫ y : Duo, asymSys.K x y
      * Real.sin (asymTheta y - asymTheta x))) = 1 := by
    simp only [duo_volume, integral_count, duo_sum]
    norm_num [asymSys, asymTheta, Real.sin_neg, Real.sin_pi_div_two]
    decide
  have hrhs : asymSys.Omega_avg * (volume (Set.univ : Set Duo)).toReal = 2 := by
    show (1:ℝ) * ((Measure.count : Measure Duo) Set.univ).toReal = 2
    rw [Measure.count_univ]
    have hcard : Fintype.card Duo = 2 := rfl
    simp [hcard]
  rw [hlhs, hrhs]; norm_num

end SymmetricKernel

/-! ## 17. A trajectory with no closed form that still reaches the minimum

  §15's `pairRelax` settles vacuity for O20 by exhibiting a trajectory that runs
  from an unsynchronised state into the potential's global minimum. It does so by
  *solving* the equation: on two oscillators the phase difference obeys a scalar
  ODE that integrates to `2 arctan(c e^{-2t})`, and every statement about it is a
  statement about that formula.

  That method does not scale, and it is the reason a general theorem was needed.
  On three sites the Kuramoto system has no closed-form solution, so nothing in
  §15's style can be repeated. This section runs the general theorem instead:
  `is_kuramoto_trajectory_exists` supplies a trajectory through an explicit
  initial configuration, and
  `kuramoto_tendsto_global_minimum` (`Phase4_RotatingFrame.lean` §7) proves it
  converges to a phase-locked configuration which is a global minimiser of the
  potential — with the trajectory itself never written down, and no formula for
  its limit.

  The initial data is `(0, 0, ½)`: two oscillators together and one displaced.
  It is genuinely unsynchronised (`trioStart_not_locked`), it satisfies the arc
  condition `|θᵢ - θⱼ| ≤ π/2`, and its excess `2(1 - cos ½)` is below the
  threshold `a/2 = ½` — the numerical content is `cos ½ > ¾`, which
  `Real.cos_bound` supplies.

  §17.1 then builds a `ThermodynamicCover` on that limit. This is what discharges
  `ThermodynamicCover.thermodynamic_equilibrium` on an instance rather than
  assuming it: the configuration the cover is required to sit at is *reached*,
  from data that does not start there.
-/

section TrioDynamics

open Filter Topology

/-- Three sites, unit coupling, no natural frequencies. -/
noncomputable def trioSys : KuramotoSystem (Fin 3) where
  omega := fun _ => 0
  A := fun _ _ => 1
  symm := fun _ _ => rfl

/-- Two oscillators together and one displaced by a half radian. -/
noncomputable def trioStart : Fin 3 → ℝ := ![0, 0, 1/2]

lemma trioSys_omega : ∀ i, trioSys.omega i = 0 := fun _ => rfl

lemma trioSys_coupling : ∀ i j, (1:ℝ) ≤ trioSys.A i j := fun _ _ => le_rfl

/-- `cos ½ > ¾`, from the quartic Taylor bound. This is the whole numerical
content of the witness. -/
lemma cos_half_gt : (3:ℝ)/4 < Real.cos (1/2) := by
  have h := Real.cos_bound (x := 1/2) (by rw [abs_of_nonneg] <;> norm_num)
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
  have h2 := abs_le.mp h
  norm_num at h2 ⊢
  linarith [h2.1]

lemma cos_half_lt_one : Real.cos (1/2) < 1 := by
  have h := Real.cos_bound (x := 1/2) (by rw [abs_of_nonneg] <;> norm_num)
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
  have h2 := abs_le.mp h
  norm_num at h2 ⊢
  linarith [h2.2]

/-- The excess of the initial configuration above the minimum: four of the nine
ordered pairs see the displacement. -/
lemma trioStart_excess :
    potentialExcess trioSys trioStart = 2 * (1 - Real.cos (1/2)) := by
  rw [potentialExcess_eq]
  simp only [trioSys, trioStart, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [show (0:ℝ) - 0 = 0 by ring, show (1:ℝ)/2 - 0 = 1/2 by ring,
    show (0:ℝ) - 1/2 = -(1/2) by ring, show (1:ℝ)/2 - 1/2 = 0 by ring]
  rw [Real.cos_neg, Real.cos_zero]
  ring

/-- The initial configuration is **not** phase-locked: it is not placed at the
limit it will reach. -/
theorem trioStart_not_locked : ¬ is_phase_locked trioStart := by
  intro h
  have := h 2 0
  simp only [trioStart, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at this
  rw [show (1:ℝ)/2 - 0 = 1/2 by ring] at this
  linarith [cos_half_lt_one, this]

lemma trioStart_small : 2 * potentialExcess trioSys trioStart < 1 := by
  rw [trioStart_excess]
  linarith [cos_half_gt]

lemma trioStart_init : ∀ i j, |trioStart i - trioStart j| ≤ Real.pi/2 := by
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [trioStart] <;>
    rw [abs_le] <;> constructor <;> norm_num <;> linarith

/-- **The general theorem, fired on a trajectory nobody can write down.**

There is a Kuramoto trajectory on three sites through the unsynchronised
configuration `(0, 0, ½)`, and it converges to a phase-locked configuration that
minimises the dynamic potential and carries order parameter `r² = 1`.

Neither the trajectory nor its limit is exhibited by a formula — the trajectory
comes from `is_kuramoto_trajectory_exists` and the limit from
`kuramoto_tendsto_global_minimum`, which builds it as `θ(0) + ∫₀^∞ θ̇`. This is
the sense in which §7 says more than §15: three-oscillator Kuramoto has no closed
form, so §15's method cannot produce this statement at any effort. -/
theorem trio_reaches_minimum :
    ∃ theta : ℝ → Fin 3 → ℝ,
      is_kuramoto_trajectory trioSys theta
      ∧ theta 0 = trioStart
      ∧ ¬ is_phase_locked (theta 0)
      ∧ ∃ thetaInf : Fin 3 → ℝ,
          (∀ i, Tendsto (fun t => theta t i) atTop (𝓝 (thetaInf i)))
          ∧ is_phase_locked thetaInf
          ∧ (∀ phi, kuramoto_potential_dynamic trioSys thetaInf
                ≤ kuramoto_potential_dynamic trioSys phi)
          ∧ order_parameter_r_sq thetaInf = 1 := by
  obtain ⟨theta, h_traj, h0⟩ := is_kuramoto_trajectory_exists trioSys 0 trioStart
  refine ⟨theta, h_traj, h0, by rw [h0]; exact trioStart_not_locked, ?_⟩
  exact kuramoto_tendsto_global_minimum trioSys trioSys_omega one_pos trioSys_coupling
    theta h_traj (by rw [h0]; exact trioStart_small) (by rw [h0]; exact trioStart_init)

end TrioDynamics

/-! ## 32. Two sites, two legal covers, two answers

`exists_isUniformCover_mean_patch_order_eq_one` says maximal patch agreement is
available on some legal cover, for every configuration. On its own that could be
read as a defect of the observable, so this section fences that reading: patch
order on a *fixed* cover is a real measurement of the state, and here it returns
zero.

Two sites in antiphase. The global resultant is zero. The one-patch cover — both
sites in one patch, each site in one patch, a legal `IsUniformCover` with
`c = 2`, `m = 1` — reports zero as well. The cover by single sites reports one.
One configuration, two legal covers, the two ends of the range, so what moved the
answer was the choice and not the state.

This is the cover-side counterpart of the avatar region of
`Phase6_Reconstruction`: nothing here says either cover is the wrong one to use.
It says which one is used is part of the claim. -/

section CoverChoice

/-- Two sites in antiphase. The same configuration appears in the agency
regressions under its own name; it is spelled again here because this section is
about covers of it rather than about content. -/
noncomputable def pairAntiphase : Fin 2 → ℝ := ![0, Real.pi]

/-- **The global resultant is zero.** The two phasors cancel. -/
theorem pairAntiphase_incoherent : order_parameter_r_sq pairAntiphase = 0 := by
  have hsum : ∑ i : Fin 2, Complex.exp (Complex.I * (pairAntiphase i : ℂ)) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [pairAntiphase, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [mul_comm, Complex.exp_pi_mul_I]
    ring
  rw [order_parameter_r_sq, order_parameter_complex, hsum, mul_zero, map_zero]

/-- Both sites in a single patch: the coarsest cover of two sites, and a
partition rather than an overlapping family. -/
def bothCover : Fin 1 → Finset (Fin 2) := fun _ => {0, 1}

/-- It is a legal cover: every patch holds two sites and every site lies in one
patch. -/
theorem isUniformCover_bothCover : IsUniformCover bothCover 2 1 where
  card_patch := by decide
  multiplicity := by decide

/-- The patch's resultant vanishes: within the one patch the two phasors are the
ones that cancel. -/
theorem patch_resultant_bothCover (b : Fin 1) :
    patch_resultant pairAntiphase (bothCover b) = 0 := by
  have hsum : ∑ i ∈ bothCover b, Complex.exp (Complex.I * (pairAntiphase i : ℂ)) = 0 := by
    show ∑ i ∈ ({0, 1} : Finset (Fin 2)), Complex.exp (Complex.I * (pairAntiphase i : ℂ)) = 0
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [pairAntiphase, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [mul_comm, Complex.exp_pi_mul_I]
    ring
  rw [patch_resultant, hsum, mul_zero]

/-- **A fixed legal cover reports zero.** Patch order is not identically one: on
this cover it measures the state, and the state is incoherent. -/
theorem mean_patch_order_bothCover : mean_patch_order pairAntiphase bothCover = 0 := by
  rw [mean_patch_order]
  simp [patch_resultant_bothCover]

/-- …and the finest legal cover reports one on the same configuration. -/
theorem mean_patch_order_singleton_pairAntiphase :
    mean_patch_order pairAntiphase (fun i : Fin 2 => ({i} : Finset (Fin 2))) = 1 :=
  mean_patch_order_singleton pairAntiphase

/-- **The choice is the whole difference.** One configuration whose global
resultant is zero; two covers, both legal; the reported agreement is zero on one
and one on the other. A patch-agreement claim that does not say which cover it
was measured on has not said what it measured. -/
theorem mean_patch_order_depends_on_cover :
    order_parameter_r_sq pairAntiphase = 0
      ∧ IsUniformCover bothCover 2 1
      ∧ mean_patch_order pairAntiphase bothCover = 0
      ∧ IsUniformCover (fun i : Fin 2 => ({i} : Finset (Fin 2))) 1 1
      ∧ mean_patch_order pairAntiphase (fun i : Fin 2 => ({i} : Finset (Fin 2))) = 1 :=
  ⟨pairAntiphase_incoherent, isUniformCover_bothCover, mean_patch_order_bothCover,
    isUniformCover_singleton, mean_patch_order_singleton_pairAntiphase⟩

end CoverChoice

end Examples
end PhysicsOfConsciousness
