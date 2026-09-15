import Mathlib
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics

open Finset Set Filter Topology Complex

namespace PhysicsOfConsciousness

variable {V : Type*} [Fintype V] [DecidableEq V]

-- 1. Dynamical Trajectories
-- A trajectory is a time-parameterized family of phases satisfying the Kuramoto ODEs
def is_kuramoto_trajectory (sys : KuramotoSystem V) (theta : ℝ → V → ℝ) : Prop :=
  ∀ (i : V) (t : ℝ), 
    HasDerivAt (fun t => theta t i) 
      (sys.omega i + ∑ j, sys.A i j * Real.sin (theta t j - theta t i)) t

omit [DecidableEq V] in
/-- `is_kuramoto_trajectory` is exactly "integral curve of `kuramotoField`". The
definition above is stated componentwise, which is what the descent results
want; the ODE library wants the bundled form. On a finite index type
`hasDerivAt_pi` says the two are the same thing. -/
lemma is_kuramoto_trajectory_iff (sys : KuramotoSystem V) (theta : ℝ → V → ℝ) :
    is_kuramoto_trajectory sys theta ↔ ∀ t, HasDerivAt theta (kuramotoField sys (theta t)) t :=
  ⟨fun h t => hasDerivAt_pi.2 fun i => h i t, fun h i t => hasDerivAt_pi.1 (h t) i⟩

omit [DecidableEq V] in
/-- **Kuramoto trajectories are determined by their value at any one time.**
Two solutions of the same system agreeing at a single instant agree for all
time, forwards *and* backwards, on all of `ℝ`.

This is Picard–Lindelöf uniqueness, and it is global rather than local because
`kuramotoField_lipschitz` is global: the field is Lipschitz on the whole state
space, not merely on a ball, so no continuation argument is needed.

Existence is the companion statement and is proved separately, in
`is_kuramoto_trajectory_exists` below; `kuramoto_cauchy_problem` packages the
two into one `ExistsUnique`. -/
theorem is_kuramoto_trajectory_unique (sys : KuramotoSystem V)
    (theta psi : ℝ → V → ℝ)
    (hth : is_kuramoto_trajectory sys theta) (hps : is_kuramoto_trajectory sys psi)
    (t₀ : ℝ) (h0 : theta t₀ = psi t₀) : theta = psi :=
  ODE_solution_unique_univ (K := Real.toNNReal (2 * ∑ i, ∑ j, |sys.A i j|))
    (v := fun _ => kuramotoField sys) (s := fun _ => Set.univ) (t₀ := t₀)
    (fun _ => (kuramotoField_lipschitz sys).lipschitzOnWith)
    (fun t => ⟨(is_kuramoto_trajectory_iff sys theta).1 hth t, trivial⟩)
    (fun t => ⟨(is_kuramoto_trajectory_iff sys psi).1 hps t, trivial⟩) h0

omit [DecidableEq V] in
/-- **Local existence on a symmetric window** `(t₀ - T, t₀ + T)`, for every
`T > 0`.

This is Picard–Lindelöf, and the only work is in checking `IsPicardLindelof`.
Its `mul_max_le` field asks for `L · T ≤ a - r`, where `a` is the radius of the
ball on which the sup bound `L` and the Lipschitz constant hold: existence is
guaranteed only for as long as the flow cannot leave that ball. For a field
bounded and Lipschitz on the *whole* space — which is what
`kuramotoField_norm_le` and `kuramotoField_lipschitz` give — the constraint is
vacuous, because `a := L·T` may be chosen after `T`. Taking `r = 0` puts the
initial state at the centre of the ball.

Mathlib delivers a `HasDerivWithinAt` on the closed interval; on the open
interval that upgrades to `HasDerivAt`, since `Icc (t₀ - T) (t₀ + T)` is a
neighbourhood of each of its interior points. -/
private lemma kuramoto_exists_on_window (sys : KuramotoSystem V) (t₀ : ℝ) (x₀ : V → ℝ)
    {T : ℝ} (hT : 0 < T) :
    ∃ alpha : ℝ → V → ℝ, alpha t₀ = x₀ ∧
      ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T), HasDerivAt alpha (kuramotoField sys (alpha t)) t := by
  set Lb : ℝ := (∑ i, |sys.omega i|) + ∑ i, ∑ j, |sys.A i j| with hLbdef
  have hLb0 : 0 ≤ Lb := by
    have h1 : (0:ℝ) ≤ ∑ i, |sys.omega i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have h2 : (0:ℝ) ≤ ∑ i, ∑ j, |sys.A i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  have hpl : IsPicardLindelof (E := V → ℝ) (fun _ : ℝ => kuramotoField sys)
      (tmin := t₀ - T) (tmax := t₀ + T) ⟨t₀, by constructor <;> linarith⟩ x₀
      (Real.toNNReal (Lb * T)) 0 (Real.toNNReal Lb)
      (Real.toNNReal (2 * ∑ i, ∑ j, |sys.A i j|)) := by
    refine IsPicardLindelof.of_time_independent (fun x _ => ?_)
      ((kuramotoField_lipschitz sys).lipschitzOnWith) ?_
    · rw [Real.coe_toNNReal _ hLb0]; exact kuramotoField_norm_le sys x
    · have hmax : max (t₀ + T - t₀) (t₀ - (t₀ - T)) = T := by simp [max_self]
      rw [Real.coe_toNNReal _ hLb0, Real.coe_toNNReal _ (by positivity)]
      simp only [NNReal.coe_zero, sub_zero]
      rw [hmax]
  obtain ⟨alpha, halpha0, halpha⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨alpha, halpha0, fun t ht =>
    (halpha t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

omit [DecidableEq V] in
/-- **Every initial state launches a trajectory, defined for all time.**
Together with `is_kuramoto_trajectory_unique` this makes the Kuramoto initial
value problem well-posed on all of `ℝ`, and it settles open item **O20(a)**.

The proof is the gluing that the file previously lacked. Mathlib has no
global-in-time existence theorem — `IsPicardLindelof` builds its solution as a
fixed point in a function space on a *bounded* interval, and the interval's
length is capped by the ball radius over the field's sup norm. What rescues the
statement is that for this field the cap is not binding: by
`kuramotoField_norm_le` and `kuramotoField_lipschitz` the hypotheses hold on
every ball, so `kuramoto_exists_on_window` produces a solution `αₙ` on
`(t₀ - n - 1, t₀ + n + 1)` for every `n`. Uniqueness on an interval
(`ODE_solution_unique_of_mem_Ioo`) makes the family coherent — `αₘ` and `αₙ`
agree wherever both are defined — and

    θ(t) := α_{⌈|t - t₀|⌉} (t)

is then a solution on all of `ℝ`. The derivative at `t` is read off the single
solution `αₙ`, `n := ⌈|t - t₀|⌉`: on the whole window of `αₙ` the glued function
agrees with it — whatever index `⌈|s - t₀|⌉` takes there, coherence identifies
the two — so `θ =ᶠ[𝓝 t] αₙ` and `θ` inherits `αₙ`'s derivative.

**What it does not establish.** Nothing about the trajectory's behaviour: this
says a solution exists, not that it converges, and not that it phase-locks. For
a trajectory that provably runs into the potential minimum see `Examples.lean`
§15; for why convergence in general is still open see the scope note there and
`potential_min_iff_phase_locked`. -/
theorem is_kuramoto_trajectory_exists (sys : KuramotoSystem V) (t₀ : ℝ) (x₀ : V → ℝ) :
    ∃ theta : ℝ → V → ℝ, is_kuramoto_trajectory sys theta ∧ theta t₀ = x₀ := by
  classical
  have hloc : ∀ n : ℕ, ∃ alpha : ℝ → V → ℝ, alpha t₀ = x₀ ∧
      ∀ t ∈ Set.Ioo (t₀ - ((n:ℝ)+1)) (t₀ + ((n:ℝ)+1)),
        HasDerivAt alpha (kuramotoField sys (alpha t)) t := fun n =>
    kuramoto_exists_on_window sys t₀ x₀ (by positivity)
  choose alpha halpha0 halpha using hloc
  -- The windows are nested and each solution is unique on its own window, so the
  -- family is coherent: a shorter window's solution agrees with every longer one.
  have hconsist : ∀ m n : ℕ, m ≤ n → ∀ s : ℝ, |s - t₀| < (m:ℝ) + 1 →
      alpha m s = alpha n s := by
    intro m n hmn s hs
    have hmn' : (m:ℝ) + 1 ≤ (n:ℝ) + 1 := by
      have : (m:ℝ) ≤ (n:ℝ) := Nat.cast_le.mpr hmn
      linarith
    have hsub : Set.Ioo (t₀ - ((m:ℝ)+1)) (t₀ + ((m:ℝ)+1))
        ⊆ Set.Ioo (t₀ - ((n:ℝ)+1)) (t₀ + ((n:ℝ)+1)) :=
      Set.Ioo_subset_Ioo (by linarith) (by linarith)
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have hmem : s ∈ Set.Ioo (t₀ - ((m:ℝ)+1)) (t₀ + ((m:ℝ)+1)) := by
      rw [abs_lt] at hs; constructor <;> [linarith [hs.1]; linarith [hs.2]]
    have ht₀mem : t₀ ∈ Set.Ioo (t₀ - ((m:ℝ)+1)) (t₀ + ((m:ℝ)+1)) := by
      constructor <;> linarith
    exact ODE_solution_unique_of_mem_Ioo
      (K := Real.toNNReal (2 * ∑ i, ∑ j, |sys.A i j|))
      (v := fun _ => kuramotoField sys) (s := fun _ => Set.univ)
      (fun t _ => (kuramotoField_lipschitz sys).lipschitzOnWith) ht₀mem
      (fun t ht => ⟨halpha m t ht, trivial⟩)
      (fun t ht => ⟨halpha n t (hsub ht), trivial⟩)
      (by rw [halpha0 m, halpha0 n]) hmem
  set theta : ℝ → V → ℝ := fun t => alpha ⌈|t - t₀|⌉₊ t with hthdef
  -- On any window, the glued function is the solution indexed by that window.
  have key : ∀ n : ℕ, ∀ s : ℝ, |s - t₀| < (n:ℝ) + 1 → theta s = alpha n s := by
    intro n s hs
    rcases le_total ⌈|s - t₀|⌉₊ n with h | h
    · exact hconsist _ n h s (lt_of_le_of_lt (Nat.le_ceil _) (by linarith))
    · exact (hconsist n _ h s hs).symm
  have hderiv : ∀ t, HasDerivAt theta (kuramotoField sys (theta t)) t := by
    intro t
    have htn : |t - t₀| ≤ (⌈|t - t₀|⌉₊ : ℝ) := Nat.le_ceil _
    set n : ℕ := ⌈|t - t₀|⌉₊ with hn
    have h1 : |t - t₀| < (n:ℝ) + 1 := by linarith
    rw [abs_lt] at h1
    have hnbhd : Set.Ioo (t₀ - ((n:ℝ)+1)) (t₀ + ((n:ℝ)+1)) ∈ 𝓝 t :=
      Ioo_mem_nhds (by linarith [h1.1]) (by linarith [h1.2])
    have heq : theta =ᶠ[𝓝 t] alpha n := by
      filter_upwards [hnbhd] with s hs
      exact key n s (by rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    have hthetat : theta t = alpha n t :=
      key n t (by rw [abs_lt]; exact ⟨by linarith, by linarith⟩)
    rw [hthetat]
    exact (halpha n t ⟨by linarith [h1.1], by linarith [h1.2]⟩).congr_of_eventuallyEq heq
  refine ⟨theta, (is_kuramoto_trajectory_iff sys theta).2 hderiv, ?_⟩
  show alpha ⌈|t₀ - t₀|⌉₊ t₀ = x₀
  simpa using halpha0 ⌈|t₀ - t₀|⌉₊

omit [DecidableEq V] in
/-- **The Kuramoto initial value problem is well-posed.** Through every state,
at every instant, there passes exactly one trajectory, and it is defined on all
of `ℝ`.

This is `is_kuramoto_trajectory_exists` and `is_kuramoto_trajectory_unique` in
one statement. Its point is that `is_kuramoto_trajectory` is not an
under-inhabited predicate: the development's dynamical results quantify over a
family that is exactly as large as the state space, one trajectory per initial
condition. -/
theorem kuramoto_cauchy_problem (sys : KuramotoSystem V) (t₀ : ℝ) (x₀ : V → ℝ) :
    ∃! theta : ℝ → V → ℝ, is_kuramoto_trajectory sys theta ∧ theta t₀ = x₀ := by
  obtain ⟨theta, hth, hth0⟩ := is_kuramoto_trajectory_exists sys t₀ x₀
  exact ⟨theta, ⟨hth, hth0⟩, fun psi hpsi =>
    is_kuramoto_trajectory_unique sys psi theta hpsi.1 hth t₀ (by rw [hpsi.2, hth0])⟩

-- 2. Macroscopic Order Parameter
noncomputable def order_parameter_complex (theta : V → ℝ) : ℂ :=
  (1 / (Fintype.card V : ℂ)) * ∑ j, Complex.exp (I * (theta j : ℂ))

noncomputable def order_parameter_r_sq (theta : V → ℝ) : ℝ :=
  Complex.normSq (order_parameter_complex theta)

def is_phase_locked (theta : V → ℝ) : Prop :=
  ∀ i j, Real.cos (theta i - theta j) = 1

private lemma exp_eq_of_cos_eq_one (x y : ℝ) (h : Real.cos (x - y) = 1) :
  Complex.exp (I * (x : ℂ)) = Complex.exp (I * (y : ℂ)) := by
  have h1 : (Real.cos (x - y) : ℂ) + (Real.sin (x - y) : ℂ) * I = 1 := by
    have h2 : Real.sin (x - y) = 0 := by
      have : Real.cos (x - y) ^ 2 + Real.sin (x - y) ^ 2 = 1 := Real.cos_sq_add_sin_sq (x - y)
      rw [h] at this
      have : Real.sin (x - y) ^ 2 = 0 := by linarith
      exact sq_eq_zero_iff.mp this
    rw [h, h2]
    simp
  have h2 : Complex.exp (I * ((x - y) : ℂ)) = 1 := by
    rw [mul_comm I _, Complex.exp_mul_I]
    exact_mod_cast h1
  have h3 : Complex.exp (I * (x : ℂ)) * Complex.exp (-I * (y : ℂ)) = 1 := by
    calc Complex.exp (I * (x : ℂ)) * Complex.exp (-I * (y : ℂ))
      _ = Complex.exp (I * x - I * y) := by rw [← Complex.exp_add]; ring_nf
      _ = Complex.exp (I * (x - y)) := by congr 1; ring
      _ = 1 := h2
  calc Complex.exp (I * (x : ℂ))
    _ = Complex.exp (I * (x : ℂ)) * Complex.exp (-I * (y : ℂ)) * Complex.exp (I * (y : ℂ)) := by
      rw [mul_assoc, ← Complex.exp_add]
      have : -I * (y:ℂ) + I * (y:ℂ) = 0 := by ring
      rw [this, Complex.exp_zero, mul_one]
    _ = 1 * Complex.exp (I * (y : ℂ)) := by rw [h3]
    _ = Complex.exp (I * (y : ℂ)) := one_mul _

omit [DecidableEq V] in
theorem phase_locked_implies_r_sq_eq_one [Nonempty V] (theta : V → ℝ) (h_lock : is_phase_locked theta) :
  order_parameter_r_sq theta = 1 := by
  obtain ⟨v0⟩ := id ‹Nonempty V›
  have H : ∀ j, Complex.exp (I * (theta j : ℂ)) = Complex.exp (I * (theta v0 : ℂ)) := fun j =>
    exp_eq_of_cos_eq_one (theta j) (theta v0) (h_lock j v0)
  unfold order_parameter_r_sq order_parameter_complex
  simp [H]
  rw [Complex.normSq_eq_norm_sq]
  have h1 : ‖Complex.exp (I * (theta v0 : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I (theta v0)
  rw [h1]
  simp

-- 3. The Lyapunov potential derived from heat dissipation minimization
noncomputable def kuramoto_potential_dynamic (sys : KuramotoSystem V) (theta : V → ℝ) : ℝ :=
  - (1 / 2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta j - theta i)

omit [DecidableEq V] in
/--
**The constant configuration is a global minimum of the reduced potential, for a
positively coupled system.**

`h_pos` is not a technical convenience and it is the hypothesis that divides this
development in two. `KuramotoSystem.A` is `V → V → ℝ`, symmetric and otherwise
unconstrained, so *signed* — frustrated — couplings are representable in the
setting. But every result here that says where the dynamics ends assumes
positivity: this theorem, `potential_min_iff_phase_locked` below, the class field
`Phase5_GlobalSection.ThermodynamicCover.A_pos` (hence every conclusion of
Derivation 5), and `Phase4_RotatingFrame.kuramoto_tendsto_global_minimum`, which
needs the strictly stronger uniform bound `0 < a ≤ A i j` because `a` enters the
Łojasiewicz constant. A system satisfying `h_pos` is an unfrustrated ferromagnet
whose potential has a single minimum up to a global phase shift.

By contrast, nothing about the sign of `A` is used by `is_kuramoto_trajectory_exists`
or `is_kuramoto_trajectory_unique`, by `Phase4_RotatingFrame.dynamic_potential_antitone`
and `dynamic_potential_tendsto`, or by `velocity_sq_tendsto_zero`. **That** the
motion stops is frustration-agnostic; **where** it stops is not.

This matters outside Lean. The manuscript grounds the substrate's memory capacity
in geometric frustration — a jagged landscape of near-degenerate states — which is
exactly what `h_pos` excludes. The system that stores memory and the system these
theorems describe are not the same system, and the manuscript now scopes the
frustration claim out of the chain rather than asserting it beside theorems that
rule it out.
-/
theorem phase_locked_minimizes_potential 
  (sys : KuramotoSystem V) (h_pos : ∀ i j, sys.A i j > 0) (theta : V → ℝ) :
  kuramoto_potential_dynamic sys (fun _ => 0) ≤ kuramoto_potential_dynamic sys theta := by
  unfold kuramoto_potential_dynamic
  apply mul_le_mul_of_nonpos_left
  · apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    have h1 : Real.cos ((fun _ => (0 : ℝ)) j - (fun _ => (0 : ℝ)) i) = 1 := by simp
    rw [h1]
    have h2 : Real.cos (theta j - theta i) ≤ 1 := Real.cos_le_one (theta j - theta i)
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt (h_pos i j))
  · norm_num

omit [DecidableEq V] in
/-- **Every phase-locked configuration is a global minimum**, not just the
constant one. `phase_locked_minimizes_potential` proves it for `theta ≡ 0`;
since the potential only sees the phase *differences*, and `is_phase_locked`
says every difference has cosine `1`, the value at any locked configuration is
the same number `-½ ∑ᵢⱼ Aᵢⱼ`.

This is the converse of `potential_min_implies_phase_locked`, and the two
together (`potential_min_iff_phase_locked`) say the minimisers of the reduced
potential are *exactly* the locked states. Its use is in Phase 5: a
`ThermodynamicCover` may carry a phase field that is not the constant function,
provided the values differ by multiples of `2π`. -/
theorem phase_locked_minimizes_potential'
    (sys : KuramotoSystem V) (h_pos : ∀ i j, sys.A i j > 0) (theta : V → ℝ)
    (h_lock : is_phase_locked theta) (phi : V → ℝ) :
    kuramoto_potential_dynamic sys theta ≤ kuramoto_potential_dynamic sys phi := by
  have h_const : kuramoto_potential_dynamic sys theta
      = kuramoto_potential_dynamic sys (fun _ => 0) := by
    unfold kuramoto_potential_dynamic
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h_lock j i]
    simp
  rw [h_const]
  exact phase_locked_minimizes_potential sys h_pos phi

omit [DecidableEq V] in
lemma potential_min_implies_phase_locked
  (sys : KuramotoSystem V) (h_pos : ∀ i j, sys.A i j > 0)
  (theta : V → ℝ)
  (h_min : ∀ phi, kuramoto_potential_dynamic sys theta ≤ kuramoto_potential_dynamic sys phi) :
  is_phase_locked theta := by
  have h1 : kuramoto_potential_dynamic sys theta ≤ kuramoto_potential_dynamic sys (fun _ => 0) := h_min (fun _ => 0)
  have h2 : kuramoto_potential_dynamic sys (fun _ => 0) = - (1 / 2) * ∑ i, ∑ j, sys.A i j := by
    unfold kuramoto_potential_dynamic
    simp
  have h3 : kuramoto_potential_dynamic sys theta = - (1 / 2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta j - theta i) := by
    unfold kuramoto_potential_dynamic
    rfl
  have h4 : - (1 / 2) * ∑ i, ∑ j, sys.A i j * Real.cos (theta j - theta i) ≤ - (1 / 2) * ∑ i, ∑ j, sys.A i j := by
    rw [h2, h3] at h1
    exact h1
  have h5 : ∑ i, ∑ j, sys.A i j ≤ ∑ i, ∑ j, sys.A i j * Real.cos (theta j - theta i) := by
    linarith [h4]
  have h6 : ∑ i, ∑ j, sys.A i j * (1 - Real.cos (theta j - theta i)) ≤ 0 := by
    calc ∑ i, ∑ j, sys.A i j * (1 - Real.cos (theta j - theta i))
      _ = ∑ i, ∑ j, (sys.A i j - sys.A i j * Real.cos (theta j - theta i)) := by congr; ext; congr; ext; ring
      _ = (∑ i, ∑ j, sys.A i j) - (∑ i, ∑ j, sys.A i j * Real.cos (theta j - theta i)) := by
        simp only [sum_sub_distrib]
      _ ≤ 0 := sub_nonpos.mpr h5
  
  intro i j
  have h_nonneg : ∀ i j, (0 : ℝ) ≤ sys.A i j * (1 - Real.cos (theta j - theta i)) := by
    intro i1 j1
    have : (0 : ℝ) ≤ sys.A i1 j1 := le_of_lt (h_pos i1 j1)
    have : (0 : ℝ) ≤ 1 - Real.cos (theta j1 - theta i1) := sub_nonneg.mpr (Real.cos_le_one (theta j1 - theta i1))
    positivity
  
  have h_sum_zero : ∑ i, ∑ j, sys.A i j * (1 - Real.cos (theta j - theta i)) = 0 := by
    have h_nonneg_sum : (0 : ℝ) ≤ ∑ i, ∑ j, sys.A i j * (1 - Real.cos (theta j - theta i)) :=
      sum_nonneg (s := univ) (fun i1 _ => sum_nonneg (s := univ) (fun j1 _ => h_nonneg i1 j1))
    linarith [h_nonneg_sum]
  
  have h_term_zero : sys.A i j * (1 - Real.cos (theta j - theta i)) = 0 := by
    have h_inner_sum : ∑ j1, sys.A i j1 * (1 - Real.cos (theta j1 - theta i)) = 0 := by
      have h_sum1 : ∀ i1 ∈ (univ : Finset V), (0 : ℝ) ≤ ∑ j1, sys.A i1 j1 * (1 - Real.cos (theta j1 - theta i1)) :=
        fun i1 _ => sum_nonneg (s := univ) (fun j1 _ => h_nonneg i1 j1)
      exact (sum_eq_zero_iff_of_nonneg h_sum1).mp h_sum_zero i (mem_univ i)
    exact (sum_eq_zero_iff_of_nonneg (fun j1 _ => h_nonneg i j1)).mp h_inner_sum j (mem_univ j)
  
  have h_1_minus_cos : 1 - Real.cos (theta j - theta i) = 0 := by
    cases mul_eq_zero.mp h_term_zero with
    | inl h => linarith [h_pos i j]
    | inr h => exact h
  have hcos1 : Real.cos (theta j - theta i) = 1 := by linarith
  have hcos2 : Real.cos (theta i - theta j) = 1 := by
    rw [← Real.cos_neg]
    have : -(theta i - theta j) = theta j - theta i := by ring
    rw [this]
    exact hcos1
  exact hcos2

omit [DecidableEq V] in
/-- **The minimisers of the reduced Kuramoto potential are exactly the
phase-locked states.** Both directions, in one statement.

What it does not say: nothing here is about the *dynamics*. This characterises
the minimisers of a functional. That a trajectory of `is_kuramoto_trajectory`
reaches one of them is `kuramoto_tendsto_global_minimum` in
`Phase4_RotatingFrame.lean` §7, and it holds under hypotheses on the initial
data — unconditionally it is false, since splay and twisted configurations are
equilibria too. -/
theorem potential_min_iff_phase_locked
    (sys : KuramotoSystem V) (h_pos : ∀ i j, sys.A i j > 0) (theta : V → ℝ) :
    (∀ phi, kuramoto_potential_dynamic sys theta ≤ kuramoto_potential_dynamic sys phi)
      ↔ is_phase_locked theta :=
  ⟨potential_min_implies_phase_locked sys h_pos theta,
   fun h_lock => phase_locked_minimizes_potential' sys h_pos theta h_lock⟩

/-! ## 6. Coherence as a quantitative bound on phase disagreement

`phase_locked_implies_r_sq_eq_one` is the exact endpoint of a scale that is
otherwise missing: below perfect locking, the order parameter says nothing here
about how far apart two individual phases are. The results in this section
supply that scale, and they are what carries coupling-gated coherence into the
content agreement of `Phase5_ContentDynamics`.

The step that makes it work is the identity `N² r² = ∑ᵢ∑ⱼ cos(θᵢ − θⱼ)`. Every
summand of `1 − cos` is nonnegative, so a *single* pair is bounded by the whole
double sum: a global average controls each local difference, with a factor `N²`
that is the honest price of extracting a pointwise statement from a mean.
-/

omit [DecidableEq V] in
private lemma exp_I_re (t : ℝ) : (Complex.exp (Complex.I * (t : ℂ))).re = Real.cos t := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re]

omit [DecidableEq V] in
private lemma exp_I_im (t : ℝ) : (Complex.exp (Complex.I * (t : ℂ))).im = Real.sin t := by
  rw [mul_comm, Complex.exp_mul_I]
  simp [Complex.sin_ofReal_re]

omit [DecidableEq V] in
/-- **The order parameter is the mean pairwise phase cosine.** Stated multiplied
through by `N²` so that no division appears and no nonvanishing side condition
is needed beyond `Nonempty`. -/
theorem order_parameter_r_sq_eq_mean_cos [Nonempty V] (theta : V → ℝ) :
    (Fintype.card V : ℝ) ^ 2 * order_parameter_r_sq theta
      = ∑ i, ∑ j, Real.cos (theta i - theta j) := by
  have hNr : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set S : ℂ := ∑ j, Complex.exp (Complex.I * (theta j : ℂ)) with hS
  have h1 : S.re = ∑ j, Real.cos (theta j) := by
    rw [hS, Complex.re_sum]
    exact Finset.sum_congr rfl fun j _ => exp_I_re (theta j)
  have h2 : S.im = ∑ j, Real.sin (theta j) := by
    rw [hS, Complex.im_sum]
    exact Finset.sum_congr rfl fun j _ => exp_I_im (theta j)
  have hnorm : Complex.normSq S
      = (∑ j, Real.cos (theta j)) ^ 2 + (∑ j, Real.sin (theta j)) ^ 2 := by
    rw [Complex.normSq_apply, h1, h2]; ring
  have h3 : Complex.normSq (1 / (Fintype.card V : ℂ)) = 1 / (Fintype.card V : ℝ) ^ 2 := by
    rw [Complex.normSq_div, Complex.normSq_natCast]
    simp
    rw [sq, mul_inv]
  have key : (∑ j, Real.cos (theta j)) ^ 2 + (∑ j, Real.sin (theta j)) ^ 2
      = ∑ i, ∑ j, Real.cos (theta i - theta j) := by
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (Real.cos_sub (theta i) (theta j)).symm
  unfold order_parameter_r_sq order_parameter_complex
  rw [← hS, Complex.normSq_mul, hnorm, h3, key]
  field_simp

omit [DecidableEq V] in
/-- **Coherence bounds every individual phase gap.** The `N²` is real and not an
artifact: one badly placed oscillator among `N` moves the order parameter by
`O(1/N)`, so a pointwise guarantee from a global mean must pay for it. -/
theorem cos_gap_le_of_coherence [Nonempty V] (theta : V → ℝ) (i j : V) :
    1 - Real.cos (theta i - theta j)
      ≤ (Fintype.card V : ℝ) ^ 2 * (1 - order_parameter_r_sq theta) := by
  have hid := order_parameter_r_sq_eq_mean_cos theta
  have hcard : ∑ _a : V, ∑ _b : V, (1 : ℝ) = (Fintype.card V : ℝ) ^ 2 := by
    simp [Finset.card_univ, sq]
  have hsum : (Fintype.card V : ℝ) ^ 2 * (1 - order_parameter_r_sq theta)
      = ∑ a, ∑ b, (1 - Real.cos (theta a - theta b)) := by
    rw [mul_sub, mul_one, hid, ← hcard, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
  have hrow : ∑ b, (1 - Real.cos (theta i - theta b))
      ≤ ∑ a, ∑ b, (1 - Real.cos (theta a - theta b)) :=
    Finset.single_le_sum
      (f := fun a => ∑ b, (1 - Real.cos (theta a - theta b)))
      (fun a _ => Finset.sum_nonneg fun b _ => by
        linarith [Real.cos_le_one (theta a - theta b)])
      (Finset.mem_univ i)
  have hterm : 1 - Real.cos (theta i - theta j)
      ≤ ∑ b, (1 - Real.cos (theta i - theta b)) :=
    Finset.single_le_sum
      (f := fun b => 1 - Real.cos (theta i - theta b))
      (fun b _ => by linarith [Real.cos_le_one (theta i - theta b)])
      (Finset.mem_univ j)
  rw [hsum]
  linarith

/-- A phase read as the point of the unit circle it names. A content model that
reads `θ` as a real number is not `2π`-periodic and so is not a function of the
phase at all; factoring through this is what makes the encoder well posed. -/
noncomputable def circlePoint (t : ℝ) : ℝ × ℝ := (Real.cos t, Real.sin t)

/-- Chord separation of two phases: the Euclidean distance between their circle
points. This is the metric in which an encoder's Lipschitz constant is declared. -/
noncomputable def chord (a b : ℝ) : ℝ :=
  Real.sqrt ((Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2)

theorem chord_sq_eq (a b : ℝ) :
    (Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2
      = 2 * (1 - Real.cos (a - b)) := by
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

theorem chord_nonneg (a b : ℝ) : 0 ≤ chord a b := Real.sqrt_nonneg _

omit [DecidableEq V] in
/-- **Coherence bounds the chord separation of any two phases.** This is
`cos_gap_le_of_coherence` in the metric an encoder is Lipschitz for. At
`r² = 1` the right side is zero, which recovers exact agreement. -/
theorem chord_le_of_coherence [Nonempty V] (theta : V → ℝ) (i j : V) :
    chord (theta i) (theta j)
      ≤ Real.sqrt 2 * (Fintype.card V : ℝ) *
          Real.sqrt (1 - order_parameter_r_sq theta) := by
  have hN : (0 : ℝ) ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hgap := cos_gap_le_of_coherence theta i j
  have hNpos : (0 : ℝ) < (Fintype.card V : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hc : (0 : ℝ) ≤ 1 - order_parameter_r_sq theta := by
    have hself := cos_gap_le_of_coherence theta i i
    rw [sub_self, Real.cos_zero] at hself
    have h2 : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := pow_pos hNpos 2
    have hm : (Fintype.card V : ℝ) ^ 2 * 0
        ≤ (Fintype.card V : ℝ) ^ 2 * (1 - order_parameter_r_sq theta) := by
      rw [mul_zero]; linarith
    exact le_of_mul_le_mul_left hm h2
  have hstep : chord (theta i) (theta j)
      ≤ Real.sqrt (2 * ((Fintype.card V : ℝ) ^ 2 * (1 - order_parameter_r_sq theta))) := by
    unfold chord
    rw [chord_sq_eq]
    exact Real.sqrt_le_sqrt (by linarith)
  refine hstep.trans_eq ?_
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
    Real.sqrt_mul (sq_nonneg (Fintype.card V : ℝ)), Real.sqrt_sq hN]
  ring

omit [Fintype V] [DecidableEq V] in
/-- Perfect locking makes the chord bound vanish, so the quantitative statement
has the exact one as its endpoint rather than sitting beside it. -/
theorem chord_eq_zero_of_phase_locked [Nonempty V] (theta : V → ℝ)
    (h : is_phase_locked theta) (i j : V) : chord (theta i) (theta j) = 0 := by
  unfold chord
  rw [chord_sq_eq, h i j]
  simp


end PhysicsOfConsciousness
