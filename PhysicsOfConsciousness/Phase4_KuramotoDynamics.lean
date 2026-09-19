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


/-! ## 6. Patch order, winding states, and what the resultant cannot see

`order_parameter_r_sq` is invariant under a global phase shift and otherwise
indifferent to *where* a phase sits, so it reads a field winding across a
periodic array as incoherent even though every neighbourhood of it is locked.
This section proves that, and proves that the two states are stationary for one
and the same coupling, so that `K` does not determine `r` is a theorem here
rather than a reading of a sweep.

Three results carry it:

* `order_parameter_r_sq_winding` — the global resultant of a `q`-fold winding on
  a ring of `n` sites is exactly zero whenever `n ∤ q`.
* `norm_order_parameter_le_mean_patch_order` — the mean resultant of a uniform
  cover by patches is never below the global resultant, so patch order is the
  strictly finer observable. This is the estimator `travelling_wave.local_order`
  computes, whose sliding box cover is the `c = m` case.
* `winding_is_kuramoto_trajectory` and `const_is_kuramoto_trajectory` — under a
  circulant symmetric coupling at identical frequencies both the uniform state
  and the winding state are stationary, the drift of the latter cancelling by
  pairing each displacement with its negative.

Nothing here relaxes the convergence results. `velocity_tendsto_zero` assumes
only `omega = 0` and holds of a winding trivially. `kuramoto_tendsto_global_minimum`
additionally requires the quarter-turn initial spread `|θ 0 i - θ 0 j| ≤ π/2`,
which a winding spanning the circle violates, so it is silent on this regime by
construction; this section says what happens instead.
-/

/-- The resultant of a patch: the mean of `e^{iθ}` over a subset of the sites. -/
noncomputable def patch_resultant (theta : V → ℝ) (P : Finset V) : ℂ :=
  (1 / (P.card : ℂ)) * ∑ i ∈ P, Complex.exp (I * (theta i : ℂ))

/-- Mean patch order over an indexed family of patches: the average of the patch
resultants' *magnitudes*, taken after the modulus rather than before it. That
order of operations is the whole content of the observable. -/
noncomputable def mean_patch_order {B : Type*} [Fintype B]
    (theta : V → ℝ) (P : B → Finset V) : ℝ :=
  (1 / (Fintype.card B : ℝ)) * ∑ b, ‖patch_resultant theta (P b)‖

/-- A cover in which every patch has `c` sites and every site lies in `m`
patches. Overlap is allowed: a partition is the case `m = 1`, and the sliding
box of side `c` on a periodic array is the case `m = c`. -/
structure IsUniformCover {B : Type*} [Fintype B] (P : B → Finset V) (c m : ℕ) : Prop where
  card_patch : ∀ b, (P b).card = c
  multiplicity : ∀ i : V, (Finset.univ.filter fun b => i ∈ P b).card = m

/-- Double counting over a family of patches: summing a function patchwise
weights each site by the number of patches containing it. -/
lemma sum_over_patches {B : Type*} [Fintype B] (P : B → Finset V) (f : V → ℂ) :
    ∑ b, ∑ i ∈ P b, f i
      = ∑ i, ((Finset.univ.filter fun b => i ∈ P b).card : ℂ) * f i := by
  have hb : ∀ b : B, ∑ i ∈ P b, f i = ∑ i, if i ∈ P b then f i else 0 := by
    intro b; rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [hb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The counting identity a uniform cover satisfies: `|B| · c = |V| · m`. -/
lemma IsUniformCover.card_mul {B : Type*} [Fintype B] {P : B → Finset V} {c m : ℕ}
    (h : IsUniformCover P c m) : Fintype.card B * c = Fintype.card V * m := by
  have := sum_over_patches P (fun _ => (1 : ℂ))
  simp only [mul_one, Finset.sum_const, h.card_patch, h.multiplicity,
    Finset.card_univ, nsmul_eq_mul] at this
  exact_mod_cast this

/-- **The patch resultants average back to the global resultant.** The mean is
taken before the modulus here, which is why no information is lost; taking it
after is `mean_patch_order`, and the gap between the two is the phase structure
the global observable discards. -/
theorem mean_patch_resultant {B : Type*} [Fintype B] [Nonempty B] [Nonempty V]
    (theta : V → ℝ) {P : B → Finset V} {c m : ℕ} (h : IsUniformCover P c m) (hc : 0 < c) :
    (1 / (Fintype.card B : ℂ)) * ∑ b, patch_resultant theta (P b)
      = order_parameter_complex theta := by
  have hB : (Fintype.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hV : (Fintype.card V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hcard : (Fintype.card B : ℂ) * c = (Fintype.card V : ℂ) * m := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) h.card_mul
  simp only [patch_resultant, h.card_patch, ← Finset.mul_sum]
  rw [sum_over_patches]
  simp only [h.multiplicity, ← Finset.mul_sum]
  rw [order_parameter_complex]
  have hcoef : (1 / (Fintype.card B : ℂ)) * ((1 / (c : ℂ)) * (m : ℂ))
      = 1 / (Fintype.card V : ℂ) := by
    field_simp
    linear_combination -hcard
  rw [← hcoef]
  ring

/-- **Patch order dominates global order.** `|mean| ≤ mean |·|` over `ℂ`, applied
to the identity above. The inequality is what makes a low resultant at sustained
patch order a statement about spatial structure rather than about coupling. -/
theorem norm_order_parameter_le_mean_patch_order {B : Type*} [Fintype B] [Nonempty B]
    [Nonempty V] (theta : V → ℝ) {P : B → Finset V} {c m : ℕ}
    (h : IsUniformCover P c m) (hc : 0 < c) :
    ‖order_parameter_complex theta‖ ≤ mean_patch_order theta P := by
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  rw [← mean_patch_resultant theta h hc, mean_patch_order, norm_mul]
  gcongr
  · simp
  · exact norm_sum_le _ _

/-- The same domination in the squared observable the rest of the development
states coherence in. -/
theorem order_parameter_r_sq_le_mean_patch_order_sq {B : Type*} [Fintype B] [Nonempty B]
    [Nonempty V] (theta : V → ℝ) {P : B → Finset V} {c m : ℕ}
    (h : IsUniformCover P c m) (hc : 0 < c) :
    order_parameter_r_sq theta ≤ (mean_patch_order theta P) ^ 2 := by
  have h1 := norm_order_parameter_le_mean_patch_order theta h hc
  have h0 : (0 : ℝ) ≤ ‖order_parameter_complex theta‖ := norm_nonneg _
  rw [order_parameter_r_sq, Complex.normSq_eq_norm_sq]
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- **A patch whose phases concentrate about a common value has resultant at
least that concentration.** Stated through `cos (θ i - a)` rather than through
`|θ i - a|` because the bound must survive the `2π` wrap: on a ring the phases of
an arc are close on the circle and not close in `ℝ`. -/
theorem le_norm_patch_resultant (theta : V → ℝ) (P : Finset V) (hP : P.Nonempty)
    (a c₀ : ℝ) (h : ∀ i ∈ P, c₀ ≤ Real.cos (theta i - a)) :
    c₀ ≤ ‖patch_resultant theta P‖ := by
  have hN : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
  set z : ℂ := patch_resultant theta P with hz
  have hrot : Complex.exp (-((a : ℂ) * I)) * z
      = ((1 / (P.card : ℝ) : ℝ) : ℂ) * ∑ i ∈ P, Complex.exp (((theta i - a : ℝ) : ℂ) * I) := by
    rw [hz, patch_resultant,
      show ((1 / (P.card : ℝ) : ℝ) : ℂ) = 1 / (P.card : ℂ) by push_cast; ring,
      ← mul_assoc, mul_comm (Complex.exp (-((a : ℂ) * I))) (1 / (P.card : ℂ)), mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hre : (Complex.exp (-((a : ℂ) * I)) * z).re
      = (1 / (P.card : ℝ)) * ∑ i ∈ P, Real.cos (theta i - a) := by
    rw [hrot, Complex.re_ofReal_mul, Complex.re_sum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => Complex.exp_ofReal_mul_I_re _)
  have hbound : c₀ ≤ (Complex.exp (-((a : ℂ) * I)) * z).re := by
    rw [hre]
    have hsum : (P.card : ℝ) * c₀ ≤ ∑ i ∈ P, Real.cos (theta i - a) := by
      calc (P.card : ℝ) * c₀ = ∑ _i ∈ P, (c₀ : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum h
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hN]
    nlinarith [hsum]
  calc c₀ ≤ (Complex.exp (-((a : ℂ) * I)) * z).re := hbound
    _ ≤ ‖Complex.exp (-((a : ℂ) * I)) * z‖ := Complex.re_le_norm _
    _ = ‖z‖ := by
        rw [norm_mul]
        have hone : ‖Complex.exp (-((a : ℂ) * I))‖ = 1 := by
          rw [show -((a : ℂ) * I) = ((-a : ℝ) : ℂ) * I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I (-a)
        rw [hone, one_mul]

omit [Fintype V] [DecidableEq V] in
/-- A bound holding on every patch passes to the mean. -/
lemma le_mean_patch_order {B : Type*} [Fintype B] [Nonempty B] (theta : V → ℝ)
    (P : B → Finset V) {c₀ : ℝ} (h : ∀ b, c₀ ≤ ‖patch_resultant theta (P b)‖) :
    c₀ ≤ mean_patch_order theta P := by
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  rw [mean_patch_order, one_div, inv_mul_eq_div, le_div_iff₀ hB]
  calc c₀ * Fintype.card B = ∑ _b : B, (c₀ : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun b _ => h b

/-- The cover by single sites: the limit in which a patch resolves no structure
at all. -/
lemma isUniformCover_singleton : IsUniformCover (fun i : V => ({i} : Finset V)) 1 1 where
  card_patch := by intro b; simp
  multiplicity := by intro i; simp [Finset.filter_eq]

omit [Fintype V] [DecidableEq V] in
lemma norm_patch_resultant_singleton (theta : V → ℝ) (i : V) :
    ‖patch_resultant theta ({i} : Finset V)‖ = 1 := by
  rw [patch_resultant]
  simp [mul_comm]

omit [DecidableEq V] in
/-- Under the singleton cover every configuration has patch order one, which is
the sharp statement of how little the finest patch observable constrains the
global one. -/
lemma mean_patch_order_singleton [Nonempty V] (theta : V → ℝ) :
    mean_patch_order theta (fun i : V => ({i} : Finset V)) = 1 := by
  have hV : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mean_patch_order]
  simp only [norm_patch_resultant_singleton, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  field_simp

omit [Fintype V] [DecidableEq V] in
private lemma norm_expI (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I t

/-! ### Windings on a finite abelian group

The ring is one geometry and the sheet the sweep integrates is another: the
twist `travelling_wave.py` imposes lives on a periodic `(side, side)` array
under a toroidal kernel, which is `ZMod n × ZMod n` and not `ZMod n`. Every
cancellation below uses only that the sites form a finite abelian group and that
the kernel is even in the separation, so the statements are made there and the
ring and the torus are both instances of them.

What carries a winding is a character together with a chosen real lift of it.
The character is what the amplitude layer of §7 acts on; the lift is what the
phase model needs, because `is_kuramoto_trajectory` takes a real-valued `θ` and
a character does not supply one. -/

/-- A winding on `G`: a unit character `chi`, together with a real phase `psi`
lifting it. `map_add` is the only algebraic input and `lift` ties the two fields
together; constant modulus, the oddness of the phase and every cancellation
below are derived from the pair. -/
structure WindingData (G : Type*) [AddCommGroup G] where
  /-- The character: a unit phasor, multiplicative in the site index. -/
  chi : G → ℂ
  /-- A real-valued lift of `chi`. The phase model needs one and a character
  does not supply it: on the ring `psi` goes through `ZMod.val`, which is a
  residue, so `psi` is additive only up to whole turns while `chi` is additive
  exactly. -/
  psi : G → ℝ
  /-- The character is a homomorphism to the unit circle. -/
  map_add : ∀ a b, chi (a + b) = chi a * chi b
  /-- `psi` lifts `chi`, which is what makes the defect invisible to `exp`. -/
  lift : ∀ g, Complex.exp (I * (psi g : ℂ)) = chi g

namespace WindingData

variable {G : Type*} [AddCommGroup G] (W : WindingData G)

@[simp] lemma norm_chi (g : G) : ‖W.chi g‖ = 1 := by
  rw [← W.lift g]; exact norm_expI _

lemma chi_ne_zero (g : G) : W.chi g ≠ 0 := by
  intro hcon
  have h := W.norm_chi g
  rw [hcon, norm_zero] at h
  exact zero_ne_one h

@[simp] lemma chi_zero : W.chi 0 = 1 := by
  have h := W.map_add 0 0
  rw [add_zero] at h
  have h2 : W.chi 0 * (W.chi 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h]; ring
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (W.chi_ne_zero 0)
  · linear_combination h3

/-- The character is conjugated by negation, which is the source of every
oddness statement below. -/
lemma chi_neg (d : G) : W.chi (-d) = (starRingEnd ℂ) (W.chi d) := by
  have h1 : W.chi d * W.chi (-d) = 1 := by
    rw [← W.map_add, add_neg_cancel, W.chi_zero]
  have h2 : W.chi d * (starRingEnd ℂ) (W.chi d) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, W.norm_chi]
    norm_num
  exact mul_left_cancel₀ (W.chi_ne_zero d) (h1.trans h2.symm)

@[simp] lemma re_chi (g : G) : (W.chi g).re = Real.cos (W.psi g) := by
  rw [← W.lift g, exp_I_re]

@[simp] lemma im_chi (g : G) : (W.chi g).im = Real.sin (W.psi g) := by
  rw [← W.lift g, exp_I_im]

lemma sin_psi_neg (d : G) : Real.sin (W.psi (-d)) = - Real.sin (W.psi d) := by
  rw [← W.im_chi, ← W.im_chi, W.chi_neg, Complex.conj_im]

/-- **The phase difference across a separation depends only on the separation.**
The lift's defect is a whole number of turns and `exp` does not see it, so this
is the general form of `sin_winding_add`: no residue arithmetic survives. -/
lemma expI_psi_sub (i d : G) :
    Complex.exp (I * ((W.psi (i + d) - W.psi i : ℝ) : ℂ)) = W.chi d := by
  rw [show ((W.psi (i + d) - W.psi i : ℝ) : ℂ)
      = (W.psi (i + d) : ℂ) - (W.psi i : ℂ) by push_cast; ring,
    mul_sub, Complex.exp_sub, W.lift, W.lift, W.map_add,
    mul_comm (W.chi i) (W.chi d), mul_div_assoc, div_self (W.chi_ne_zero i), mul_one]

lemma sin_psi_sub (i d : G) : Real.sin (W.psi (i + d) - W.psi i) = Real.sin (W.psi d) := by
  rw [← W.im_chi d, ← W.expI_psi_sub i d, exp_I_im]

lemma cos_psi_sub (i d : G) : Real.cos (W.psi (i + d) - W.psi i) = Real.cos (W.psi d) := by
  rw [← W.re_chi d, ← W.expI_psi_sub i d, exp_I_re]

/-- **Two windings make a winding on the product.** The sheet is the ring twice
over: `psi` adds, `chi` multiplies, and the lift survives both. This is the only
step the torus needs that the ring did not already have. -/
def prod {H : Type*} [AddCommGroup H] (W : WindingData G) (W' : WindingData H) :
    WindingData (G × H) where
  chi := fun g => W.chi g.1 * W'.chi g.2
  psi := fun g => W.psi g.1 + W'.psi g.2
  map_add := by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, W.map_add, W'.map_add]
    ring
  lift := by
    intro g
    rw [show I * ((W.psi g.1 + W'.psi g.2 : ℝ) : ℂ)
        = I * (W.psi g.1 : ℂ) + I * (W'.psi g.2 : ℂ) by push_cast; ring,
      Complex.exp_add, W.lift, W'.lift]

end WindingData

/-- The phasor advanced per site by a `q`-fold winding on a ring of `n` sites. -/
noncomputable def windingPhasor (n : ℕ) (q : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * I * q / n)

/-- The winding configuration on a ring of `n` sites: phase `2πq·k/n` at site
`k`, so that the field turns `q` times on going once around. -/
noncomputable def winding (n : ℕ) (q : ℤ) : ZMod n → ℝ :=
  fun k => 2 * Real.pi * q * (k.val : ℝ) / n

@[simp] lemma winding_zero (n : ℕ) [NeZero n] (q : ℤ) : winding n q 0 = 0 := by
  simp [winding]

/-- The winding is additive in the site index up to a whole number of turns.
`val` is a residue, not a homomorphism to `ℝ`, and the defect is exactly
`2π`-periodic — which is why the ring supplies a `WindingData` and not a
homomorphism. -/
lemma winding_add (n : ℕ) [NeZero n] (q : ℤ) (a b : ZMod n) :
    ∃ k : ℤ, winding n q (a + b) = winding n q a + winding n q b + k * (2 * Real.pi) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set D : ℕ := (a.val + b.val) / n with hD
  set R : ℕ := (a.val + b.val) % n with hR
  refine ⟨-(q * (D : ℤ)), ?_⟩
  have hmod : (R : ℝ) = (a.val : ℝ) + (b.val : ℝ) - (n : ℝ) * (D : ℝ) := by
    have h := Nat.div_add_mod (a.val + b.val) n
    have h' : ((n * D + R : ℕ) : ℝ) = ((a.val + b.val : ℕ) : ℝ) := congrArg _ h
    push_cast at h'
    linarith
  simp only [winding, ZMod.val_add, ← hR, hmod]
  push_cast
  field_simp
  ring

lemma expI_winding_add (n : ℕ) [NeZero n] (q : ℤ) (a b : ZMod n) :
    Complex.exp (I * (winding n q (a + b) : ℂ))
      = Complex.exp (I * (winding n q a : ℂ)) * Complex.exp (I * (winding n q b : ℂ)) := by
  obtain ⟨k, hk⟩ := winding_add n q a b
  rw [hk, show I * ((winding n q a + winding n q b + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ)
      = I * (winding n q a : ℂ) + I * (winding n q b : ℂ) + (k : ℂ) * (2 * Real.pi * I) by
        push_cast; ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The ring's winding as a `WindingData`. Everything §6 and §7 prove about
windings is proved about this object's general shape and specialized back here. -/
noncomputable def ringWinding (n : ℕ) [NeZero n] (q : ℤ) : WindingData (ZMod n) where
  chi := fun k => Complex.exp (I * (winding n q k : ℂ))
  psi := winding n q
  map_add := expI_winding_add n q
  lift := fun _ => rfl

@[simp] lemma ringWinding_psi (n : ℕ) [NeZero n] (q : ℤ) : (ringWinding n q).psi = winding n q :=
  rfl

@[simp] lemma ringWinding_chi (n : ℕ) [NeZero n] (q : ℤ) (k : ZMod n) :
    (ringWinding n q).chi k = Complex.exp (I * (winding n q k : ℂ)) := rfl

/-- **The sheet the sweep integrates.** `travelling_wave.py` imposes
`θ[r,c] = 2πq·c/side` on a periodic `(side, side)` array under a toroidal
kernel: that state is this object at `q₁ = 0`. -/
noncomputable def torusWinding (n : ℕ) [NeZero n] (q₁ q₂ : ℤ) :
    WindingData (ZMod n × ZMod n) :=
  (ringWinding n q₁).prod (ringWinding n q₂)

lemma windingPhasor_ne_one {n : ℕ} [NeZero n] {q : ℤ} (hq : ¬ ((n : ℤ) ∣ q)) :
    windingPhasor n q ≠ 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [windingPhasor, Ne, Complex.exp_eq_one_iff]
  rintro ⟨m, hm⟩
  refine hq ⟨m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 : ℂ) * Real.pi * I ≠ 0 := by simp [Complex.I_ne_zero, hpi]
  field_simp at hm
  exact_mod_cast hm

/-- The ring winding is nontrivial exactly where the phasor is, which is the
hypothesis the general order-parameter statement takes. -/
lemma ringWinding_chi_one_ne_one {n : ℕ} [NeZero n] [Fact (1 < n)] {q : ℤ}
    (hq : ¬ ((n : ℤ) ∣ q)) : (ringWinding n q).chi 1 ≠ 1 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hval : winding n q 1 = 2 * Real.pi * q / n := by rw [winding, ZMod.val_one]; ring
  rw [ringWinding_chi, hval,
    show I * ((2 * Real.pi * q / n : ℝ) : ℂ) = 2 * Real.pi * I * q / n by push_cast; ring]
  exact windingPhasor_ne_one hq

section AbelianSites

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- An odd function on a finite abelian group sums to zero, by reindexing along
negation. -/
lemma sum_eq_zero_of_odd (g : G → ℝ) (hg : ∀ d, g (-d) = - g d) : ∑ d, g d = 0 := by
  have h : ∑ d : G, g d = - ∑ d : G, g d := by
    calc ∑ d : G, g d = ∑ d : G, g (-d) :=
          (Fintype.sum_equiv (Equiv.neg G) (fun d => g (-d)) g fun _ => rfl).symm
      _ = ∑ d : G, -g d := Finset.sum_congr rfl fun d _ => hg d
      _ = - ∑ d : G, g d := by rw [Finset.sum_neg_distrib]
  linarith

omit [DecidableEq G] in
/-- **The order parameter vanishes on any nontrivial winding.** The site sum is
invariant under a shift, which multiplies it by the character's value there; if
that value is not one the sum must be zero. On the ring this is `n ∤ q`; on the
torus it is a winding number on either axis. The observable in which `K_c = 2D`
is stated therefore cannot see the winding at all. -/
theorem order_parameter_complex_char [Nonempty G] (W : WindingData G) {g₀ : G}
    (hg : W.chi g₀ ≠ 1) : order_parameter_complex W.psi = 0 := by
  have key : (∑ k : G, Complex.exp (I * (W.psi k : ℂ))) = 0 := by
    set S := ∑ k : G, Complex.exp (I * (W.psi k : ℂ)) with hS
    have hchi : S = ∑ k : G, W.chi k := Finset.sum_congr rfl fun k _ => W.lift k
    have h1 : S = W.chi g₀ * S := by
      calc S = ∑ k : G, W.chi (k + g₀) :=
            hchi.trans (Fintype.sum_equiv (Equiv.addRight g₀)
              (fun k => W.chi (k + g₀)) W.chi (fun _ => rfl)).symm
        _ = ∑ k : G, W.chi g₀ * W.chi k :=
            Finset.sum_congr rfl fun k _ => by rw [W.map_add, mul_comm]
        _ = W.chi g₀ * S := by rw [← Finset.mul_sum, ← hchi]
    have h2 : (1 - W.chi g₀) * S = 0 := by rw [sub_mul, one_mul, ← h1]; ring
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (by linear_combination -h : W.chi g₀ = 1) hg
    · exact h
  rw [order_parameter_complex, key, mul_zero]

omit [DecidableEq G] in
theorem order_parameter_r_sq_char [Nonempty G] (W : WindingData G) {g₀ : G}
    (hg : W.chi g₀ ≠ 1) : order_parameter_r_sq W.psi = 0 := by
  rw [order_parameter_r_sq, order_parameter_complex_char W hg, map_zero]

/-- Nearest-neighbour patches along a chosen separation: the coarsest cover that
is not the singleton one. -/
def pairCover (g : G) (k : G) : Finset G := {k, k + g}

lemma isUniformCover_pairCover {g : G} (hg : g ≠ 0) : IsUniformCover (pairCover g) 2 2 where
  card_patch := by
    intro b
    rw [pairCover, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        intro h
        exact hg (by simpa using h.symm)),
      Finset.card_singleton]
  multiplicity := by
    intro i
    have hset : (Finset.univ.filter fun b => i ∈ pairCover g b) = {i, i - g} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairCover, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h]; abel)
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h]; abel)
    rw [hset, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        intro h
        exact hg (by simpa using h.symm)),
      Finset.card_singleton]

/-- **A winding keeps its neighbourhoods locked.** Patch order across a chosen
separation is at least `cos (psi g)`, which tends to one as the same winding is
spread over more sites, while `order_parameter_r_sq_char` puts the global
resultant at zero. The two observables measure different things, and the sweep
in `travelling_wave.py` measures the gap between them. -/
theorem cos_le_mean_patch_order_char [Nonempty G] (W : WindingData G) (g : G) :
    Real.cos (W.psi g) ≤ mean_patch_order W.psi (pairCover g) := by
  refine le_mean_patch_order _ _ fun k => ?_
  refine le_norm_patch_resultant _ _ ⟨k, by simp [pairCover]⟩ (W.psi k) _ ?_
  intro i hi
  simp only [pairCover, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · rw [sub_self, Real.cos_zero]
    exact Real.cos_le_one _
  · exact le_of_eq (W.cos_psi_sub k g).symm

/-- A translation-invariant (circulant) coupling at identical natural
frequencies. `KuramotoSystem.A` is a general `V → V → ℝ`, so the isotropy the
cancellation needs has to be supplied: `f` depends on the separation alone and
`hf` makes it even in that separation. -/
def circulantSystem (f : G → ℝ) (hf : ∀ d, f (-d) = f d) : KuramotoSystem G where
  omega := fun _ => 0
  A := fun i j => f (j - i)
  symm := by
    intro i j
    rw [show i - j = -(j - i) by abel, hf]

omit [Fintype G] [DecidableEq G] in
@[simp] lemma circulantSystem_omega (f : G → ℝ) (hf : ∀ d, f (-d) = f d)
    (i : G) : (circulantSystem f hf).omega i = 0 := rfl

omit [Fintype G] [DecidableEq G] in
@[simp] lemma circulantSystem_A (f : G → ℝ) (hf : ∀ d, f (-d) = f d)
    (i j : G) : (circulantSystem f hf).A i j = f (j - i) := rfl

omit [DecidableEq G] in
/-- The drift of a winding under a circulant even kernel is zero at every site:
reindexing by separation makes the summand odd in `d` against a kernel even in
it, and pairing `d` with `-d` cancels the sum. Nothing about the ring enters. -/
theorem circulant_drift_char (W : WindingData G) (f : G → ℝ)
    (hf : ∀ d, f (-d) = f d) (i : G) :
    ∑ j, f (j - i) * Real.sin (W.psi j - W.psi i) = 0 := by
  have hreindex : ∑ j : G, f (j - i) * Real.sin (W.psi j - W.psi i)
      = ∑ d : G, f d * Real.sin (W.psi d) := by
    rw [← Fintype.sum_equiv (Equiv.addLeft i)
      (fun d => f ((i + d) - i) * Real.sin (W.psi (i + d) - W.psi i))
      (fun j => f (j - i) * Real.sin (W.psi j - W.psi i)) fun _ => rfl]
    exact Finset.sum_congr rfl fun d _ => by
      rw [add_sub_cancel_left, W.sin_psi_sub]
  rw [hreindex]
  refine sum_eq_zero_of_odd _ fun d => ?_
  rw [hf, W.sin_psi_neg]
  ring

omit [DecidableEq G] in
/-- **A winding is stationary.** Nothing moves: at identical frequencies with an
even kernel the winding is a standing phase gradient, not a travelling one, and
its vanishing resultant is a consequence of the winding rather than of any
motion. -/
theorem char_is_kuramoto_trajectory (W : WindingData G) (f : G → ℝ)
    (hf : ∀ d, f (-d) = f d) :
    is_kuramoto_trajectory (circulantSystem f hf) (fun _ => W.psi) := by
  intro i t
  have hdrift : (circulantSystem f hf).omega i
      + ∑ j, (circulantSystem f hf).A i j
          * Real.sin (W.psi j - W.psi i) = 0 := by
    simp only [circulantSystem_omega, circulantSystem_A, zero_add]
    exact circulant_drift_char W f hf i
  rw [hdrift]
  exact hasDerivAt_const t _

omit [DecidableEq G] in
/-- The uniform state is stationary for the same system, which is what makes the
pair a statement about one coupling rather than about two. -/
theorem const_is_kuramoto_trajectory (f : G → ℝ)
    (hf : ∀ d, f (-d) = f d) (c : ℝ) :
    is_kuramoto_trajectory (circulantSystem f hf) (fun _ _ => c) := by
  intro i t
  have hdrift : (circulantSystem f hf).omega i
      + ∑ _j : G, (circulantSystem f hf).A i _j * Real.sin (c - c) = 0 := by
    simp
  rw [hdrift]
  exact hasDerivAt_const t _

/-- **The coupling does not determine the order parameter.** One circulant
system has two stationary states: the uniform one at `r² = 1`, and a nontrivial
winding at `r² = 0` whose patch order across a separation is still at least
`cos (psi g)`. No bound on `K` separates them, because they share it. -/
theorem coupling_does_not_determine_order [Nonempty G] (W : WindingData G) {g₀ : G}
    (hg : W.chi g₀ ≠ 1) (f : G → ℝ) (hf : ∀ d, f (-d) = f d) (c : ℝ) (g : G) :
    (is_kuramoto_trajectory (circulantSystem f hf) (fun _ _ => c)
        ∧ order_parameter_r_sq (fun _ : G => c) = 1)
      ∧ (is_kuramoto_trajectory (circulantSystem f hf) (fun _ => W.psi)
        ∧ order_parameter_r_sq W.psi = 0
        ∧ Real.cos (W.psi g) ≤ mean_patch_order W.psi (pairCover g)) :=
  ⟨⟨const_is_kuramoto_trajectory f hf c,
      phase_locked_implies_r_sq_eq_one _ (by intro i j; simp)⟩,
    char_is_kuramoto_trajectory W f hf, order_parameter_r_sq_char W hg,
    cos_le_mean_patch_order_char W g⟩

end AbelianSites

/-! ### The ring and the torus

The statements above at their two instances. The ring keeps the names the
publication cites; the torus is the geometry `travelling_wave.py` integrates,
and it costs one `WindingData.prod`. -/

/-- Nearest-neighbour patches on the ring. -/
def ringPair (n : ℕ) (k : ZMod n) : Finset (ZMod n) := {k, k + 1}

lemma isUniformCover_ringPair (n : ℕ) [NeZero n] [Fact (1 < n)] :
    IsUniformCover (ringPair n) 2 2 :=
  isUniformCover_pairCover (g := (1 : ZMod n)) one_ne_zero

theorem circulant_drift_winding {n : ℕ} [NeZero n] (q : ℤ) (f : ZMod n → ℝ)
    (hf : ∀ d, f (-d) = f d) (i : ZMod n) :
    ∑ j, f (j - i) * Real.sin (winding n q j - winding n q i) = 0 :=
  circulant_drift_char (ringWinding n q) f hf i

/-- **A winding state is stationary**, on the ring. -/
theorem winding_is_kuramoto_trajectory {n : ℕ} [NeZero n] (q : ℤ) (f : ZMod n → ℝ)
    (hf : ∀ d, f (-d) = f d) :
    is_kuramoto_trajectory (circulantSystem f hf) (fun _ => winding n q) :=
  char_is_kuramoto_trajectory (ringWinding n q) f hf

theorem order_parameter_complex_winding {n : ℕ} [NeZero n] [Fact (1 < n)] {q : ℤ}
    (hq : ¬ ((n : ℤ) ∣ q)) : order_parameter_complex (winding n q) = 0 :=
  order_parameter_complex_char (ringWinding n q) (ringWinding_chi_one_ne_one hq)

theorem order_parameter_r_sq_winding {n : ℕ} [NeZero n] [Fact (1 < n)] {q : ℤ}
    (hq : ¬ ((n : ℤ) ∣ q)) : order_parameter_r_sq (winding n q) = 0 :=
  order_parameter_r_sq_char (ringWinding n q) (ringWinding_chi_one_ne_one hq)

/-- Nearest-neighbour patch order on the ring is at least `cos (2πq/n)`, which
approaches one as the same winding is spread over more sites. -/
theorem cos_le_mean_patch_order_winding (n : ℕ) [NeZero n] [Fact (1 < n)] (q : ℤ) :
    Real.cos (2 * Real.pi * q / n) ≤ mean_patch_order (winding n q) (ringPair n) := by
  have hval : winding n q 1 = 2 * Real.pi * q / n := by rw [winding, ZMod.val_one]; ring
  rw [← hval]
  exact cos_le_mean_patch_order_char (ringWinding n q) 1

/-- **The torus carries the same two states.** The sheet of the sweep, at any
even toroidal kernel: a winding on either axis is stationary and invisible to
the global resultant, and the uniform state is stationary at the same coupling.
This is the geometry `travelling_wave.py` integrates. -/
theorem torus_coupling_does_not_determine_order {n : ℕ} [NeZero n] [Fact (1 < n)]
    {q₁ q₂ : ℤ} (hq : ¬ ((n : ℤ) ∣ q₂)) (f : ZMod n × ZMod n → ℝ)
    (hf : ∀ d, f (-d) = f d) (c : ℝ) (g : ZMod n × ZMod n) :
    (is_kuramoto_trajectory (circulantSystem f hf) (fun _ _ => c)
        ∧ order_parameter_r_sq (fun _ : ZMod n × ZMod n => c) = 1)
      ∧ (is_kuramoto_trajectory (circulantSystem f hf) (fun _ => (torusWinding n q₁ q₂).psi)
        ∧ order_parameter_r_sq (torusWinding n q₁ q₂).psi = 0
        ∧ Real.cos ((torusWinding n q₁ q₂).psi g)
            ≤ mean_patch_order (torusWinding n q₁ q₂).psi (pairCover g)) := by
  refine coupling_does_not_determine_order (torusWinding n q₁ q₂) (g₀ := (0, 1)) ?_ f hf c g
  have h : (torusWinding n q₁ q₂).chi (0, 1)
      = (ringWinding n q₁).chi 0 * (ringWinding n q₂).chi 1 := rfl
  rw [h, (ringWinding n q₁).chi_zero, one_mul]
  exact ringWinding_chi_one_ne_one hq

/-! ## 7. An amplitude field, and the standing structure it buys

Every oscillator in §1--§6 sits on the unit circle, so the state carries a phase
and no amplitude, and a field with an amplitude node — `u = cos(kx)cos(ωt)` — has
no representation in what those sections integrate. This section adds the degree
of freedom, in the form that keeps the architecture: the **real** Stuart--Landau
field

    ż i = (μ - |z i|²) * z i + ∑ j, A i j * (z j - z i),

which is the gradient flow of

    F z = ∑ i, (|z i|⁴/4 - μ * |z i|²/2) + (1/4) * ∑ i, ∑ j, A i j * |z i - z j|²

against the real inner product on `ℂ^V ≅ ℝ^(2V)`. Complex coefficients on the
cubic or on the coupling — the genuine Ginzburg--Landau equation — destroy that
gradient structure, and every convergence result in this development rests on it,
so the real case is the one that inherits the architecture rather than replacing
it.

Four results follow:

* `deriv_phase_of_amplitude_trajectory` and `amplitude_phase_is_kuramoto` — where
  the amplitudes are positive, the phase of an amplitude trajectory obeys
  `θ̇ i = ∑ j, A i j * (r j / r i) * sin (θ j - θ i)` exactly, which is
  `is_kuramoto_trajectory` as soon as the amplitudes agree. The phase model is
  this model's phase equation with the amplitude ratios set to one, so the two
  layers are one object rather than two.
* `windingState_is_amplitude_trajectory_iff` — on the ring with the circulant
  kernel of §6, `z k = a * ξ^k` with `ξ = exp (2πiq/n)` is stationary exactly
  when `a² = μ + windingLambda n q f`.
* `exists_windingState_iff` and `phase_model_admits_winding_outside_band` — that
  winding exists **iff** `μ + windingLambda n q f > 0`. The phase model admits
  every winding number at every coupling (`winding_is_kuramoto_trajectory` has no
  hypothesis on `q` or `f`); the amplitude model admits a band, and a winding
  outside it has nowhere to sit.
* `standing_wave_of_amplitude_band` — at `q = n/2` the phasor is `-1`, the state
  is real and exact, and its lab-frame reading is `a * (-1)^k * cos (Ωt)`: a
  standing wave in the framework's own integrated dynamics. The phase model has
  no such object, every site there having unit modulus.

### Scope

1. **A ring has no spiral.** A cortical phase singularity is a two-dimensional
   defect: a point of the sheet around which phase advances by a whole turn and
   at which amplitude vanishes. `ZMod n` has no interior, so the results here
   reach a winding and not a spiral, and the exact solutions never have the
   defining feature — `‖windingState n q a k‖ = |a|` at every site, so no site is
   a zero. Removing this limit means `ZMod n × ZMod n`, which is not a corollary
   of anything below. Until it is done the layer speaks about the electrode loop
   of `Phase5_PhaseLifts` and not about what the loop encircles.
2. **Relaxational dynamics has no propagation speed.** Real coefficients give no
   nonlinear dispersion, and `circulant_drift_winding` proves the phase drift is
   exactly zero, so nothing here travels. A cortical wave measurement always
   reports a speed and this model predicts none. Supplying one needs
   heterogeneous frequencies or complex coefficients, and both cost the gradient
   structure that makes this layer cheap.
3. **`‖z‖` is a normal-form radius; a measured envelope is not.** The winding
   that `Phase5_PhaseLifts` tests for is read off locally unwrapped experimental
   phase maps, whose amplitude is the envelope of an analytic signal. `‖z i‖`
   here is a distance from an unstable fixed point in a Hopf normal form.
   Identifying the two is a physical assumption of the same kind as the Landauer
   identification that `Phase3_LandauerBridge` carries as a named hypothesis, and
   it is not made anywhere in this file.
4. **Stuart--Landau is local in parameter space.** The normal form is valid near
   a supercritical Hopf bifurcation, where the resting state has just lost
   stability. Much cortical wave phenomenology is excitable-medium behaviour
   instead — a stable rest state and a threshold that gets crossed — and the two
   produce similar-looking maps from different mechanisms. This layer models one
   of them and says nothing about which one applies.
5. **`μ` has no cortical estimate.** The band `μ + windingLambda n q f > 0` is
   structural: the distance from the bifurcation is measured nowhere in this
   development, so the band predicts no numeral and discriminates no experiment.
6. **Nothing connects a winding sector to content.** Making a defect computable
   from a dynamical state rather than postulated from data is not making it mean
   anything, and this layer's contribution to the content question is zero.

Two things do not come for free and are not claimed. A cosine profile is *not* a
stationary state: the cubic term does not preserve a single Fourier mode, so only
the circularly polarised modes are exact and the only real one among them is the
alternating mode of `standing_wave_of_amplitude_band`. A standing wave with an
interior amplitude node is a fixed point of a nonlinear system with no closed
form, reached by bifurcation from `μ = -windingLambda n q f`.
-/

omit [DecidableEq V] in
/-- `e^{iy} · conj e^{ix} = e^{i(y-x)}`: the rotation that reads a pair of phases
against each other, and the step every polar computation below goes through. -/
private lemma expI_mul_conj (x y : ℝ) :
    Complex.exp (I * (y : ℂ)) * (starRingEnd ℂ) (Complex.exp (I * (x : ℂ)))
      = Complex.exp (I * ((y - x : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The real Stuart--Landau field on the same coupling the phase model uses:
a cubic local term with parameter `μ` and a diffusive coupling through `A`. -/
noncomputable def amplitudeField (mu : ℝ) (A : V → V → ℝ) (z : V → ℂ) : V → ℂ :=
  fun i => ((mu : ℂ) - ((‖z i‖ : ℂ)) ^ 2) * z i + ∑ j, ((A i j : ℝ) : ℂ) * (z j - z i)

/-- A trajectory of the amplitude field, stated componentwise exactly as
`is_kuramoto_trajectory` is. -/
def is_amplitude_trajectory (mu : ℝ) (A : V → V → ℝ) (z : ℝ → V → ℂ) : Prop :=
  ∀ (i : V) (t : ℝ), HasDerivAt (fun s => z s i) (amplitudeField mu A (z t) i) t

omit [DecidableEq V] in
/-- A time-independent state is a trajectory exactly when the field vanishes on
it. This is what makes every stationarity claim below an algebraic identity. -/
lemma is_amplitude_trajectory_const_iff (mu : ℝ) (A : V → V → ℝ) (w : V → ℂ) :
    is_amplitude_trajectory mu A (fun _ => w) ↔ ∀ i, amplitudeField mu A w i = 0 := by
  constructor
  · intro h i
    exact ((hasDerivAt_const (0 : ℝ) (w i)).unique (h i 0)).symm
  · intro h i t
    rw [h i]
    exact hasDerivAt_const t _

omit [DecidableEq V] in
/-- **The tangential part of the amplitude field.** Against the polar form,
`Im (ż i · conj (z i))` is the Kuramoto drift weighted by the amplitudes: the
local cubic term is a real multiple of `z i` and contributes nothing, and each
coupling term contributes `A i j · r i · r j · sin (θ j - θ i)`. Dividing by
`r i ²` is what turns this into a phase equation. -/
lemma im_amplitudeField_mul_conj (mu : ℝ) (A : V → V → ℝ) (z : V → ℂ) (r th : V → ℝ)
    (hz : ∀ i, z i = ((r i : ℝ) : ℂ) * Complex.exp (I * (th i : ℂ))) (i : V) :
    (amplitudeField mu A z i * (starRingEnd ℂ) (z i)).im
      = ∑ j, A i j * (r i * r j) * Real.sin (th j - th i) := by
  have hpair : ∀ j : V, (z j * (starRingEnd ℂ) (z i)).im = r i * r j * Real.sin (th j - th i) := by
    intro j
    rw [hz j, hz i, map_mul, Complex.conj_ofReal,
      show ((r j : ℂ) * Complex.exp (I * (th j : ℂ)))
          * ((r i : ℂ) * (starRingEnd ℂ) (Complex.exp (I * (th i : ℂ))))
        = ((r i * r j : ℝ) : ℂ)
          * (Complex.exp (I * (th j : ℂ)) * (starRingEnd ℂ) (Complex.exp (I * (th i : ℂ)))) by
        push_cast; ring,
      expI_mul_conj, Complex.im_ofReal_mul, exp_I_im]
  rw [amplitudeField, add_mul, Complex.add_im, Finset.sum_mul, Complex.im_sum]
  have h1 : (((mu : ℂ) - ((‖z i‖ : ℂ)) ^ 2) * z i * (starRingEnd ℂ) (z i)).im = 0 := by
    rw [show ((mu : ℂ) - ((‖z i‖ : ℂ)) ^ 2) = ((mu - ‖z i‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      mul_assoc, Complex.im_ofReal_mul, Complex.mul_conj]
    simp
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, sub_mul, Complex.im_ofReal_mul, Complex.sub_im, hpair j, hpair i]
  simp only [sub_self, Real.sin_zero, mul_zero, sub_zero]
  ring

/-- The derivative of a polar path, `d/dt (r e^{iθ}) = (ṙ + i r θ̇) e^{iθ}`. -/
private lemma hasDerivAt_polar {r th : ℝ → ℝ} {r' th' t : ℝ}
    (hr : HasDerivAt r r' t) (hth : HasDerivAt th th' t) :
    HasDerivAt (fun s => ((r s : ℝ) : ℂ) * Complex.exp (I * ((th s : ℝ) : ℂ)))
      (((r' : ℂ) + (r t : ℂ) * I * (th' : ℂ)) * Complex.exp (I * ((th t : ℝ) : ℂ))) t := by
  have h1 : HasDerivAt (fun s => ((r s : ℝ) : ℂ)) ((r' : ℂ)) t := hr.ofReal_comp
  have h2 : HasDerivAt (fun s => I * ((th s : ℝ) : ℂ)) (I * (th' : ℂ)) t :=
    (hth.ofReal_comp).const_mul I
  have h3 := h1.mul h2.cexp
  rw [show (↑r' * Complex.exp (I * ((th t : ℝ) : ℂ))
        + ((r t : ℝ) : ℂ) * (Complex.exp (I * ((th t : ℝ) : ℂ)) * (I * (th' : ℂ))))
      = (((r' : ℂ) + (r t : ℂ) * I * (th' : ℂ)) * Complex.exp (I * ((th t : ℝ) : ℂ))) by
      ring] at h3
  exact h3

omit [DecidableEq V] in
/-- **X1: the phase equation of the amplitude model is Kuramoto.** At a site of
positive amplitude the phase of an amplitude trajectory moves at exactly

    θ̇ i = ∑ j, A i j * (r j / r i) * sin (θ j - θ i),

the Kuramoto drift with each coupling weighted by the ratio of the amplitudes.
No approximation and no slow-amplitude assumption enters: the identity is the
imaginary part of `ż i · conj (z i)`, divided by `r i ²`. -/
theorem deriv_phase_of_amplitude_trajectory {mu : ℝ} {A : V → V → ℝ} {z : ℝ → V → ℂ}
    {r th : ℝ → V → ℝ} (hz : is_amplitude_trajectory mu A z)
    (hpolar : ∀ s i, z s i = ((r s i : ℝ) : ℂ) * Complex.exp (I * (th s i : ℂ)))
    {i : V} {t : ℝ} (hri : 0 < r t i) {r' th' : ℝ}
    (hr : HasDerivAt (fun s => r s i) r' t) (hth : HasDerivAt (fun s => th s i) th' t) :
    th' = ∑ j, A i j * (r t j / r t i) * Real.sin (th t j - th t i) := by
  have hfun : (fun s => z s i) = fun s => ((r s i : ℝ) : ℂ) * Complex.exp (I * (th s i : ℂ)) := by
    funext s; exact hpolar s i
  have hpol := hasDerivAt_polar hr hth
  have hzi := hz i t
  rw [hfun] at hzi
  have huniq : amplitudeField mu A (z t) i
      = (((r' : ℂ) + (r t i : ℂ) * I * (th' : ℂ)) * Complex.exp (I * (th t i : ℂ))) :=
    hzi.unique hpol
  have hconj := congrArg (fun w : ℂ => (w * (starRingEnd ℂ) (z t i)).im) huniq
  rw [im_amplitudeField_mul_conj mu A (z t) (r t) (th t) (fun j => hpolar t j) i] at hconj
  have hrhs : ((((r' : ℂ) + (r t i : ℂ) * I * (th' : ℂ)) * Complex.exp (I * (th t i : ℂ)))
      * (starRingEnd ℂ) (z t i)).im = r t i ^ 2 * th' := by
    rw [hpolar t i, map_mul, Complex.conj_ofReal,
      show (((r' : ℂ) + (r t i : ℂ) * I * (th' : ℂ)) * Complex.exp (I * (th t i : ℂ)))
          * ((r t i : ℂ) * (starRingEnd ℂ) (Complex.exp (I * (th t i : ℂ))))
        = ((r t i : ℂ) * ((r' : ℂ) + (r t i : ℂ) * I * (th' : ℂ)))
          * (Complex.exp (I * (th t i : ℂ)) * (starRingEnd ℂ) (Complex.exp (I * (th t i : ℂ)))) by
        ring,
      expI_mul_conj]
    simp only [sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    simp [Complex.mul_im, Complex.mul_re]
    ring
  rw [hrhs] at hconj
  have hri2 : (0 : ℝ) < r t i ^ 2 := by positivity
  have hsum : r t i ^ 2 * (∑ j, A i j * (r t j / r t i) * Real.sin (th t j - th t i))
      = ∑ j, A i j * (r t i * r t j) * Real.sin (th t j - th t i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  exact (mul_left_cancel₀ (ne_of_gt hri2) (hsum.trans hconj)).symm

omit [DecidableEq V] in
/-- **The bridge.** An amplitude trajectory whose amplitudes are positive and
equal across sites has a phase that is a Kuramoto trajectory of the same
coupling. The phase model is this model with the amplitude ratios set to one, so
the loop winding of `Phase5_PhaseLifts` becomes computable from a dynamical state
rather than postulated of a measurement. -/
theorem amplitude_phase_is_kuramoto (sys : KuramotoSystem V) (hom : ∀ i, sys.omega i = 0)
    {mu : ℝ} {z : ℝ → V → ℂ} {r th : ℝ → V → ℝ}
    (hz : is_amplitude_trajectory mu sys.A z)
    (hpolar : ∀ s i, z s i = ((r s i : ℝ) : ℂ) * Complex.exp (I * (th s i : ℂ)))
    (hpos : ∀ s i, 0 < r s i) (huni : ∀ s i j, r s i = r s j)
    (hr : ∀ i, Differentiable ℝ fun s => r s i)
    (hth : ∀ i, Differentiable ℝ fun s => th s i) :
    is_kuramoto_trajectory sys th := by
  intro i t
  have hthd := (hth i t).hasDerivAt
  have key := deriv_phase_of_amplitude_trajectory hz hpolar (hpos t i) (hr i t).hasDerivAt hthd
  have hratio : ∑ j, sys.A i j * (r t j / r t i) * Real.sin (th t j - th t i)
      = ∑ j, sys.A i j * Real.sin (th t j - th t i) :=
    Finset.sum_congr rfl fun j _ => by
      rw [huni t j i, div_self (ne_of_gt (hpos t i)), mul_one]
  rw [hom i, zero_add, ← hratio, ← key]
  exact hthd

section AmplitudeWindings

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A winding given an amplitude: `z g = a · chi g`. Its modulus is `|a|` at
every site — no site is a zero, which is why nothing here is a phase
singularity. -/
noncomputable def charState (W : WindingData G) (a : ℝ) : G → ℂ :=
  fun g => ((a : ℝ) : ℂ) * W.chi g

/-- The coupling eigenvalue a winding sees: `λ = ∑ d, f d * (Re (chi d) - 1)`,
real by the evenness of `f`, and nonpositive for a nonnegative kernel. It is
what shifts the existence threshold away from `μ > 0`. -/
noncomputable def charLambda (W : WindingData G) (f : G → ℝ) : ℝ :=
  ∑ d, f d * ((W.chi d).re - 1)

omit [Fintype G] [DecidableEq G] in
lemma charState_add (W : WindingData G) (a : ℝ) (i d : G) :
    charState W a (i + d) = charState W a i * W.chi d := by
  rw [charState, charState, W.map_add]
  ring

omit [Fintype G] [DecidableEq G] in
/-- **No site of a winding state is a zero.** The modulus is constant across the
sites, which is the exact sense in which these solutions are windings and not
spirals: a phase singularity is a point at which the amplitude vanishes. -/
@[simp] lemma norm_charState (W : WindingData G) (a : ℝ) (g : G) :
    ‖charState W a g‖ = |a| := by
  rw [charState, norm_mul, W.norm_chi, mul_one, Complex.norm_real, Real.norm_eq_abs]

omit [Fintype G] [DecidableEq G] in
lemma charState_ne_zero (W : WindingData G) {a : ℝ} (ha : a ≠ 0) (g : G) :
    charState W a g ≠ 0 := by
  intro hcon
  have h := norm_charState W a g
  rw [hcon, norm_zero] at h
  exact ha (abs_eq_zero.mp h.symm)

omit [DecidableEq G] in
/-- The kernel sum a winding produces is real and equals `charLambda`: the
imaginary part is odd in the separation against an even kernel, so it cancels
exactly as the phase drift does in `circulant_drift_char`. -/
lemma sum_kernel_chi (W : WindingData G) (f : G → ℝ) (hf : ∀ d, f (-d) = f d) :
    ∑ d, ((f d : ℝ) : ℂ) * (W.chi d - 1) = ((charLambda W f : ℝ) : ℂ) := by
  have him : ∑ d : G, f d * (W.chi d).im = 0 :=
    sum_eq_zero_of_odd _ fun d => by
      rw [hf, W.im_chi, W.im_chi, W.sin_psi_neg]; ring
  apply Complex.ext
  · rw [Complex.re_sum, Complex.ofReal_re, charLambda]
    exact Finset.sum_congr rfl fun d _ => by
      rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
  · rw [Complex.im_sum, Complex.ofReal_im, ← him]
    exact Finset.sum_congr rfl fun d _ => by
      rw [Complex.im_ofReal_mul, Complex.sub_im, Complex.one_im, sub_zero]

omit [DecidableEq G] in
/-- **The amplitude field acts on a winding as a single real scalar.** The cubic
term contributes `-a²`, the coupling contributes `charLambda W f`, and the state
itself is carried unchanged: the §6 cancellation with the cubic term absorbed
into the amplitude. -/
theorem amplitudeField_charState (W : WindingData G) (f : G → ℝ)
    (hf : ∀ d, f (-d) = f d) (mu a : ℝ) (i : G) :
    amplitudeField mu (circulantSystem f hf).A (charState W a) i
      = ((mu - a ^ 2 + charLambda W f : ℝ) : ℂ) * charState W a i := by
  have hcoup : ∑ j, (((circulantSystem f hf).A i j : ℝ) : ℂ)
        * (charState W a j - charState W a i)
      = charState W a i * ((charLambda W f : ℝ) : ℂ) := by
    rw [← Fintype.sum_equiv (Equiv.addLeft i)
      (fun d => (((circulantSystem f hf).A i (i + d) : ℝ) : ℂ)
        * (charState W a (i + d) - charState W a i))
      (fun j => (((circulantSystem f hf).A i j : ℝ) : ℂ)
        * (charState W a j - charState W a i)) fun _ => rfl]
    rw [Finset.sum_congr rfl (fun d _ =>
      show (((circulantSystem f hf).A i (i + d) : ℝ) : ℂ)
          * (charState W a (i + d) - charState W a i)
        = charState W a i * (((f d : ℝ) : ℂ) * (W.chi d - 1)) by
        rw [circulantSystem_A, add_sub_cancel_left, charState_add]; ring),
      ← Finset.mul_sum, sum_kernel_chi W f hf]
  simp only [amplitudeField, hcoup, norm_charState]
  rw [show (((|a| : ℝ)) : ℂ) ^ 2 = ((a ^ 2 : ℝ) : ℂ) by
    rw [← Complex.ofReal_pow, sq_abs]]
  push_cast
  ring

omit [DecidableEq G] in
/-- **X2: windings are exact, and they carry an amplitude.** `z g = a · chi g`
is stationary exactly when `a² = μ + λ`. The phase model's winding is the
`a = 1` shadow of this; here the amplitude is determined by the winding and the
kernel together. -/
theorem charState_is_amplitude_trajectory_iff (W : WindingData G) (f : G → ℝ)
    (hf : ∀ d, f (-d) = f d) (mu a : ℝ) (ha : a ≠ 0) :
    is_amplitude_trajectory mu (circulantSystem f hf).A (fun _ => charState W a)
      ↔ a ^ 2 = mu + charLambda W f := by
  rw [is_amplitude_trajectory_const_iff]
  constructor
  · intro h
    have h0 := h 0
    rw [amplitudeField_charState] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · have h2 : mu - a ^ 2 + charLambda W f = 0 := by exact_mod_cast h1
      linarith
    · exact absurd h1 (charState_ne_zero W ha 0)
  · intro h i
    rw [amplitudeField_charState, show mu - a ^ 2 + charLambda W f = 0 by linarith]
    simp

omit [DecidableEq G] in
/-- **X3: an existence band the phase model cannot state.** A winding of
positive amplitude exists **iff** `μ + λ > 0`. -/
theorem exists_charState_iff (W : WindingData G) (f : G → ℝ)
    (hf : ∀ d, f (-d) = f d) (mu : ℝ) :
    (∃ a : ℝ, 0 < a ∧ is_amplitude_trajectory mu (circulantSystem f hf).A
        (fun _ => charState W a))
      ↔ 0 < mu + charLambda W f := by
  constructor
  · rintro ⟨a, ha, htraj⟩
    have h := (charState_is_amplitude_trajectory_iff W f hf mu a (ne_of_gt ha)).1 htraj
    nlinarith
  · intro h
    have hs : 0 < Real.sqrt (mu + charLambda W f) := Real.sqrt_pos.2 h
    exact ⟨Real.sqrt (mu + charLambda W f), hs,
      (charState_is_amplitude_trajectory_iff W f hf mu _ (ne_of_gt hs)).2
        (Real.sq_sqrt h.le)⟩

omit [DecidableEq G] in
/-- **The two layers disagree about the state space.** Outside the band the
phase model still carries the winding as a stationary state —
`char_is_kuramoto_trajectory` constrains neither the winding nor the kernel —
while the amplitude model has no state of that winding at all. -/
theorem phase_model_admits_char_outside_band (W : WindingData G) (f : G → ℝ)
    (hf : ∀ d, f (-d) = f d) (mu : ℝ) (hband : mu + charLambda W f ≤ 0) :
    is_kuramoto_trajectory (circulantSystem f hf) (fun _ => W.psi)
      ∧ ¬ ∃ a : ℝ, 0 < a ∧ is_amplitude_trajectory mu (circulantSystem f hf).A
          (fun _ => charState W a) :=
  ⟨char_is_kuramoto_trajectory W f hf,
    fun h => absurd ((exists_charState_iff W f hf mu).1 h) (not_lt.2 hband)⟩

end AmplitudeWindings

/-! ### The amplitude layer on the ring and on the torus -/

/-- The winding state of §6 given an amplitude: `z k = a · ξ^k` with
`ξ = exp (2πiq/n)`. -/
noncomputable def windingState (n : ℕ) [NeZero n] (q : ℤ) (a : ℝ) : ZMod n → ℂ :=
  charState (ringWinding n q) a

/-- The coupling eigenvalue a `q`-fold winding sees:
`λ q = ∑ d, f d * (cos (2πqd/n) - 1)`. -/
noncomputable def windingLambda (n : ℕ) [NeZero n] (q : ℤ) (f : ZMod n → ℝ) : ℝ :=
  charLambda (ringWinding n q) f

lemma windingLambda_eq (n : ℕ) [NeZero n] (q : ℤ) (f : ZMod n → ℝ) :
    windingLambda n q f = ∑ d, f d * (Real.cos (winding n q d) - 1) :=
  Finset.sum_congr rfl fun d _ => by rw [(ringWinding n q).re_chi]; rfl

lemma windingState_apply (n : ℕ) [NeZero n] (q : ℤ) (a : ℝ) (k : ZMod n) :
    windingState n q a k = ((a : ℝ) : ℂ) * Complex.exp (I * (winding n q k : ℂ)) := rfl

lemma windingState_add (n : ℕ) [NeZero n] (q : ℤ) (a : ℝ) (i d : ZMod n) :
    windingState n q a (i + d)
      = windingState n q a i * Complex.exp (I * (winding n q d : ℂ)) :=
  charState_add (ringWinding n q) a i d

/-- **No site of a winding state is a zero**, which is why nothing here is a
phase singularity: the modulus is constant across the ring. -/
lemma norm_windingState (n : ℕ) [NeZero n] (q : ℤ) (a : ℝ) (k : ZMod n) :
    ‖windingState n q a k‖ = |a| :=
  norm_charState (ringWinding n q) a k

lemma windingState_ne_zero {n : ℕ} [NeZero n] (q : ℤ) {a : ℝ} (ha : a ≠ 0) (k : ZMod n) :
    windingState n q a k ≠ 0 :=
  charState_ne_zero (ringWinding n q) ha k

theorem amplitudeField_windingState {n : ℕ} [NeZero n] (q : ℤ) (f : ZMod n → ℝ)
    (hf : ∀ d, f (-d) = f d) (mu a : ℝ) (i : ZMod n) :
    amplitudeField mu (circulantSystem f hf).A (windingState n q a) i
      = ((mu - a ^ 2 + windingLambda n q f : ℝ) : ℂ) * windingState n q a i :=
  amplitudeField_charState (ringWinding n q) f hf mu a i

/-- **X2 on the ring.** `z k = a · ξ^k` is stationary exactly when
`a² = μ + λ q`. -/
theorem windingState_is_amplitude_trajectory_iff {n : ℕ} [NeZero n] (q : ℤ) (f : ZMod n → ℝ)
    (hf : ∀ d, f (-d) = f d) (mu a : ℝ) (ha : a ≠ 0) :
    is_amplitude_trajectory mu (circulantSystem f hf).A (fun _ => windingState n q a)
      ↔ a ^ 2 = mu + windingLambda n q f :=
  charState_is_amplitude_trajectory_iff (ringWinding n q) f hf mu a ha

/-- **X3 on the ring.** A `q`-fold winding of positive amplitude exists **iff**
`μ + λ q > 0`. -/
theorem exists_windingState_iff {n : ℕ} [NeZero n] (q : ℤ) (f : ZMod n → ℝ)
    (hf : ∀ d, f (-d) = f d) (mu : ℝ) :
    (∃ a : ℝ, 0 < a ∧ is_amplitude_trajectory mu (circulantSystem f hf).A
        (fun _ => windingState n q a))
      ↔ 0 < mu + windingLambda n q f :=
  exists_charState_iff (ringWinding n q) f hf mu

theorem phase_model_admits_winding_outside_band {n : ℕ} [NeZero n] (q : ℤ) (f : ZMod n → ℝ)
    (hf : ∀ d, f (-d) = f d) (mu : ℝ) (hband : mu + windingLambda n q f ≤ 0) :
    is_kuramoto_trajectory (circulantSystem f hf) (fun _ => winding n q)
      ∧ ¬ ∃ a : ℝ, 0 < a ∧ is_amplitude_trajectory mu (circulantSystem f hf).A
          (fun _ => windingState n q a) :=
  phase_model_admits_char_outside_band (ringWinding n q) f hf mu hband

/-- **The band on the sheet.** The same existence statement on the geometry
`travelling_wave.py` integrates: on the torus a winding of a given pair of
numbers exists exactly where its own kernel eigenvalue clears `-μ`. -/
theorem exists_torus_windingState_iff {n : ℕ} [NeZero n] (q₁ q₂ : ℤ)
    (f : ZMod n × ZMod n → ℝ) (hf : ∀ d, f (-d) = f d) (mu : ℝ) :
    (∃ a : ℝ, 0 < a ∧ is_amplitude_trajectory mu (circulantSystem f hf).A
        (fun _ => charState (torusWinding n q₁ q₂) a))
      ↔ 0 < mu + charLambda (torusWinding n q₁ q₂) f :=
  exists_charState_iff (torusWinding n q₁ q₂) f hf mu

/-- At the half turn `n = 2q` the winding advances by `π` per site. -/
lemma winding_antipodal {n : ℕ} [NeZero n] {q : ℤ} (hq : (n : ℤ) = 2 * q) (k : ZMod n) :
    winding n q k = Real.pi * k.val := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnq : (n : ℝ) = 2 * (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hnq
    exact hn0 hnq
  rw [winding, hnq]
  field_simp

/-- The half-turn winding state is *real*: `ξ = -1`, so the state alternates in
sign along the ring and has no imaginary part to rotate. -/
lemma windingState_antipodal {n : ℕ} [NeZero n] {q : ℤ} (hq : (n : ℤ) = 2 * q) (a : ℝ)
    (k : ZMod n) : windingState n q a k = ((a * (-1) ^ k.val : ℝ) : ℂ) := by
  rw [windingState_apply, winding_antipodal hq,
    show I * ((Real.pi * (k.val : ℕ) : ℝ) : ℂ) = (k.val : ℂ) * ((Real.pi : ℂ) * I) by
      push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  push_cast
  ring

/-- The lab-frame reading of a state of the rotating frame: `u i t = Re (z i e^{iΩt})`. -/
noncomputable def labField (z : V → ℂ) (Om : ℝ) (i : V) (t : ℝ) : ℝ :=
  (z i * Complex.exp (I * ((Om * t : ℝ) : ℂ))).re

theorem labField_windingState_antipodal {n : ℕ} [NeZero n] {q : ℤ} (hq : (n : ℤ) = 2 * q)
    (a Om : ℝ) (k : ZMod n) (t : ℝ) :
    labField (windingState n q a) Om k t = a * (-1) ^ k.val * Real.cos (Om * t) := by
  rw [labField, windingState_antipodal hq, Complex.re_ofReal_mul, exp_I_re]

/-- **X4: a standing wave.** Inside the band, the half-turn winding is a real
stationary state whose lab-frame reading is `a · (-1)^k · cos (Ωt)`: one spatial
profile, one common time factor, every site in antiphase with its neighbours.
This is `cos(kx)cos(ωt)` at `k = π` in the framework's own integrated dynamics,
and the phase model has no such object because there every site has unit
modulus. The wave stands rather than travels, and it has no amplitude node —
`norm_windingState` puts the modulus at `|a|` everywhere. -/
theorem standing_wave_of_amplitude_band {n : ℕ} [NeZero n] {q : ℤ} (hq : (n : ℤ) = 2 * q)
    (f : ZMod n → ℝ) (hf : ∀ d, f (-d) = f d) (mu : ℝ)
    (hband : 0 < mu + windingLambda n q f) (Om : ℝ) :
    ∃ a : ℝ, 0 < a ∧
      is_amplitude_trajectory mu (circulantSystem f hf).A (fun _ => windingState n q a) ∧
      (∀ k : ZMod n, (windingState n q a k).im = 0) ∧
      ∀ (k : ZMod n) (t : ℝ),
        labField (windingState n q a) Om k t = a * (-1) ^ k.val * Real.cos (Om * t) := by
  obtain ⟨a, ha, htraj⟩ := (exists_windingState_iff q f hf mu).2 hband
  exact ⟨a, ha, htraj, fun k => by rw [windingState_antipodal hq, Complex.ofReal_im],
    fun k t => labField_windingState_antipodal hq a Om k t⟩


/-! ## 8. Defects, and why the exact solutions carry none

`spatial_kernel.defect_winding` reads a phase field's defect density by summing
four wrapped phase differences around every periodic `2×2` plaquette and
rounding the total to a whole turn. A phase singularity — the object
`townsend2015` and `xu2023` measure, and the one the sweep counts — is a
plaquette whose total is not zero, and it is a point at which the amplitude
vanishes.

This section says two things about that observable, and together they are the
reason the amplitude layer of §7 reaches a winding and not a spiral.

* `plaquetteCirculation_eq_zero_of_winding` — every state §7 exhibits has
  circulation **exactly** zero on every plaquette. The phase difference across a
  separation depends only on the separation, so the four sides of a plaquette
  cancel in pairs. Going to `ZMod n × ZMod n` does not change this: the torus
  supplies more windings, not defects.
* `sum_plaquetteCirculation_eq_zero` and `no_isolated_defect` — on a torus the
  circulations of *any* phase field sum to zero, because each edge is traversed
  once in each direction. So a defect cannot sit alone: they come in cancelling
  pairs. This holds of every field, not only of the exact ones, and it is what
  makes "a single spiral" not a state this geometry has.

The angle convention is a parameter rather than a definition. `_wrap` in
`spatial_kernel.py` is `2π`-periodic and odd away from the antipode, and those
two properties are exactly what the proofs consume; taking them as hypotheses
keeps the antipodal case visible instead of hidden inside a `%`. -/

section Defects

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
private lemma real_of_expI_eq {x y : ℝ}
    (h : Complex.exp (I * (x : ℂ)) = Complex.exp (I * (y : ℂ))) :
    ∃ k : ℤ, x = y + k * (2 * Real.pi) := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hmul : (I : ℂ) * ((x : ℝ) : ℂ) = I * (((y + k * (2 * Real.pi) : ℝ)) : ℂ) := by
    rw [hk]; push_cast; ring
  exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero hmul

omit [Fintype G] [DecidableEq G] in
/-- The phase advance across a separation is the phase of that separation, up to
whole turns. This is `expI_psi_sub` read back through the lift. -/
lemma psi_sub_eq_add_int_mul (W : WindingData G) (i d : G) :
    ∃ k : ℤ, W.psi (i + d) - W.psi i = W.psi d + k * (2 * Real.pi) :=
  real_of_expI_eq (by rw [W.expI_psi_sub, W.lift])

omit [Fintype G] [DecidableEq G] in
lemma psi_neg_eq_add_int_mul (W : WindingData G) (d : G) :
    ∃ k : ℤ, W.psi (-d) = - W.psi d + k * (2 * Real.pi) := by
  refine real_of_expI_eq ?_
  rw [W.lift, W.chi_neg, ← W.lift d, ← Complex.exp_conj]
  congr 1
  simp

/-- The circulation of a phase field around the periodic plaquette at `g` with
sides `e₁` and `e₂`, read through an angle convention `wrap`: the four wrapped
differences around the loop `g → g + e₂ → g + e₁ + e₂ → g + e₁ → g`. This is
`spatial_kernel.defect_winding` before its division by `2π` and its rounding,
and the loop is the one that function traverses. -/
noncomputable def plaquetteCirculation (wrap : ℝ → ℝ) (theta : G → ℝ) (e₁ e₂ g : G) : ℝ :=
  wrap (theta (g + e₂) - theta g)
    + wrap (theta (g + e₁ + e₂) - theta (g + e₂))
    + wrap (theta (g + e₁) - theta (g + e₁ + e₂))
    + wrap (theta g - theta (g + e₁))

omit [Fintype G] [DecidableEq G] in
lemma expI_psi_sub' (W : WindingData G) (a b : G) :
    Complex.exp (I * ((W.psi b - W.psi a : ℝ) : ℂ)) = W.chi (b - a) := by
  have h := W.expI_psi_sub a (b - a)
  rw [show a + (b - a) = b by abel] at h
  exact h

omit [Fintype G] [DecidableEq G] in
/-- The wrapped phase difference between two sites depends only on the
separation between them. This is the whole content of "a winding has no defect":
the four sides of a plaquette are read from the same two separations twice. -/
lemma wrap_psi_sub (W : WindingData G) {wrap : ℝ → ℝ}
    (hper : ∀ (x : ℝ) (k : ℤ), wrap (x + k * (2 * Real.pi)) = wrap x) (a b : G) :
    wrap (W.psi b - W.psi a) = wrap (W.psi (b - a)) := by
  obtain ⟨k, hk⟩ := real_of_expI_eq
    (show Complex.exp (I * ((W.psi b - W.psi a : ℝ) : ℂ))
        = Complex.exp (I * (W.psi (b - a) : ℂ)) by rw [expI_psi_sub' W a b, W.lift])
  rw [hk, hper]

omit [Fintype G] [DecidableEq G] in
lemma wrap_psi_neg (W : WindingData G) {wrap : ℝ → ℝ}
    (hper : ∀ (x : ℝ) (k : ℤ), wrap (x + k * (2 * Real.pi)) = wrap x)
    (hodd : ∀ x : ℝ, wrap (-x) = - wrap x) (d : G) :
    wrap (W.psi (-d)) = - wrap (W.psi d) := by
  obtain ⟨k, hk⟩ := psi_neg_eq_add_int_mul W d
  rw [hk, hper, hodd]

omit [Fintype G] [DecidableEq G] in
/-- **A winding carries no defect.** Every state of §7 has circulation exactly
zero around every plaquette: the phase advance across a separation does not
depend on where the separation is taken, so the two `e₁` sides of the plaquette
cancel and so do the two `e₂` sides. Nothing here is an approximation or a
density — it is zero.

This is the sense in which these solutions are windings and not spirals, and
passing to `ZMod n × ZMod n` does not improve it: the torus supplies windings
around its two non-contractible loops, and a spiral is a winding around a
contractible one, which `norm_charState` forbids by keeping the modulus equal at
every site. -/
theorem plaquetteCirculation_eq_zero_of_winding (W : WindingData G) {wrap : ℝ → ℝ}
    (hper : ∀ (x : ℝ) (k : ℤ), wrap (x + k * (2 * Real.pi)) = wrap x)
    (hodd : ∀ x : ℝ, wrap (-x) = - wrap x) (e₁ e₂ g : G) :
    plaquetteCirculation wrap W.psi e₁ e₂ g = 0 := by
  rw [plaquetteCirculation, wrap_psi_sub W hper, wrap_psi_sub W hper,
    wrap_psi_sub W hper, wrap_psi_sub W hper,
    show g + e₂ - g = e₂ by abel, show g + e₁ + e₂ - (g + e₂) = e₁ by abel,
    show g + e₁ - (g + e₁ + e₂) = -e₂ by abel, show g - (g + e₁) = -e₁ by abel,
    wrap_psi_neg W hper hodd e₂, wrap_psi_neg W hper hodd e₁]
  ring

omit [DecidableEq G] in
/-- **On a torus the defects cancel.** For *any* phase field, the circulations
of all plaquettes sum to zero: each edge is traversed once in each direction, so
an antisymmetric angle convention telescopes. No hypothesis on the field enters
— this is the geometry, not the dynamics. -/
theorem sum_plaquetteCirculation_eq_zero {wrap : ℝ → ℝ}
    (hodd : ∀ x : ℝ, wrap (-x) = - wrap x) (theta : G → ℝ) (e₁ e₂ : G) :
    ∑ g, plaquetteCirculation wrap theta e₁ e₂ g = 0 := by
  set D : G → G → ℝ := fun a b => wrap (theta b - theta a) with hD
  have hanti : ∀ a b, D b a = - D a b := by
    intro a b
    rw [hD]
    simp only
    rw [show theta a - theta b = -(theta b - theta a) by ring, hodd]
  have hsplit : ∑ g, plaquetteCirculation wrap theta e₁ e₂ g
      = (∑ g : G, D g (g + e₂)) + (∑ g : G, D (g + e₂) (g + e₁ + e₂))
        + (∑ g : G, D (g + e₁ + e₂) (g + e₁)) + (∑ g : G, D (g + e₁) g) := by
    simp only [plaquetteCirculation, hD]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hA : (∑ g : G, D (g + e₂) (g + e₁ + e₂)) = ∑ g : G, D g (g + e₁) :=
    Fintype.sum_equiv (Equiv.addRight e₂)
      (fun g => D (g + e₂) (g + e₁ + e₂)) (fun g => D g (g + e₁))
      (fun g => by simp only [Equiv.coe_addRight]; rw [add_right_comm])
  have hB : (∑ g : G, D (g + e₁ + e₂) (g + e₁)) = - ∑ g : G, D g (g + e₂) := by
    have h2 : (∑ g : G, D (g + e₁) (g + e₁ + e₂)) = ∑ g : G, D g (g + e₂) :=
      Fintype.sum_equiv (Equiv.addRight e₁)
        (fun g => D (g + e₁) (g + e₁ + e₂)) (fun g => D g (g + e₂)) (fun _ => rfl)
    calc (∑ g : G, D (g + e₁ + e₂) (g + e₁))
        = ∑ g : G, -D (g + e₁) (g + e₁ + e₂) := Finset.sum_congr rfl fun g _ => hanti _ _
      _ = - ∑ g : G, D (g + e₁) (g + e₁ + e₂) := by rw [Finset.sum_neg_distrib]
      _ = - ∑ g : G, D g (g + e₂) := by rw [h2]
  have hC : (∑ g : G, D (g + e₁) g) = - ∑ g : G, D g (g + e₁) :=
    calc (∑ g : G, D (g + e₁) g)
        = ∑ g : G, -D g (g + e₁) := Finset.sum_congr rfl fun g _ => hanti _ _
      _ = - ∑ g : G, D g (g + e₁) := by rw [Finset.sum_neg_distrib]
  rw [hsplit, hA, hB, hC]
  ring

/-- **A defect cannot sit alone.** If every plaquette but one has zero
circulation then so does that one. A single spiral is therefore not a state of
this geometry at all, whatever dynamics produced it: defects arrive in
cancelling pairs. -/
theorem no_isolated_defect {wrap : ℝ → ℝ}
    (hodd : ∀ x : ℝ, wrap (-x) = - wrap x) (theta : G → ℝ) (e₁ e₂ : G) (g₀ : G)
    (h : ∀ g, g ≠ g₀ → plaquetteCirculation wrap theta e₁ e₂ g = 0) :
    plaquetteCirculation wrap theta e₁ e₂ g₀ = 0 := by
  have hsum := sum_plaquetteCirculation_eq_zero hodd theta e₁ e₂
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ g₀),
    Finset.sum_eq_zero (fun g hg => h g (Finset.ne_of_mem_erase hg)), zero_add] at hsum
  exact hsum

end Defects

/-- **The sheet's exact states carry no defect.** `travelling_wave.py` reports a
near-zero defect density for its twisted runs; this says the exact stationary
states of that geometry have none at all, so the measurement is consistent with
the model rather than evidence of anything further. -/
theorem torusWinding_plaquetteCirculation_eq_zero {n : ℕ} [NeZero n] (q₁ q₂ : ℤ)
    {wrap : ℝ → ℝ}
    (hper : ∀ (x : ℝ) (k : ℤ), wrap (x + k * (2 * Real.pi)) = wrap x)
    (hodd : ∀ x : ℝ, wrap (-x) = - wrap x) (e₁ e₂ g : ZMod n × ZMod n) :
    plaquetteCirculation wrap (torusWinding n q₁ q₂).psi e₁ e₂ g = 0 :=
  plaquetteCirculation_eq_zero_of_winding (torusWinding n q₁ q₂) hper hodd e₁ e₂ g

end PhysicsOfConsciousness
