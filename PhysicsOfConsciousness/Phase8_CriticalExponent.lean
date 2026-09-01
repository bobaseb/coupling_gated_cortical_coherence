import PhysicsOfConsciousness.Phase8_SelfConsistency

/-!
# Phase 8 — the mean-field critical exponent

This module differentiates the von Mises moments under the integral and applies
Taylor's theorem to the ratio `E(a) = vonMisesSRatio a`.  It proves

`E(a) = 1/2 - a²/16 + o(a²)`

and uses the coherent level-set equation to obtain the path-independent limit
`r² / (K - 2D) → 1/D`.  Thus the stationary coherent solution has critical
exponent `β = 1/2`.

This is a theorem about solutions of the stationary self-consistency equation.
It proves neither dynamical selection nor the time course of a threshold
crossing.  Inferring a square-root recovery foot additionally assumes that the
physical coupling crosses `2D` with non-zero speed.
-/

open Real MeasureTheory intervalIntegral Set Filter Asymptotics
open scoped Topology

namespace PhysicsOfConsciousness

/-- The `n`th cosine moment of the unnormalized von Mises weight. -/
noncomputable def vmMoment (n : ℕ) (a : ℝ) : ℝ :=
  ∫ θ in (-π)..π, Real.cos θ ^ n * Real.exp (a * Real.cos θ)

/-- Differentiating a von Mises moment raises its cosine power by one.

The proof differentiates under the integral using the uniform bound
`exp (|a| + 1)` on a unit neighbourhood of the parameter. -/
lemma hasDerivAt_vmMoment (n : ℕ) (a : ℝ) :
    HasDerivAt (vmMoment n) (vmMoment (n + 1) a) a := by
  unfold vmMoment
  let B : ℝ := Real.exp (|a| + 1)
  have hB : Continuous (fun _ : ℝ => B) := continuous_const
  refine intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ : ℝ => Real.cos θ ^ n * Real.exp (x * Real.cos θ))
    (F' := fun x θ : ℝ => Real.cos θ ^ (n + 1) * Real.exp (x * Real.cos θ))
    (x₀ := a) (s := Metric.ball a 1)
    (μ := volume) (a := -π) (b := π) (bound := fun _ => B)
      (Metric.ball_mem_nhds a zero_lt_one) ?_ ?_ ?_ ?_
      (hB.intervalIntegrable (-π) π) ?_ |>.2
  · exact Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous (fun θ : ℝ =>
        Real.cos θ ^ n * Real.exp (x * Real.cos θ))).aestronglyMeasurable
  · exact (by fun_prop : Continuous (fun θ : ℝ =>
      Real.cos θ ^ n * Real.exp (a * Real.cos θ))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun θ : ℝ =>
      Real.cos θ ^ (n + 1) * Real.exp (a * Real.cos θ))).aestronglyMeasurable
  · filter_upwards with θ hθ
    intro x hx
    simp only [Real.norm_eq_abs]
    have hcos : |Real.cos θ| ≤ 1 := abs_cos_le_one θ
    have hxa : |x - a| < 1 := by simpa [Real.dist_eq] using hx
    have hxabs : |x| ≤ |a| + 1 := by
      calc |x| = |(x - a) + a| := by congr 1 ; ring
           _ ≤ |x - a| + |a| := abs_add_le _ _
           _ ≤ |a| + 1 := by linarith
    rw [abs_mul, abs_pow, abs_exp]
    have he : Real.exp (x * Real.cos θ) ≤ B := by
      apply Real.exp_le_exp.mpr
      calc x * Real.cos θ ≤ |x * Real.cos θ| := le_abs_self _
           _ = |x| * |Real.cos θ| := abs_mul _ _
           _ ≤ (|a| + 1) * 1 := mul_le_mul hxabs hcos (abs_nonneg _) (by positivity)
           _ = |a| + 1 := mul_one _
    have hp : |Real.cos θ| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hcos
    exact (mul_le_mul hp he (Real.exp_pos _).le zero_le_one).trans_eq (one_mul B)
  · filter_upwards with θ hθ
    intro x hx
    simpa only [id_eq, one_mul, pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id x).mul_const (Real.cos θ)).exp.const_mul (Real.cos θ ^ n))

/-- The zeroth moment at zero concentration. -/
@[simp] lemma vmMoment_zero_zero : vmMoment 0 0 = 2 * π := by simp [vmMoment]; ring
/-- The first moment at zero concentration. -/
@[simp] lemma vmMoment_one_zero : vmMoment 1 0 = 0 := by simp [vmMoment]
/-- The second moment at zero concentration. -/
@[simp] lemma vmMoment_two_zero : vmMoment 2 0 = π := by simp [vmMoment, integral_cos_sq]
/-- The third moment at zero concentration. -/
@[simp] lemma vmMoment_three_zero : vmMoment 3 0 = 0 := by
  simp [vmMoment, integral_cos_pow_three]
/-- The fourth moment at zero concentration. -/
@[simp] lemma vmMoment_four_zero : vmMoment 4 0 = 3 * π / 4 := by
  simp [vmMoment, integral_cos_pow]
  ring

/-- Every von Mises moment is differentiable in its concentration. -/
lemma differentiable_vmMoment (n : ℕ) : Differentiable ℝ (vmMoment n) :=
  fun a => (hasDerivAt_vmMoment n a).differentiableAt

/-- The derivative of a moment, as a function equality. -/
lemma deriv_vmMoment (n : ℕ) : deriv (vmMoment n) = vmMoment (n + 1) := by
  funext a
  exact (hasDerivAt_vmMoment n a).deriv

/-- Two derivatives of each moment suffice for the second-order expansion. -/
lemma contDiff_two_vmMoment (n : ℕ) : ContDiff ℝ 2 (vmMoment n) := by
  apply (contDiff_succ_iff_deriv (n := 1)).2
  refine ⟨differentiable_vmMoment n, by simp, ?_⟩
  rw [deriv_vmMoment, contDiff_one_iff_deriv]
  refine ⟨differentiable_vmMoment (n + 1), ?_⟩
  rw [deriv_vmMoment]
  exact (differentiable_vmMoment (n + 2)).continuous

/-- Rewrites `E(a)` using the zeroth and second cosine moments. -/
lemma vonMisesSRatio_eq_moments (a : ℝ) :
    vonMisesSRatio a = 1 - vmMoment 2 a / vmMoment 0 a := by
  rw [vonMisesSRatio]
  have hz : vonMisesZ a = vmMoment 0 a := by simp [vonMisesZ, vmMoment, vonMisesWeight]
  have hs : vonMisesS a = vmMoment 0 a - vmMoment 2 a := by
    rw [vonMisesS, vmMoment, vmMoment]
    rw [← intervalIntegral.integral_sub]
    · congr 1
      funext θ
      simp only [pow_zero, one_mul, vonMisesWeight, mul_comm]
      rw [show Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
      ring
    · exact (by fun_prop : Continuous (fun θ : ℝ =>
        Real.cos θ ^ 0 * Real.exp (a * Real.cos θ))).intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun θ : ℝ =>
        Real.cos θ ^ 2 * Real.exp (a * Real.cos θ))).intervalIntegrable _ _
  rw [hz, hs]
  field_simp [show vmMoment 0 a ≠ 0 by simpa [← hz] using (vonMisesZ_pos a).ne']

/-- The ratio `E` is twice continuously differentiable. -/
lemma contDiff_two_vonMisesSRatio : ContDiff ℝ 2 vonMisesSRatio := by
  have h0 := contDiff_two_vmMoment 0
  have h2 := contDiff_two_vmMoment 2
  have hn : ∀ a, vmMoment 0 a ≠ 0 := by
    intro a
    simpa [vmMoment, vonMisesZ, vonMisesWeight] using (vonMisesZ_pos a).ne'
  rw [show vonMisesSRatio = fun a => 1 - vmMoment 2 a / vmMoment 0 a by
    funext a; exact vonMisesSRatio_eq_moments a]
  exact contDiff_const.sub (h2.div h0 hn)

/-- The quotient-rule expression for the derivative of `E`. -/
noncomputable def sRatioDeriv (a : ℝ) : ℝ :=
  -((vmMoment 3 a * vmMoment 0 a - vmMoment 2 a * vmMoment 1 a) /
    vmMoment 0 a ^ 2)

/-- The derivative of `E` is `sRatioDeriv`. -/
lemma hasDerivAt_vonMisesSRatio (a : ℝ) :
    HasDerivAt vonMisesSRatio (sRatioDeriv a) a := by
  rw [show vonMisesSRatio = fun x => 1 - vmMoment 2 x / vmMoment 0 x by
    funext x; exact vonMisesSRatio_eq_moments x]
  have h0 := hasDerivAt_vmMoment 0 a
  have h2 := hasDerivAt_vmMoment 2 a
  have hn : vmMoment 0 a ≠ 0 := by
    simpa [vmMoment, vonMisesZ, vonMisesWeight] using (vonMisesZ_pos a).ne'
  apply ((hasDerivAt_const a 1).sub (h2.div h0 hn)).congr_deriv
  simp only [sRatioDeriv]
  ring

/-- Symmetry makes the first derivative of `E` vanish at zero. -/
lemma sRatioDeriv_zero : sRatioDeriv 0 = 0 := by
  simp [sRatioDeriv, vmMoment, integral_cos_sq, integral_cos_pow_three]

/-- The second derivative of `E` at zero is `-1/8`. -/
lemma hasDerivAt_sRatioDeriv_zero : HasDerivAt sRatioDeriv (-1 / 8) 0 := by
  rw [show sRatioDeriv = -((vmMoment 3 * vmMoment 0 - vmMoment 2 * vmMoment 1) /
      vmMoment 0 ^ 2) by
    funext a
    rfl]
  have h0 := hasDerivAt_vmMoment 0 0
  have h1 := hasDerivAt_vmMoment 1 0
  have h2 := hasDerivAt_vmMoment 2 0
  have h3 := hasDerivAt_vmMoment 3 0
  have hn : vmMoment 0 0 ^ 2 ≠ 0 := by
    have hp : (0:ℝ) < π := Real.pi_pos
    simp [vmMoment]
  have hd := (((h3.mul h0).sub (h2.mul h1)).div (h0.pow 2) hn).neg
  apply hd.congr_deriv
  simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat,
    Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  simp [vmMoment, integral_cos_sq, integral_cos_pow_three, integral_cos_pow]
  field_simp [Real.pi_ne_zero]
  ring

/-- Function form of the first-derivative identity. -/
lemma deriv_vonMisesSRatio : deriv vonMisesSRatio = sRatioDeriv := by
  funext a
  exact (hasDerivAt_vonMisesSRatio a).deriv

/-- Function-derivative form of the second-derivative value. -/
lemma deriv_sRatioDeriv_zero : deriv sRatioDeriv 0 = -1 / 8 :=
  hasDerivAt_sRatioDeriv_zero.deriv

/-- **The second-order expansion of the von Mises sine-square mean.**

The remainder is little-o of `a²`, which is the precise second-order statement
needed for the critical exponent.  This does not assert the stronger recorded
`O(a⁴)` remainder; no fourth derivative is required for the result below. -/
theorem vonMisesSRatio_second_order :
    (fun a : ℝ => vonMisesSRatio a - (1 / 2 - a ^ 2 / 16)) =o[𝓝 0]
      (fun a => a ^ 2) := by
  have ht := taylor_isLittleO_univ (x₀ := (0 : ℝ)) contDiff_two_vonMisesSRatio
  have hi : iteratedDeriv 2 vonMisesSRatio 0 = -1 / 8 := by
    rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
      show 1 = 0 + 1 by norm_num, iteratedDeriv_succ]
    simp [deriv_vonMisesSRatio, deriv_sRatioDeriv_zero]
  have hp : ∀ a : ℝ, taylorWithinEval vonMisesSRatio 2 univ 0 a =
      1 / 2 - a ^ 2 / 16 := by
    intro a
    rw [show 2 = 1 + 1 by norm_num, taylorWithinEval_succ]
    rw [taylorWithinEval_succ]
    simp [hi, deriv_vonMisesSRatio, sRatioDeriv_zero]
    ring
  refine ht.congr' (Filter.Eventually.of_forall fun a => ?_)
    (Filter.Eventually.of_forall fun a => ?_)
  · change vonMisesSRatio a - taylorWithinEval vonMisesSRatio 2 univ 0 a = _
    rw [hp]
  · ring

/-- **The coherent stationary branch has mean-field exponent `β = 1/2`.**

Along any family of positive coherent solutions approaching `K = 2D` from
above, `r²/(K-2D) → 1/D`.  Equivalently, the positive order parameter is
asymptotic to `sqrt ((K-2D)/D)`.  The hypotheses explicitly require stationary
solutions approaching zero; the theorem proves no stability, dynamical
selection, or time dependence. -/
theorem coherent_solution_critical_exponent
    {α : Type*} {l : Filter α} {K r : α → ℝ} {D : ℝ}
    (hD : 0 < D) (hK : Tendsto K l (𝓝 (2 * D))) (hr : Tendsto r l (𝓝 0))
    (hcoh : ∀ᶠ x in l, 2 * D < K x ∧ 0 < r x ∧
      r x = selfConsistency (K x) D (r x)) :
    Tendsto (fun x => r x ^ 2 / (K x - 2 * D)) l (𝓝 (1 / D)) := by
  let a : α → ℝ := fun x => K x * r x / D
  let rem : ℝ → ℝ := fun y => vonMisesSRatio y - (1 / 2 - y ^ 2 / 16)
  let q : ℝ → ℝ := fun y => rem y / y ^ 2
  have ha : Tendsto a l (𝓝 0) := by
    dsimp only [a]
    convert (hK.mul hr).div_const D using 2 ; ring
  have hq0 : Tendsto (fun x => q (a x)) l (𝓝 0) := by
    exact vonMisesSRatio_second_order.tendsto_div_nhds_zero.comp ha
  have hden : Tendsto (fun x => K x ^ 3 * (1 / 8 - 2 * q (a x))) l
      (𝓝 ((2 * D) ^ 3 * (1 / 8 - 2 * 0))) := by
    exact (hK.pow 3).mul (tendsto_const_nhds.sub (hq0.const_mul 2))
  have hlim : Tendsto (fun x => D ^ 2 / (K x ^ 3 * (1 / 8 - 2 * q (a x)))) l
      (𝓝 (D ^ 2 / ((2 * D) ^ 3 * (1 / 8 - 2 * 0)))) := by
    apply tendsto_const_nhds.div hden
    have : (2 * D) ^ 3 * (1 / 8 - 2 * 0) ≠ 0 := by positivity
    exact this
  have hconst : D ^ 2 / ((2 * D) ^ 3 * (1 / 8 - 2 * 0)) = 1 / D := by
    field_simp
    ring
  rw [hconst] at hlim
  apply hlim.congr'
  filter_upwards [hcoh] with x hx
  rcases hx with ⟨hKx, hrx, hfix⟩
  have hKpos : 0 < K x := lt_trans (by positivity : 0 < 2 * D) hKx
  have hane : a x ≠ 0 := by
    dsimp only [a]
    positivity
  have hdeltane : K x - 2 * D ≠ 0 := ne_of_gt (sub_pos.mpr hKx)
  have hE : vonMisesSRatio (a x) = D / K x := by
    exact (coherent_iff_sRatio_eq hD hKpos (ne_of_gt hrx)).mp hfix
  have hkey : K x - 2 * D = K x * (a x) ^ 2 * (1 / 8 - 2 * q (a x)) := by
    dsimp only [q, rem]
    field_simp [hane]
    rw [hE]
    field_simp
    ring
  rw [hkey]
  dsimp only [a]
  field_simp

/-! ### The exponent theorem is not a statement about an empty family

`coherent_solution_critical_exponent` draws its conclusion from an
`∀ᶠ`-clause, and an `∀ᶠ`-clause holds vacuously on the bottom filter.  The
theorem is therefore worth exactly as much as a family satisfying it, and this
section exhibits one rather than asserting that it exists: the coherent branch
itself, selected above threshold by `supercritical_fixed_point_existsUnique`
and approached along `𝓝[>] (2 * D)`.
-/

/-- The coherent branch as a function of the coupling: above threshold, the
unique positive solution of the self-consistency equation; elsewhere `0`. -/
noncomputable def coherentBranch (D K : ℝ) : ℝ :=
  if h : 0 < D ∧ critical_coupling D < K then
    (supercritical_fixed_point_existsUnique h.1 h.2).choose
  else 0

/-- Above threshold the branch is a positive solution of at most one. -/
lemma coherentBranch_spec {D K : ℝ} (hD : 0 < D) (hK : 2 * D < K) :
    0 < coherentBranch D K ∧ coherentBranch D K ≤ 1 ∧
      coherentBranch D K = selfConsistency K D (coherentBranch D K) := by
  have hK' : critical_coupling D < K := by rwa [critical_coupling]
  rw [coherentBranch, dite_eq_left_of_eq_true (eq_true ⟨hD, hK'⟩)]
  exact (supercritical_fixed_point_existsUnique hD hK').choose_spec.1

/-- The branch tends to zero as the coupling descends to threshold.  This is
`coherent_branch_continuous_at_threshold` read as a limit. -/
lemma coherentBranch_tendsto_zero {D : ℝ} (hD : 0 < D) :
    Tendsto (coherentBranch D) (𝓝[>] (2 * D)) (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hbranch⟩ := coherent_branch_continuous_at_threshold hD hε
  have hmem : Set.Ioo (2 * D) (2 * D + δ) ∈ 𝓝[>] (2 * D) :=
    Ioo_mem_nhdsGT (by linarith)
  filter_upwards [hmem] with K hK
  obtain ⟨hpos, _, hfix⟩ := coherentBranch_spec hD hK.1
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  exact hbranch K _ (by rw [critical_coupling]; exact hK.1)
    (by rw [critical_coupling]; exact hK.2) hpos hfix

/-- **The coherent branch witnesses the critical exponent.**

Every hypothesis of `coherent_solution_critical_exponent` is discharged by the
branch the development already proves to exist, so the exponent `β = 1/2` is a
statement about the solutions of this equation and not about an empty family.
As before, this is stationary-solution asymptotics: no stability, dynamical
selection or time course is claimed. -/
theorem coherentBranch_critical_exponent {D : ℝ} (hD : 0 < D) :
    Tendsto (fun K => coherentBranch D K ^ 2 / (K - 2 * D)) (𝓝[>] (2 * D))
      (𝓝 (1 / D)) := by
  refine coherent_solution_critical_exponent hD
    (tendsto_id.mono_left nhdsWithin_le_nhds) (coherentBranch_tendsto_zero hD) ?_
  filter_upwards [self_mem_nhdsWithin] with K hK
  obtain ⟨hpos, _, hfix⟩ := coherentBranch_spec hD hK
  exact ⟨hK, hpos, hfix⟩

end PhysicsOfConsciousness
