import Mathlib

/-!
# Phase 10 — typical agreement is set by effective resistance

The chaining bound through overlapping patches is a worst case: it is attained
by a phase gradient, and it grows linearly in the number of hops. Noise does not
produce that configuration. At identical natural frequencies a noisy coupled
sheet is a gradient system whose stationary density is `∝ exp(−E_K(θ)/D)`, and
in the harmonic approximation the variance of the phase difference between two
sites is `D` times their effective resistance, the couplings `K i j` acting as
conductances. That identity is Gaussian algebra and is checked numerically in
`simulations/unity_agreement.py`; this module proves the parts that hold without
the approximation.

* **`energy K u`.** The Dirichlet energy `½ Σ_{i,j} K i j (u i − u j)²` of a
  phase configuration `u`.
* **`conductance K a b`.** The effective conductance between `a` and `b`: the
  least energy of a configuration whose phase difference across them is one.
  The effective resistance is its reciprocal.

The results:

* **`conductance_mul_sq_le_energy`.** Every configuration's phase difference
  across `a, b` is bounded by its energy: `C (u a − u b)² ≤ E_K(u)`. The
  resistance is thus the best constant turning energy into disagreement.
* **`conductance_mono`** (Rayleigh monotonicity). Adding coupling never lowers
  the conductance. A long-range tail added to a short-range kernel can
  therefore only improve the typical agreement, whatever its shape.
* **`le_conductance_of_edge`.** A direct coupling caps the resistance:
  `K a b ≤ C`, at any distance between `a` and `b`.
* **`conductance_le_shell`** (Nash-Williams). Nested shells around `a`, with
  the coupling reaching at most one shell, act as conductors in series: the
  conductance is at most `1 / Σ_k 1/C_k`, `C_k` the coupling crossing shell `k`.
* **`conductance_mul_log_le`.** When the crossing coupling grows at most
  linearly with the shell index, as it does for bounded-range coupling on a
  planar sheet, the resistance grows at least like `log n / c`. Short-range
  coupling therefore cannot give distance-independent agreement on a sheet;
  how slowly it degrades is set by `c`, which grows with the kernel's width.
* **`integral_dist_sq_le`.** A Lipschitz encoder transfers phase agreement to
  content agreement in mean square: the mean-square content discrepancy is at
  most `L²` times the mean-square phase difference, under any distribution of
  configurations. With the harmonic identity the root-mean-square content
  discrepancy is at most `L √(D / C)`.

Non-vacuity — a series pair of couplings with conductance `½`, raised to at least
`1` by a direct edge, and a shell bound attained on the same row — is
`Examples/AgreementResistance.lean`.
-/

open MeasureTheory

namespace PhysicsOfConsciousness.PhysicalUnity

variable {ι : Type*} [Fintype ι]

/-- The Dirichlet energy of a phase configuration `u` under the couplings `K`. -/
noncomputable def energy (K : ι → ι → ℝ) (u : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ p : ι × ι, K p.1 p.2 * (u p.1 - u p.2) ^ 2

/-- The effective conductance between `a` and `b`: the least energy of a
configuration with unit phase difference across them. -/
noncomputable def conductance (K : ι → ι → ℝ) (a b : ι) : ℝ :=
  sInf (energy K '' {u | u a - u b = 1})

lemma energy_nonneg {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) (u : ι → ℝ) :
    0 ≤ energy K u :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => mul_nonneg (hK _ _) (sq_nonneg _))

lemma energy_smul (K : ι → ι → ℝ) (c : ℝ) (u : ι → ℝ) :
    energy K (c • u) = c ^ 2 * energy K u := by
  have h (p : ι × ι) : K p.1 p.2 * ((c • u) p.1 - (c • u) p.2) ^ 2 =
      c ^ 2 * (K p.1 p.2 * (u p.1 - u p.2) ^ 2) := by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [energy, h, ← Finset.mul_sum]
  ring

lemma energy_mono {K K' : ι → ι → ℝ} (hKK' : ∀ i j, K i j ≤ K' i j) (u : ι → ℝ) :
    energy K u ≤ energy K' u := by
  unfold energy
  gcongr with p
  exact hKK' _ _

lemma bddBelow_energy {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) (s : Set (ι → ℝ)) :
    BddBelow (energy K '' s) :=
  ⟨0, by rintro _ ⟨u, -, rfl⟩; exact energy_nonneg hK u⟩

lemma conductance_nonneg {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) (a b : ι) :
    0 ≤ conductance K a b :=
  Real.sInf_nonneg (by rintro _ ⟨u, -, rfl⟩; exact energy_nonneg hK u)

lemma nonempty_unitDrop [DecidableEq ι] {a b : ι} (hab : a ≠ b) :
    (energy K '' {u : ι → ℝ | u a - u b = 1}).Nonempty :=
  ⟨_, Pi.single a 1, by simp [hab.symm], rfl⟩

/-- **Energy bounds disagreement.** The squared phase difference across `a, b`,
weighted by their effective conductance, never exceeds the configuration's
energy. -/
theorem conductance_mul_sq_le_energy {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (a b : ι) (u : ι → ℝ) : conductance K a b * (u a - u b) ^ 2 ≤ energy K u := by
  set d := u a - u b
  rcases eq_or_ne d 0 with hd | hd
  · simp [hd, energy_nonneg hK u]
  have hv : (d⁻¹ • u) a - (d⁻¹ • u) b = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub]
    exact inv_mul_cancel₀ hd
  have hle : conductance K a b ≤ energy K (d⁻¹ • u) :=
    csInf_le (bddBelow_energy hK _) ⟨_, hv, rfl⟩
  rw [energy_smul, inv_pow] at hle
  have hd2 : 0 < d ^ 2 := by positivity
  calc conductance K a b * d ^ 2 ≤ (d ^ 2)⁻¹ * energy K u * d ^ 2 :=
        mul_le_mul_of_nonneg_right hle hd2.le
    _ = energy K u := by field_simp

/-- **Rayleigh monotonicity.** Adding coupling never lowers the effective
conductance, so it never raises the effective resistance. -/
theorem conductance_mono [DecidableEq ι] {K K' : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hKK' : ∀ i j, K i j ≤ K' i j) {a b : ι} (hab : a ≠ b) :
    conductance K a b ≤ conductance K' a b := by
  refine le_csInf (nonempty_unitDrop hab) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact (csInf_le (bddBelow_energy hK _) ⟨u, hu, rfl⟩).trans (energy_mono hKK' u)

/-- **A direct coupling caps the resistance.** Whatever the distance between `a`
and `b`, their effective conductance is at least the coupling that joins them
directly. -/
theorem le_conductance_of_edge [DecidableEq ι] {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hsym : ∀ i j, K i j = K j i) {a b : ι} (hab : a ≠ b) :
    K a b ≤ conductance K a b := by
  refine le_csInf (nonempty_unitDrop hab) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hu' : u b - u a = -1 := by simp only [Set.mem_ofPred_eq] at hu; linarith
  have hsub : ({(a, b), (b, a)} : Finset (ι × ι)) ⊆ Finset.univ := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p : ι × ι => K p.1 p.2 * (u p.1 - u p.2) ^ 2)
    (fun p _ _ => mul_nonneg (hK _ _) (sq_nonneg _))
  have hne : (a, b) ≠ (b, a) := fun h => hab (Prod.mk.inj h).1
  rw [Finset.sum_pair hne] at hsum
  simp only [Set.mem_ofPred_eq] at hu
  rw [hu, hu', hsym b a] at hsum
  unfold energy
  linarith

/-- Whether the ordered pair `p` straddles the boundary between shell `k` and
shell `k + 1` of the shell index `h`. -/
def Crosses (h : ι → ℕ) (k : ℕ) (p : ι × ι) : Prop :=
  (h p.1 = k ∧ h p.2 = k + 1) ∨ (h p.1 = k + 1 ∧ h p.2 = k)

instance (h : ι → ℕ) (k : ℕ) (p : ι × ι) : Decidable (Crosses h k p) := by
  unfold Crosses; infer_instance

/-- The coupling that crosses from shell `k` to shell `k + 1`. -/
noncomputable def shellCapacity (K : ι → ι → ℝ) (h : ι → ℕ) (k : ℕ) : ℝ :=
  (1 / 2) * ∑ p : ι × ι, if Crosses h k p then K p.1 p.2 else 0

/-- The shell test configuration: the weight of the shells from `i`'s own to the
`n`-th. -/
noncomputable def shellPotential (h : ι → ℕ) (n : ℕ) (t : ℕ → ℝ) (i : ι) : ℝ :=
  ∑ k ∈ Finset.Ico (min (h i) n) n, t k

omit [Fintype ι] in
lemma shellPotential_sub_of_succ (h : ι → ℕ) (n : ℕ) (t : ℕ → ℝ) {i j : ι}
    (hij : h j = h i + 1) :
    shellPotential h n t i - shellPotential h n t j = if h i < n then t (h i) else 0 := by
  unfold shellPotential
  rw [hij]
  split_ifs with hn
  · rw [min_eq_left hn.le, min_eq_left (Nat.succ_le_of_lt hn),
      Finset.sum_eq_sum_Ico_succ_bot hn]
    ring
  · push Not at hn
    rw [min_eq_right hn, min_eq_right (hn.trans (Nat.le_succ _))]
    ring

omit [Fintype ι] in
lemma sq_shellPotential_sub {K : ι → ι → ℝ} {h : ι → ℕ}
    (hrange : ∀ i j, K i j ≠ 0 → h j ≤ h i + 1 ∧ h i ≤ h j + 1) (n : ℕ) (t : ℕ → ℝ)
    (p : ι × ι) :
    K p.1 p.2 * (shellPotential h n t p.1 - shellPotential h n t p.2) ^ 2 =
      ∑ k ∈ Finset.range n, t k ^ 2 * (if Crosses h k p then K p.1 p.2 else 0) := by
  obtain ⟨i, j⟩ := p
  by_cases hK : K i j = 0
  · simp [hK]
  obtain ⟨h1, h2⟩ := hrange i j hK
  rcases (show h i = h j ∨ h j = h i + 1 ∨ h i = h j + 1 by omega) with he | he | he
  · have hc : ∀ k, ¬ Crosses h k (i, j) := by intro k; simp only [Crosses]; omega
    simp [shellPotential, he, hc]
  · have hc : ∀ k, Crosses h k (i, j) ↔ h i = k := by intro k; simp only [Crosses]; omega
    simp only [shellPotential_sub_of_succ h n t he, hc, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hn hn' hn' <;> simp only [Finset.mem_range] at * <;>
      first | (exfalso; omega) | ring
  · have hc : ∀ k, Crosses h k (i, j) ↔ h j = k := by intro k; simp only [Crosses]; omega
    have hsub := shellPotential_sub_of_succ h n t he
    have hneg : shellPotential h n t i - shellPotential h n t j =
        -(shellPotential h n t j - shellPotential h n t i) := by ring
    simp only [hneg, neg_sq, hsub, hc, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hn hn' hn' <;> simp only [Finset.mem_range] at * <;>
      first | (exfalso; omega) | ring

/-- **The energy of the shell configuration** is the shell capacities weighted by
the squared shell steps. -/
lemma energy_shellPotential {K : ι → ι → ℝ} {h : ι → ℕ}
    (hrange : ∀ i j, K i j ≠ 0 → h j ≤ h i + 1 ∧ h i ≤ h j + 1) (n : ℕ) (t : ℕ → ℝ) :
    energy K (shellPotential h n t) = ∑ k ∈ Finset.range n, t k ^ 2 * shellCapacity K h k := by
  unfold energy shellCapacity
  simp only [sq_shellPotential_sub hrange n t]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]; ring

/-- **Shells in series bound the conductance** (Nash-Williams). Let the shell
index `h` put `a` in shell `0` and `b` at or beyond shell `n`, and let the
coupling reach at most one shell: `K i j ≠ 0` only between sites whose shells
differ by at most one. Then the shells act as conductors in series, and the
effective conductance is at most `1 / Σ_{k<n} 1/C_k`, where `C_k` is the coupling
crossing from shell `k` to shell `k + 1`. -/
theorem conductance_le_shell {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) {h : ι → ℕ}
    (hrange : ∀ i j, K i j ≠ 0 → h j ≤ h i + 1 ∧ h i ≤ h j + 1) {a b : ι} {n : ℕ}
    (ha : h a = 0) (hb : n ≤ h b) (hn : n ≠ 0)
    (hC : ∀ k < n, 0 < shellCapacity K h k) :
    conductance K a b ≤ (∑ k ∈ Finset.range n, (shellCapacity K h k)⁻¹)⁻¹ := by
  set C := shellCapacity K h
  set S := ∑ k ∈ Finset.range n, (C k)⁻¹
  have hS : 0 < S := Finset.sum_pos (fun k hk => inv_pos.mpr (hC k (Finset.mem_range.mp hk)))
    (Finset.nonempty_range_iff.mpr hn)
  set t : ℕ → ℝ := fun k => (C k)⁻¹ / S
  have hdrop : shellPotential h n t a - shellPotential h n t b = 1 := by
    simp only [shellPotential, ha, hb, min_eq_left, min_eq_right, Nat.zero_le,
      Finset.Ico_self, Finset.sum_empty, ← Finset.range_eq_Ico, t, ← Finset.sum_div]
    rw [zero_div, sub_zero]
    exact div_self hS.ne'
  have hE : energy K (shellPotential h n t) = S⁻¹ := by
    rw [energy_shellPotential hrange]
    have hk : ∀ k ∈ Finset.range n, t k ^ 2 * C k = (C k)⁻¹ / S ^ 2 := by
      intro k hk
      have := (hC k (Finset.mem_range.mp hk)).ne'
      simp only [t]; field_simp
    rw [Finset.sum_congr rfl hk, ← Finset.sum_div]
    change S / S ^ 2 = S⁻¹
    field_simp
  calc conductance K a b ≤ energy K (shellPotential h n t) :=
        csInf_le (bddBelow_energy hK _) ⟨_, hdrop, rfl⟩
    _ = S⁻¹ := hE

/-- **On a plane, short-range coupling gives resistance growing at least like the
log of the distance.** If the coupling crossing shell `k` grows at most linearly,
`C_k ≤ c (k + 1)` — as it does for a coupling of bounded range on a planar sheet,
where shell `k` has perimeter proportional to `k` — then the effective
resistance to a site beyond shell `n` is at least `log (n + 1) / c`. Agreement
under noise therefore degrades without bound as the sites separate. -/
theorem conductance_mul_log_le {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) {h : ι → ℕ}
    (hrange : ∀ i j, K i j ≠ 0 → h j ≤ h i + 1 ∧ h i ≤ h j + 1) {a b : ι} {n : ℕ}
    (ha : h a = 0) (hb : n ≤ h b) (hn : n ≠ 0) {c : ℝ}
    (hC : ∀ k < n, 0 < shellCapacity K h k)
    (hlin : ∀ k < n, shellCapacity K h k ≤ c * (k + 1)) :
    conductance K a b * Real.log (n + 1) ≤ c := by
  have hc : 0 < c := by
    have := (hC 0 (Nat.pos_of_ne_zero hn)).trans_le (hlin 0 (Nat.pos_of_ne_zero hn))
    simpa using this
  set S := ∑ k ∈ Finset.range n, (shellCapacity K h k)⁻¹
  have hS : Real.log (n + 1) / c ≤ S := by
    have hH := log_add_one_le_harmonic n
    push_cast [harmonic] at hH
    rw [div_le_iff₀ hc, Finset.sum_mul]
    refine hH.trans (Finset.sum_le_sum fun k hk => ?_)
    have hk := Finset.mem_range.mp hk
    rw [inv_mul_eq_div, le_div_iff₀ (hC k hk), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    linarith [hlin k hk]
  have hlog : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  have hSpos : 0 < S := Finset.sum_pos
    (fun k hk => inv_pos.mpr (hC k (Finset.mem_range.mp hk))) (Finset.nonempty_range_iff.mpr hn)
  calc conductance K a b * Real.log (n + 1) ≤ S⁻¹ * (c * S) := by
        refine mul_le_mul (conductance_le_shell hK hrange ha hb hn hC) ?_ hlog
          (inv_nonneg.mpr hSpos.le)
        rwa [div_le_iff₀ hc, mul_comm] at hS
    _ = c := by field_simp

omit [Fintype ι] in
/-- **Phase agreement becomes content agreement.** Under any distribution of
configurations, an `L`-Lipschitz encoder's mean-square content discrepancy
between `a` and `b` is at most `L²` times their mean-square phase difference. -/
theorem integral_dist_sq_le {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace (ι → ℝ)]
    {μ : Measure (ι → ℝ)} {Φ : ℝ → Y} {L : NNReal} (hΦ : LipschitzWith L Φ) (a b : ι)
    (hint : Integrable (fun θ : ι → ℝ => (θ a - θ b) ^ 2) μ) :
    ∫ θ, dist (Φ (θ a)) (Φ (θ b)) ^ 2 ∂μ ≤ (L : ℝ) ^ 2 * ∫ θ, (θ a - θ b) ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (hint.const_mul _) (Filter.Eventually.of_forall fun θ => ?_)
  have h := hΦ.dist_le_mul (θ a) (θ b)
  rw [Real.dist_eq] at h
  calc dist (Φ (θ a)) (Φ (θ b)) ^ 2 ≤ ((L : ℝ) * |θ a - θ b|) ^ 2 :=
        pow_le_pow_left₀ dist_nonneg h 2
    _ = (L : ℝ) ^ 2 * (θ a - θ b) ^ 2 := by rw [mul_pow, sq_abs]

end PhysicsOfConsciousness.PhysicalUnity
