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
* **`one_le_conductance_of_chain`.** A lower bound on the conductance from a
  chain of site sets running from `{a}` to `{b}`: the phase drop telescopes
  through the chain's means, each level's drop is bounded by the energy, and the
  resistance is at most `2 (Σ_k ρ k)²`, with `ρ k² κ_k #S_k #S_{k+1} ≥ 1`.
* **`le_conductance_of_powerLaw`.** Through a dyadic chain out from `a` and in
  to `b`, whose level weights shrink geometrically
  (`le_conductance_of_geometric`), a coupling that decays no faster than
  `r ^ −(2+σ)` with `σ < 2` gives a conductance bounded below independently of
  the distance: agreement under noise that does not degrade with separation.
* **`integral_dist_sq_le`.** A Lipschitz encoder transfers phase agreement to
  content agreement in mean square: the mean-square content discrepancy is at
  most `L²` times the mean-square phase difference, under any distribution of
  configurations. With the harmonic identity the root-mean-square content
  discrepancy is at most `L √(D / C)`.

Non-vacuity — a series pair of couplings with conductance `½`, raised to at least
`1` by a direct edge, a shell bound attained on the same row, and the power-law
chain bound met on it — is
`Examples/AgreementResistance.lean`.
-/

open MeasureTheory Finset

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
/-- The mean of a configuration over a finite set of sites. -/
noncomputable def mean (S : Finset ι) (u : ι → ℝ) : ℝ := (∑ x ∈ S, u x) / #S

omit [Fintype ι] in
/-- The difference of two means is the mean of the pairwise differences. -/
lemma mean_sub_mean {S T : Finset ι} (hS : S.Nonempty) (hT : T.Nonempty) (u : ι → ℝ) :
    (mean S u - mean T u) * (#S * #T) = ∑ p ∈ S ×ˢ T, (u p.1 - u p.2) := by
  have hS' : (#S : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hT' : (#T : ℝ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  rw [sum_product, mean, mean]
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  field_simp

/-- **One level of an averaging chain.** If the coupling between every site of
`S` and every site of `T` is at least `κ`, the drop between the means of `S` and
`T`, weighted by `κ #S #T`, is bounded by the coupling energy between them. -/
lemma mul_sq_mean_sub_le {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) {S T : Finset ι}
    (hS : S.Nonempty) (hT : T.Nonempty) {κ : ℝ} (hκ : ∀ x ∈ S, ∀ y ∈ T, κ ≤ K x y)
    (u : ι → ℝ) : κ * (#S * #T) * (mean S u - mean T u) ^ 2 ≤ 2 * energy K u := by
  have hn : (0 : ℝ) < #S * #T := by
    have := hS.card_pos; have := hT.card_pos; positivity
  have hE : ∑ p ∈ S ×ˢ T, K p.1 p.2 * (u p.1 - u p.2) ^ 2 ≤ 2 * energy K u := by
    rw [energy, ← mul_assoc]; norm_num
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
      fun p _ _ => mul_nonneg (hK _ _) (sq_nonneg _)
  refine le_trans ?_ hE
  rcases lt_or_ge κ 0 with hκ0 | hκ0
  · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hκ0.le hn.le)
      (sq_nonneg _)).trans (sum_nonneg fun p _ => mul_nonneg (hK _ _) (sq_nonneg _))
  -- Cauchy–Schwarz over the pairs of `S ×ˢ T`.
  have hcs := sq_sum_le_card_mul_sum_sq (s := S ×ˢ T) (f := fun p => u p.1 - u p.2)
  rw [← mean_sub_mean hS hT, card_product, Nat.cast_mul, mul_pow] at hcs
  have hsq : (#S * #T : ℝ) * (mean S u - mean T u) ^ 2 ≤
      ∑ p ∈ S ×ˢ T, (u p.1 - u p.2) ^ 2 := by
    have : (#S * #T : ℝ) * ((#S * #T : ℝ) * (mean S u - mean T u) ^ 2) ≤
        (#S * #T : ℝ) * ∑ p ∈ S ×ˢ T, (u p.1 - u p.2) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this hn
  calc κ * (#S * #T) * (mean S u - mean T u) ^ 2
      ≤ κ * ∑ p ∈ S ×ˢ T, (u p.1 - u p.2) ^ 2 := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsq hκ0
    _ ≤ ∑ p ∈ S ×ˢ T, K p.1 p.2 * (u p.1 - u p.2) ^ 2 := by
        rw [mul_sum]
        refine sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        obtain ⟨hx, hy⟩ := mem_product.mp hp
        exact hκ _ hx _ hy

/-- **Averaging chains bound the resistance.** Let `S 0 = {a}`, …, `S m = {b}` be
nonempty sets of sites, with the coupling between consecutive sets `S k` and
`S (k + 1)` at least `κ k` everywhere, and let `ρ k ≥ 0` satisfy
`ρ k ² κ k #S k #S (k+1) ≥ 1`. Then `1 ≤ 2 (Σ ρ)² C`: the effective resistance is
at most `2 (Σ_k ρ k)²`. The phase drop from `a` to `b` telescopes through the means
of the chain, and each level's drop is bounded by the energy. -/
theorem one_le_conductance_of_chain [DecidableEq ι] {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    {a b : ι} (hab : a ≠ b) {m : ℕ} {S : ℕ → Finset ι} (hS : ∀ k ≤ m, (S k).Nonempty)
    (ha : S 0 = {a}) (hb : S m = {b}) {κ ρ : ℕ → ℝ}
    (hκ : ∀ k < m, ∀ x ∈ S k, ∀ y ∈ S (k + 1), κ k ≤ K x y)
    (hρ0 : ∀ k < m, 0 ≤ ρ k) (hρ : ∀ k < m, 1 ≤ ρ k ^ 2 * (κ k * (#(S k) * #(S (k + 1))))) :
    1 ≤ 2 * (∑ k ∈ range m, ρ k) ^ 2 * conductance K a b := by
  set R := ∑ k ∈ range m, ρ k
  have hu : ∀ u : ι → ℝ, u a - u b = 1 → 1 ≤ 2 * R ^ 2 * energy K u := by
    intro u hu
    set s := √(2 * energy K u)
    have hs : s ^ 2 = 2 * energy K u := Real.sq_sqrt (by linarith [energy_nonneg hK u])
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hlevel : ∀ k < m, mean (S k) u - mean (S (k + 1)) u ≤ ρ k * s := by
      intro k hk
      have h1 := mul_sq_mean_sub_le hK (hS k hk.le) (hS (k + 1) hk) (hκ k hk) u
      have h2 := hρ k hk
      set d := mean (S k) u - mean (S (k + 1)) u
      have hd : d ^ 2 ≤ (ρ k * s) ^ 2 := by
        have : 0 ≤ κ k * (#(S k) * #(S (k + 1))) := by
          by_contra h; push Not at h; nlinarith [sq_nonneg (ρ k)]
        rw [mul_pow, hs]
        nlinarith [sq_nonneg d, sq_nonneg (ρ k)]
      exact abs_le_of_sq_le_sq' hd (mul_nonneg (hρ0 k hk) hs0) |>.2
    have htel : ∑ k ∈ range m, (mean (S k) u - mean (S (k + 1)) u) = 1 := by
      rw [sum_range_sub' (fun k => mean (S k) u), ha, hb]
      simpa [mean] using hu
    have h1 : 1 ≤ R * s := by
      rw [← htel, sum_mul]
      exact sum_le_sum fun k hk => hlevel k (mem_range.mp hk)
    have : 1 ≤ (R * s) ^ 2 := by nlinarith
    rw [mul_pow, hs] at this
    linarith
  obtain ⟨_, ⟨u₀, hu₀, rfl⟩⟩ := nonempty_unitDrop (K := K) hab
  have hR : 0 < 2 * R ^ 2 := by
    have := hu u₀ hu₀
    rcases (show 0 ≤ 2 * R ^ 2 by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h] at this; norm_num at this
  have : (2 * R ^ 2)⁻¹ ≤ conductance K a b := by
    refine le_csInf (nonempty_unitDrop hab) ?_
    rintro _ ⟨u, hu', rfl⟩
    rw [inv_le_iff_one_le_mul₀ hR, mul_comm]
    exact hu u hu'
  rwa [inv_le_iff_one_le_mul₀ hR, mul_comm] at this

/-- A chain that widens geometrically from both ends: the weights `q ^ min k (m-1-k)`
sum to at most `2 / (1 − q)`, whatever the length `m`. -/
lemma sum_pow_min_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) (m : ℕ) :
    ∑ k ∈ range m, q ^ min k (m - 1 - k) ≤ 2 / (1 - q) := by
  have h1 : ∑ k ∈ range m, q ^ k ≤ 1 / (1 - q) := by
    have h := geom_sum_Ico_le_of_lt_one (x := q) (m := 0) (n := m) hq0 hq
    rwa [← range_eq_Ico, pow_zero] at h
  have h2 : ∑ k ∈ range m, q ^ (m - 1 - k) ≤ 1 / (1 - q) := by
    rw [sum_range_reflect (fun k => q ^ k) m]; exact h1
  have h3 : (2 : ℝ) / (1 - q) = 1 / (1 - q) + 1 / (1 - q) := by ring
  calc ∑ k ∈ range m, q ^ min k (m - 1 - k)
      ≤ ∑ k ∈ range m, (q ^ k + q ^ (m - 1 - k)) := sum_le_sum fun k _ => by
        rcases min_choice k (m - 1 - k) with h | h <;> rw [h] <;>
          linarith [pow_nonneg hq0 k, pow_nonneg hq0 (m - 1 - k)]
    _ ≤ 2 / (1 - q) := by rw [sum_add_distrib, h3]; linarith

/-- **Geometric chains give distance-independent conductance.** If the chain's
level weights shrink geometrically away from both ends, `ρ k = A q ^ min k (m-1-k)`
with `q < 1`, the conductance is at least `(1 − q)² / (8 A²)`, a bound that does
not depend on the chain's length and so not on the distance between `a` and `b`. -/
theorem le_conductance_of_geometric [DecidableEq ι] {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    {a b : ι} (hab : a ≠ b) {m : ℕ} {S : ℕ → Finset ι} (hS : ∀ k ≤ m, (S k).Nonempty)
    (ha : S 0 = {a}) (hb : S m = {b}) {κ : ℕ → ℝ}
    (hκ : ∀ k < m, ∀ x ∈ S k, ∀ y ∈ S (k + 1), κ k ≤ K x y) {A q : ℝ} (hA : 0 < A)
    (hq0 : 0 ≤ q) (hq : q < 1)
    (hρ : ∀ k < m, 1 ≤ (A * q ^ min k (m - 1 - k)) ^ 2 * (κ k * (#(S k) * #(S (k + 1))))) :
    (1 - q) ^ 2 / (8 * A ^ 2) ≤ conductance K a b := by
  have h := one_le_conductance_of_chain hK hab hS ha hb hκ (fun k _ => by positivity) hρ
  set R := ∑ k ∈ range m, A * q ^ min k (m - 1 - k)
  have h1q : 0 < 1 - q := by linarith
  have hR : R ≤ 2 * A / (1 - q) := by
    have := mul_le_mul_of_nonneg_left (sum_pow_min_le hq0 hq m) hA.le
    rw [mul_sum] at this
    calc R ≤ A * (2 / (1 - q)) := this
      _ = 2 * A / (1 - q) := by ring
  have hR0 : 0 ≤ R := sum_nonneg fun k _ => by positivity
  have hC := conductance_nonneg hK a b
  have hR2 : R ^ 2 ≤ (2 * A / (1 - q)) ^ 2 := pow_le_pow_left₀ hR0 hR 2
  rw [div_le_iff₀ (by positivity)]
  calc (1 - q) ^ 2 ≤ (1 - q) ^ 2 * (2 * R ^ 2 * conductance K a b) := by
        nlinarith [sq_nonneg (1 - q)]
    _ ≤ (1 - q) ^ 2 * (2 * (2 * A / (1 - q)) ^ 2 * conductance K a b) := by gcongr
    _ = conductance K a b * (8 * A ^ 2) := by field_simp; ring

/-- **A power-law tail with `σ < 2` bounds the resistance at every distance.**
Let the chain run out from `a` through sets of scale `2 ^ j`, `j = min i (m − i)`,
and back in to `b`: set `i` holds at least `α 4 ^ j` sites, as a disc of radius
`2 ^ j` does on a planar sheet, and the coupling between consecutive sets is at
least `β (2 ^ j) ^ −(2+σ)`, as a kernel `K(r) ≳ r ^ −(2+σ)` gives between sites a
bounded multiple of `2 ^ j` apart. For `σ < 2` the conductance is at least
`(1 − q)² α² β / 8` with `q = 2 ^ −(2−σ)/2 < 1`, independent of `m` and so of the
distance: the level weights fall as `q ^ j`, because the pairs between two sets
grow as `16 ^ j` and their coupling falls only as `2 ^ −(2+σ) j`. -/
theorem le_conductance_of_powerLaw [DecidableEq ι] {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    {a b : ι} (hab : a ≠ b) {m : ℕ} {S : ℕ → Finset ι} (hS : ∀ k ≤ m, (S k).Nonempty)
    (ha : S 0 = {a}) (hb : S m = {b}) {α β σ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hσ : σ < 2)
    (hcard : ∀ i ≤ m, α * 4 ^ min i (m - i) ≤ #(S i))
    (hκ : ∀ k < m, ∀ x ∈ S k, ∀ y ∈ S (k + 1),
      β * ((2 : ℝ) ^ min k (m - 1 - k)) ^ (-(2 + σ)) ≤ K x y) :
    (1 - (2 : ℝ) ^ (-(2 - σ) / 2)) ^ 2 * (α ^ 2 * β) / 8 ≤ conductance K a b := by
  set q : ℝ := (2 : ℝ) ^ (-(2 - σ) / 2)
  have hq0 : 0 ≤ q := by positivity
  have hq : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set A := (α * √β)⁻¹
  have hA : 0 < A := by positivity
  have hA2 : A ^ 2 * (α ^ 2 * β) = 1 := by
    simp only [A, inv_pow, mul_pow, Real.sq_sqrt hβ.le]
    field_simp
  have hgeo := le_conductance_of_geometric hK hab hS ha hb hκ hA hq0 hq ?_
  · have e : α ^ 2 * β = 1 / A ^ 2 := by
      rw [eq_div_iff (by positivity)]; linarith [hA2]
    rw [e]; convert hgeo using 1; ring
  intro k hk
  set j := min k (m - 1 - k)
  set r : ℝ := (2 : ℝ) ^ j
  have hr : 0 < r := by positivity
  have hqj : q ^ j = r ^ (-(2 - σ) / 2) := by
    simp only [q, r]
    rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast_mul (by norm_num), mul_comm]
  have h4 : (4 : ℝ) ^ j = r ^ (2 : ℝ) := by
    simp only [r]; rw [Real.rpow_two, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hcS : α * r ^ (2 : ℝ) ≤ #(S k) := by
    rw [← h4]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) hα.le).trans
      (hcard k hk.le)
  have hcT : α * r ^ (2 : ℝ) ≤ #(S (k + 1)) := by
    rw [← h4]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) hα.le).trans
      (hcard (k + 1) hk)
  have hexp : (r ^ (-(2 - σ) / 2)) ^ 2 * r ^ (-(2 + σ)) * (r ^ (2 : ℝ) * r ^ (2 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_add hr, ← Real.rpow_add hr,
      ← Real.rpow_add hr]
    norm_num; ring_nf; simp
  have hr2 : 0 ≤ α * r ^ (2 : ℝ) := by positivity
  calc (1 : ℝ) = A ^ 2 * (α ^ 2 * β) *
        ((r ^ (-(2 - σ) / 2)) ^ 2 * r ^ (-(2 + σ)) * (r ^ (2 : ℝ) * r ^ (2 : ℝ))) := by
        rw [hA2, hexp]; ring
    _ = (A * q ^ j) ^ 2 * (β * r ^ (-(2 + σ)) * ((α * r ^ (2 : ℝ)) * (α * r ^ (2 : ℝ)))) := by
        rw [hqj]; ring
    _ ≤ (A * q ^ j) ^ 2 * (β * r ^ (-(2 + σ)) * (#(S k) * #(S (k + 1)))) := by
        gcongr

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
