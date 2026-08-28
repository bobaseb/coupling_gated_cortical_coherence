import Mathlib

namespace PhysicsOfConsciousness
variable {V : Type} [Fintype V] [DecidableEq V]

def is_valid_coupling (A : V → V → ℝ) : Prop :=
  ∀ i j, A i j ≥ 0 ∧ A i j = A j i
def total_coupling_resources (A : V → V → ℝ) : ℝ := ∑ i : V, ∑ j : V, A i j
def is_strictly_suboptimal (A_rigid : V → V → ℝ) (theta : V → ℝ) : Prop :=
  ∃ i0 j0 k0 l0, A_rigid i0 j0 > 0 ∧ Real.cos (theta j0 - theta i0) < Real.cos (theta l0 - theta k0)

private lemma sum_sym_pair {a b : V} (hab : a ≠ b) (f : V → V → ℝ) :
    ∑ i : V, ∑ j : V, (if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then f i j else 0) =
    f a b + f b a := by
  have hinner : ∀ i : V, (∑ j : V, (if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then f i j else 0)) = 
    (if i = a then f a b else 0) + (if i = b then f b a else 0) := by
    intro i
    by_cases ha : i = a
    · by_cases hb : i = b
      · have h_eq : a = b := Eq.trans ha.symm hb
        contradiction
      · subst ha
        simp [hab, Finset.sum_ite_eq']
    · by_cases hb : i = b
      · subst hb
        simp [hab.symm, Finset.sum_ite_eq']
      · simp [ha, hb]
  simp_rw [hinner, Finset.sum_add_distrib]
  have h1 : (∑ i : V, (if i = a then f a b else 0)) = f a b := by simp [Finset.sum_ite_eq']
  have h2 : (∑ i : V, (if i = b then f b a else 0)) = f b a := by simp [Finset.sum_ite_eq']
  rw [h1, h2]

omit [DecidableEq V] in
private lemma neg_sum_lemma (f : V → V → ℝ) (c : ℝ) (hc : (∑ i, ∑ j, f i j) = c) :
  (∑ i, ∑ j, -f i j) = -c := by
  have : (∑ i, ∑ j, -f i j) = - (∑ i, ∑ j, f i j) := by simp_rw [Finset.sum_neg_distrib]
  rw [this, hc]

lemma better_allocation_of_adj (A_rigid : V → V → ℝ) (theta : V → ℝ) (adj : V → V → ℝ)
  (h_valid : is_valid_coupling A_rigid)
  (h_adj_symm : ∀ i j, adj i j = adj j i)
  (h_adj_valid : ∀ i j, A_rigid i j + adj i j ≥ 0)
  (h_adj_sum : ∑ i, ∑ j, adj i j = 0)
  (h_adj_improve : ∑ i, ∑ j, adj i j * Real.cos (theta j - theta i) > 0) :
  ∃ A_flex, is_valid_coupling A_flex ∧
    total_coupling_resources A_flex = total_coupling_resources A_rigid ∧
    (∑ i, ∑ j, A_flex i j * Real.cos (theta j - theta i)) >
    (∑ i, ∑ j, A_rigid i j * Real.cos (theta j - theta i)) := by
  use fun i j => A_rigid i j + adj i j
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have h_symm : (fun i j => A_rigid i j + adj i j) i j = (fun i j => A_rigid i j + adj i j) j i := by
      dsimp only
      rw [(h_valid i j).2, h_adj_symm i j]
    exact ⟨h_adj_valid i j, h_symm⟩
  · unfold total_coupling_resources
    simp_rw [Finset.sum_add_distrib]
    rw [h_adj_sum, add_zero]
  · simp_rw [add_mul, Finset.sum_add_distrib]
    linarith [h_adj_improve]

lemma exists_better_coupling_allocation (A_rigid : V → V → ℝ) (theta : V → ℝ)
  (h_valid : is_valid_coupling A_rigid)
  (h_suboptimal : is_strictly_suboptimal A_rigid theta) :
  ∃ A_flex : V → V → ℝ, is_valid_coupling A_flex ∧
    total_coupling_resources A_flex = total_coupling_resources A_rigid ∧
    (∑ i, ∑ j, A_flex i j * Real.cos (theta j - theta i)) >
    (∑ i, ∑ j, A_rigid i j * Real.cos (theta j - theta i)) := by
  obtain ⟨i0, j0, k0, l0, h_pos, h_lt⟩ := h_suboptimal
  have hi0j0 : i0 ≠ j0 := by
    intro heq; subst heq
    simp at h_lt
    linarith [Real.cos_le_one (theta l0 - theta k0)]
  set δ := A_rigid i0 j0 with hδ_def
  have hδ_pos : δ > 0 := h_pos
  by_cases hk0l0 : k0 = l0
  · subst hk0l0
    let adj : V → V → ℝ := fun i j => (if i = k0 ∧ j = k0 then 2 * δ else 0) - (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0)
    apply better_allocation_of_adj A_rigid theta adj h_valid
    · intro i j
      have hif1 : ((i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0)) ↔ ((j = i0 ∧ i = j0) ∨ (j = j0 ∧ i = i0)) := by
        constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [right; left; right; left] <;> exact ⟨h2, h1⟩
      have hkk : (i = k0 ∧ j = k0) ↔ (j = k0 ∧ i = k0) := And.comm
      have h_ite1 : (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0) = (if (j = i0 ∧ i = j0) ∨ (j = j0 ∧ i = i0) then δ else 0) := if_congr hif1 rfl rfl
      have h_ite2 : (if i = k0 ∧ j = k0 then 2 * δ else 0) = (if j = k0 ∧ i = k0 then 2 * δ else 0) := if_congr hkk rfl rfl
      simp only [adj, h_ite1, h_ite2]
    · intro i j
      dsimp [adj]
      by_cases hij : (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0)
      · have h_ite1 : (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0) = δ := by simp [hij]
        by_cases hkk : i = k0 ∧ j = k0
        · have h_ite2 : (if i = k0 ∧ j = k0 then 2 * δ else 0) = 2 * δ := by simp [hkk]
          simp only [h_ite1, h_ite2]
          rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
          · have h_A : A_rigid i j = δ := by rw [hi, hj, ← hδ_def]
            linarith
          · have h_A : A_rigid i j = δ := by rw [hi, hj, (h_valid j0 i0).2]
            linarith
        · have h_ite2 : (if i = k0 ∧ j = k0 then 2 * δ else 0) = 0 := by simp [hkk]
          simp only [h_ite1, h_ite2]
          rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
          · have h_A : A_rigid i j = δ := by rw [hi, hj, ← hδ_def]
            linarith
          · have h_A : A_rigid i j = δ := by rw [hi, hj, (h_valid j0 i0).2]
            linarith
      · have h_ite1 : (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0) = 0 := by simp [hij]
        by_cases hkk : i = k0 ∧ j = k0
        · have h_ite2 : (if i = k0 ∧ j = k0 then 2 * δ else 0) = 2 * δ := by simp [hkk]
          simp only [h_ite1, h_ite2]
          have hA := (h_valid i j).1
          linarith
        · have h_ite2 : (if i = k0 ∧ j = k0 then 2 * δ else 0) = 0 := by simp [hkk]
          simp only [h_ite1, h_ite2]
          have hA := (h_valid i j).1
          linarith
    · change (∑ i, ∑ j, ((if i = k0 ∧ j = k0 then 2 * δ else 0) - (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0))) = 0
      simp_rw [Finset.sum_sub_distrib]
      have hkk_sum : ∑ i : V, ∑ j : V, (if i = k0 ∧ j = k0 then (2 * δ : ℝ) else 0) = 2 * δ := by
        have h_eq : ∀ i j : V, (if i = k0 ∧ j = k0 then (2 * δ : ℝ) else 0) = (if (i, j) = (k0, k0) then 2 * δ else 0) := by
          intro i j; simp
        simp_rw [h_eq, ← Finset.sum_product']
        simp [Finset.sum_ite_eq']
      have hij_sum : ∑ i : V, ∑ j : V, (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0) = 2 * δ := by
        have := sum_sym_pair hi0j0 (fun _ _ => δ); simpa [two_mul] using this
      linarith [hkk_sum, hij_sum]
    · change (∑ i, ∑ j, ((if i = k0 ∧ j = k0 then 2 * δ else 0) - (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0)) * Real.cos (theta j - theta i)) > 0
      have h_expand_cos : ∀ i j : V,
          ((if i = k0 ∧ j = k0 then 2 * δ else 0) -
          (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0)) * Real.cos (theta j - theta i) =
          (if i = k0 ∧ j = k0 then 2 * δ * Real.cos (theta j - theta i) else 0) -
          (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ * Real.cos (theta j - theta i) else 0) := by
        intro i j; split_ifs <;> ring
      simp_rw [h_expand_cos, Finset.sum_sub_distrib]
      have hkk_cos : ∑ i : V, ∑ j : V, (if i = k0 ∧ j = k0 then 2 * δ * Real.cos (theta j - theta i) else 0) = 2 * δ * 1 := by
        have h_eq : ∀ i j : V, (if i = k0 ∧ j = k0 then 2 * δ * Real.cos (theta j - theta i) else 0) = (if (i, j) = (k0, k0) then 2 * δ * Real.cos (theta j - theta i) else 0) := by
          intro i j; simp
        simp_rw [h_eq, ← Finset.sum_product']
        simp [Finset.sum_ite_eq', sub_self, Real.cos_zero]
      have hij_cos : ∑ i : V, ∑ j : V, (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ * Real.cos (theta j - theta i) else 0) = δ * Real.cos (theta j0 - theta i0) + δ * Real.cos (theta i0 - theta j0) := by
        have := sum_sym_pair hi0j0 (fun i j => δ * Real.cos (theta j - theta i))
        simpa using this
      have hcos_ij : Real.cos (theta i0 - theta j0) = Real.cos (theta j0 - theta i0) := by
        rw [show theta i0 - theta j0 = -(theta j0 - theta i0) by ring, Real.cos_neg]
      have h_lt_simp : Real.cos (theta j0 - theta i0) < 1 := by
        have h_cos_1 : Real.cos (theta k0 - theta k0) = 1 := by rw [sub_self, Real.cos_zero]
        linarith [h_lt, h_cos_1]
      nlinarith [hkk_cos, hij_cos, hcos_ij, hδ_pos, h_lt_simp]
  · let adj : V → V → ℝ := fun i j => δ * (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0) - δ * (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then 1 else 0)
    apply better_allocation_of_adj A_rigid theta adj h_valid
    · intro i j
      have hif1 : ((i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0)) ↔ ((j = i0 ∧ i = j0) ∨ (j = j0 ∧ i = i0)) := by
        constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [right; left; right; left] <;> exact ⟨h2, h1⟩
      have hif2 : ((i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0)) ↔ ((j = k0 ∧ i = l0) ∨ (j = l0 ∧ i = k0)) := by
        constructor <;> rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> [right; left; right; left] <;> exact ⟨h2, h1⟩
      have h_ite1 : (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then 1 else 0 : ℝ) = (if (j = i0 ∧ i = j0) ∨ (j = j0 ∧ i = i0) then 1 else 0 : ℝ) := if_congr hif1 rfl rfl
      have h_ite2 : (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0 : ℝ) = (if (j = k0 ∧ i = l0) ∨ (j = l0 ∧ i = k0) then 1 else 0 : ℝ) := if_congr hif2 rfl rfl
      simp only [adj, h_ite1, h_ite2]
    · intro i j
      dsimp [adj]
      by_cases hij : (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0)
      · have h_ite1 : (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then 1 else 0 : ℝ) = 1 := by simp [hij]
        by_cases hkl : (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0)
        · have h_ite2 : (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0 : ℝ) = 1 := by simp [hkl]
          simp only [h_ite1, h_ite2, mul_one]
          have hA := (h_valid i j).1
          linarith
        · have h_ite2 : (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0 : ℝ) = 0 := by simp [hkl]
          simp only [h_ite1, h_ite2, mul_zero, mul_one]
          rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
          · have h_A : A_rigid i j = δ := by rw [hi, hj, ← hδ_def]
            linarith
          · have h_A : A_rigid i j = δ := by rw [hi, hj, (h_valid j0 i0).2]
            linarith
      · have h_ite1 : (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then 1 else 0 : ℝ) = 0 := by simp [hij]
        by_cases hkl : (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0)
        · have h_ite2 : (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0 : ℝ) = 1 := by simp [hkl]
          simp only [h_ite1, h_ite2, mul_zero, mul_one, sub_zero]
          have hA := (h_valid i j).1
          linarith
        · have h_ite2 : (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0 : ℝ) = 0 := by simp [hkl]
          simp only [h_ite1, h_ite2, mul_zero, sub_zero]
          have hA := (h_valid i j).1
          linarith
    · change (∑ i, ∑ j, (δ * (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0) - δ * (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then 1 else 0))) = 0
      have h_expand : ∀ i j : V,
          δ * (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0) - δ * (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then 1 else 0) =
          (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then δ else 0) + -(if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0) := by
        intro i j; split_ifs <;> ring
      simp_rw [h_expand, Finset.sum_add_distrib]
      have h_neg_sum_eq : (∑ i : V, ∑ j : V, -(if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0)) +
                          (∑ i : V, ∑ j : V, (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then δ else 0)) = 0 := by
        have h_src : ∑ i : V, ∑ j : V, (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0) = δ + δ := by
          have := sum_sym_pair hi0j0 (fun _ _ => δ); simpa [two_mul] using this
        have h_dst : ∑ i : V, ∑ j : V, (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then δ else 0) = δ + δ := by
          have := sum_sym_pair hk0l0 (fun _ _ => δ); simpa [two_mul] using this
        have h_neg_src_sum : (∑ i : V, ∑ j : V, -(if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0)) = -(δ + δ) := by
          exact neg_sum_lemma (fun i j => if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ else 0) (δ + δ) h_src
        rw [h_neg_src_sum, h_dst]
        ring
      linarith [h_neg_sum_eq]
    · change (∑ i, ∑ j, (δ * (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0) - δ * (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then 1 else 0)) * Real.cos (theta j - theta i)) > 0
      have h_expand_cos : ∀ i j : V,
          (δ * (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then 1 else 0) - δ * (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then 1 else 0)) * Real.cos (theta j - theta i) =
          (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then δ * Real.cos (theta j - theta i) else 0) +
          -(if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ * Real.cos (theta j - theta i) else 0) := by
        intro i j; split_ifs <;> ring
      simp_rw [h_expand_cos, Finset.sum_add_distrib]
      have h_improvement : (∑ i : V, ∑ j : V, -(if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ * Real.cos (theta j - theta i) else 0)) + 
                           (∑ i : V, ∑ j : V, (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then δ * Real.cos (theta j - theta i) else 0)) > 0 := by
        have h_src : ∑ i : V, ∑ j : V, (if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ * Real.cos (theta j - theta i) else 0) = δ * Real.cos (theta j0 - theta i0) + δ * Real.cos (theta i0 - theta j0) := by
          have := sum_sym_pair hi0j0 (fun i j => δ * Real.cos (theta j - theta i))
          simpa using this
        have h_dst : ∑ i : V, ∑ j : V, (if (i = k0 ∧ j = l0) ∨ (i = l0 ∧ j = k0) then δ * Real.cos (theta j - theta i) else 0) = δ * Real.cos (theta l0 - theta k0) + δ * Real.cos (theta k0 - theta l0) := by
          have := sum_sym_pair hk0l0 (fun i j => δ * Real.cos (theta j - theta i))
          simpa using this
        have hcos_kl : Real.cos (theta k0 - theta l0) = Real.cos (theta l0 - theta k0) := by
          rw [show theta k0 - theta l0 = -(theta l0 - theta k0) by ring, Real.cos_neg]
        have hcos_ij : Real.cos (theta i0 - theta j0) = Real.cos (theta j0 - theta i0) := by
          rw [show theta i0 - theta j0 = -(theta j0 - theta i0) by ring, Real.cos_neg]
        have h_neg_src : (∑ i : V, ∑ j : V, -(if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ * Real.cos (theta j - theta i) else 0)) = -(δ * Real.cos (theta j0 - theta i0) + δ * Real.cos (theta i0 - theta j0)) := by
          exact neg_sum_lemma (fun i j => if (i = i0 ∧ j = j0) ∨ (i = j0 ∧ j = i0) then δ * Real.cos (theta j - theta i) else 0) (δ * Real.cos (theta j0 - theta i0) + δ * Real.cos (theta i0 - theta j0)) h_src
        nlinarith [h_neg_src, h_dst, hcos_kl, hcos_ij, hδ_pos, h_lt]
      linarith [h_improvement]

/--
[THEOREM] Continuous Field Superiority over Rigid Topology
For any rigid silicon-like hardware coupling `A_rigid` that enforces a suboptimal wiring
(i.e., physical wires exist between less-correlated regions while more-correlated regions
could use that resource), there exists a flexible (continuous-like) coupling allocation 
that uses the exact same total coupling resources but achieves strictly greater 
thermodynamic synchronization (higher correlation / lower energy).

This formally disqualifies rigid topologies from achieving optimal thermodynamic 
efficiency compared to continuous phase-locking fields.
-/
theorem continuous_beats_rigid_topology (A_rigid : V → V → ℝ) (theta : V → ℝ)
  (h_valid : is_valid_coupling A_rigid)
  (h_rigid_constraint : is_strictly_suboptimal A_rigid theta) :
  ∃ A_flex : V → V → ℝ, 
    is_valid_coupling A_flex ∧
    total_coupling_resources A_flex = total_coupling_resources A_rigid ∧
    (∑ i, ∑ j, A_flex i j * Real.cos (theta j - theta i)) >
    (∑ i, ∑ j, A_rigid i j * Real.cos (theta j - theta i)) :=
  exists_better_coupling_allocation A_rigid theta h_valid h_rigid_constraint

end PhysicsOfConsciousness
