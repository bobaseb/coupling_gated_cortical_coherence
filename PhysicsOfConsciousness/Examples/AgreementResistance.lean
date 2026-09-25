import PhysicsOfConsciousness.Phase10_AgreementResistance

/-!
# Examples/AgreementResistance.lean — the resistance bounds are attained

§39. Three sites in a row, unit couplings between neighbours.

* **Series.** The conductance between the two ends is exactly `½`: the
  configuration `![1, ½, 0]` has energy `½`, and every configuration with unit
  phase difference across the ends has at least that. The bound of
  `conductance_mul_sq_le_energy` is therefore attained, not only valid.
* **A direct edge.** Joining the ends by a unit coupling raises their
  conductance to at least `1` (`le_conductance_of_edge`), strictly above the
  series value, so the improvement that `conductance_mono` permits occurs.
* **Shells.** Taking each site as its own shell, both crossings carry unit
  coupling, and `conductance_le_shell` gives `1 / (1 + 1) = ½`: the series
  value, so the Nash-Williams bound is attained. With `c = 1` the same row
  meets every hypothesis of `conductance_mul_log_le`.
* **A power-law chain.** Taking the sites as the levels `{0}, {1}, {2}` of a
  chain meets every hypothesis of `le_conductance_of_powerLaw` with `σ = 0`,
  `α = ¼` and `β = 1`, and the bound `1/512` it gives lies below the series
  value `½`.
-/

namespace PhysicsOfConsciousness.PhysicalUnity.Examples

/-- Unit couplings between neighbours on three sites in a row. -/
def series : Fin 3 → Fin 3 → ℝ := ![![0, 1, 0], ![1, 0, 1], ![0, 1, 0]]

/-- The same row with the ends also joined by a unit coupling. -/
def ring3 : Fin 3 → Fin 3 → ℝ := ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]

theorem series_nonneg (i j : Fin 3) : 0 ≤ series i j := by
  fin_cases i <;> fin_cases j <;> simp [series]

theorem ring3_nonneg (i j : Fin 3) : 0 ≤ ring3 i j := by
  fin_cases i <;> fin_cases j <;> simp [ring3]

theorem ring3_symm (i j : Fin 3) : ring3 i j = ring3 j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem energy_series (u : Fin 3 → ℝ) :
    energy series u = (u 0 - u 1) ^ 2 + (u 1 - u 2) ^ 2 := by
  simp [energy, series, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

theorem conductance_series : conductance series 0 2 = 1 / 2 := by
  apply le_antisymm
  · refine csInf_le (bddBelow_energy series_nonneg _) ⟨![1, 1 / 2, 0], by simp, ?_⟩
    rw [energy_series]; simp; norm_num
  · refine le_csInf (nonempty_unitDrop (by decide)) ?_
    rintro _ ⟨u, hu, rfl⟩
    simp only [Set.mem_ofPred_eq] at hu
    rw [energy_series]
    nlinarith [sq_nonneg (u 0 - u 1 - (u 1 - u 2))]

theorem series_lt_ring3 : conductance series 0 2 < conductance ring3 0 2 := by
  rw [conductance_series]
  have h := le_conductance_of_edge ring3_nonneg ring3_symm (a := 0) (b := 2) (by decide)
  have h1 : ring3 0 2 = 1 := rfl
  linarith

/-- Each site of the row is its own shell. -/
def shell : Fin 3 → ℕ := fun i => i

theorem series_range (i j : Fin 3) (h : series i j ≠ 0) :
    shell j ≤ shell i + 1 ∧ shell i ≤ shell j + 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [series, shell]

theorem shellCapacity_series (k : ℕ) (hk : k < 2) : shellCapacity series shell k = 1 := by
  interval_cases k <;>
    simp [shellCapacity, Crosses, series, shell, Fintype.sum_prod_type, Fin.sum_univ_three] <;>
    norm_num

theorem conductance_series_le_shell : conductance series 0 2 ≤ 1 / 2 := by
  have h := conductance_le_shell series_nonneg series_range (a := 0) (b := 2) (n := 2)
    rfl le_rfl (by norm_num) (fun k hk => by rw [shellCapacity_series k hk]; norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    shellCapacity_series 0 (by norm_num), shellCapacity_series 1 (by norm_num)] at h
  norm_num at h ⊢
  exact h

theorem conductance_series_mul_log_le : conductance series 0 2 * Real.log (2 + 1) ≤ 1 := by
  have := conductance_mul_log_le series_nonneg series_range (a := 0) (b := 2) (n := 2) (c := 1)
    rfl le_rfl (by norm_num) (fun k hk => by rw [shellCapacity_series k hk]; norm_num)
    (fun k hk => by rw [shellCapacity_series k hk]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
  exact_mod_cast this

/-- Each site of the row is its own level of an averaging chain. -/
def level : ℕ → Finset (Fin 3)
  | 0 => {0}
  | 1 => {1}
  | _ => {2}

theorem conductance_series_of_powerLaw : 1 / 512 ≤ conductance series 0 2 := by
  have h := le_conductance_of_powerLaw series_nonneg (a := 0) (b := 2) (by decide) (m := 2)
    (S := level) (fun k _ => by unfold level; split <;> simp) rfl rfl (α := 1 / 4) (β := 1) (σ := 0)
    (by norm_num) one_pos (by norm_num)
    (fun i hi => by interval_cases i <;> simp [level] <;> norm_num)
    (fun k hk x hx y hy => by
      interval_cases k <;> simp_all [level, series])
  have hq : (2 : ℝ) ^ (-(2 - (0 : ℝ)) / 2) = 1 / 2 := by
    rw [show -(2 - (0 : ℝ)) / 2 = -1 by norm_num, Real.rpow_neg_one]; norm_num
  rw [hq] at h
  norm_num at h ⊢
  exact h

end PhysicsOfConsciousness.PhysicalUnity.Examples
