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

end PhysicsOfConsciousness.PhysicalUnity.Examples
