import PhysicsOfConsciousness.Phase10_UnityWindow

/-!
# Examples/UnityWindow.lean — the relaxation edge is met exactly

§41. The halving map `y ↦ y / 2` on the line, with discrepancy `|y|`, contracts
by exactly `½` per step, so both relaxation bounds apply with `κ = ρ = ½`.
Starting from `8` with tolerance `1`, the predicted relaxation time is
`log 8 / log 2 = 3`: the discrepancy is at most `1` at step `3`
(`disc_iterate_le_of_log_le`) and still above `1` at step `2`
(`lt_disc_iterate_of_lt_log`). Neither edge can be moved.
-/

namespace PhysicsOfConsciousness.PhysicalUnity.Examples

/-- Halve the discrepancy. -/
noncomputable def halve (y : ℝ) : ℝ := y / 2

theorem halve_contracts (y : ℝ) : |halve y| ≤ 1 / 2 * |y| := by
  simp [halve, abs_div]; ring_nf; rfl

theorem halve_slow (y : ℝ) : 1 / 2 * |y| ≤ |halve y| := by
  simp [halve, abs_div]; ring_nf; rfl

theorem log_eight_div_log_two : Real.log (8 / 1) / Real.log (1 / (1 / 2)) = 3 := by
  have h8 : (8 : ℝ) / 1 = 2 ^ 3 := by norm_num
  rw [h8, Real.log_pow, one_div_one_div]
  have : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp; norm_num

theorem halve_agrees_at_three : |halve^[3] 8| ≤ 1 :=
  disc_iterate_le_of_log_le (D := Set.univ) (Set.mapsTo_univ _ _) (by norm_num) (by norm_num)
    (fun y _ => halve_contracts y) (Set.mem_univ _) (d₀ := 8) (by norm_num) (by norm_num)
    (by norm_num) (by rw [log_eight_div_log_two]; norm_num)

theorem halve_disagrees_at_two : 1 < |halve^[2] 8| :=
  lt_disc_iterate_of_lt_log (D := Set.univ) (disc := fun y => |y|) (Set.mapsTo_univ _ _)
    (ρ := 1 / 2) (by norm_num) (by norm_num) (fun y _ => halve_slow y) (Set.mem_univ _)
    (by norm_num) (by norm_num)
    (by simp only [abs_of_pos (show (0 : ℝ) < 8 by norm_num)]; rw [log_eight_div_log_two]; norm_num)

end PhysicsOfConsciousness.PhysicalUnity.Examples
