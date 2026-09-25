import PhysicsOfConsciousness.Phase10_PhysicalUnity

/-!
# Examples/PhysicalUnity.lean — both sides of the margin theorem are inhabited

§38. Two regions, one real micro quantity each.

* **A bit.** Region 0's quantity against the threshold 0. The readout takes
  both values, so the margin is not the margin of a constant map, and at a
  state off the threshold `not_physicallyEnforced_of_bits` applies under the
  identity dynamics.
* **A diffusive pair.** Each region moves a quarter of the way toward the
  other. Region 1's content, its own quantity, depends on region 0's micro
  state at every scale, and the discrepancy `|y 0 − y 1|` halves in one step,
  so agreement between them is physically enforced at every state. The
  definition is therefore not empty, and what excludes the bit is its margin,
  not the definition.
-/

open Filter Topology

namespace PhysicsOfConsciousness.PhysicalUnity.Examples

/-- Two regions with one real micro quantity each. -/
abbrev Pair := Fin 2 → ℝ

/-- The bit "region 0's quantity is positive". -/
noncomputable def bit (y : Pair) : Bool := decide ((0 : ℝ) < y 0)

theorem bit_nonconstant : bit ![1, 0] ≠ bit ![-1, 0] := by
  simp [bit]

/-- The bit is not physically enforced at `![1, 0]`, under the identity dynamics
and for any discrepancy. -/
theorem bit_not_physicallyEnforced (i : Fin 2) (disc : Pair → ℝ) :
    ¬ PhysicallyEnforced (S := fun _ : Fin 2 => ℝ) id (fun y (_ : Unit) => bit y) i disc
      ![1, 0] :=
  not_physicallyEnforced_of_bits (κ := Unit) continuous_id (fun _ => continuous_apply 0)
    (fun _ => 0) (by simp) i disc

/-- Each region moves a quarter of the way toward the other. -/
noncomputable def diffuse (y : Pair) : Pair := ![y 0 + (y 1 - y 0) / 4, y 1 + (y 0 - y 1) / 4]

theorem diffuse_gradedDependence (x : Pair) :
    GradedDependence (S := fun _ : Fin 2 => ℝ) diffuse (fun y => y 1) 0 x := by
  intro h
  have h' : ∀ᶠ s in 𝓝[≠] (x 0), _ := nhdsWithin_le_nhds h
  obtain ⟨s, hs, hne⟩ := (h'.and self_mem_nhdsWithin).exists
  simp [diffuse] at hs
  exact hne hs

theorem diffuse_contracts (x : Pair) :
    Contracts (S := fun _ : Fin 2 => ℝ) diffuse (fun y => |y 0 - y 1|) x := by
  refine ⟨1 / 2, by norm_num, Eventually.of_forall fun y => le_of_eq ?_⟩
  have : diffuse y 0 - diffuse y 1 = (y 0 - y 1) / 2 := by
    simp [diffuse]; ring
  show |diffuse y 0 - diffuse y 1| = 1 / 2 * |y 0 - y 1|
  rw [this, abs_div, abs_two]; ring

theorem diffuse_physicallyEnforced (x : Pair) :
    PhysicallyEnforced (S := fun _ : Fin 2 => ℝ) diffuse (fun y => y 1) 0
      (fun y => |y 0 - y 1|) x :=
  ⟨diffuse_gradedDependence x, diffuse_contracts x⟩

end PhysicsOfConsciousness.PhysicalUnity.Examples
