/-
  Examples/Phase7.lean — wiring rigidity, and the continuum separation

  §8 witnesses both halves. On three sites wired only to the maximally
  anti-correlated pair, `is_strictly_suboptimal` is *derived* from the wiring
  rather than assumed. On the real line, a single-site architecture carrying a
  thousand units of weight registers exactly zero field correlation against a
  unit patch that registers one.
-/

import PhysicsOfConsciousness.Phase7_Rigidity

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 8. Wiring rigidity, and the continuum separation

`Phase7_Rigidity` claims two things that are worth nothing without instances:
that `is_strictly_suboptimal` — the hypothesis `Phase7_HardwareComparison` had to
assume — follows from a wiring pattern that misses the best pair, and that a
finitely-sited architecture registers nothing in the field functional. Both are
exhibited here. -/

/-- A three-site substrate whose only wire joins sites `0` and `1`. -/
def rigidWiring : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 0)}

/-- Sites `0` and `2` are in phase; site `1` is in antiphase. The architecture's
one wire therefore joins the maximally *anti*-correlated pair, while the
perfectly correlated pair `(0, 2)` has no wire at all. -/
noncomputable def rigidPhases : Fin 3 → ℝ := fun i => if i = 1 then Real.pi else 0

theorem rigidWiring_bound :
    ∀ p ∈ rigidWiring, Real.cos (rigidPhases p.2 - rigidPhases p.1) ≤ -1 := by
  intro p hp
  fin_cases hp <;> simp [rigidPhases]

theorem rigid_unwired_better : (-1 : ℝ) < Real.cos (rigidPhases 2 - rigidPhases 0) := by
  simp [rigidPhases]

/-- The architecture can spend its whole budget, and the best it can buy is
`-1`: total anti-correlation. -/
theorem exists_rigid_coupling :
    ∃ A, RealizableIn rigidWiring 1 A ∧ totalCorrelation rigidPhases A = -1 := by
  obtain ⟨A, hA, hval⟩ :=
    exists_realizable_pair rigidWiring 1 zero_le_one rigidPhases 0 1
      (by decide) (by decide) (by decide)
  exact ⟨A, hA, by rw [hval]; simp [rigidPhases]⟩

/-- **The hypothesis is derived, and the gap is `2`.** Every coupling this
architecture can realize at unit budget is strictly suboptimal — no longer an
assumption — and an unconstrained reallocation of the same budget beats it by at
least `2`, the full swing from anti-correlation to correlation. -/
theorem rigid_architecture_is_beaten (A : Fin 3 → Fin 3 → ℝ)
    (hA : RealizableIn rigidWiring 1 A) :
    is_strictly_suboptimal A rigidPhases
      ∧ ∃ A', is_valid_coupling A' ∧ total_coupling_resources A' = 1
          ∧ totalCorrelation rigidPhases A' - totalCorrelation rigidPhases A ≥ 2 := by
  refine ⟨rigid_is_strictly_suboptimal rigidWiring 1 (-1) one_pos rigidPhases 0 2 A hA
      rigidWiring_bound rigid_unwired_better, ?_⟩
  obtain ⟨A', hvalid, hres, _, hgap⟩ :=
    rigid_gap rigidWiring 1 (-1) one_pos rigidPhases 0 2 (by decide) A hA
      rigidWiring_bound rigid_unwired_better
  refine ⟨A', hvalid, hres, ?_⟩
  have : (1 : ℝ) * (Real.cos (rigidPhases 2 - rigidPhases 0) - (-1)) = 2 := by
    simp [rigidPhases]; norm_num
  linarith [hgap, this.symm.le, this.le]

/-- Phase 7's reallocation lemma now fires with no assumed hypothesis: the
suboptimality it needs comes from the wiring. -/
theorem rigid_architecture_beaten_by_phase7 (A : Fin 3 → Fin 3 → ℝ)
    (hA : RealizableIn rigidWiring 1 A) :
    ∃ A_flex : Fin 3 → Fin 3 → ℝ, is_valid_coupling A_flex ∧
      total_coupling_resources A_flex = total_coupling_resources A ∧
      (∑ i, ∑ j, A_flex i j * Real.cos (rigidPhases j - rigidPhases i)) >
      (∑ i, ∑ j, A i j * Real.cos (rigidPhases j - rigidPhases i)) :=
  exists_better_coupling_allocation A rigidPhases hA.1
    (rigid_architecture_is_beaten A hA).1

/-! ### The continuum half -/

/-- A single-site architecture on the real line, carrying a thousand units of
coupling weight — all of it at the origin. -/
noncomputable def pointArchitecture : ℝ → ℝ → ℝ := fun x _ => if x = 0 then 1000 else 0

theorem pointArchitecture_sited : SitedOn ({0} : Finset ℝ) pointArchitecture := by
  intro x hx y
  simp only [pointArchitecture, ite_eq_right_iff]
  intro h
  exact absurd (by simp [h]) hx

/-- **Weight at a point buys nothing.** However large the coupling at the origin,
the field correlation is exactly zero — for every phase field. -/
theorem pointArchitecture_field_zero (theta : ℝ → ℝ) :
    fieldCorrelation volume theta pointArchitecture = 0 :=
  fieldCorrelation_sited_eq_zero volume {0} pointArchitecture pointArchitecture_sited theta

/-- A unit patch of unit-strength field coupling registers `1`. -/
theorem patch_field_one :
    fieldCorrelation volume (fun _ => 0) (patchKernel (Set.Ico (0 : ℝ) 1) 1) = 1 := by
  rw [fieldCorrelation_patchKernel volume _ measurableSet_Ico 1]
  simp

/-- The typed separation, instantiated: a `Finset ℝ` of sites against a set of
positive measure. -/
example (theta : ℝ → ℝ) :
    fieldCorrelation volume theta pointArchitecture
      < fieldCorrelation volume (fun _ => 0) (patchKernel (Set.Ico (0 : ℝ) 1) 1) :=
  sited_architecture_below_field_optimum volume {0} pointArchitecture pointArchitecture_sited
    theta (Set.Ico 0 1) measurableSet_Ico (by simp) (by simp) 1 one_pos

end Examples
end PhysicsOfConsciousness
