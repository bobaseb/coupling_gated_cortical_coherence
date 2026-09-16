/-
  Examples/FiniteRegion.lean — finite architectures that the continuum can see

  §26. `Examples/Phase7.lean` §8 puts a thousand units of coupling weight at one
  point of the real line and the field functional registers zero. This section
  puts twelve units on two *cells* of the same line — an interval of mass one
  and an interval of mass three, under an atomless measure — and the same
  functional registers twelve. The difference between the two witnesses is the
  measure of the support, not the number of components.
-/

import PhysicsOfConsciousness.Phase7_FiniteRegion
import PhysicsOfConsciousness.Examples.Phase7

open MeasureTheory

namespace PhysicsOfConsciousness
namespace Examples
namespace FiniteRegionWitness

open PhysicsOfConsciousness.FiniteRegion

/-! ## 26. Two cells on the line, and the weight they register

The substrate is `[0, 4)` with Lebesgue measure: finite, and with no atoms. The
mesh cuts it at `1`, so the two cells carry masses `1` and `3` — deliberately
unequal, because the embedding's density divides by them. -/

/-- The substrate measure: Lebesgue restricted to `[0, 4)`. -/
noncomputable def sub : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 4)

instance : IsFiniteMeasure sub := by
  constructor
  rw [sub, Measure.restrict_apply_univ, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top

instance : NullSingletonClass sub := by
  rw [sub]; infer_instance

/-- The two-cell mesh: everything below `1` in one cell, everything else in the
other. -/
noncomputable abbrev mesh : KernelMesh ℝ where
  size := 2
  locate := fun x => if x < 1 then 0 else 1
  locate_measurable := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_Iio
  sample := ![0, 2]

theorem cell_zero : mesh.cell 0 = Set.Iio 1 := by
  ext x
  simp only [KernelMesh.cell, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iio, mesh]
  split_ifs with h <;> simp [h]

theorem cell_one : mesh.cell 1 = Set.Ici 1 := by
  ext x
  simp only [KernelMesh.cell, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ici, mesh]
  split_ifs with h
  · simp [h]
  · simp
    linarith [not_lt.1 h]

theorem inter_zero : Set.Iio (1 : ℝ) ∩ Set.Ico 0 4 = Set.Ico 0 1 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩

theorem inter_one : Set.Ici (1 : ℝ) ∩ Set.Ico 0 4 = Set.Ico 1 4 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ico]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩

theorem mass_zero : mass mesh sub 0 = 1 := by
  rw [mass, measureReal_def, cell_zero, sub, Measure.restrict_apply measurableSet_Iio,
    inter_zero, Real.volume_Ico]
  norm_num

theorem mass_one : mass mesh sub 1 = 3 := by
  rw [mass, measureReal_def, cell_one, sub, Measure.restrict_apply measurableSet_Ici,
    inter_one, Real.volume_Ico]
  norm_num

theorem mass_ne_zero : ∀ i, mass mesh sub i ≠ 0 := by
  intro i
  match i with
  | 0 => rw [mass_zero]; norm_num
  | 1 => rw [mass_one]; norm_num

/-- A symmetric, nonnegative, zero-diagonal coupling matrix on the two cells:
six units each way between them. -/
def wiring : Fin 2 → Fin 2 → ℝ := ![![0, 6], ![6, 0]]

theorem wiring_symm : ∀ i j, wiring i j = wiring j i := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [wiring]

theorem wiring_nonneg : ∀ i j, 0 ≤ wiring i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [wiring]

theorem wiring_diagonal : ∀ i, wiring i i = 0 := by
  intro i; fin_cases i <;> simp [wiring]

/-- Both cells at the same phase. -/
def phases : Fin 2 → ℝ := ![0, 0]

/-- The discrete total coupling weight, and the discrete phase correlation: both
twelve, because the phases are locked. -/
theorem wiring_resources : total_coupling_resources wiring = 12 := by
  simp [total_coupling_resources, wiring, Fin.sum_univ_two]
  norm_num

theorem wiring_correlation : totalCorrelation phases wiring = 12 := by
  simp [totalCorrelation, wiring, phases, Fin.sum_univ_two]
  norm_num

/-- **The resource is matched.** The continuum kernel integral of the embedded
matrix is the discrete weight it was built from. -/
theorem embedded_resources :
    ∫ x, (∫ y, cellKernel mesh sub wiring x y ∂sub) ∂sub = 12 := by
  rw [kernelIntegral_cellKernel mesh sub wiring mass_ne_zero, wiring_resources]

/-- **And the continuum registers it.** Twelve units of weight spread over two
intervals of positive measure give twelve units of field correlation — against
the zero that the same functional returns for any weight at a point. -/
theorem embedded_correlation :
    fieldCorrelation sub (cellPhase mesh phases) (cellKernel mesh sub wiring) = 12 := by
  rw [fieldCorrelation_cellKernel mesh sub wiring phases mass_ne_zero, wiring_correlation]

/-- **The delimitation, on the witness.** This kernel is not sited on any finite
set of points, so `fieldCorrelation_sited_eq_zero` does not reach it. A finite
architecture vanishes in the continuum functional when it is represented by
points, and not when it is represented by cells. -/
theorem embedded_not_sitedOn (F : Finset ℝ) : ¬ SitedOn F (cellKernel mesh sub wiring) := by
  refine cellKernel_not_sitedOn mesh sub wiring phases mass_ne_zero ?_ F
  rw [wiring_correlation]
  norm_num

/-- The contrast in one statement: the same functional, an atomless substrate,
weight at points registering nothing and weight on cells registering its whole
discrete value. -/
theorem points_versus_cells (theta : ℝ → ℝ) :
    fieldCorrelation volume theta pointArchitecture = 0 ∧
      fieldCorrelation sub (cellPhase mesh phases) (cellKernel mesh sub wiring) = 12 :=
  ⟨pointArchitecture_field_zero theta, embedded_correlation⟩

/-! ### The control for the fixed-support gap

`rigid_architecture_is_beaten` (§8) forces a gap of `2` because the architecture's
one wire misses the perfectly correlated pair. Wire that pair instead and the
gap is not merely smaller — there is none to force: the architecture's best
allocation is optimal among *all* valid couplings of the same weight. -/

/-- The same three sites and phases, wired to the correlated pair `(0, 2)`. -/
def flexWiring : Finset (Fin 3 × Fin 3) := {(0, 2), (2, 0)}

theorem rigidPhases_max (p : Fin 3 × Fin 3) :
    Real.cos (rigidPhases p.2 - rigidPhases p.1)
      ≤ Real.cos (rigidPhases 2 - rigidPhases 0) := by
  have hle : Real.cos (rigidPhases p.2 - rigidPhases p.1) ≤ 1 := Real.cos_le_one _
  rw [show Real.cos (rigidPhases 2 - rigidPhases 0) = 1 by simp [rigidPhases]]
  exact hle

/-- **No forced gap.** With the best distinct pair inside its support, the
architecture realizes a coupling no valid coupling of the same total weight
beats. The separation of §8 is about the missing wire. -/
theorem flex_architecture_not_beaten :
    ∃ A, RealizableIn flexWiring 1 A ∧
      ∀ B, is_valid_coupling B → total_coupling_resources B = 1 →
        totalCorrelation rigidPhases B ≤ totalCorrelation rigidPhases A :=
  no_forced_gap_of_best_wired flexWiring 1 zero_le_one rigidPhases 0 2 (by decide)
    (by decide) (by decide) rigidPhases_max

#print axioms mass_zero
#print axioms mass_one
#print axioms embedded_resources
#print axioms embedded_correlation
#print axioms embedded_not_sitedOn
#print axioms points_versus_cells
#print axioms flex_architecture_not_beaten

end FiniteRegionWitness
end Examples
end PhysicsOfConsciousness
