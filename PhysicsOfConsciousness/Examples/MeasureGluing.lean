import PhysicsOfConsciousness.Phase1_MeasureGluing

/-!
# Actual measures on overlapping open subsets of the real line

The two local measures agree at the shared atom and differ away from the
intersection. Their unique extension counts the overlap once. An infinite
singleton cover supplies the finite-mass counterexample.
-/
open MeasureTheory Set
namespace PhysicsOfConsciousness.Examples.MeasureGluing

noncomputable def point (x : ℝ) : FiniteMeasure ℝ := ⟨Measure.dirac x, inferInstance⟩
@[simp] theorem point_measure (x : ℝ) : (point x : Measure ℝ) = Measure.dirac x := rfl

def patch : Bool → Set ℝ
  | false => Iio 1
  | true => Ioi (-1)
noncomputable def localMeasure : Bool → FiniteMeasure ℝ
  | false => point (-2) + point 0
  | true => point 0 + point 2
noncomputable def glued : FiniteMeasure ℝ := point (-2) + point 0 + point 2

theorem cover : ⋃ i, patch i = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  by_cases h : x < 1
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    change -1 < x
    linarith

theorem overlap_agrees (i j : Bool) :
    (localMeasure i : Measure ℝ).restrict (patch i ∩ patch j) =
      (localMeasure j : Measure ℝ).restrict (patch i ∩ patch j) := by
  cases i <;> cases j <;>
    norm_num [localMeasure, patch, FiniteMeasure.toMeasure_add, point_measure, Measure.restrict_add, restrict_dirac]

theorem glued_restrict (i : Bool) :
    (glued : Measure ℝ).restrict (patch i) = (localMeasure i : Measure ℝ).restrict (patch i) := by
  cases i <;> norm_num [glued, localMeasure, patch, FiniteMeasure.toMeasure_add, point_measure,
    Measure.restrict_add, restrict_dirac]

/-- Finite-cover gluing applies to distinct local measures on a continuous
substrate. This witness does not establish a cortical content model. -/
theorem glued_unique : ∃! ν : FiniteMeasure ℝ, ∀ i,
    (ν : Measure ℝ).restrict (patch i) = (localMeasure i : Measure ℝ).restrict (patch i) :=
  SpatialMeasure.finite_glue_unique patch (by intro i; cases i; exact measurableSet_Iio; exact measurableSet_Ioi)
    cover localMeasure overlap_agrees

/-- Every measure fitting the two patches is the three-atom measure; the
shared atom is counted exactly once. -/
theorem extension_eq (ν : FiniteMeasure ℝ)
    (hν : ∀ i, (ν : Measure ℝ).restrict (patch i) =
      (localMeasure i : Measure ℝ).restrict (patch i)) : ν = glued :=
  ExistsUnique.unique glued_unique hν glued_restrict

theorem glued_mass : (glued : Measure ℝ) univ = 3 := by
  norm_num [glued, FiniteMeasure.toMeasure_add, point_measure]

theorem local_measures_differ : localMeasure false ≠ localMeasure true := by
  intro h
  have := congrArg (fun μ : FiniteMeasure ℝ => (μ : Measure ℝ) {2}) h
  norm_num [localMeasure, FiniteMeasure.toMeasure_add, point_measure] at this

/-- Countably many compatible singleton masses need not have finite total mass. -/
theorem infinite_cover_has_no_finite_extension :
    ¬ ∃ μ : FiniteMeasure ℕ, ∀ n, (μ : Measure ℕ) {n} = 1 :=
  SpatialMeasure.no_finite_measure_of_unit_atoms

#print axioms extension_eq
#print axioms infinite_cover_has_no_finite_extension

end PhysicsOfConsciousness.Examples.MeasureGluing

