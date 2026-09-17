import Mathlib

/-!
# Finite spatial measures on a finite cover

Compatible finite measures on finitely many measurable patches determine one
finite measure. Disjointification prevents double-counting overlaps. The number
of sites can be infinite; finiteness concerns the cover and the local masses.
There is no mass-one normalization or physical interpretation in this result.
-/

open MeasureTheory Set
namespace PhysicsOfConsciousness.SpatialMeasure

/-- Compatible restrictions on a finite measurable cover have a unique finite
extension. Values of the supplied measures outside their patches are irrelevant.
The result assumes actual measure agreement, rather than agreement only after
sheafification. It does not assert normalization or identify perceptual content. -/
theorem finite_glue_unique {X I : Type*} [MeasurableSpace X] [Fintype I]
    (U : I → Set X) (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (μ : I → FiniteMeasure X)
    (hcompat : ∀ i j, (μ i : Measure X).restrict (U i ∩ U j) =
      (μ j : Measure X).restrict (U i ∩ U j)) :
    ∃! ν : FiniteMeasure X, ∀ i,
      (ν : Measure X).restrict (U i) = (μ i : Measure X).restrict (U i) := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let : LocallyFiniteOrderBot I := LocallyFiniteOrderBot.ofIic I (fun i => Finset.univ.filter (fun j => j ≤ i)) (by simp)
  let D := disjointed U
  have hD (i : I) : MeasurableSet (D i) := by
    dsimp [D]
    rw [disjointed_eq_inter_compl]
    exact (hU i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hU j).compl)
  have hDU : ⋃ i, D i = univ := (iUnion_disjointed (f := U)).trans hcover
  let ν : FiniteMeasure X := ⟨∑ i, (μ i : Measure X).restrict (D i), inferInstance⟩
  have hν (i : I) : (ν : Measure X).restrict (U i) = (μ i : Measure X).restrict (U i) := by
    change (∑ j, (μ j : Measure X).restrict (D j)).restrict (U i) = _
    rw [← Measure.sum_fintype, Measure.restrict_sum _ (hU i)]
    have hpiece (j : I) : ((μ j : Measure X).restrict (D j)).restrict (U i) =
        ((μ i : Measure X).restrict (U i)).restrict (D j) := by
      rw [Measure.restrict_restrict (hU i), Measure.restrict_restrict (hD j), inter_comm (D j)]
      have hsub : U i ∩ D j ⊆ U j ∩ U i := fun _ hx =>
        ⟨disjointed_subset U j hx.2, hx.1⟩
      simpa only [Measure.restrict_restrict_of_subset hsub] using
        congrArg (fun m : Measure X => m.restrict (U i ∩ D j)) (hcompat j i)
    simp_rw [hpiece]
    rw [← Measure.restrict_iUnion (disjoint_disjointed U) hD, hDU, Measure.restrict_univ]
  refine ⟨ν, hν, fun ξ hξ => ?_⟩
  apply FiniteMeasure.toMeasure_injective
  exact Measure.ext_of_iUnion_eq_univ hcover fun i => (hξ i).trans (hν i).symm

/-- The finite-cover restriction has content: unit masses on all singleton
patches of the natural numbers admit no finite global measure. A countably
infinite cover would need an additional total-mass bound. -/
theorem no_finite_measure_of_unit_atoms :
    ¬ ∃ μ : FiniteMeasure ℕ, ∀ n, (μ : Measure ℕ) {n} = 1 := by
  rintro ⟨μ, hμ⟩
  have heq : (μ : Measure ℕ) = Measure.count := by
    apply Measure.ext_of_singleton
    intro n
    simp [hμ]
  have hf := measure_lt_top (μ : Measure ℕ) univ
  rw [heq, Measure.count_univ] at hf
  simp at hf

#print axioms finite_glue_unique
#print axioms no_finite_measure_of_unit_atoms

end PhysicsOfConsciousness.SpatialMeasure

