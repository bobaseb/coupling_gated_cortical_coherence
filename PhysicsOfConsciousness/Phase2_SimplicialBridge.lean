import PhysicsOfConsciousness.Phase1_Primitives
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import PhysicsOfConsciousness.Phase3_CombinatorialThermodynamics

namespace PhysicsOfConsciousness

structure AbstractSimplicialComplex (V : Type*) where
  faces : Set (Finset V)
  downward_closed : ∀ {s t : Finset V}, s ∈ faces → t ⊆ s → t ∈ faces

/--
A triangulation of `M`.

**Known gap.** Nothing here connects `complex` and `embedding` to `edge_region`:
an instance may pair an arbitrary simplicial complex with arbitrary (even empty,
even overlapping) edge regions. Consequently `edge_weight` is an integral over an
unconstrained set, and `weight_symm` merely unfolds the assumed
`edge_region_symm` field rather than deriving symmetry from geometry. Any claim
that this class "discretizes" a manifold should be read with that in mind. The
missing conditions — `edge_region u v` is anchored to `embedding u` and `embedding v`,
regions are disjoint across distinct edges, and they cover `M` — are exactly what mesh
refinement convergence needs. They are collected in `IsRegularTriangulation`
(`Phase2_MeshConvergence.lean`), which is a *predicate on* a `TriangulatedManifold` rather
than a strengthening of this class: existing instances are unaffected, and every result
that needs the geometry now says so in its hypotheses.
-/
class TriangulatedManifold (M : Type*) [TopologicalSpace M] where
  V : Type*
  complex : AbstractSimplicialComplex V
  embedding : V → M
  edge_region : V → V → Set M
  edge_region_symm : ∀ u v, edge_region u v = edge_region v u

def is_edge {V : Type*} (s : Finset V) : Prop := s.card = 2

structure DiscreteThermodynamics (M : Type*) [TopologicalSpace M] [TriangulatedManifold M] [MeasurableSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] 
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ⊤ M] where
  volume_measure : MeasureTheory.Measure M
  scalar_magnitude : CovariantTensor2 I M → M → ℝ
  magnitude_nonneg : ∀ T x, 0 ≤ scalar_magnitude T x

namespace DiscreteThermodynamics
variable {M : Type*} [TopologicalSpace M] [TriangulatedManifold M] [MeasurableSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] 
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ⊤ M]

-- The coupling weight w(u, v) is defined constructively as the Lebesgue-Bochner integral 
-- of the scalar magnitude of the stress-energy tensor over the edge region.
noncomputable def edge_weight (DT : DiscreteThermodynamics M (E := E) (H := H) (I := I)) (T : CovariantTensor2 I M) (u v : TriangulatedManifold.V M) : ℝ :=
  ∫ x in (TriangulatedManifold.edge_region u v), DT.scalar_magnitude T x ∂DT.volume_measure

-- Symmetry is proved naturally from the geometric symmetry of the edge region.
theorem weight_symm (DT : DiscreteThermodynamics M (E := E) (H := H) (I := I)) (T : CovariantTensor2 I M) (u v : TriangulatedManifold.V M) : 
  edge_weight DT T u v = edge_weight DT T v u := by
  unfold edge_weight
  rw [TriangulatedManifold.edge_region_symm u v]

-- Positivity is proved natively from the non-negativity of the scalar magnitude.
theorem weight_nonneg (DT : DiscreteThermodynamics M (E := E) (H := H) (I := I)) (T : CovariantTensor2 I M) (u v : TriangulatedManifold.V M) : 
  0 ≤ edge_weight DT T u v := by
  unfold edge_weight
  apply MeasureTheory.integral_nonneg
  intro x
  exact DT.magnitude_nonneg T x

end DiscreteThermodynamics

-- Kuramoto Model dynamically derived from continuous field thermodynamics
noncomputable def induced_kuramoto_system (M : Type*) [TopologicalSpace M] [TriangulatedManifold M] [MeasurableSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] 
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ⊤ M]
  (DT : DiscreteThermodynamics M (E := E) (H := H) (I := I))
  [Fintype (TriangulatedManifold.V M)] [DecidableEq (TriangulatedManifold.V M)]
  (T : CovariantTensor2 I M) (omega : TriangulatedManifold.V M → ℝ) : 
  KuramotoSystem (TriangulatedManifold.V M) where
  omega := omega
  A := fun u v => DiscreteThermodynamics.edge_weight DT T u v
  symm := fun u v => DiscreteThermodynamics.weight_symm DT T u v





-- ============================================================================
-- MESH REFINEMENT — moved to Phase2_MeshConvergence.lean
-- ============================================================================

/-
`mesh_refinement_convergence` used to be stated here as a `def … : Prop` in a
"Conjectures" section. It was withdrawn: the statement was not merely unproven, it was
**false and malformed**.

1. *Dead binder.* `∀ (TM : TriangulatedManifold M) [Fintype TM.V]` bound `TM`, but the body
   wrote `TriangulatedManifold.V M` and `TriangulatedManifold.edge_region`, which resolve
   by **instance search**, not through `TM`. The binder was never used.

2. *Refutable.* Nothing required `edge_region` to cover `M`, and `Metric.diam ∅ = 0 < δ`
   for every `δ > 0`. The triangulation whose edge regions are all empty therefore
   satisfied the mesh hypothesis while contributing `0` to the sum, forcing `|0 - ∫ f| < ε`
   for all `ε > 0` — false for any `f` with `∫ f ≠ 0`.

`Phase2_MeshConvergence.lean` replaces it with a **theorem** of the same name, quantified
over a *sequence* of triangulations with fineness tending to zero, each required to be an
`IsRegularTriangulation` (measurable, non-degenerate, pairwise disjoint, covering, and
anchored to the `complex`/`embedding` data — precisely the conditions this class leaves
open, as flagged in the doc-string of `TriangulatedManifold` above).

**Numerical counterpart** — `simulations/mesh_refinement.py`:
  • Computes the continuous Kuramoto potential V_cont on a 1D ring [0, 2π) using
    a fine Riemann sum (N=2000) with Gaussian coupling and sinusoidal phase.
  • Computes discrete potentials V_disc on meshes of size N = {10, 20, 40, 80, 160, 320, 640}.
  • Plots |V_disc - V_cont| in log-log scale, confirming O(1/N²) convergence.
  • Saves the convergence plot to `simulations/mesh_refinement_convergence.png`.

  Run: `python simulations/mesh_refinement.py` (function `run_mesh_refinement_simulation`).

  The Lean theorem proves convergence, not the O(1/N²) rate: its error bound is
  `ε · μ(support)` with `ε` a modulus of continuity of the integrand.
-/


end PhysicsOfConsciousness
