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
A triangulation of `M`: bare data.

This class pairs a simplicial complex with an embedding of its vertices and a family of
edge regions, and imposes only that the regions are symmetric. Nothing here ties `complex`
and `embedding` to `edge_region`, so an instance may pair an arbitrary complex with
arbitrary — even empty, even overlapping — regions.

The conditions that make the pairing an actual triangulation are collected in
`IsRegularTriangulation` below: regions measurable, no self-loops, every nonempty region
sitting on a genuine face of the complex with its endpoints in the region's closure,
distinct edges disjoint, and the whole family covering a named region `S`.

They are kept out of this class deliberately, so that `TriangulatedManifold` remains *data*
and regularity remains a *property* which a result either needs or does not. Everything
that needs the geometry now says so, and the two consumers say it in the two available
ways: `DiscreteThermodynamics` carries an `IsRegularTriangulation` **field**, so its edge
weights are integrals over geometrically constrained sets rather than arbitrary ones; and
`mesh_refinement_convergence` (`Phase2_MeshConvergence.lean`) takes it as a **hypothesis**,
since it quantifies over a whole sequence of triangulations.
-/
class TriangulatedManifold (M : Type*) [TopologicalSpace M] where
  V : Type*
  complex : AbstractSimplicialComplex V
  embedding : V → M
  edge_region : V → V → Set M
  edge_region_symm : ∀ u v, edge_region u v = edge_region v u

def is_edge {V : Type*} (s : Finset V) : Prop := s.card = 2

/-! ### Symmetric double sums over edges -/

/--
A symmetric function with vanishing diagonal, summed over all ordered pairs, is twice its
sum over the pairs `u < v`. The linear order is only bookkeeping: it selects one
representative of each unordered pair.
-/
theorem sum_sum_of_symm {V : Type*} [Fintype V] [LinearOrder V] (g : V → V → ℝ)
    (hsymm : ∀ u v, g u v = g v u) (hdiag : ∀ u, g u u = 0) :
    ∑ u, ∑ v, g u v
      = 2 * ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2), g p.1 p.2 := by
  classical
  have hprod : ∑ u, ∑ v, g u v = ∑ p ∈ (Finset.univ : Finset (V × V)), g p.1 p.2 := by
    rw [Fintype.sum_prod_type]
  have hgt : ∑ p ∈ Finset.univ.filter (fun p : V × V => p.2 < p.1), g p.1 p.2
      = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2), g p.1 p.2 := by
    refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_ <;>
      simp_all
  have hsplit : ∑ p ∈ (Finset.univ : Finset (V × V)), g p.1 p.2
      = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2), g p.1 p.2
        + ∑ p ∈ Finset.univ.filter (fun p : V × V => p.2 < p.1), g p.1 p.2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : V × V => p.1 < p.2)]
    congr 1
    refine (Finset.sum_subset ?_ ?_).symm
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact not_lt.2 hp.le
    · intro p hp hp'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp hp'
      have : p.1 = p.2 := le_antisymm hp' hp
      rw [this]
      exact hdiag _
  rw [hprod, hsplit, hgt]
  ring

/--
**The half-sum is the midpoint rule.** For a symmetric weight `w` with no self-loops, the
manuscript's discrete energy `½ ∑ᵤ ∑ᵥ w u v · φ u` — which samples the *first* endpoint,
and so is not itself symmetric — equals the sum over unordered edges of the weight times
the *average* of `φ` over the two endpoints.

Without this, reading `½ ∑ᵤ ∑ᵥ` as a Riemann sum would be a category error: the double sum
visits each edge region twice, and only after pairing the two visits does a single sampled
value per cell appear.
-/
theorem sum_sum_mul_of_symm {V : Type*} [Fintype V] [LinearOrder V] (w : V → V → ℝ)
    (φ : V → ℝ) (hsymm : ∀ u v, w u v = w v u) (hdiag : ∀ u, w u u = 0) :
    (1 / 2 : ℝ) * ∑ u, ∑ v, w u v * φ u
      = ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2),
          w p.1 p.2 * ((φ p.1 + φ p.2) / 2) := by
  classical
  have hswap : ∑ u, ∑ v, w u v * φ v = ∑ u, ∑ v, w u v * φ u := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ => by rw [hsymm]
  have hg := sum_sum_of_symm (fun u v => w u v * ((φ u + φ v) / 2))
    (fun u v => by rw [hsymm]; ring) (fun u => by rw [hdiag]; ring)
  have hexpand : ∑ u, ∑ v, w u v * ((φ u + φ v) / 2)
      = ((∑ u, ∑ v, w u v * φ u) + ∑ u, ∑ v, w u v * φ v) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hexpand, hswap] at hg
  linarith

/-! ### Regular triangulations -/

/--
The conditions `TriangulatedManifold` leaves unimposed, and which the false conjecture
recorded at the end of this file silently needed. `S` is the region the triangulation
covers.

`anchored` and `face_of_complex` are what tie `edge_region` to the simplicial data: a
region may only sit on an actual face of the complex, and the embedded vertices of that
face must lie in its closure. Closure, not membership: cells are disjoint, so a vertex
shared by two edges belongs to at most one of them — in the standard half-open partition of
an interval it is a boundary point of both. Without `covers` the everywhere-empty
triangulation refutes convergence.

Only a topological and a measurable structure are needed to *state* these conditions; the
metric enters in `Phase2_MeshConvergence.lean`, where cell diameters are measured.
-/
structure IsRegularTriangulation {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (TM : TriangulatedManifold M) [LinearOrder TM.V] (S : Set M) : Prop where
  /-- Edge regions can be integrated over. -/
  measurable_region : ∀ u v, MeasurableSet (TM.edge_region u v)
  /-- A vertex has no edge to itself. -/
  no_self_region : ∀ u, TM.edge_region u u = ∅
  /-- A region only occurs on an actual edge of the complex. -/
  face_of_complex : ∀ u v, (TM.edge_region u v).Nonempty →
    ({u, v} : Finset TM.V) ∈ TM.complex.faces
  /-- Regions are anchored to the embedded vertices of their edge. -/
  anchored : ∀ u v, (TM.edge_region u v).Nonempty →
    TM.embedding u ∈ closure (TM.edge_region u v)
  /-- Distinct edges have disjoint regions. -/
  disjoint_region : ∀ u v u' v', u < v → u' < v' → (u, v) ≠ (u', v') →
    Disjoint (TM.edge_region u v) (TM.edge_region u' v')
  /-- The regions cover `S`. -/
  covers : ⋃ u, ⋃ v, TM.edge_region u v = S

/--
The covered region, re-indexed by *unordered* edges: every point of `S` lies in the region
of exactly one pair `u < v`.

Symmetry supplies the pair in the wrong order and `no_self_region` rules out the diagonal,
so nothing is lost by restricting the union. This is the form the union is needed in
whenever cells are summed over, since it is the pairs `u < v` that are pairwise disjoint.
-/
theorem iUnion_lt_edge_region {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (TM : TriangulatedManifold M) [LinearOrder TM.V] {S : Set M}
    (h : IsRegularTriangulation TM S) :
    ⋃ p : {p : TM.V × TM.V // p.1 < p.2}, TM.edge_region p.1.1 p.1.2 = S := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun p => ?_) fun x hxS => ?_
  · rw [← h.covers]
    exact Set.subset_iUnion_of_subset p.1.1 (Set.subset_iUnion _ p.1.2)
  have hx : x ∈ ⋃ u, ⋃ v, TM.edge_region u v := by rw [h.covers]; exact hxS
  simp only [Set.mem_iUnion] at hx
  obtain ⟨u, v, hxuv⟩ := hx
  rcases lt_trichotomy u v with hlt | heq | hgt
  · exact Set.mem_iUnion.2 ⟨⟨(u, v), hlt⟩, hxuv⟩
  · exact absurd (heq ▸ hxuv) (by rw [h.no_self_region]; exact Set.notMem_empty x)
  · refine Set.mem_iUnion.2 ⟨⟨(v, u), hgt⟩, ?_⟩
    rw [TM.edge_region_symm]
    exact hxuv

/-! ### Discrete thermodynamics on a regular triangulation -/

/--
The discretization of a continuum stress-energy field onto a triangulation.

The `region`/`regular` pair is what makes this a *derivation* of the coupling matrix rather
than a relabelling of one. Without it `edge_weight` below would be an integral over an
unconstrained set: `weight_symm` would still hold (it only unfolds `edge_region_symm`), but
nothing would connect a nonzero weight to an edge of the complex, nothing would stop two
edges from claiming the same energy twice, and the total coupling would bear no relation to
the energy of any region of `M`. With it, all three become theorems — `weight_self`,
`face_of_weight_ne_zero`, and `total_weight_eq_setIntegral`.

The triangulation `TM` and the model `I` are explicit parameters rather than instance
arguments. They have to be: neither appears in the resulting type, so were they instance
arguments no projection out of a `DiscreteThermodynamics` could recover them, and the
structure would be unusable without a *global* `TriangulatedManifold M` instance — which is
exactly what a space carrying a whole sequence of triangulations must not have.
`Examples.lean` §6 witnesses this on the uniform grid.
-/
structure DiscreteThermodynamics {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (TM : TriangulatedManifold M) [LinearOrder TM.V]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I ⊤ M] where
  volume_measure : MeasureTheory.Measure M
  scalar_magnitude : CovariantTensor2 I M → M → ℝ
  magnitude_nonneg : ∀ T x, 0 ≤ scalar_magnitude T x
  /-- The part of `M` the triangulation discretizes. -/
  region : Set M
  /-- The triangulation is regular over `region`. -/
  regular : IsRegularTriangulation TM region

namespace DiscreteThermodynamics

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  {TM : TriangulatedManifold M} [LinearOrder TM.V]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ⊤ M]

/-- The coupling weight `w(u, v)`, defined constructively as the Lebesgue–Bochner integral
of the scalar magnitude of the stress-energy tensor over the edge region. -/
noncomputable def edge_weight (DT : DiscreteThermodynamics TM I)
    (T : CovariantTensor2 I M) (u v : TM.V) : ℝ :=
  ∫ x in TM.edge_region u v, DT.scalar_magnitude T x ∂DT.volume_measure

/-- Symmetry, from the geometric symmetry of the edge region. -/
theorem weight_symm (DT : DiscreteThermodynamics TM I) (T : CovariantTensor2 I M) (u v : TM.V) :
    edge_weight DT T u v = edge_weight DT T v u := by
  unfold edge_weight
  rw [TM.edge_region_symm u v]

/-- Non-negativity, from the non-negativity of the scalar magnitude. -/
theorem weight_nonneg (DT : DiscreteThermodynamics TM I) (T : CovariantTensor2 I M) (u v : TM.V) :
    0 ≤ edge_weight DT T u v := by
  unfold edge_weight
  apply MeasureTheory.integral_nonneg
  intro x
  exact DT.magnitude_nonneg T x

/-- **No self-coupling.** A vertex carries no edge to itself, so the diagonal of the induced
coupling matrix vanishes. This is what lets the ordered double sum over `V × V` be read as a
sum over unordered edges (`sum_sum_of_symm`). -/
theorem weight_self (DT : DiscreteThermodynamics TM I) (T : CovariantTensor2 I M) (u : TM.V) :
    edge_weight DT T u u = 0 := by
  unfold edge_weight
  rw [DT.regular.no_self_region u]
  simp

/-- **The coupling graph is carried by the complex.** A nonzero weight on `(u, v)` forces
`{u, v}` to be an actual face of the simplicial complex: the discretization cannot invent a
coupling between vertices the triangulation does not join.

This is the statement that was unavailable while `DiscreteThermodynamics` left
`edge_region` disconnected from `complex`. -/
theorem face_of_weight_ne_zero (DT : DiscreteThermodynamics TM I) (T : CovariantTensor2 I M)
    {u v : TM.V} (h : edge_weight DT T u v ≠ 0) :
    ({u, v} : Finset TM.V) ∈ TM.complex.faces := by
  refine DT.regular.face_of_complex u v ?_
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  refine h ?_
  unfold edge_weight
  rw [hempty]
  simp

/--
**The edge weights partition the stress-energy of the discretized region.**

`½ ∑ᵤ ∑ᵥ w(u,v) = ∫_region |T|`: the total coupling strength of the induced Kuramoto system
is exactly the scalar stress-energy carried by the region the triangulation covers — nothing
counted twice, nothing dropped. `disjoint_region` supplies "nothing counted twice", `covers`
supplies "nothing dropped", and `no_self_region` with `edge_region_symm` are what collapse
the ordered double sum onto unordered edges.

This is the precise sense in which `DiscreteThermodynamics` *derives* the coupling matrix
from the continuum instead of positing it, and it is exactly what fails without regularity:
the everywhere-empty triangulation gives all weights `0` while `∫_region |T|` need not
vanish.
-/
theorem total_weight_eq_setIntegral [Fintype TM.V] (DT : DiscreteThermodynamics TM I)
    (T : CovariantTensor2 I M)
    (hint : MeasureTheory.IntegrableOn (DT.scalar_magnitude T) DT.region DT.volume_measure) :
    (1 / 2 : ℝ) * ∑ u, ∑ v, edge_weight DT T u v
      = ∫ x in DT.region, DT.scalar_magnitude T x ∂DT.volume_measure := by
  classical
  have hcov := iUnion_lt_edge_region TM DT.regular
  have hsub : ∀ p : {p : TM.V × TM.V // p.1 < p.2}, TM.edge_region p.1.1 p.1.2 ⊆ DT.region := by
    intro p
    rw [← hcov]
    exact Set.subset_iUnion
      (fun q : {q : TM.V × TM.V // q.1 < q.2} => TM.edge_region q.1.1 q.1.2) p
  have hsplit : ∫ x in DT.region, DT.scalar_magnitude T x ∂DT.volume_measure
      = ∑ p : {p : TM.V × TM.V // p.1 < p.2},
          ∫ x in TM.edge_region p.1.1 p.1.2, DT.scalar_magnitude T x ∂DT.volume_measure := by
    rw [← hcov]
    exact MeasureTheory.integral_iUnion_fintype (fun p => DT.regular.measurable_region _ _)
      (fun p q hpq => DT.regular.disjoint_region _ _ _ _ p.2 q.2
        fun hc => hpq (Subtype.ext hc))
      (fun p => hint.mono_set (hsub p))
  have hsubtype : ∑ p ∈ Finset.univ.filter (fun p : TM.V × TM.V => p.1 < p.2),
        edge_weight DT T p.1 p.2
      = ∑ p : {p : TM.V × TM.V // p.1 < p.2}, edge_weight DT T p.1.1 p.1.2 :=
    Finset.sum_subtype _ (by simp) _
  rw [sum_sum_of_symm (fun u v => edge_weight DT T u v)
      (fun u v => weight_symm DT T u v) (fun u => weight_self DT T u), hsubtype, hsplit]
  have hpt : ∀ p : {p : TM.V × TM.V // p.1 < p.2}, edge_weight DT T p.1.1 p.1.2
      = ∫ x in TM.edge_region p.1.1 p.1.2, DT.scalar_magnitude T x ∂DT.volume_measure :=
    fun _ => rfl
  rw [Finset.sum_congr rfl fun p _ => hpt p]
  ring

end DiscreteThermodynamics

/-- The Kuramoto system induced by a discretized stress-energy field: the coupling matrix is
the family of edge weights, and its symmetry is `weight_symm` rather than an assumption. -/
noncomputable def induced_kuramoto_system {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (TM : TriangulatedManifold M) [LinearOrder TM.V] [Fintype TM.V]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ⊤ M]
    (DT : DiscreteThermodynamics TM I) (T : CovariantTensor2 I M) (omega : TM.V → ℝ) :
    KuramotoSystem TM.V where
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
anchored to the `complex`/`embedding` data — precisely the conditions `TriangulatedManifold`
leaves open, as flagged in its doc-string above).

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
