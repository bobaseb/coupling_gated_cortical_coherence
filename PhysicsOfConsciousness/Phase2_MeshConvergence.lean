import PhysicsOfConsciousness.Phase2_SimplicialBridge

/-!
# Phase 2 (continued): mesh refinement convergence

`Phase2_SimplicialBridge.lean` defined edge weights as Lebesgue–Bochner integrals of a
stress-energy magnitude over `edge_region u v`, and stated mesh refinement convergence as
a conjecture. That conjecture was **false as stated** (see the audit note in
`Phase2_SimplicialBridge.lean`): nothing forced the edge regions to cover the manifold, so
the everywhere-empty triangulation refuted it.

This file replaces it with a proved statement. The repair has three parts.

1. **`Mesh`** — a finite family of pairwise disjoint measurable cells. This is the structure
   the old conjecture was missing: *disjointness* and an explicit *support*.

2. **`abs_riemannSum_sub_setIntegral_le`** — the quantitative Riemann-sum bound. If each
   sampled value `val i` is within `ε` of `f` everywhere on its own cell, the weighted sum
   `∑ᵢ μ(cellᵢ)·val i` differs from `∫_support f` by at most `ε·μ(support)`. Note this is an
   *error estimate at fixed mesh*, not a limit; the limit
   (`tendsto_riemannSum_of_tendsto_fineness`) follows from it by uniform continuity once a
   *sequence* of meshes with fineness tending to `0` is supplied — the second thing the old
   statement lacked.

3. **`IsRegularTriangulation`** (defined in `Phase2_SimplicialBridge.lean`, alongside the
   class it constrains) — exactly the conditions `TriangulatedManifold` fails to impose:
   edge regions are measurable, carry no self-loops, are disjoint across distinct edges,
   cover `S`, are *anchored* to the simplicial data (`embedding u` lies in the closure of
   every nonempty `edge_region u v`) and only occur on faces of the complex. Under these,
   `mesh_refinement_convergence` is a theorem.

The discrete energy `½ ∑ᵤ ∑ᵥ μ(R u v)·f(embedding u)` of the manuscript is *not* an
arbitrary choice of sample point: by `sum_sum_mul_of_symm` (also in
`Phase2_SimplicialBridge.lean`) it is exactly the midpoint rule
`∑_{u<v} μ(R u v)·(f(embedding u) + f(embedding v))/2` over unordered edges. That
identification is what lets the symmetric double sum be read as a Riemann sum at all.

**Numerical counterpart, and the rate.** `simulations/mesh_refinement.py` measures the
same convergence on a 1D ring and reports the empirical rate O(1/N²). *This file* proves
convergence, not a rate: the bound here is `ε·μ(support)` with `ε` the modulus of
continuity, which for a Lipschitz integrand gives O(mesh size). The rate is proved
elsewhere and cannot be proved here. `Examples.lean` §6.1 shows that on the concrete
`[0,1)` grid the discrete energy *is* Mathlib's composite trapezoidal rule
(`grid_discreteEnergy_eq_trapezoidal`), so `trapezoidal_error_le_of_c2` gives
`ζ/(12N²)` for a `C²` integrand (`grid_energy_error_le`), with the bound attained at
`N = 1`. It cannot be stated at this level of generality: a `Mesh` lives over a
`PseudoMetricSpace`, on which there is no second derivative for `ζ` to bound. Second-order
accuracy is a property of a quadrature rule on an interval, not of a partition of a metric
space.

**Witness.** `Examples.lean` §6 builds a genuine refining sequence — the uniform partition
of `[0,1)` into `n` cells — and instantiates these theorems on it, so the hypotheses below
are known to be simultaneously satisfiable by a non-degenerate example.
-/

namespace PhysicsOfConsciousness

open MeasureTheory Metric Filter Topology Set

universe u v

/-! ### A finite mesh -/

/--
A finite mesh on `M`: finitely many pairwise disjoint measurable cells.

Deliberately *not* required to cover `M` — `support` records what it does cover, and the
covering condition is imposed where it is needed rather than assumed globally. Cells are
allowed to be empty; they contribute nothing.
-/
structure Mesh (M : Type u) [PseudoMetricSpace M] [MeasurableSpace M] where
  /-- Index type of the cells. -/
  ι : Type v
  /-- Finiteness of the index type. -/
  fintypeι : Fintype ι
  /-- The cells. -/
  cell : ι → Set M
  /-- Cells are measurable, so they can be integrated over. -/
  measurable_cell : ∀ i, MeasurableSet (cell i)
  /-- Distinct cells are disjoint: this is what makes the sum below a partition sum. -/
  disjoint_cell : Pairwise (Function.onFun Disjoint cell)

attribute [instance] Mesh.fintypeι

namespace Mesh

variable {M : Type u} [PseudoMetricSpace M] [MeasurableSpace M]

/-- The part of `M` the mesh covers. -/
def support (K : Mesh M) : Set M := ⋃ i, K.cell i

/-- The weighted sum `∑ᵢ μ(cellᵢ)·val i`. With `val i` a sampled value of `f` this is the
Riemann sum of `f` over the mesh. -/
noncomputable def riemannSum (K : Mesh M) (μ : Measure M) (val : K.ι → ℝ) : ℝ :=
  ∑ i, μ.real (K.cell i) * val i

theorem measurableSet_support (K : Mesh M) : MeasurableSet K.support :=
  MeasurableSet.iUnion K.measurable_cell

theorem cell_subset_support (K : Mesh M) (i : K.ι) : K.cell i ⊆ K.support :=
  Set.subset_iUnion _ i

/-- Finite additivity: the integral over the support is the sum of the cell integrals. -/
theorem setIntegral_support (K : Mesh M) (μ : Measure M) (f : M → ℝ)
    (hf : IntegrableOn f K.support μ) :
    ∫ x in K.support, f x ∂μ = ∑ i, ∫ x in K.cell i, f x ∂μ := by
  rw [support, integral_iUnion_fintype K.measurable_cell K.disjoint_cell
    (fun i => hf.mono_set (K.cell_subset_support i))]

/--
**Riemann-sum error bound.** If each sampled value `val i` approximates `f` to within `ε`
throughout its own cell, the weighted sum differs from the integral over the support by at
most `ε · μ(support)`.

This is the quantitative core of mesh refinement. It is stated at fixed mesh: the mesh size
enters only through the hypothesis `hval`, which shrinking cells make easier to satisfy for
a (uniformly) continuous integrand.
-/
theorem abs_riemannSum_sub_setIntegral_le (K : Mesh M) (μ : Measure M) (f : M → ℝ)
    (val : K.ι → ℝ) {ε : ℝ} (hμ : μ K.support ≠ ⊤) (hf : IntegrableOn f K.support μ)
    (hval : ∀ i, ∀ x ∈ K.cell i, |val i - f x| ≤ ε) :
    |K.riemannSum μ val - ∫ x in K.support, f x ∂μ| ≤ ε * μ.real K.support := by
  have hcell : ∀ i, μ (K.cell i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hμ (measure_mono (K.cell_subset_support i))
  have hint : ∀ i, IntegrableOn f (K.cell i) μ := fun i =>
    hf.mono_set (K.cell_subset_support i)
  have key : ∀ i : K.ι,
      |μ.real (K.cell i) * val i - ∫ x in K.cell i, f x ∂μ| ≤ ε * μ.real (K.cell i) := by
    intro i
    have hsub : ∫ x in K.cell i, (val i - f x) ∂μ
        = μ.real (K.cell i) * val i - ∫ x in K.cell i, f x ∂μ := by
      have hc : IntegrableOn (fun _ : M => val i) (K.cell i) μ :=
        integrableOn_const (hcell i)
      rw [integral_sub hc (hint i), setIntegral_const, smul_eq_mul]
    rw [← hsub, ← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const (hcell i).lt_top ?_
    intro x hx
    rw [Real.norm_eq_abs]
    exact hval i x hx
  calc |K.riemannSum μ val - ∫ x in K.support, f x ∂μ|
      = |∑ i, (μ.real (K.cell i) * val i - ∫ x in K.cell i, f x ∂μ)| := by
        rw [riemannSum, K.setIntegral_support μ f hf, Finset.sum_sub_distrib]
    _ ≤ ∑ i, |μ.real (K.cell i) * val i - ∫ x in K.cell i, f x ∂μ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * μ.real (K.cell i) := Finset.sum_le_sum fun i _ => key i
    _ = ε * μ.real K.support := by
        rw [← Finset.mul_sum, support, measureReal_iUnion_fintype K.disjoint_cell
          K.measurable_cell hcell]

/--
**Mesh refinement convergence, abstract form.** Along a sequence of meshes with common
support `S`, whose sampled values approximate `f` on their cells with an error that is
eventually uniformly small, the Riemann sums converge to `∫_S f`.

The hypothesis `hval` is what a *refining* sequence buys: see
`tendsto_riemannSum_of_tendsto_fineness`, where it is derived from uniform continuity and
fineness tending to zero.
-/
theorem tendsto_riemannSum {μ : Measure M} {f : M → ℝ} {S : Set M}
    (hμS : μ S ≠ ⊤) (hfS : IntegrableOn f S μ)
    (K : ℕ → Mesh M) (hsupp : ∀ n, (K n).support = S)
    (val : (n : ℕ) → (K n).ι → ℝ)
    (hval : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i, ∀ x ∈ (K n).cell i, |val n i - f x| ≤ ε) :
    Tendsto (fun n => (K n).riemannSum μ (val n)) atTop (𝓝 (∫ x in S, f x ∂μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc0 : (0:ℝ) ≤ μ.real S := measureReal_nonneg
  have hε'0 : 0 < ε / (2 * (μ.real S + 1)) := by
    apply div_pos hε; linarith
  obtain ⟨N, hN⟩ := (hval _ hε'0).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have hbound := (K n).abs_riemannSum_sub_setIntegral_le μ f (val n)
    (by rw [hsupp]; exact hμS) (by rw [hsupp]; exact hfS) (hN n hn)
  rw [hsupp n] at hbound
  rw [Real.dist_eq]
  have hstep : ε / (2 * (μ.real S + 1)) * μ.real S ≤ ε / 2 := by
    have h1 : ε / (2 * (μ.real S + 1)) * μ.real S
        ≤ ε / (2 * (μ.real S + 1)) * (μ.real S + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hε'0.le
    have h2 : ε / (2 * (μ.real S + 1)) * (μ.real S + 1) = ε / 2 := by field_simp
    linarith
  linarith

/--
**Mesh refinement convergence for sampled values.** The concrete instance of
`tendsto_riemannSum`: the integrand is uniformly continuous and each `val n i` is the
average of `f` at two points lying within `m n` of the whole cell, with `m n → 0`.

The sample points are only required to be *close to* the cell, not inside it: a vertex of a
triangulation typically lies on the boundary between two half-open cells and belongs to
neither. Taking `a = b` covers the ordinary one-point Riemann sum; taking the two endpoints
of an edge gives the midpoint rule of `discreteEnergy`.
-/
theorem tendsto_riemannSum_of_tendsto_fineness {μ : Measure M} {f : M → ℝ} {S : Set M}
    (hf : UniformContinuous f) (hμS : μ S ≠ ⊤) (hfS : IntegrableOn f S μ)
    (K : ℕ → Mesh M) (hsupp : ∀ n, (K n).support = S)
    (m : ℕ → ℝ) (hm : Tendsto m atTop (𝓝 0))
    (val : (n : ℕ) → (K n).ι → ℝ)
    (hsample : ∀ n i, ∃ a b : M, (∀ x ∈ (K n).cell i, dist a x ≤ m n) ∧
      (∀ x ∈ (K n).cell i, dist b x ≤ m n) ∧ val n i = (f a + f b) / 2) :
    Tendsto (fun n => (K n).riemannSum μ (val n)) atTop (𝓝 (∫ x in S, f x ∂μ)) := by
  refine tendsto_riemannSum hμS hfS K hsupp val ?_
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1 hf ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hm δ hδ0
  filter_upwards [eventually_ge_atTop N] with n hn i x hx
  have hmn : m n < δ := by
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  obtain ⟨a, b, ha, hb, hval⟩ := hsample n i
  have hfa : |f a - f x| ≤ ε := by
    have h := hδ (a := a) (b := x) (lt_of_le_of_lt (ha x hx) hmn)
    rw [Real.dist_eq] at h; exact h.le
  have hfb : |f b - f x| ≤ ε := by
    have h := hδ (a := b) (b := x) (lt_of_le_of_lt (hb x hx) hmn)
    rw [Real.dist_eq] at h; exact h.le
  rw [hval]
  have hrw : (f a + f b) / 2 - f x = ((f a - f x) + (f b - f x)) / 2 := by ring
  rw [hrw, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  calc |f a - f x + (f b - f x)| / 2 ≤ (|f a - f x| + |f b - f x|) / 2 := by
        gcongr; exact abs_add_le _ _
    _ ≤ (ε + ε) / 2 := by gcongr
    _ = ε := by ring

omit [MeasurableSpace M] in
/-- A point in the closure of a cell of diameter at most `r` is within `r` of every point
of that cell. This is what lets a triangulation's vertices — which sit on cell boundaries
and typically belong to no cell — serve as sample points. -/
theorem dist_le_of_mem_closure {S : Set M} {a x : M} {r : ℝ} (ha : a ∈ closure S)
    (hx : x ∈ S) (hr : ∀ y ∈ S, ∀ z ∈ S, dist y z ≤ r) : dist a x ≤ r := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 ha ε hε
  calc dist a x ≤ dist a y + dist y x := dist_triangle _ _ _
    _ ≤ ε + r := add_le_add hxy.le (hr y hy x hx)
    _ = r + ε := by ring

end Mesh

/-! ### Meshes from regular triangulations -/

variable {M : Type u} [PseudoMetricSpace M] [MeasurableSpace M]

/-- The mesh of a regular triangulation: one cell per unordered edge. -/
noncomputable def meshOfTriangulation (TM : TriangulatedManifold M) [Fintype TM.V]
    [LinearOrder TM.V] {S : Set M} (h : IsRegularTriangulation TM S) : Mesh M where
  ι := {p : TM.V × TM.V // p.1 < p.2}
  fintypeι := Subtype.fintype _
  cell := fun p => TM.edge_region p.1.1 p.1.2
  measurable_cell := fun p => h.measurable_region _ _
  disjoint_cell := by
    intro p q hpq
    exact h.disjoint_region _ _ _ _ p.2 q.2 fun hc => hpq (Subtype.ext hc)

@[simp]
theorem cell_meshOfTriangulation (TM : TriangulatedManifold M) [Fintype TM.V]
    [LinearOrder TM.V] {S : Set M} (h : IsRegularTriangulation TM S)
    (p : (meshOfTriangulation TM h).ι) :
    (meshOfTriangulation TM h).cell p = TM.edge_region p.1.1 p.1.2 := rfl

/-- The cells of `meshOfTriangulation` are the edge regions of the pairs `u < v`. -/
theorem support_eq_iUnion (TM : TriangulatedManifold M) [Fintype TM.V]
    [LinearOrder TM.V] {S : Set M} (h : IsRegularTriangulation TM S) :
    (meshOfTriangulation TM h).support
      = ⋃ p : {p : TM.V × TM.V // p.1 < p.2}, TM.edge_region p.1.1 p.1.2 := rfl

/-- A regular triangulation's mesh covers exactly `S` — the covering condition the old
conjecture lacked, and without which it was refutable. -/
theorem support_meshOfTriangulation (TM : TriangulatedManifold M) [Fintype TM.V]
    [LinearOrder TM.V] {S : Set M} (h : IsRegularTriangulation TM S) :
    (meshOfTriangulation TM h).support = S :=
  (support_eq_iUnion TM h).trans (iUnion_lt_edge_region TM h)

/--
The discrete energy of a triangulation: the manuscript's `½ ∑ᵤ ∑ᵥ w(u,v) f(u)`, with the
edge weight `w(u,v) = μ(edge_region u v)` and `f` sampled at the embedded first endpoint.
-/
noncomputable def discreteEnergy (TM : TriangulatedManifold M) [Fintype TM.V]
    (μ : MeasureTheory.Measure M) (f : M → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ u, ∑ v, μ.real (TM.edge_region u v) * f (TM.embedding u)

/-- The discrete energy is the mesh Riemann sum with the midpoint sample on each edge. -/
theorem discreteEnergy_eq_riemannSum (TM : TriangulatedManifold M) [Fintype TM.V]
    [LinearOrder TM.V] {S : Set M} (h : IsRegularTriangulation TM S) (μ : MeasureTheory.Measure M)
    (f : M → ℝ) :
    discreteEnergy TM μ f
      = (meshOfTriangulation TM h).riemannSum μ
          (fun p => (f (TM.embedding p.1.1) + f (TM.embedding p.1.2)) / 2) := by
  classical
  rw [discreteEnergy, sum_sum_mul_of_symm _ _ (fun u v => by rw [TM.edge_region_symm])
    (fun u => by rw [h.no_self_region]; simp)]
  exact Finset.sum_subtype _ (by simp) _

/--
**Mesh refinement convergence.** Along a sequence of regular triangulations of `S` whose
edge regions shrink to points, the discrete energy converges to the continuous energy
`∫_S f`.

This is the corrected replacement for the conjecture of the same name in
`Phase2_SimplicialBridge.lean`. Four things changed, and all four were necessary:

* the statement quantifies over a **sequence** `TM : ℕ → TriangulatedManifold M` with a
  fineness sequence `m n → 0`, instead of asserting a single `δ` good for *all*
  triangulations of small mesh;
* the triangulations are required to be **regular** (`IsRegularTriangulation`), which is
  what rules out the everywhere-empty triangulation that refuted the old statement;
* the region covered is named (`S`) rather than assumed to be all of `M`: finitely many
  small cells cannot cover an unbounded space, so the old form was unsatisfiable for the
  intended examples;
* the sequence variable is genuinely used — the old statement bound `TM` and then resolved
  `TriangulatedManifold.V M` by instance search, so its binder was dead. Check with
  `set_option pp.explicit true in #check @mesh_refinement_convergence`.

The integrand is a real-valued density on `M`; in the intended application it is the scalar
magnitude of the stress-energy tensor, whose edge integrals are the coupling weights of
`DiscreteThermodynamics.edge_weight`.

`Examples.lean` §6 discharges every hypothesis on the uniform partition of `[0,1)`.
-/
theorem mesh_refinement_convergence (μ : MeasureTheory.Measure M) (f : M → ℝ) {S : Set M}
    (hf : UniformContinuous f) (hμS : μ S ≠ ⊤) (hfS : IntegrableOn f S μ)
    (TM : ℕ → TriangulatedManifold M) [∀ n, Fintype (TM n).V] [∀ n, LinearOrder (TM n).V]
    (hreg : ∀ n, IsRegularTriangulation (TM n) S)
    (m : ℕ → ℝ) (hm : Tendsto m atTop (𝓝 0))
    (hfine : ∀ n u v, ∀ x ∈ (TM n).edge_region u v, ∀ y ∈ (TM n).edge_region u v,
      dist x y ≤ m n) :
    Tendsto (fun n => discreteEnergy (TM n) μ f) atTop (𝓝 (∫ x in S, f x ∂μ)) := by
  set K : ℕ → Mesh M := fun n => meshOfTriangulation (TM n) (hreg n) with hK
  set val : (n : ℕ) → (K n).ι → ℝ := fun n p =>
    (f ((TM n).embedding p.1.1) + f ((TM n).embedding p.1.2)) / 2 with hvaldef
  have hsupp : ∀ n, (K n).support = S := fun n =>
    support_meshOfTriangulation (TM n) (hreg n)
  have hrewrite : (fun n => discreteEnergy (TM n) μ f)
      = fun n => (K n).riemannSum μ (val n) := by
    funext n
    exact discreteEnergy_eq_riemannSum (TM n) (hreg n) μ f
  rw [hrewrite]
  refine Mesh.tendsto_riemannSum_of_tendsto_fineness hf hμS hfS K hsupp m hm val ?_
  intro n i
  refine ⟨(TM n).embedding i.1.1, (TM n).embedding i.1.2, ?_, ?_, rfl⟩
  · intro x hx
    exact Mesh.dist_le_of_mem_closure ((hreg n).anchored _ _ ⟨x, hx⟩) hx
      (fun y hy z hz => hfine n _ _ y hy z hz)
  · intro x hx
    have hne : ((TM n).edge_region i.1.2 i.1.1).Nonempty := by
      rw [(TM n).edge_region_symm]; exact ⟨x, hx⟩
    have hcl := (hreg n).anchored i.1.2 i.1.1 hne
    rw [(TM n).edge_region_symm] at hcl
    exact Mesh.dist_le_of_mem_closure hcl hx (fun y hy z hz => hfine n _ _ y hy z hz)

end PhysicsOfConsciousness
