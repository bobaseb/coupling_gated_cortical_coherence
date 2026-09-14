import Mathlib

/-!
# Finite cell-pair reconstruction of a coupling kernel

A mesh locates every substrate point in a measurable cell and chooses one
sample per cell. A discrete weight is extended over the whole cell pair;
it is not supported only on the vertices. The weighted finite energy equals
the product-measure integral of this reconstruction. Continuous kernels on a
compact substrate converge pointwise and in integral under spatial refinement.
No temporal evolution, thermodynamic budget or cortical identification is
deduced. `Examples/MicroscopicCoupling.lean` witnesses nonconstant energies on
an atomless substrate.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness

/-- Bare finite partition and sampling data. Measurability is needed to assign
cell masses; refinement and kernel regularity are separate hypotheses. -/
structure KernelMesh (M : Type*) [MeasurableSpace M] where
  size : ℕ
  locate : M → Fin size
  locate_measurable : Measurable locate
  sample : Fin size → M

namespace KernelMesh

variable {M : Type*} [MeasurableSpace M]

def cell (G : KernelMesh M) (i : Fin G.size) : Set M := G.locate ⁻¹' {i}

def snap (G : KernelMesh M) (x : M) : M := G.sample (G.locate x)

/-- Each matrix entry acts throughout its cell pair. Cell volumes, rather than
the cardinality of vertices, determine its contribution to continuum energy. -/
def kernel (G : KernelMesh M) (K : M → M → ℝ) (x y : M) : ℝ :=
  K (G.snap x) (G.snap y)

noncomputable def energy (G : KernelMesh M) (μ : Measure M) (K : M → M → ℝ) : ℝ :=
  ∑ ij : Fin G.size × Fin G.size,
    μ.real (G.cell ij.1) * μ.real (G.cell ij.2) * K (G.sample ij.1) (G.sample ij.2)

/-- The finite cell-mass sum is exactly the reconstructed kernel's integral.
This identity needs no continuity or refinement, but it does need finite mass
and measurable cells. It asserts nothing about phase trajectories. -/
theorem energy_eq_integral (G : KernelMesh M) (μ : Measure M) [IsFiniteMeasure μ]
    (K : M → M → ℝ) :
    G.energy μ K = ∫ z, G.kernel K z.1 z.2 ∂μ.prod μ := by
  let index : M × M → Fin G.size × Fin G.size := fun z => (G.locate z.1, G.locate z.2)
  have hi : Measurable index :=
    (G.locate_measurable.comp measurable_fst).prodMk
      (G.locate_measurable.comp measurable_snd)
  let value : Fin G.size × Fin G.size → ℝ := fun ij => K (G.sample ij.1) (G.sample ij.2)
  change _ = ∫ z, value (index z) ∂μ.prod μ
  rw [← integral_map_of_stronglyMeasurable hi (measurable_of_countable value).stronglyMeasurable,
    integral_fintype (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro ij _
  have hcell : index ⁻¹' {ij} = G.cell ij.1 ×ˢ G.cell ij.2 := by
    ext z
    simp [index, cell, Prod.ext_iff]
  simp only [Measure.real, Measure.map_apply hi (measurableSet_singleton ij), hcell,
    Measure.prod_prod, ENNReal.toReal_mul, smul_eq_mul, value]

theorem snap_measurable (G : KernelMesh M) : Measurable G.snap :=
  (measurable_of_countable G.sample).comp G.locate_measurable

section Topological

variable [TopologicalSpace M]

/-- Spatial consistency of both cell samples gives consistency of the pair
kernel. No convergence in the number of executed actions is assumed or used. -/
theorem kernel_tendsto (G : ℕ → KernelMesh M) (K : M → M → ℝ)
    (hK : Continuous (Function.uncurry K))
    (hG : ∀ x, Tendsto (fun n => (G n).snap x) atTop (𝓝 x)) (x y : M) :
    Tendsto (fun n => (G n).kernel K x y) atTop (𝓝 (K x y)) :=
  hK.continuousAt.tendsto.comp ((hG x).prodMk_nhds (hG y))

/-- The product-space limit also passes through the energy integral. Compactness
bounds the continuous kernel and finite substrate mass makes that bound
integrable. The limiting kernel is the specified hardware law, not a kernel
inferred from a scalar limit or a heat allowance. -/
theorem energy_tendsto [CompactSpace M] [SecondCountableTopology M] [BorelSpace M]
    (G : ℕ → KernelMesh M)
    (μ : Measure M) [IsFiniteMeasure μ] (K : M → M → ℝ)
    (hK : Continuous (Function.uncurry K))
    (hG : ∀ x, Tendsto (fun n => (G n).snap x) atTop (𝓝 x)) :
    Tendsto (fun n => (G n).energy μ K) atTop (𝓝 (∫ z, K z.1 z.2 ∂μ.prod μ)) := by
  let f : C(M × M, ℝ) := ⟨Function.uncurry K, hK⟩
  simp_rw [energy_eq_integral]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (hK.measurable.comp (((G n).snap_measurable.comp measurable_fst).prodMk
      ((G n).snap_measurable.comp measurable_snd))).aestronglyMeasurable
  · exact integrable_const ‖f‖
  · intro n
    exact ae_of_all _ fun z => f.norm_coe_le_norm ((G n).snap z.1, (G n).snap z.2)
  · exact ae_of_all _ fun z => kernel_tendsto G K hK hG z.1 z.2

end Topological

/-- A shrinking spatial error bound implies the sample consistency used by
the kernel theorem. The bound concerns locations, never learning iterates. -/
theorem snap_tendsto_of_dist [PseudoMetricSpace M] (G : ℕ → KernelMesh M)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ n x, dist ((G n).snap x) x ≤ δ n) (x : M) :
    Tendsto (fun n => (G n).snap x) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => hf n x) hδ

end KernelMesh

end PhysicsOfConsciousness
