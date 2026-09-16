import PhysicsOfConsciousness.Phase2_KernelMesh
import PhysicsOfConsciousness.Phase7_Rigidity

/-!
# Finite regions in the continuum functional

`fieldCorrelation_sited_eq_zero` says that on a substrate with no atoms a kernel
supported on finitely many *points* registers exactly zero coupling energy. That
is a sharp statement, and it is easy to over-read: it looks like a verdict on
finitely many components, when it is a statement about sets of measure zero.

This module draws the line. A finite architecture is embedded in the continuum
not as points but as finitely many measurable **cells** of positive mass — the
cells of a `KernelMesh` — with a coupling matrix `A` spread over each cell pair
at density `A i j / (m i * m j)` and a phase field constant on each cell. Then:

* `integral_locate_pair` — the iterated integral of any function of the two cell
  indices is the corresponding mass-weighted double sum;
* `kernelIntegral_cellKernel` — the continuum kernel integral is `∑ᵢ∑ⱼ A i j`,
  the discrete total coupling weight, so the comparison is resource-matched;
* `fieldCorrelation_cellKernel` — the continuum phase correlation is
  `totalCorrelation`, the discrete sum, exactly;
* `cellKernel_not_sitedOn` — and such a kernel is therefore *not* sited on any
  finite set of points whenever the discrete correlation is nonzero.

## What is matched and what is not

The matched resource is **total coupling weight**: the number `∑ᵢ∑ⱼ A i j`, which
the embedding preserves. Reading that number as joules is a separate step and
needs priced hardware; `Phase9_InstalledCoupling` is where an installed energy
enters, and nothing here supplies one.

The embedding is piecewise constant. It supplies no continuous field dynamics,
no refinement limit (that is `KernelMesh.energy_tendsto`, about a different
functional) and no claim that a device with finitely many components is or is
not conscious. What it establishes is narrower and, for reading §3 of
`Phase7_Rigidity` correctly, necessary: the vanishing there is an artefact of
representing finite sites by points under an atomless measure, and not a
property of finiteness.

The genuine resource-matched separation remains the fixed-support one of §1–2 of
`Phase7_Rigidity`, which is about *which pairs an architecture has a wire for*.
`no_forced_gap_of_best_wired` is its control: an architecture whose support
contains the best-correlated distinct pair is optimal at its resource, so the
gap `rigid_gap` exhibits is forced by the missing wire and by nothing else.
-/

open MeasureTheory

namespace PhysicsOfConsciousness.FiniteRegion

open PhysicsOfConsciousness

variable {X : Type*} [MeasurableSpace X]

/-- The mass of a mesh cell. Positive mass is the hypothesis that separates this
embedding from the point-supported one. -/
noncomputable def mass (G : KernelMesh X) (μ : Measure X) (i : Fin G.size) : ℝ :=
  μ.real (G.cell i)

/-- **Integration of a cell-indexed function.** A function constant on each cell
integrates to the mass-weighted sum of its values. Measurability of `locate` is
what makes the cells measurable; no continuity or refinement is used. -/
theorem integral_locate (G : KernelMesh X) (μ : Measure X) [IsFiniteMeasure μ]
    (g : Fin G.size → ℝ) :
    ∫ x, g (G.locate x) ∂μ = ∑ i, mass G μ i * g i := by
  rw [← integral_map_of_stronglyMeasurable G.locate_measurable
      (measurable_of_countable g).stronglyMeasurable,
    integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Measure.real, Measure.map_apply G.locate_measurable (measurableSet_singleton i),
    smul_eq_mul, mass, KernelMesh.cell]

/-- The iterated form: a function of the two cell indices integrates to the
mass-weighted double sum. This is the identity the rest of the module is. -/
theorem integral_locate_pair (G : KernelMesh X) (μ : Measure X) [IsFiniteMeasure μ]
    (g : Fin G.size → Fin G.size → ℝ) :
    ∫ x, (∫ y, g (G.locate x) (G.locate y) ∂μ) ∂μ
      = ∑ i, ∑ j, mass G μ i * (mass G μ j * g i j) := by
  have hinner : ∀ x : X, (∫ y, g (G.locate x) (G.locate y) ∂μ)
      = ∑ j, mass G μ j * g (G.locate x) j := fun x => integral_locate G μ (g (G.locate x))
  simp_rw [hinner]
  rw [integral_locate G μ fun i => ∑ j, mass G μ j * g i j]
  exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _

/-- **The finite-region embedding of a coupling matrix.** Each matrix entry is
spread uniformly over its cell pair at the density that preserves its weight.
Outside the cells there is nothing to spread over: `locate` assigns every point
a cell, and a coupling that should not reach a region is embedded by setting the
corresponding entries of `A` to zero. -/
noncomputable def cellKernel (G : KernelMesh X) (μ : Measure X)
    (A : Fin G.size → Fin G.size → ℝ) : X → X → ℝ :=
  fun x y => A (G.locate x) (G.locate y) /
    (mass G μ (G.locate x) * mass G μ (G.locate y))

/-- The phase field constant on each cell. -/
def cellPhase (G : KernelMesh X) (t : Fin G.size → ℝ) : X → ℝ := fun x => t (G.locate x)

/-- A symmetric matrix embeds as a symmetric kernel. -/
theorem cellKernel_symm (G : KernelMesh X) (μ : Measure X)
    {A : Fin G.size → Fin G.size → ℝ} (hA : ∀ i j, A i j = A j i) (x y : X) :
    cellKernel G μ A x y = cellKernel G μ A y x := by
  simp only [cellKernel, hA (G.locate x) (G.locate y), mul_comm]

/-- A nonnegative matrix embeds as a nonnegative kernel, given nonnegative cell
masses. -/
theorem cellKernel_nonneg (G : KernelMesh X) (μ : Measure X)
    {A : Fin G.size → Fin G.size → ℝ} (hA : ∀ i j, 0 ≤ A i j) (x y : X) :
    0 ≤ cellKernel G μ A x y := by
  refine div_nonneg (hA _ _) (mul_nonneg ?_ ?_) <;>
    exact ENNReal.toReal_nonneg

/-- A zero diagonal embeds as a kernel vanishing on each cell's own block: no
point couples to a point of its own cell. -/
theorem cellKernel_diagonal (G : KernelMesh X) (μ : Measure X)
    {A : Fin G.size → Fin G.size → ℝ} (hA : ∀ i, A i i = 0) {x y : X}
    (h : G.locate x = G.locate y) : cellKernel G μ A x y = 0 := by
  simp only [cellKernel, h, hA (G.locate y), zero_div]

/-- **The resource is matched.** The continuum kernel integral of the embedding
is the discrete total coupling weight. The cells' masses cancel against the
density, which is what the density was chosen for.

`total_coupling_resources` counts weight, not energy; identifying it with joules
requires priced hardware and is not done here. -/
theorem kernelIntegral_cellKernel (G : KernelMesh X) (μ : Measure X) [IsFiniteMeasure μ]
    (A : Fin G.size → Fin G.size → ℝ) (hm : ∀ i, mass G μ i ≠ 0) :
    ∫ x, (∫ y, cellKernel G μ A x y ∂μ) ∂μ = total_coupling_resources A := by
  rw [show (fun x => ∫ y, cellKernel G μ A x y ∂μ)
      = fun x => ∫ y, (fun i j => A i j / (mass G μ i * mass G μ j))
        (G.locate x) (G.locate y) ∂μ from rfl,
    integral_locate_pair G μ fun i j => A i j / (mass G μ i * mass G μ j)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hi := hm i
  have hj := hm j
  field_simp

/-- **The phase correlation is matched too.** With the phase constant on each
cell, the continuum coupling energy of the embedded matrix is exactly the
discrete `totalCorrelation` of the matrix against the cell phases. -/
theorem fieldCorrelation_cellKernel (G : KernelMesh X) (μ : Measure X) [IsFiniteMeasure μ]
    (A : Fin G.size → Fin G.size → ℝ) (t : Fin G.size → ℝ) (hm : ∀ i, mass G μ i ≠ 0) :
    fieldCorrelation μ (cellPhase G t) (cellKernel G μ A) = totalCorrelation t A := by
  rw [fieldCorrelation,
    show (fun x => ∫ y, cellKernel G μ A x y * Real.cos (cellPhase G t y - cellPhase G t x) ∂μ)
      = fun x => ∫ y, (fun i j => A i j / (mass G μ i * mass G μ j) *
        Real.cos (t j - t i)) (G.locate x) (G.locate y) ∂μ from rfl,
    integral_locate_pair G μ
      fun i j => A i j / (mass G μ i * mass G μ j) * Real.cos (t j - t i)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hi := hm i
  have hj := hm j
  field_simp

/-- **The delimitation.** A finite-region reconstruction that registers any
coupling energy at all is not supported on finitely many points. The vanishing
in `fieldCorrelation_sited_eq_zero` is therefore about measure-zero support, not
about a finite number of components.

Nothing here says such a kernel is physically realizable, or that a device built
from finitely many components has one. -/
theorem cellKernel_not_sitedOn (G : KernelMesh X) (μ : Measure X) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (A : Fin G.size → Fin G.size → ℝ) (t : Fin G.size → ℝ)
    (hm : ∀ i, mass G μ i ≠ 0) (hne : totalCorrelation t A ≠ 0) (F : Finset X) :
    ¬ SitedOn F (cellKernel G μ A) := by
  intro hsited
  apply hne
  rw [← fieldCorrelation_cellKernel G μ A t hm]
  exact fieldCorrelation_sited_eq_zero μ F _ hsited (cellPhase G t)

/-! ## The control for the fixed-support gap

`rigid_gap` exhibits a strict improvement whenever the best-correlated distinct
pair is one the architecture has no wire for. The theorem below is the other
side: when the support does contain that pair, the architecture is optimal at
its resource, so nothing forces a gap. The separation in §1–2 of
`Phase7_Rigidity` is therefore about the missing wire and not about finiteness,
rigidity or discreteness as such. -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **No forced gap when the best pair is wired.** An architecture whose support
contains a pair of maximal phase correlation realizes a coupling that no valid
coupling of the same total weight beats. -/
theorem no_forced_gap_of_best_wired (S : Finset (V × V)) (R : ℝ) (hR : 0 ≤ R)
    (theta : V → ℝ) (a b : V) (hab : a ≠ b) (ha : (a, b) ∈ S) (hb : (b, a) ∈ S)
    (hmax : ∀ p : V × V, Real.cos (theta p.2 - theta p.1) ≤ Real.cos (theta b - theta a)) :
    ∃ A, RealizableIn S R A ∧
      ∀ B, is_valid_coupling B → total_coupling_resources B = R →
        totalCorrelation theta B ≤ totalCorrelation theta A := by
  obtain ⟨A, hAreal, hAval⟩ := exists_realizable_pair S R hR theta a b hab ha hb
  refine ⟨A, hAreal, fun B hBvalid hBres => ?_⟩
  rw [hAval]
  exact totalCorrelation_le_of_realizable Finset.univ R (Real.cos (theta b - theta a)) theta B
    ⟨hBvalid, hBres, fun p hp => absurd (Finset.mem_univ p) hp⟩ fun p _ => hmax p

#print axioms integral_locate
#print axioms integral_locate_pair
#print axioms kernelIntegral_cellKernel
#print axioms fieldCorrelation_cellKernel
#print axioms cellKernel_not_sitedOn
#print axioms no_forced_gap_of_best_wired

end PhysicsOfConsciousness.FiniteRegion
