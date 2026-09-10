/-
  Examples/Phase2.lean — a refining sequence of triangulations of `[0,1)`

  §6, including §6.1's rate. The uniform partition into `N` half-open cells is
  the only proof that `IsRegularTriangulation`'s conditions — cells disjoint yet
  covering, every vertex anchored to each of its edges — are simultaneously
  satisfiable, and the grid then carries a `DiscreteThermodynamics` whose edge
  weights are integrals rather than choices. The scalar magnitude read off the
  stress-energy is a modelling choice, and the file exhibits two instances that
  differ only in it.
-/

import PhysicsOfConsciousness.Phase1_Primitives
import PhysicsOfConsciousness.Phase2_MeshConvergence

open MeasureTheory CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped ENNReal NNReal

namespace PhysicsOfConsciousness
namespace Examples

/-! ## 6. A refining sequence of triangulations of `[0,1)`

`Phase2_MeshConvergence.mesh_refinement_convergence` proves that the discrete energy of a
sequence of `IsRegularTriangulation`s converges to the continuous energy. That is worth
nothing if `IsRegularTriangulation` cannot be inhabited — and its conditions do pull against
each other: the cells must be pairwise **disjoint** yet **cover** the region, while every
vertex must be **anchored** to each of its edges' regions. A vertex shared by two cells can
belong to at most one of them, which is exactly why `anchored` is stated with `closure`.

This section discharges the obligation with the uniform partition of `[0,1)` into `N`
half-open cells `[i/N, (i+1)/N)` on `N+1` vertices embedded at `i/N`, and then runs the
convergence theorem on it. The witness is checked to be non-degenerate in three ways:

* cells have measure `1/N`, so they are not empty (`gridCell_measure`);
* the mesh really shrinks — `m n = 1/(n+1) → 0`, not `0` from the start;
* the approximations really move: for the tent function `x ↦ |x - ½|` the discrete energy
  is `1/2` at `N = 1` and `1/4` at `N = 2`, so the limit is not being reached by a constant
  sequence (`tent_energy_one`, `tent_energy_two`).

The triangulation is one-dimensional. The sub-section "The grid as a
`DiscreteThermodynamics`" below carries it over to the discretization structure itself, but
still in one dimension: nothing here witnesses the case of a genuinely 2- or 3-dimensional
edge region.
-/


/-- The `i`-th cell of the uniform partition of `[0,1)` into `N` pieces. -/
def gridCell (N i : ℕ) : Set ℝ := Set.Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N)

/-- Faces: sets of pairwise-consecutive vertices. -/
def gridComplex (N : ℕ) : AbstractSimplicialComplex (Fin (N + 1)) where
  faces := {s | ∀ a ∈ s, ∀ b ∈ s, (a : ℕ) ≤ (b : ℕ) + 1 ∧ (b : ℕ) ≤ (a : ℕ) + 1}
  downward_closed := fun hs hts a ha b hb => hs a (hts ha) b (hts hb)

/-- The uniform triangulation of `[0,1)` by `N` cells and `N+1` vertices. -/
@[reducible] noncomputable def gridTriangulation (N : ℕ) : TriangulatedManifold ℝ where
  V := Fin (N + 1)
  complex := gridComplex N
  embedding := fun i => (i : ℕ) / N
  edge_region := fun u v =>
    if (u : ℕ) + 1 = (v : ℕ) then gridCell N u
    else if (v : ℕ) + 1 = (u : ℕ) then gridCell N v
    else ∅
  edge_region_symm := by
    intro u v
    split_ifs <;> first | rfl | omega

@[simp] theorem gridV (N : ℕ) : (gridTriangulation N).V = Fin (N + 1) := rfl

instance instFintypeGridV (N : ℕ) : Fintype (gridTriangulation N).V :=
  (inferInstance : Fintype (Fin (N + 1)))

instance instLinearOrderGridV (N : ℕ) : LinearOrder (gridTriangulation N).V :=
  (inferInstance : LinearOrder (Fin (N + 1)))

theorem gridCell_subset (N i : ℕ) (h : i + 1 ≤ N) : gridCell N i ⊆ Set.Ico (0:ℝ) 1 := by
  have hN : (0:ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  intro x hx
  rw [gridCell, Set.mem_Ico] at hx
  rw [Set.mem_Ico]
  constructor
  · refine le_trans ?_ hx.1
    positivity
  · refine lt_of_lt_of_le hx.2 ?_
    rw [div_le_one hN]
    exact_mod_cast h

theorem gridCell_dist (N i : ℕ) {x y : ℝ} (hx : x ∈ gridCell N i) (hy : y ∈ gridCell N i) :
    dist x y ≤ 1 / N := by
  rw [gridCell, Set.mem_Ico] at hx hy
  have h := Real.dist_le_of_mem_Icc (x := x) (y := y)
    ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩
  refine h.trans (le_of_eq ?_)
  ring

@[simp] theorem grid_edge_region (N : ℕ) (u v : Fin (N + 1)) :
    (gridTriangulation N).edge_region u v =
      if (u : ℕ) + 1 = (v : ℕ) then gridCell N u
      else if (v : ℕ) + 1 = (u : ℕ) then gridCell N v else ∅ := rfl

@[simp] theorem grid_embedding (N : ℕ) (u : Fin (N + 1)) :
    (gridTriangulation N).embedding u = (u : ℕ) / N := rfl

theorem gridCell_disjoint (N : ℕ) (hN : 0 < N) {i j : ℕ} (h : i ≠ j) :
    Disjoint (gridCell N i) (gridCell N j) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [gridCell, gridCell, Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 : ((i : ℝ) + 1) / N ≤ (j : ℝ) / N := by
      refine (div_le_div_iff_of_pos_right hNR).2 ?_
      exact_mod_cast hlt
    calc min (((i : ℝ) + 1) / N) (((j : ℝ) + 1) / N) ≤ ((i : ℝ) + 1) / N := min_le_left _ _
      _ ≤ (j : ℝ) / N := h1
      _ ≤ max ((i : ℝ) / N) ((j : ℝ) / N) := le_max_right _ _
  · have h1 : ((j : ℝ) + 1) / N ≤ (i : ℝ) / N := by
      refine (div_le_div_iff_of_pos_right hNR).2 ?_
      exact_mod_cast hlt
    calc min (((i : ℝ) + 1) / N) (((j : ℝ) + 1) / N) ≤ ((j : ℝ) + 1) / N := min_le_right _ _
      _ ≤ (i : ℝ) / N := h1
      _ ≤ max ((i : ℝ) / N) ((j : ℝ) / N) := le_max_left _ _

theorem grid_edge_region_lt (N : ℕ) {u v : Fin (N + 1)} (h : u < v) :
    (gridTriangulation N).edge_region u v =
      if (u : ℕ) + 1 = (v : ℕ) then gridCell N u else ∅ := by
  rw [grid_edge_region]
  have hvu : ¬((v : ℕ) + 1 = (u : ℕ)) := by
    rw [Fin.lt_def] at h; omega
  split_ifs <;> rfl

theorem gridRegular (N : ℕ) (hN : 0 < N) :
    IsRegularTriangulation (gridTriangulation N) (Set.Ico (0:ℝ) 1) where
  measurable_region := by
    intro u v
    rw [grid_edge_region]
    split_ifs <;> simp [gridCell]
  no_self_region := by
    intro u
    rw [grid_edge_region]
    split_ifs <;> first | rfl | omega
  face_of_complex := by
    intro u v hne
    have hcond : (u : Fin (N + 1)).val + 1 = (v : Fin (N + 1)).val ∨
        (v : Fin (N + 1)).val + 1 = (u : Fin (N + 1)).val := by
      by_contra hc
      rw [not_or] at hc
      rw [grid_edge_region] at hne
      split_ifs at hne with h1 h2
      · exact hc.1 h1
      · exact hc.2 h2
      · exact Set.not_nonempty_empty hne
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
  anchored := by
    intro u v hne
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    rw [grid_edge_region] at hne ⊢
    split_ifs at hne ⊢ with h1 h2
    · rw [gridCell, closure_Ico (by intro hc; rw [div_eq_div_iff hNR.ne' hNR.ne'] at hc; linarith)]
      rw [grid_embedding, Set.mem_Icc]
      constructor
      · exact le_refl _
      · gcongr
        linarith
    · rw [gridCell, closure_Ico (by intro hc; rw [div_eq_div_iff hNR.ne' hNR.ne'] at hc; linarith)]
      rw [grid_embedding, Set.mem_Icc]
      have : ((u : Fin (N + 1)).val : ℝ) = ((v : Fin (N + 1)).val : ℝ) + 1 := by
        exact_mod_cast h2.symm
      rw [this]
      constructor
      · gcongr
        linarith
      · exact le_refl _
    · exact absurd hne Set.not_nonempty_empty
  disjoint_region := by
    intro u v u' v' huv huv' hne
    rw [grid_edge_region_lt N huv, grid_edge_region_lt N huv']
    split_ifs with h1 h2 h3
    · refine gridCell_disjoint N hN ?_
      intro hc
      refine hne ?_
      have huu : (u : Fin (N + 1)) = u' := Fin.ext hc
      have hvv : (v : Fin (N + 1)) = v' := Fin.ext (by omega)
      rw [huu, hvv]
    · exact Set.disjoint_empty _
    · exact Set.empty_disjoint _
    · exact Set.empty_disjoint _
  covers := by
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · refine Set.iUnion_subset fun u => Set.iUnion_subset fun v => ?_
      rw [grid_edge_region]
      split_ifs with h1 h2
      · exact gridCell_subset N _ (by have := (v : Fin (N + 1)).isLt; omega)
      · exact gridCell_subset N _ (by have := (u : Fin (N + 1)).isLt; omega)
      · exact Set.empty_subset _
    · rw [Set.mem_Ico] at hx
      have hxN : 0 ≤ x * N := mul_nonneg hx.1 (le_of_lt hNR)
      have h1 : (⌊x * N⌋₊ : ℝ) ≤ x * N := Nat.floor_le hxN
      have h2 : x * N < ⌊x * N⌋₊ + 1 := Nat.lt_floor_add_one _
      have hiN : ⌊x * N⌋₊ < N := by
        refine (Nat.floor_lt hxN).2 ?_
        calc x * N < 1 * N := by exact mul_lt_mul_of_pos_right hx.2 hNR
          _ = N := one_mul _
      refine Set.mem_iUnion.2 ⟨(⟨⌊x * N⌋₊, by omega⟩ : Fin (N + 1)),
        Set.mem_iUnion.2 ⟨(⟨⌊x * N⌋₊ + 1, by omega⟩ : Fin (N + 1)), ?_⟩⟩
      rw [grid_edge_region]
      split_ifs with h3 h4
      · rw [gridCell, Set.mem_Ico]
        refine ⟨(div_le_iff₀ hNR).2 ?_, (lt_div_iff₀ hNR).2 ?_⟩
        · exact h1
        · exact h2
      · simp at h3
      · simp at h3

theorem grid_fine (N : ℕ) (u v : Fin (N + 1)) {x y : ℝ}
    (hx : x ∈ (gridTriangulation N).edge_region u v)
    (hy : y ∈ (gridTriangulation N).edge_region u v) : dist x y ≤ 1 / N := by
  rw [grid_edge_region] at hx hy
  split_ifs at hx hy with h1 h2
  · exact gridCell_dist N _ hx hy
  · exact gridCell_dist N _ hx hy
  · exact absurd hx (Set.notMem_empty x)

theorem grid_mesh_refinement (f : ℝ → ℝ) (hf : UniformContinuous f) :
    Tendsto (fun n : ℕ => discreteEnergy (gridTriangulation (n + 1)) volume f) atTop
      (𝓝 (∫ x in Set.Ico (0:ℝ) 1, f x)) := by
  have hint : IntegrableOn f (Set.Ico (0:ℝ) 1) volume :=
    (hf.continuous.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  refine mesh_refinement_convergence volume f hf (by simp) hint
    (fun n => gridTriangulation (n + 1)) (fun n => gridRegular (n + 1) n.succ_pos)
    (fun n => 1 / ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat ?_
  intro n u v x hx y hy
  have h := grid_fine (n + 1) u v hx hy
  push_cast at h
  exact h

/-- Cells are non-degenerate: each has measure `1/N`. -/
theorem gridCell_measure (N : ℕ) (hN : 0 < N) (i : ℕ) :
    volume.real (gridCell N i) = 1 / N := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [gridCell, Real.volume_real_Ico_of_le (by gcongr; linarith)]
  field_simp
  ring

/-- The tent function `x ↦ |x - ½|`, Lipschitz hence uniformly continuous. -/
theorem tent_uniformContinuous : UniformContinuous (fun x : ℝ => |x - 1/2|) := by
  have h : (fun x : ℝ => |x - 1/2|) = fun x : ℝ => dist x (1/2) := by
    funext x; rw [Real.dist_eq]
  rw [h]
  exact (LipschitzWith.dist_left (1/2 : ℝ)).uniformContinuous

example : Tendsto
    (fun n : ℕ => discreteEnergy (gridTriangulation (n + 1)) volume (fun x => |x - 1/2|))
    atTop (𝓝 (∫ x in Set.Ico (0:ℝ) 1, |x - 1/2|)) :=
  grid_mesh_refinement _ tent_uniformContinuous

theorem tent_energy_one :
    discreteEnergy (gridTriangulation 1) volume (fun x => |x - 1/2|) = 1/2 := by
  simp [discreteEnergy, Fin.sum_univ_two, grid_edge_region, grid_embedding, gridCell]
  norm_num

theorem tent_energy_two :
    discreteEnergy (gridTriangulation 2) volume (fun x => |x - 1/2|) = 1/4 := by
  simp [discreteEnergy, Fin.sum_univ_three, grid_edge_region, grid_embedding, gridCell]
  norm_num

/-- The approximations genuinely move: refining the mesh changes the answer, so the
convergence above is not the trivial convergence of a constant sequence. -/
example : discreteEnergy (gridTriangulation 1) volume (fun x => |x - 1/2|)
    ≠ discreteEnergy (gridTriangulation 2) volume (fun x => |x - 1/2|) := by
  rw [tent_energy_one, tent_energy_two]
  norm_num

/-! ### The grid as a `DiscreteThermodynamics`

`DiscreteThermodynamics` now carries its own `IsRegularTriangulation` field, so its edge
weights are integrals over a geometrically constrained family of regions rather than over
arbitrary sets. That strengthening is worth nothing unless something satisfies it, and
until now the structure had **no instance anywhere in the development** — every theorem
about `edge_weight` was conditional on a structure not shown to be realizable.

This section supplies one, on the same uniform grid, and checks it is not degenerate:

* each consecutive edge carries weight exactly `1/N` (`gridThermo_edge_weight`), so the
  weights are positive and genuinely track the mesh;
* the weights sum to the total energy of the covered region — `½ ∑ᵤ ∑ᵥ w(u,v) = 1` for every
  `N` (`gridThermo_total`), which is `total_weight_eq_setIntegral` on this instance and is
  exactly what the everywhere-empty triangulation would violate;
* the scalar magnitude is a *choice*, and it matters: `gridThermo'` differs from
  `gridThermo` in that field alone, the partition theorem holds for both, and the coupling
  matrices differ on every edge (`gridThermo_magnitude_matters`). This is open item **O7**,
  decided and recorded on the field itself.

Two limitations, stated so they are not read as more than they are. The scalar magnitude is
`|T(∂,∂)|` on the one-dimensional tangent space, so it *is* a function of the stress-energy
tensor, but the tensor exhibited (`unitTensor`) is constant; nothing here witnesses a
spatially varying stress-energy. And the substrate is `ℝ` as a manifold over itself, so the
edge regions are intervals, not the 2- or 3-dimensional cells of the intended application.
-/

/-- The constant unit bilinear form on the tangent spaces of `ℝ`, used as a concrete
stress-energy tensor. -/
noncomputable def unitTensor : CovariantTensor2 (modelWithCornersSelf ℝ ℝ) ℝ :=
  fun _ => ContinuousLinearMap.mul ℝ ℝ

@[simp] theorem unitTensor_apply (x a b : ℝ) : unitTensor x a b = a * b := rfl

/-- The uniform grid, discretizing the constant unit stress-energy on `[0,1)`.

The triangulation and the model are explicit arguments of `DiscreteThermodynamics` — see
its doc-string — which is what lets a *sequence* of triangulations of the same space each
carry their own thermodynamics. -/
noncomputable def gridThermo (N : ℕ) (hN : 0 < N) :
    DiscreteThermodynamics (gridTriangulation N) (modelWithCornersSelf ℝ ℝ) where
  volume_measure := volume
  scalar_magnitude := fun T x => |T x (1:ℝ) (1:ℝ)|
  magnitude_nonneg := fun _ _ => abs_nonneg _
  region := Set.Ico 0 1
  regular := gridRegular N hN

@[simp] theorem gridThermo_magnitude (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (gridThermo N hN).scalar_magnitude unitTensor x = 1 := by
  show |unitTensor x (1:ℝ) (1:ℝ)| = 1
  rw [unitTensor_apply]
  norm_num

@[simp] theorem gridThermo_volume (N : ℕ) (hN : 0 < N) :
    (gridThermo N hN).volume_measure = volume := rfl

@[simp] theorem gridThermo_region (N : ℕ) (hN : 0 < N) :
    (gridThermo N hN).region = Set.Ico 0 1 := rfl

/-- Consecutive vertices are coupled with weight `1/N`: the weights are positive, and they
shrink with the mesh. -/
theorem gridThermo_edge_weight (N : ℕ) (hN : 0 < N) (u v : Fin (N + 1))
    (h : (u : ℕ) + 1 = (v : ℕ)) :
    DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor u v = 1 / N := by
  have hreg : (gridTriangulation N).edge_region u v = gridCell N u := by
    rw [grid_edge_region]
    simp [h]
  rw [DiscreteThermodynamics.edge_weight]
  simp only [gridThermo_magnitude, gridThermo_volume, hreg]
  rw [setIntegral_const, smul_eq_mul, mul_one]
  exact gridCell_measure N hN u

/-- **The coupling weights partition the energy.** `total_weight_eq_setIntegral` on this
instance: the whole coupling matrix sums to the energy of `[0,1)`, which is `1`, for every
`N`. Nothing is double counted by the overlapping double sum and nothing is left uncovered.
-/
theorem gridThermo_total (N : ℕ) (hN : 0 < N) :
    (1 / 2 : ℝ) * ∑ u, ∑ v,
        DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor u v = 1 := by
  have hfun : (gridThermo N hN).scalar_magnitude unitTensor = fun _ : ℝ => (1:ℝ) := by
    funext x
    exact gridThermo_magnitude N hN x
  have hint : IntegrableOn ((gridThermo N hN).scalar_magnitude unitTensor)
      (gridThermo N hN).region (gridThermo N hN).volume_measure := by
    rw [hfun, gridThermo_volume, gridThermo_region]
    exact integrableOn_const (by simp)
  rw [DiscreteThermodynamics.total_weight_eq_setIntegral (gridThermo N hN) unitTensor hint]
  simp only [gridThermo_magnitude, gridThermo_volume, gridThermo_region]
  rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ico_of_le (by norm_num)]
  norm_num

/-! #### The scalar magnitude is a modelling choice, and it is load-bearing

Open item **O7** asked whether `DiscreteThermodynamics.scalar_magnitude` — the scalar the
discretization reads off a stress-energy tensor, constrained only to be non-negative —
should be constrained further or marked as modelling. The decision, recorded on the field
itself in `Phase2_SimplicialBridge.lean`, is to keep it a choice. These three declarations
are the half of that decision that is a theorem rather than a comment.

`gridThermo'` is the *same* grid, the same tensor, the same regions and the same regularity
proof as `gridThermo`, differing in one field: it reads twice the magnitude. Both are legal
instances, and `gridThermo'_total` shows the structure theorem survives the change —
`total_weight_eq_setIntegral` holds for both, with the energy it partitions moving from `1`
to `2`. `gridThermo_magnitude_matters` shows the coupling matrix does not: the two induced
Kuramoto systems have different weights on every edge. So the choice is a physical input
with numerical consequences, not a formality — which is why it is marked and not removed.
-/

/-- A second thermodynamics on the same grid, reading twice the magnitude. Nothing else
differs, including the regularity proof. -/
noncomputable def gridThermo' (N : ℕ) (hN : 0 < N) :
    DiscreteThermodynamics (gridTriangulation N) (modelWithCornersSelf ℝ ℝ) where
  volume_measure := volume
  scalar_magnitude := fun T x => 2 * |T x (1:ℝ) (1:ℝ)|
  magnitude_nonneg := fun _ _ => by positivity
  region := Set.Ico 0 1
  regular := gridRegular N hN

@[simp] theorem gridThermo'_magnitude (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (gridThermo' N hN).scalar_magnitude unitTensor x = 2 := by
  show 2 * |unitTensor x (1:ℝ) (1:ℝ)| = 2
  rw [unitTensor_apply]
  norm_num

@[simp] theorem gridThermo'_volume (N : ℕ) (hN : 0 < N) :
    (gridThermo' N hN).volume_measure = volume := rfl

@[simp] theorem gridThermo'_region (N : ℕ) (hN : 0 < N) :
    (gridThermo' N hN).region = Set.Ico 0 1 := rfl

theorem gridThermo'_edge_weight (N : ℕ) (hN : 0 < N) (u v : Fin (N + 1))
    (h : (u : ℕ) + 1 = (v : ℕ)) :
    DiscreteThermodynamics.edge_weight (gridThermo' N hN) unitTensor u v = 2 / N := by
  have hreg : (gridTriangulation N).edge_region u v = gridCell N u := by
    rw [grid_edge_region]
    simp [h]
  rw [DiscreteThermodynamics.edge_weight]
  simp only [gridThermo'_magnitude, gridThermo'_volume, hreg]
  rw [setIntegral_const, smul_eq_mul, gridCell_measure N hN u]
  ring

/-- **The structure theorem is stable under the choice.** `total_weight_eq_setIntegral`
holds for the doubled magnitude too; what moves is the energy it partitions, from `1` to
`2`. Nothing about symmetry, the vanishing diagonal, or the coupling graph depends on which
scalar invariant is read. -/
theorem gridThermo'_total (N : ℕ) (hN : 0 < N) :
    (1 / 2 : ℝ) * ∑ u, ∑ v,
        DiscreteThermodynamics.edge_weight (gridThermo' N hN) unitTensor u v = 2 := by
  have hfun : (gridThermo' N hN).scalar_magnitude unitTensor = fun _ : ℝ => (2:ℝ) := by
    funext x
    exact gridThermo'_magnitude N hN x
  have hint : IntegrableOn ((gridThermo' N hN).scalar_magnitude unitTensor)
      (gridThermo' N hN).region (gridThermo' N hN).volume_measure := by
    rw [hfun, gridThermo'_volume, gridThermo'_region]
    exact integrableOn_const (by simp)
  rw [DiscreteThermodynamics.total_weight_eq_setIntegral (gridThermo' N hN) unitTensor hint]
  simp only [gridThermo'_magnitude, gridThermo'_volume, gridThermo'_region]
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ico_of_le (by norm_num)]
  norm_num

/-- **…and the numbers are not.** Two legal instances over the same triangulation, the same
tensor and the same regions give different coupling matrices. The scalar magnitude is
therefore a physical input the framework does not fix, and the induced Kuramoto system
depends on it — the exact content of the `[MODELLING]` marking on the field. -/
theorem gridThermo_magnitude_matters (N : ℕ) (hN : 0 < N) :
    DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor
        ⟨0, by omega⟩ ⟨1, by omega⟩
      ≠ DiscreteThermodynamics.edge_weight (gridThermo' N hN) unitTensor
        ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [gridThermo_edge_weight N hN _ _ rfl, gridThermo'_edge_weight N hN _ _ rfl]
  intro hc
  rw [div_eq_div_iff (by linarith) (by linarith)] at hc
  linarith

/-- A nonzero weight forces an actual face of the complex: on the grid, `face_of_weight_ne_zero`
says the coupling graph is the path graph the triangulation describes and nothing more. -/
example (N : ℕ) (hN : 0 < N) (u v : Fin (N + 1))
    (h : DiscreteThermodynamics.edge_weight (gridThermo N hN) unitTensor u v ≠ 0) :
    ({u, v} : Finset (Fin (N + 1))) ∈ (gridTriangulation N).complex.faces :=
  DiscreteThermodynamics.face_of_weight_ne_zero (gridThermo N hN) unitTensor h


/-! ### 6.1 The rate, and what the abstract mesh cannot state

`Phase2_MeshConvergence` proves that the discrete energy *converges* to the
continuous energy; it proves no rate, and its header says why. The bound there is
`ε·μ(support)` with `ε` the modulus of continuity, which for a Lipschitz
integrand gives `O(1/N)` — while `simulations/mesh_refinement.py` measures
`O(1/N²)` on the same problem. Open item **O16** recorded the gap between the two.

The recorded obstacle was the wrong one. O16 said the missing piece was a
midpoint error term "`taylor_mean_remainder_lagrange` per cell". It is not:
Mathlib carries the **composite** trapezoidal bound already
(`trapezoidal_error_le_of_c2`, `Mathlib/MeasureTheory/Integral/IntervalIntegral/
TrapezoidalRule.lean`), so what was actually missing was the identification of
this development's `discreteEnergy` with Mathlib's `trapezoidal_integral`. That
identification is `grid_discreteEnergy_eq_trapezoidal`, and it is where all the
work below is: the double sum over `Fin (N+1) × Fin (N+1)` of edge-region
measures has to be collapsed to a sum over `Finset.range`.

With it, `grid_energy_error_le` gives `ζ/(12N²)` for a `C²` integrand, which is
the rate the simulation reports.

**The scope point, which O16 asked to be recorded either way.** This is a theorem
about *this grid*, not about `Mesh`. It cannot be stated at the level of
`Phase2_MeshConvergence`, because an abstract `Mesh` lives over a
`PseudoMetricSpace` on which no second derivative exists — there is nothing for
`ζ` to bound. Second-order accuracy is a property of a quadrature rule on an
interval, not of a partition of a metric space, and the development's generality
is what puts it out of reach in general rather than any missing Mathlib result.

One thing found in passing and worth recording: Mathlib's
`trapezoidal_error_le_of_c2` asks for the second-derivative bound at **every**
real `x`, not merely on `[[a,b]]`. Outside the interval the `derivWithin` is `0`
for lack of unique differentiability, so the hypothesis is still discharged
(`sq_iteratedDerivWithin_bound` does it), but the case split is an artefact of
the statement rather than of the mathematics.
-/

section MeshRate
open scoped Interval

theorem edge_measure_split (N : ℕ) (hN : 0 < N) (a b : ℕ) :
    volume.real (if a + 1 = b then gridCell N a else if b + 1 = a then gridCell N b else ∅)
      = (if a + 1 = b then 1 / (N:ℝ) else 0) + (if b + 1 = a then 1 / (N:ℝ) else 0) := by
  split_ifs with h1 h2
  · omega
  · rw [gridCell_measure N hN]; ring
  · rw [gridCell_measure N hN]; ring
  · simp

theorem sum_edge_measure (N : ℕ) {a : ℕ} (ha : a < N + 1) :
    ∑ b ∈ Finset.range (N + 1),
        ((if a + 1 = b then 1 / (N:ℝ) else 0) + (if b + 1 = a then 1 / (N:ℝ) else 0))
      = (if a < N then 1 / (N:ℝ) else 0) + (if 0 < a then 1 / (N:ℝ) else 0) := by
  rw [Finset.sum_add_distrib]
  have e1 : (∑ b ∈ Finset.range (N + 1), if a + 1 = b then 1 / (N:ℝ) else 0)
      = if a < N then 1 / (N:ℝ) else 0 := by
    have h : (∑ b ∈ Finset.range (N + 1), if a + 1 = b then 1 / (N:ℝ) else 0)
        = ∑ b ∈ Finset.range (N + 1), if b = a + 1 then 1 / (N:ℝ) else 0 :=
      Finset.sum_congr rfl fun b _ => if_congr eq_comm rfl rfl
    rw [h, Finset.sum_ite_eq' (Finset.range (N + 1)) (a + 1) (fun _ => 1 / (N:ℝ))]
    exact if_congr (by simp only [Finset.mem_range]; omega) rfl rfl
  have e2 : (∑ b ∈ Finset.range (N + 1), if b + 1 = a then 1 / (N:ℝ) else 0)
      = if 0 < a then 1 / (N:ℝ) else 0 := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp
    · have h : (∑ b ∈ Finset.range (N + 1), if b + 1 = a then 1 / (N:ℝ) else 0)
          = ∑ b ∈ Finset.range (N + 1), if b = a - 1 then 1 / (N:ℝ) else 0 :=
        Finset.sum_congr rfl fun b _ => if_congr (by omega) rfl rfl
      rw [h, Finset.sum_ite_eq' (Finset.range (N + 1)) (a - 1) (fun _ => 1 / (N:ℝ))]
      exact if_congr (by simp only [Finset.mem_range]; omega) rfl rfl
  rw [e1, e2]

/-- The discrete energy of the grid, as a sum over `range`. -/
theorem grid_discreteEnergy_eq_range (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) :
    discreteEnergy (gridTriangulation N) volume f
      = (1 / 2 : ℝ) * ∑ a ∈ Finset.range (N + 1),
          f ((a : ℝ) / N) * ((if a < N then 1 / (N:ℝ) else 0) + (if 0 < a then 1 / (N:ℝ) else 0)) := by
  have hE : discreteEnergy (gridTriangulation N) volume f
      = (1 / 2 : ℝ) * ∑ u : Fin (N + 1), ∑ v : Fin (N + 1),
          volume.real ((gridTriangulation N).edge_region u v) * f (((u : ℕ) : ℝ) / N) := rfl
  rw [hE]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun a => f ((a : ℝ) / N) *
    ((if a < N then 1 / (N:ℝ) else 0) + (if 0 < a then 1 / (N:ℝ) else 0))) (N + 1)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hinner : ∀ v : Fin (N + 1),
      volume.real ((gridTriangulation N).edge_region u v) * f (((u : ℕ) : ℝ) / N)
        = ((if (u:ℕ) + 1 = (v:ℕ) then 1 / (N:ℝ) else 0)
            + (if (v:ℕ) + 1 = (u:ℕ) then 1 / (N:ℝ) else 0)) * f (((u:ℕ) : ℝ) / N) := by
    intro v
    rw [grid_edge_region, edge_measure_split N hN]
  rw [Finset.sum_congr rfl (fun v _ => hinner v), ← Finset.sum_mul]
  rw [Fin.sum_univ_eq_sum_range (fun b =>
    (if (u:ℕ) + 1 = b then 1 / (N:ℝ) else 0) + (if b + 1 = (u:ℕ) then 1 / (N:ℝ) else 0)) (N + 1)]
  rw [sum_edge_measure N u.isLt]
  ring


/-- **The grid's discrete energy is Mathlib's composite trapezoidal rule** on `[0,1]`
with `N` cells. -/
theorem grid_discreteEnergy_eq_trapezoidal (m : ℕ) (f : ℝ → ℝ) :
    discreteEnergy (gridTriangulation (m + 1)) volume f
      = trapezoidal_integral f (m + 1) 0 1 := by
  have hNR : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [grid_discreteEnergy_eq_range (m + 1) (Nat.succ_pos m) f, trapezoidal_integral]
  have hsplit : ∀ a ∈ Finset.range (m + 2),
      f ((a : ℝ) / ((m : ℕ) + 1 : ℕ))
          * ((if a < m + 1 then 1 / (((m : ℕ) + 1 : ℕ) : ℝ) else 0)
             + (if 0 < a then 1 / (((m : ℕ) + 1 : ℕ) : ℝ) else 0))
        = (f ((a : ℝ) / ((m : ℝ) + 1)) * (if a < m + 1 then 1 / ((m : ℝ) + 1) else 0))
          + (f ((a : ℝ) / ((m : ℝ) + 1)) * (if 0 < a then 1 / ((m : ℝ) + 1) else 0)) := by
    intro a _
    push_cast
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hT : (∑ a ∈ Finset.range (m + 2),
        f ((a : ℝ) / ((m : ℝ) + 1)) * (if a < m + 1 then 1 / ((m : ℝ) + 1) else 0))
      = ∑ a ∈ Finset.range (m + 1), f ((a : ℝ) / ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
    rw [Finset.sum_range_succ]
    rw [ite_eq_right (lt_irrefl _), mul_zero, add_zero]
    exact Finset.sum_congr rfl fun a ha => by
      rw [ite_eq_left (Finset.mem_range.mp ha)]; ring
  have hU : (∑ a ∈ Finset.range (m + 2),
        f ((a : ℝ) / ((m : ℝ) + 1)) * (if 0 < a then 1 / ((m : ℝ) + 1) else 0))
      = ∑ i ∈ Finset.range (m + 1), f (((i : ℝ) + 1) / ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
    rw [Finset.sum_range_succ']
    rw [ite_eq_right (lt_irrefl 0), mul_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ => by
      rw [ite_eq_left (Nat.succ_pos i)]; push_cast; ring
  rw [hT, hU, Finset.sum_range_succ' (fun a => f ((a : ℝ) / ((m : ℝ) + 1)) / ((m : ℝ) + 1)) m,
    Finset.sum_range_succ (fun i => f (((i : ℝ) + 1) / ((m : ℝ) + 1)) / ((m : ℝ) + 1)) m]
  have hz : ((0 : ℕ) : ℝ) / ((m : ℝ) + 1) = 0 := by norm_num
  have ho : (((m : ℝ) + 1)) / ((m : ℝ) + 1) = 1 := div_self hNR
  have hshift : ∀ i ∈ Finset.range m,
      f ((((i : ℕ) + 1 : ℕ) : ℝ) / ((m : ℝ) + 1)) / ((m : ℝ) + 1)
        = f (((i : ℝ) + 1) / ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
    intro i _; push_cast; ring
  rw [Finset.sum_congr rfl hshift, hz, ho]
  have hsum : ∀ k ∈ Finset.range m,
      f (0 + ((k : ℝ) + 1) * (1 - 0) / (((m + 1 : ℕ)) : ℝ))
        = f (((k : ℝ) + 1) / ((m : ℝ) + 1)) := by
    intro k _
    congr 1
    push_cast
    ring
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hsum, ← Finset.sum_div]
  push_cast
  field_simp
  ring


/-- **The O(1/N²) rate, on the concrete witness.** For a `C²` integrand with second
derivative bounded by `ζ`, the grid's discrete energy differs from the continuous
energy by at most `ζ/(12N²)`. -/
theorem grid_energy_error_le {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f [[(0:ℝ), 1]])
    {ζ : ℝ} (hζ : ∀ x, |iteratedDerivWithin 2 f [[(0:ℝ), 1]] x| ≤ ζ)
    {N : ℕ} (hN : 0 < N) :
    |discreteEnergy (gridTriangulation N) volume f - ∫ x in Set.Ico (0:ℝ) 1, f x|
      ≤ ζ / (12 * (N:ℝ) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have h := trapezoidal_error_le_of_c2 (a := 0) (b := 1) hf hζ (Nat.succ_pos m)
  rw [trapezoidal_error] at h
  have hint : (∫ x in (0:ℝ)..1, f x) = ∫ x in Set.Ico (0:ℝ) 1, f x := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioc]
  rw [grid_discreteEnergy_eq_trapezoidal m f, ← hint]
  refine h.trans (le_of_eq ?_)
  norm_num


/-- The identity, cross-checked against a value computed by hand: `tent_energy_two`
says the discrete energy of the tent function on two cells is `1/4`, and the
trapezoidal rule must therefore give `1/4` too. -/
example : trapezoidal_integral (fun x => |x - 1/2|) 2 0 1 = 1/4 :=
  (grid_discreteEnergy_eq_trapezoidal 1 _).symm.trans tent_energy_two

/-- The second derivative of `y ↦ y²`, bounded on all of `ℝ`, which is what
Mathlib's trapezoidal bound asks for. Outside `[0,1]` the set has no unique
differentiability, so the iterated `derivWithin` is `0` there. -/
theorem sq_iteratedDerivWithin_bound (x : ℝ) :
    |iteratedDerivWithin 2 (fun y : ℝ => y ^ 2) [[(0:ℝ), 1]] x| ≤ 2 := by
  by_cases hx : x ∈ [[(0:ℝ), 1]]
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
      (by fun_prop) hx]
    have h2 : iteratedDeriv 2 (fun y : ℝ => y ^ 2) x = 2 := by simp
    rw [h2]; norm_num
  · have hnu : ¬ UniqueDiffWithinAt ℝ [[(0:ℝ), 1]] x := by
      intro h
      exact hx (by simpa [isCompact_uIcc.isClosed.closure_eq] using h.mem_closure)
    rw [iteratedDerivWithin_succ, derivWithin_zero_of_not_uniqueDiffWithinAt hnu]
    norm_num

/-- **A non-degenerate instance of the rate.** For `y ↦ y²` the bound is
`1/(6N²)`, and the integrand is not one the trapezoidal rule integrates exactly,
so the error is genuinely `Θ(1/N²)` rather than `0`. -/
theorem grid_energy_error_sq {N : ℕ} (hN : 0 < N) :
    |discreteEnergy (gridTriangulation N) volume (fun y => y ^ 2)
        - ∫ x in Set.Ico (0:ℝ) 1, x ^ 2| ≤ 1 / (6 * (N:ℝ) ^ 2) := by
  have h := grid_energy_error_le (f := fun y : ℝ => y ^ 2)
    (by fun_prop) sq_iteratedDerivWithin_bound hN
  refine h.trans (le_of_eq ?_)
  ring

/-- The constant case, where the trapezoidal rule is exact: the bound is `0`, so
the grid's discrete energy of a constant is *exactly* its integral. This also
checks the normalisation of the identity. -/
theorem grid_energy_const (c : ℝ) {N : ℕ} (hN : 0 < N) :
    discreteEnergy (gridTriangulation N) volume (fun _ => c)
      = ∫ _x in Set.Ico (0:ℝ) 1, c := by
  have hζ : ∀ x, |iteratedDerivWithin 2 (fun _ : ℝ => c) [[(0:ℝ), 1]] x| ≤ 0 := by
    intro x; rw [iteratedDerivWithin_const]; norm_num
  have h := grid_energy_error_le (f := fun _ : ℝ => c) contDiffOn_const hζ hN
  rw [zero_div] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))


/-- The integral the grid is approximating, for `y ↦ y²`. -/
theorem integral_sq_Ico : (∫ x in Set.Ico (0:ℝ) 1, x ^ 2) = 1 / 3 := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_pow]
  norm_num

/-- **The bound is attained**, at `N = 1`: one cell, `|1/2 − 1/3| = 1/6`, which is
exactly `ζ/(12N²)` for `ζ = 2`. So `grid_energy_error_sq` is not a vacuous
over-estimate, and the constant cannot be improved. -/
theorem grid_energy_error_sq_one :
    |discreteEnergy (gridTriangulation 1) volume (fun y => y ^ 2)
        - ∫ x in Set.Ico (0:ℝ) 1, x ^ 2| = 1 / 6 := by
  rw [grid_discreteEnergy_eq_trapezoidal 0 _, integral_sq_Ico, trapezoidal_integral]
  norm_num

end MeshRate

end Examples
end PhysicsOfConsciousness
