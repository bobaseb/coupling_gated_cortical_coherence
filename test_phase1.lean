import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.ContinuousMap.Basic

def BoundaryField (X V : Type) [TopologicalSpace X] [TopologicalSpace V] :=
  ContinuousMap X V

def is_topologically_trivial {X V : Type} [TopologicalSpace X] [TopologicalSpace V]
  (f : BoundaryField X V) : Prop :=
  ∃ (c : V), Nonempty (ContinuousMap.Homotopy f (ContinuousMap.const X c))

def has_topological_defect {X V : Type} [TopologicalSpace X] [TopologicalSpace V]
  (f : BoundaryField X V) : Prop :=
  ¬ is_topologically_trivial f

theorem defect_inevitability
  {X D V : Type} [TopologicalSpace X] [TopologicalSpace D] [TopologicalSpace V]
  (i : ContinuousMap X D) (f : ContinuousMap D V) (d0 : D)
  (H : ContinuousMap.Homotopy (ContinuousMap.id D) (ContinuousMap.const D d0)) :
  is_topologically_trivial (f.comp i) := by
  use f d0
  let H2 : ContinuousMap.Homotopy (ContinuousMap.id D |>.comp i) (ContinuousMap.const D d0 |>.comp i) :=
    ContinuousMap.Homotopy.comp H (ContinuousMap.Homotopy.refl i)
  let H3 : ContinuousMap.Homotopy (f.comp i) (ContinuousMap.const X (f d0)) :=
    ContinuousMap.Homotopy.comp (ContinuousMap.Homotopy.refl f) H2
  exact ⟨H3⟩

theorem boundary_defect_forces_interior_vacuum_break
  {X D V : Type} [TopologicalSpace X] [TopologicalSpace D] [TopologicalSpace V]
  (i : ContinuousMap X D) (d0 : D)
  (H : ContinuousMap.Homotopy (ContinuousMap.id D) (ContinuousMap.const D d0))
  (g : BoundaryField X V) (h_defect : has_topological_defect g) :
  ¬ ∃ (f : ContinuousMap D V), f.comp i = g := by
  intro ⟨f, h_ext⟩
  have h_trivial := defect_inevitability i f d0 H
  rw [h_ext] at h_trivial
  exact h_defect h_trivial
