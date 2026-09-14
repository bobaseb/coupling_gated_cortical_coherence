import PhysicsOfConsciousness.Phase2_MeshConvergence
import PhysicsOfConsciousness.Phase3_AgencyThermodynamics

/-!
# Phase 3 (continued): the coupling a finite agent actuates

`Phase2_MeshConvergence.lean` proves that a refining sequence of regular
triangulations sends the discrete coupling energy `discreteEnergy` to the
continuum energy `∫_S f`. `Phase3_AgencyThermodynamics.lean` proves that a
finite feedback step's entropy reduction is paid for in heat. The abstract
chain's n5 consumes an arbitrary quadrature; this module defines one whose
amplitude depends on that step through a supplied constitutive law.

This file supplies the missing relation, in the one direction that is honestly
available. `ActuatedCoupling` names a single physical arrangement in which the
executed step *sets the amplitude* of the coupling density the field carries:
the density is `gain • drive • base`, where `drive` is the order the step
actually established and `gain` converts established order into coupling
strength. Two things then follow.

* `actuated_coarseGrains` — the actuated energies converge under refinement.
  This is `mesh_refinement_convergence` applied to the actuated density, and it
  is a fact about refinement, not about the budget. It must be: the manuscript
  states, and this file does not disturb, that no theorem derives convergence
  from a heat budget.
* `actuated_limit_le_of_drive_le` — a ceiling on the order established is a
  ceiling on the continuum limit. `Chain.actuated_limit_le_budget` supplies the
  ceiling that matters, `gain * (budget / θ) * ∫_S base`, from
  `ActiveBound.entropy_budget`. This is the relation that was missing: the
  agent's heat allowance bounds how much coupling it can actuate. It is stated
  in two places because `ActiveBound` is defined in `Chain.lean`, which imports
  this file.

What is derived is therefore that the energy sequence belongs to the named
process and that the budget bounds where it lands — not that the budget causes
convergence.

**Scope.** `gain` and `base` are physical inputs: this file does not derive the
conversion from established order to coupling strength, nor the density profile,
from a microscopic model. The drive is an ensemble entropy difference; its
conversion to density is a model law, not a pathwise action, and the work of a
separate actuator implementing it is not accounted for. Both inputs are named as
fields and both are fenced by
regressions in `Examples/ActuatedCoupling.lean`. The refinement index is the
*mesh* index of `mesh : ℕ → TriangulatedManifold M` and is unrelated to
`FiniteFeedbackStep.iterate`'s learning clock; convergence over learning time
would not establish this limit.

**No kernel is produced.** The actuated object is a scalar density on `M` and
its energy quadrature, never a kernel on `M × M`. `Chain.lean` §9 proves that
coarse-graining cannot produce one, and nothing here evades that.
-/

open MeasureTheory Filter Topology

namespace PhysicsOfConsciousness

universe u v

/--
**One arrangement in which a finite agent sets a field's coupling amplitude.**

The fields divide into three groups.

* The named process — `step`, its thermal scale `temperature` and its heat
  observable `heat`. These are the same data `ActiveBound` constrains, so a
  budget for *this* process bounds *this* coupling.
* The actuation mechanism — `base`, the coupling density profile at unit drive,
  and `gain`, the nonnegative conversion from established order to coupling
  amplitude. These two are the model's physical inputs.
* The refinement data — a sequence of triangulations of `region` that are
  regular and whose cells shrink, together with the integrability side
  conditions `mesh_refinement_convergence` requires.

The vertex universe is explicit, and the finite vertex types and their orders
are recovered from the named mesh sequence through structure fields.
-/
structure ActuatedCoupling (M : Type u) (Xs S : Type*)
    [PseudoMetricSpace M] [MeasurableSpace M] [Fintype Xs] [Fintype S] where
  /-- The named feedback process whose execution sets the coupling amplitude. -/
  step : FiniteFeedbackStep Xs S
  /-- The process's thermal scale. -/
  temperature : ℝ
  /-- The process's heat observable, in its own reservoir. -/
  heat : Xs → S → S → ℝ
  /-- The coupling density profile the field carries at unit drive. A physical input. -/
  base : M → ℝ
  /-- Conversion from established order to coupling amplitude. A physical input. -/
  gain : ℝ
  gain_nonneg : 0 ≤ gain
  /-- The substrate measure. -/
  volume : MeasureTheory.Measure M
  /-- The region the triangulations cover. -/
  region : Set M
  /-- The refining sequence. Its index is spatial, not a learning clock. -/
  mesh : ℕ → TriangulatedManifold.{u, v} M
  /-- Each triangulation is finite. Carried as a field, not an instance argument:
  a space bearing a *sequence* of triangulations has no canonical one
  (`PhysicsOfConsciousness/AGENTS.md` §4). -/
  [meshFintype : ∀ n, Fintype (mesh n).V]
  /-- The bookkeeping order that selects one representative of each unordered edge. -/
  [meshOrder : ∀ n, LinearOrder (mesh n).V]
  regular : ∀ n, IsRegularTriangulation (mesh n) region
  /-- The fineness sequence, tending to zero. -/
  fineness : ℕ → ℝ
  fineness_tendsto : Tendsto fineness atTop (𝓝 0)
  fine : ∀ n u v, ∀ x ∈ (mesh n).edge_region u v, ∀ y ∈ (mesh n).edge_region u v,
    dist x y ≤ fineness n
  base_uniformContinuous : UniformContinuous base
  region_ne_top : volume region ≠ ⊤
  base_integrable : IntegrableOn base region volume

namespace ActuatedCoupling

variable {M Xs S : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
  [Fintype Xs] [Fintype S]

/-- **The order the executed step established**: the entropy its joint law lost.
This is the quantity `ActiveBound` bounds by `budget / θ`, and the quantity the
actuation mechanism converts into coupling amplitude. It carries a sign: a step
that disorders its joint law drives the coupling negative. -/
noncomputable def drive (A : ActuatedCoupling M Xs S) : ℝ :=
  shannon_entropy A.step.initial.p - shannon_entropy A.step.final.p

/-- **The coupling density the executed step actuates.** The profile is fixed;
the agent sets its amplitude. -/
noncomputable def density (A : ActuatedCoupling M Xs S) : M → ℝ :=
  fun x => A.gain * A.drive * A.base x

/-- **The actuated coupling energy at refinement level `n`.** -/
noncomputable def energy (A : ActuatedCoupling M Xs S) (n : ℕ) : ℝ :=
  letI := A.meshFintype n
  discreteEnergy (A.mesh n) A.volume A.density

/-- **The continuum coupling the arrangement converges to.** -/
noncomputable def continuumLimit (A : ActuatedCoupling M Xs S) : ℝ :=
  A.gain * A.drive * ∫ x in A.region, A.base x ∂A.volume

end ActuatedCoupling

/-- The discrete energy is linear in the density: scaling the density scales the
quadrature. This is what lets the agent's amplitude be pulled out of the
refinement limit. -/
theorem discreteEnergy_const_mul {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    (TM : TriangulatedManifold M) [Fintype TM.V]
    (μ : MeasureTheory.Measure M) (c : ℝ) (f : M → ℝ) :
    discreteEnergy TM μ (fun x => c * f x) = c * discreteEnergy TM μ f := by
  simp only [discreteEnergy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

namespace ActuatedCoupling

variable {M Xs S : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
  [Fintype Xs] [Fintype S]

/--
**The actuated energies converge under mesh refinement.**

This is `mesh_refinement_convergence` at the actuated density, with the agent's
amplitude pulled through by `discreteEnergy_const_mul`. The `ActiveBound`
premise plays no part, and is deliberately absent: convergence here is a fact
about the refinement data, exactly as the manuscript says. What the theorem adds
over the bare mesh result is *whose* energy sequence this is — the named
process's, through `density`.
-/
theorem actuated_coarseGrains (A : ActuatedCoupling M Xs S) :
    Tendsto A.energy atTop (𝓝 A.continuumLimit) := by
  let := A.meshFintype
  let := A.meshOrder
  have hbase := mesh_refinement_convergence A.volume A.base A.base_uniformContinuous
    A.region_ne_top A.base_integrable A.mesh A.regular A.fineness A.fineness_tendsto A.fine
  have hrw : A.energy = fun n => A.gain * A.drive * discreteEnergy (A.mesh n) A.volume A.base := by
    funext n
    exact discreteEnergy_const_mul (A.mesh n) A.volume _ A.base
  rw [hrw, continuumLimit]
  exact hbase.const_mul _

/--
**A bound on the established order caps the coupling actuated.**

The mechanism converts order into coupling at a nonnegative gain, so a ceiling
on the drive is a ceiling on the continuum limit. `Chain.lean` supplies the
ceiling that matters — `ActiveBound.entropy_budget`, giving `c = budget / θ` —
which is how the agent's heat allowance comes to bound its coupling. Stated here
with the ceiling abstract because `ActiveBound` is defined downstream in
`Chain.lean`, which imports this file.

It is an upper bound only: the arrangement may actuate less. It says nothing
about convergence, which `actuated_coarseGrains` supplies separately.

The hypothesis `0 ≤ ∫_S base` is the statement that the profile carries
nonnegative total coupling; without it a negative profile inverts the inequality.
-/
theorem actuated_limit_le_of_drive_le (A : ActuatedCoupling M Xs S) {c : ℝ}
    (hdrive : A.drive ≤ c) (hbase : 0 ≤ ∫ x in A.region, A.base x ∂A.volume) :
    A.continuumLimit ≤ A.gain * c * ∫ x in A.region, A.base x ∂A.volume :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdrive A.gain_nonneg) hbase

end ActuatedCoupling

end PhysicsOfConsciousness
