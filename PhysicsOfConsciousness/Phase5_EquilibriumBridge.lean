import PhysicsOfConsciousness.Phase5_GlobalSection
import PhysicsOfConsciousness.Phase4_RotatingFrame

/-!
# The bridge from the dynamics to the cover

`ThermodynamicCover` (`Phase5_GlobalSection.lean`) carries a field
`thermodynamic_equilibrium`: the assertion that the cover's phase field
minimises the reduced Kuramoto potential. Every conclusion of Derivation 5 — the
existence and uniqueness of the global section, and therefore the invariant
measure — is conditional on it, and until now it was an *instance obligation*:
each witness discharged it by exhibiting a phase field that was locked by
construction, so the configuration Derivation 5 needs was assumed rather than
reached.

`Phase4_RotatingFrame.lean` §7 produces exactly that configuration from a
dynamics. `kuramoto_tendsto_global_minimum` takes initial data within a quarter
turn and below the energy threshold `a/2` and returns a limit that is
phase-locked and minimises the potential. Nothing connected the two files: they
are siblings in the import order, `Phase5_GlobalSection` reaching Phase 4 only
through `Phase4_MacroscopicScaling`, and the potential minimiser produced by one
was never fed to the class that asks for it in the other.

This module is that connection, and it is deliberately small. It contains two
declarations:

* `kuramoto_limit_minimizes` — the convergence theorem re-stated against a
  *given* limit rather than the one it constructs internally, so that a caller
  who already has a phase field can learn that it minimises the potential. The
  proof is uniqueness of limits in a Hausdorff space and nothing else.
* `ThermodynamicCover.ofConvergentTrajectory` — the constructor. It takes a
  `LocalSectionSynchronization` whose phase field is the limit of a Kuramoto
  trajectory satisfying the §7 hypotheses, and returns a `ThermodynamicCover`
  whose `thermodynamic_equilibrium` field is discharged by that convergence.

## What this changes, stated precisely

Before: an instance of `ThermodynamicCover` had to *assert* that its phase field
sits at the potential minimum, and every witness in `Examples.lean` asserted it
of a field that was constant, or constant-up-to-`2π`, by construction.

After: an instance may instead *exhibit a trajectory* running into the phase
field from initial data that is not phase-locked, and the field is discharged
from the limit. `Examples.lean` §17 does this on three sites, where the
trajectory has no closed form.

## What this does not change

The route from the limit to minimality still runs through
`phase_locked_minimizes_potential'`: what the dynamics supplies is that the
limit is *phase-locked*, and lockedness implies minimality by a pointwise
`cos ≤ 1` argument that was already in Phase 4. The content of the bridge is
therefore that lockedness is now *derived* on a class of initial data rather
than assumed on every instance — not that a new characterisation of the minimum
has been proved.

Nor does it touch the cover's other physical hypothesis.
`LocalSectionSynchronization.section_agrees_of_phase_eq` — that synchronised
patches agree where they overlap — remains an instance obligation, and no
dynamics in this development bears on it. Derivation 5 rests on two physical
assumptions; this module converts one of them into a theorem on a class of
initial data, and leaves the other exactly where it was.

The hypotheses are also not vacuous in the other direction: they are genuinely
restrictive. Splay and twisted configurations are equilibria of the same flow,
so the arc condition `h_init` and the energy threshold `h_small` cannot be
dropped, and a cover built this way is a cover whose initial data lies in the
basin — not an arbitrary one.
-/

open CategoryTheory TopologicalSpace MeasureTheory Filter Topology
open Opposite

namespace PhysicsOfConsciousness

universe u

section Limit

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **A limit of a confined Kuramoto trajectory is a global minimiser.**

`kuramoto_tendsto_global_minimum` builds its own limit, as
`θ(0) + ∫₀^∞ θ̇`, and returns it existentially. That shape is useless to a caller
who already has a phase field in hand and needs to know it minimises the
potential — which is the situation `ThermodynamicCover` puts one in, since the
class fixes `phase` before anything is proved about it.

This is the same theorem with the limit taken as a hypothesis. The proof is
`tendsto_nhds_unique`: `ℝ` is Hausdorff, so any two limits of the same
trajectory agree, and the conclusions transport. -/
theorem kuramoto_limit_minimizes [Nonempty V]
    (sys : KuramotoSystem V) (hw : ∀ i, sys.omega i = 0)
    {a : ℝ} (ha : 0 < a) (hA : ∀ i j, a ≤ sys.A i j)
    (theta : ℝ → V → ℝ) (h_traj : is_kuramoto_trajectory sys theta)
    (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi / 2)
    (thetaInf : V → ℝ)
    (h_conv : ∀ i, Tendsto (fun t => theta t i) atTop (𝓝 (thetaInf i))) :
    is_phase_locked thetaInf ∧
      ∀ phi, kuramoto_potential_dynamic sys thetaInf ≤ kuramoto_potential_dynamic sys phi := by
  obtain ⟨psi, h_conv', h_lock, h_min, _⟩ :=
    kuramoto_tendsto_global_minimum sys hw ha hA theta h_traj h_small h_init
  have h_eq : thetaInf = psi := funext fun i => tendsto_nhds_unique (h_conv i) (h_conv' i)
  subst h_eq
  exact ⟨h_lock, h_min⟩

end Limit

section Cover

variable {X : TopCat.{u}} [MeasurableSpace X] [BorelSpace X] [TriangulatedManifold ↥X]

/-- **Derivation 5's standing hypothesis, discharged by a dynamics.**

Given a cover whose phase field is the limit of a Kuramoto trajectory that
starts inside the basin of §7 — natural frequencies identical (`hw`), coupling
uniformly positive (`ha`, `hA`), initial spread within a quarter turn
(`h_init`), initial excess below `a/2` (`h_small`) — this produces a
`ThermodynamicCover` with `thermodynamic_equilibrium` derived rather than
assumed.

The coupling matrix of the cover *is* the coupling matrix of the dynamics: the
class's `A`, `A_symm` and `A_pos` are read off `sys` and `hA` rather than chosen
independently, so the system whose equilibrium is asserted and the system whose
trajectory is run are the same system. That identification is the point of the
constructor. (It also means `A_pos` is strictly stronger here than the class
demands: `hA` gives a uniform positive lower bound `a`, not merely positivity
entry by entry, and that uniformity is what §7's estimates consume.)

**What the caller still owes.** Everything about the local sections. The
`LocalSectionSynchronization` argument carries `sync_to_section` and
`section_agrees_of_phase_eq`, and this constructor neither supplies nor weakens
them; it only requires that the `phase` field of that structure is the limit the
trajectory reaches. -/
-- The `Fintype`, `DecidableEq` and `Nonempty` witnesses on the index type are
-- explicit rather than instance-implicit on purpose: `S.I` is a projection out
-- of a structure, and instance search does not see through it at the reduced
-- transparency it runs at, so a caller would have to install local instances on
-- a projection to use the constructor at all.
@[instance_reducible]
noncomputable def ThermodynamicCover.ofConvergentTrajectory
    (S : LocalSectionSynchronization X)
    (hI : Fintype S.I) (hD : DecidableEq S.I) (hne : Nonempty S.I)
    (sys : KuramotoSystem S.I) (hw : ∀ i, sys.omega i = 0)
    {a : ℝ} (ha : 0 < a) (hA : ∀ i j, a ≤ sys.A i j)
    (theta : ℝ → S.I → ℝ) (h_traj : is_kuramoto_trajectory sys theta)
    (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi / 2)
    (h_conv : ∀ i, Tendsto (fun t => theta t i) atTop (𝓝 (S.phase i))) :
    ThermodynamicCover X where
  toLocalSectionSynchronization := S
  I_fintype := hI
  I_decidable := hD
  A := sys.A
  A_symm := sys.symm
  A_pos := fun i j => lt_of_lt_of_le ha (hA i j)
  thermodynamic_equilibrium := by
    let := hI
    let := hD
    have := hne
    exact (kuramoto_limit_minimizes sys hw ha hA theta h_traj h_small h_init S.phase h_conv).2

/-- The phase field of a cover built by `ofConvergentTrajectory` is the limit of
the trajectory, by construction — recorded so that a caller can chain the
constructor's hypothesis into `ThermodynamicCover.phase_locked` and the
Derivation 5 conclusions without unfolding the definition. -/
theorem ThermodynamicCover.ofConvergentTrajectory_phase
    (S : LocalSectionSynchronization X)
    (hI : Fintype S.I) (hD : DecidableEq S.I) (hne : Nonempty S.I)
    (sys : KuramotoSystem S.I) (hw : ∀ i, sys.omega i = 0)
    {a : ℝ} (ha : 0 < a) (hA : ∀ i j, a ≤ sys.A i j)
    (theta : ℝ → S.I → ℝ) (h_traj : is_kuramoto_trajectory sys theta)
    (h_small : 2 * potentialExcess sys (theta 0) < a)
    (h_init : ∀ i j, |theta 0 i - theta 0 j| ≤ Real.pi / 2)
    (h_conv : ∀ i, Tendsto (fun t => theta t i) atTop (𝓝 (S.phase i))) :
    (ThermodynamicCover.ofConvergentTrajectory S hI hD hne sys hw ha hA theta h_traj h_small
      h_init h_conv).phase = S.phase := rfl

end Cover

end PhysicsOfConsciousness
