/-
  Examples.lean — Non-vacuity witnesses

  Every physical postulate in this development is now carried as a *class field*
  rather than a standalone `axiom` (see `Axioms.lean` §5 for why: the standalone
  formulations were inconsistent). That change is only an improvement if the
  classes can actually be inhabited — an uninhabitable class makes every theorem
  about it vacuously true, which is no better than an inconsistent axiom.

  These files discharge that obligation for the finite-state parts of the theory
  by exhibiting concrete instances. This file is their index and imports them
  all; the witness files under `Examples/` are named for their phase or model.
  The section numbers below are stable and are the
  ones the supplement cites, so the map from a section to its file is here:

    `Examples/Bit.lean`     §1 -- the one-bit eraser and its bath
    `Examples/Cortex.lean`  §4 -- the three-site cortex and its first cover
    `Examples/Phase1.lean`  §3, §11, §19
    `Examples/Phase2.lean`  §6
    `Examples/Phase3.lean`  §2, §18
    `Examples/AgencyControl.lean` -- finite budgeted policy selection
    `Examples/PolicyLearning.lean` -- thermal policy adaptation and its costs
    `Examples/ObservationalLearning.lean` -- learning an unknown task from outcomes
    `Examples/ContinuingAgent.lean` -- sequenced episodes and a finite work allowance
    `Examples/RegisterBudget.lean` -- one register's operations and its heat ledger
    `Examples/ActuatedCoupling.lean` -- a feedback step's scalar coupling amplitude
    `Examples/MicroscopicCoupling.lean` -- a thermal switch's installed spatial mode
    `Examples/Phase4.lean`  §7, §15, §16, §17
    `Examples/Phase5.lean`  §13, §14, §17.1, §20 (overlap agreement)
    `Examples/Phase6.lean`  §10
    `Examples/Phase7.lean`  §8
    `Examples/Phase8.lean`  §5, §9, §12, §20 (continuum operator)

  **Coverage — every class carrying a physical postulate is now inhabited.**
    ✓ `StatisticalMechanics` — a one-bit erasure model with a genuine bath.
    ✓ `StructuralResonance`  — a perfectly-resonant system (KL = 0), and a detuned
      one with KL = log 2 > 0 that attains the bound with equality (§2).
    ✓ `ActionPrinciples`     — a scalar field on a one-point spacetime.
    ✓ `PredictiveDissipation` — two systems over one correlated two-bit law (§18):
      a frozen signal, whose memory is entirely predictive and which is permitted
      to dissipate nothing, and a scrambled one, whose memory predicts nothing and
      which is *forced* to dissipate its whole mutual information.
    ✓ `FiniteControlProblem` — the lamp task compares all deterministic bit
      policies on common channels and initial law. Its unique feasible optimum
      improves reward, while equal-cost failure and an infeasible stronger
      policy fence the role of the goal and the whole-update heat budget.
    ✓ `LocalSectionSynchronization` / `ThermodynamicCover` — two overlapping
      patches on a three-site substrate, with sections of the sheafified
      probability presheaf built from a phase-dependent invariant measure (§4);
      a second cover in §13 whose phase field is not constant and whose patches
      carry genuinely different local densities; and a third in §14 whose two
      patches are built from independently chosen mass profiles, so that the
      glued section is none of the data the instance carries.

  §5 additionally exercises the Phase 8 gradient-flow link on a two-site
  substrate: counting measure, a non-zero gradient, and an explicit non-constant
  flow along which entropy production decays as `e^{-2t}`.

  §6 witnesses `IsRegularTriangulation` (`Phase2_MeshConvergence`) with the uniform
  partition of `[0,1)`, and runs `mesh_refinement_convergence` on it. Its
  disjoint-yet-covering-yet-anchored conditions are in tension, so an instance is
  the only proof they are simultaneously satisfiable.

  §7 witnesses the rotating-frame reduction (`Phase4_RotatingFrame`) on a
  two-oscillator system with a common natural frequency, running
  `rotating_frame_chain` with every hypothesis discharged, and exhibits a system
  for which the full Kuramoto potential provably has no minimum.

  §8 witnesses both halves of `Phase7_Rigidity`: a three-site substrate wired to
  the one maximally anti-correlated pair, where `is_strictly_suboptimal` is
  *derived* from the wiring rather than assumed; and, on the real line, a
  single-site architecture carrying arbitrarily large weight yet registering
  exactly zero field correlation against a unit patch that registers one.

  §10 witnesses `ReflexiveBoundary` / `PredictiveModel` (`Phase6_ReflexiveTopology`)
  and the three ambient instances `reflexive_topology_implies_self` assumes about
  `GlobalSection`. It first pierces the sheafification: `massEquivOn` proves that over
  *any* open of the three-site cortex the sections of the probability sheaf are exactly
  the mass profiles on that open, read as densities against counting measure;
  `massEquiv` is the case `U = ⊤`. The metric is then the
  uniform distance between their densities, complete, and the self-prediction map is
  built through the one-site avatar — `avatarRead` then `avatarReadout`, composed by
  `ReflexiveBoundary.predict` — so it contracts by exactly one half of what the avatar
  sees (`cortexPredict_dist`) without being constant (`cortexPredict_not_const`), with a
  unique fixed point (`cortexPredict_fixed_unique`). The contraction constant is read off
  `K` and `D` rather than stipulated: `cortexResonanceRate` places the witness at `K = 3`,
  `D = 1`, `τ = 2 log 2`, and `cortexHasSelf` comes out of `K > critical_coupling 1`,
  while `cortexSubcritical_not_contracting` records that at `K = 1` the same map has no
  Banach argument at all. The earlier 0/1 metric is kept as `gsDiscreteMetric`, and
  `contracting_implies_const` records why it was empty. What is still not established is
  that any field dynamics produces this particular read-out, or that this substrate's
  coupling is `3`: the parameters are a choice of units for the witness.

  §13 answers open item O5 with both halves of an answer: a `ThermodynamicCover`
  whose phase field is *not* the constant function and whose two patches carry
  different mass profiles, read off the sections themselves through `densityOn`;
  and the record of why it cannot be improved on — `ThermodynamicCover.phase_locked`
  forces every instance to a phase-locked configuration. Built through
  `LocalSectionSynchronization.ofInvariantMeasure`, it also inherits that
  constructor's limitation: the glued section is the measure it was built from.

  §14 answers open item O19, which is the other limitation. The class no longer
  carries a global section, so this cover's two patches are built from two
  *different* mass profiles that agree only on the site they share. The gluing
  returns a third profile, and neither input restricts correctly to both patches
  (`leftW_glues_nothing`, `rightW_glues_nothing`): the global state is produced
  by the sheaf condition rather than supplied to it.

  Every declaration in these files depends only on `propext`, `Classical.choice`
  and `Quot.sound`.
-/

import PhysicsOfConsciousness.Examples.Bit
import PhysicsOfConsciousness.Examples.Cortex
import PhysicsOfConsciousness.Examples.Phase1
import PhysicsOfConsciousness.Examples.Phase2
import PhysicsOfConsciousness.Examples.Phase3
import PhysicsOfConsciousness.Examples.Agency
import PhysicsOfConsciousness.Examples.AgencyThermodynamics
import PhysicsOfConsciousness.Examples.AgencyCycle
import PhysicsOfConsciousness.Examples.AgencyControl
import PhysicsOfConsciousness.Examples.PolicyLearning
import PhysicsOfConsciousness.Examples.ObservationalLearning
import PhysicsOfConsciousness.Examples.ContinuingAgent
import PhysicsOfConsciousness.Examples.RegisterBudget
import PhysicsOfConsciousness.Examples.ActuatedCoupling
import PhysicsOfConsciousness.Examples.MicroscopicCoupling
import PhysicsOfConsciousness.Examples.Phase4
import PhysicsOfConsciousness.Examples.Phase5
import PhysicsOfConsciousness.Examples.Phase6
import PhysicsOfConsciousness.Examples.Phase7
import PhysicsOfConsciousness.Examples.Phase8
