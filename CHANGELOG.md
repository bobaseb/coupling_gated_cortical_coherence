# Changelog

`main.tex` and `supplementary.tex` state the theory's current state only
(`AGENTS.md` §5). This file is where the drafting history goes instead: what the
work claimed, what it claims now, and where the reasoning is recorded.

It exists for readers of the *repository*, including future agents. Nothing here
is addressed to a reader of the paper, who has never seen a previous draft and
should not have to.

Two things this file is not. It is not the complete record — that is
`tasks/todo.md` and its archives under `_archive/`, which carry the pass records
in full, and the Lean docstrings, which carry the technical half. And it is not
a list of everything that changed; it lists **claims that were made and are no
longer made**, which is a much shorter list and the only one worth being able to
find.

No version of this work has been posted or submitted. Nothing below was ever
published, so nothing below is a correction to the scholarly record.

---

## 2026-09-09 — S6 plasticity control: the antecedent is now measured

The claim is unchanged and the evidence for it is different. Denying that
dissipation minimization implies representational learning requires a run in
which dissipation is actually minimized, and the previous S6 run did not supply
one.

Claims that were made and are no longer made:

- That the objective descended in the S6 run. At the previous learning rate the
  gradient arm's second-half squared drift was 1377.9--1380.0 against
  1380.6--1382.3 for its frozen control: about 0.7% of the headroom between the
  frozen arm and the floor `N*mean(omega)^2/D` that the conserved mean drift
  imposes. A matched-norm random update was indistinguishable from it. The
  production rate is now selected by a committed sweep as the rate at which the
  objective descends furthest, and the gradient arm removes 0.68--0.69 of that
  headroom while the random arm removes none.
- That the kernel moved away from the template "below the level of a random
  relabelling", on the evidence of Frobenius distance against one shuffle. Most
  of that distance growth was kernel-norm growth under a resource total that
  constrains the entry sum and not the norm; a scale-free correlation moved from
  -0.020 to -0.026. The alignment claim now rests on the within-over-between
  cluster coupling ratio and a 2000-draw permutation null, with the distance and
  the correlation reported as readouts that do not carry the effect.
- That the expectation being refuted is that dissipation descent makes a system
  mirror its input. The predictive dissipation bound licenses no such reading in
  the first place: it bounds *nonpredictive* memory, which a memory carrying no
  information satisfies with room to spare.

Added rather than narrowed: the opposition between this objective and this
template is now stated as a conservation-law consequence rather than left as an
empirical surprise. Symmetric coupling fixes `sum_i v_i`, so minimizing
`sum_i v_i^2` can only equalize drift across nodes, which rewards coupling
between clusters of unlike frequency — the complement of a template rewarding
coupling within clusters of like frequency. That is what makes the run a
counterexample rather than a coincidence.

Reasoning and criteria: `tasks/s6_execution.md`.

---

## 2026-09-06 — Narrative revision after external review

Claims narrowed:

- **Uniqueness of the global section and the reflexive fixed point was presented
  as derived without further postulate.** The theorems give uniqueness *relative
  to* a cover whose local sections agree and a contracting self-prediction map.
  Choosing those — which regions, which overlaps, which encoding region, and so
  where the subject ends — is not supplied by gluing or by Banach, and is what
  E78 and E89 carry. The article now says so, and claims only that the
  construction removes the need for an additional principle to select among the
  experiences a fixed cover and map admit.
- **The square-root onset was promised before its condition.** The prediction
  holds while the phase distribution tracks the stationary branch; that
  condition is now inside the claim in the abstract and introduction rather than
  arriving later as a qualification.

Added, not withdrawn: an introduction-level spine (coherent activity, compatible
local descriptions, self-representation), a worked overlap example making
compatibility concrete before the sheaf machinery, and forward motivation for
the plasticity control. Evaluative framing was cut throughout; the scope
statements were kept.

New advisory gate `simulations/check_hedging.py`, hook `check-hedging`. It
reports disclaimer and reader-instruction language and always passes: whether a
hedge earns its place is a judgement about its paragraph, not a rule, so unlike
`check_prose` it decides nothing. Scope statements are counted for density
rather than flagged, because flagging them would be advice to overclaim.

---

## 2026-09-05 — PRX Life manuscript tightening

The main article is reorganized around a conditional cortical-coupling model,
its awakening prediction, and the completed numerical controls. Repeated proof
implementation and speculative comparisons are condensed; technical scope
remains in the supplement and Lean sources.

Claims withdrawn or narrowed:

- Dimensionless population phase-shift arithmetic does not establish cortical
  threshold crossing. A separately calibrated inverse-time factor is required.
- A monotone coupling gate does not uniquely predict a sigmoid, and the static
  square-root branch does not guarantee an observable cusp at finite ramp rate.
  The absence of a stationary fold does not exclude dynamical hysteresis.
- Squared drift is not generally thermodynamic entropy production. S6 does not
  support environmental learning; coherence also persists in frozen controls.
- Sheaf gluing and wiring-support inequalities do not exclude digital
  consciousness or establish that continuity alone supplies phenomenal unity.
- EEG pooling estimates a spatiotemporal distribution. The exploratory bin
  bootstrap does not preserve temporal dependence, and compatibility with the
  Bessel curve over a narrow range is not a discriminating confirmation.

Both publications share references.tex. Unused references and an unverified,
underspecified Lacker preprint entry are removed; the existing Sznitman chapter
is retained with publisher-verified bibliographic details. No new simulations
or Lean results are introduced. This is preparation for author review, not a
submission or a claim that the biological assumptions have been validated.

## 2026-09-03 — two of the eight named hypotheses were satisfiable without their premises

**Claimed:** that `chain`'s eight named hypotheses are eight gaps, each an
implication between two node predicates, and that the count is the checkable
number the reader can obtain with `#check @chain`.

**The problem:** two of the eight had conclusions that mentioned nothing from
their own premises. `E34` asked for `Nonempty (PredictiveDissipation Xs Sg Sg')`
and `E78` for `Nonempty (ThermodynamicCover X)`; both structures were already
inhabited at the types the joint witness uses, so `fun _ => ⟨frozenSystem⟩` and
`fun _ => ⟨cortexCover⟩` proved them without reading their hypotheses. The count
was right and two of the things counted were not gaps — an arrow whose proof
discards its premise is the manufactured-edge shape `Chain.lean` exists to
prevent.

**What is claimed now:** `E34` asks for a predictive structure whose thermal
scale is the register's own temperature, whose dissipated work is that
register's Landauer heat, and whose wasted memory is non-zero. `E78` asks for a
cover whose patch coupling is at least the mean-field constant `K` and whose
equilibrium configuration is the limit of a relaxation on that coupling
(`ThermodynamicCover.IsReachedByRelaxation`). Both are discharged in the joint
witness — by `landauerSystem` and by `trioCover3` — and each has a regression
naming a witness the bare form accepted and the strengthened form does not
(`frozenSystem_not_of_eraser`, `trioCover_not_reachedByRelaxation_three`). The
count is still eight.

**Where the reasoning is:** `tasks/todo.md`, the T2 pass record of 2026-09-03,
and the docstrings of `E34` and `E78` in `Chain.lean`.

---

## 2026-08-31 — the chain composes, and two claims about it were wrong

**Claimed:** that a machine-checked chain guarantees "no link can quietly borrow
from another, that a hypothesis cannot be smuggled in as a definition".

**The problem:** the development did not establish that. It certified ten
developments each of which compiles; no theorem anywhere stated that they run
into one another. `Phase8_SelfConsistency` — the entire `K_c = 2D` bifurcation —
was a leaf of the import graph, consumed by nothing but the root aggregator.
`Phase2_MeshConvergence` and `Phase3_PredictiveThermodynamics` were imported only
by `Examples.lean`, which consumes their witnesses and none of their theorems.
The honesty of the development was per node, not per edge.

**Claimed:** that Derivation 6 was connected to Derivation 7.

**The problem:** it was not. `self_of_supercritical` takes `critical_coupling D <
K` as its hypothesis, and `critical_coupling` is a `def` unfolding to `2 * D`.
The Self consumed the *numeral*, and would have been provable with
`Phase8_SelfConsistency.lean` deleted.

**Claimed now:** `Chain.lean` states each node as a `Prop` and each arrow as
either a theorem or a named hypothesis. `chain` derives the Self from the
capacity bound and takes **eight** named hypotheses — four formalization gaps,
two modelling assumptions, two physical commitments — each an implication
between two node statements, so deleting one fails the build.
`self_of_coherent_order_parameter` takes the *existence of the coherent order
parameter* and recovers the threshold inequality from it
(`supercritical_of_coherent`), so the last step consumes Derivation 7's theorem.
`chain_nonvacuous` discharges all eight simultaneously on the three-site
substrate.

**Two further claims fell out of the composition, and both were in Figure 1.**
The arrow from the capacity bound to the existence of a boundary is not an
inference: the capacity bound has no hypotheses, so the implication is equivalent
to assuming the boundary outright. And the arrow out of the spacetime-symmetry
box was an inference leaving a node the box itself described as consumed by no
theorem. Both are gone; the two arrows that *are* theorems (finiteness straight
to Landauer, the order parameter straight to the Self) were not drawn at all.

**Record:** `tasks/todo.md`, C1–C5 pass records.

---

## 2026-08-31 — coarse-graining produces a scalar, not a kernel

**Claimed:** "discrete couplings coarse-grain to a continuous kernel", and that
the remaining gap to the field theory was the dynamical mean-field limit
(propagation of chaos).

**Claimed now:** `mesh_refinement_convergence` converges the discrete coupling
*energy* — one real number — to `∫_S f dμ`. No theorem produces a kernel of two
continuum points, and `TriangulatedManifold.edge_region` is a subset of `M`
rather than of `M × M`, so the discrete side has no product structure to pass to
a limit. The obvious repair is blocked by a theorem: a kernel placing the weights
at the embedded vertices does carry them
(`Chain.vertexKernel_apply_embedding`) and still contributes exactly zero
continuum coupling energy on an atomless substrate
(`Chain.vertexKernel_fieldCorrelation_eq_zero`) — Derivation 8's hardware no-go
cutting against the framework's own coarse-graining step. The mean-field limit is
a real gap but it is not the first one on this edge.

**Record:** `tasks/todo.md`, C3 pass record.

---

## 2026-08-31 — Derivation 6: the Self theorem could not see the avatar

**Claimed:** that the reflexive boundary's fixed point is the Self of a system
that encodes its own state into a localized avatar.

**The problem:** `ReflexiveBoundary` carried the predictive map as free data
sitting beside the avatar, and the fixed-point theorem projected that map out
without touching the avatar. The consequence was a theorem,
`self_of_constResonance`: replacing the avatar by a constant left a legal
boundary with the same predictive model and the same Self. Derivation 6 was
Banach's theorem with a consciousness-flavoured label.

**Claimed now:** `predict` is `readout ∘ auto_resonance`, a definition rather
than a field, so the self-model runs through the avatar region or it does not
exist. `self_of_constResonance` does not typecheck; `not_self_of_constResonance`
says the opposite — blinding the avatar *moves* the Self.
`self_eq_readout_restrict` is what being a fixed point now buys: the field is
what its own localized self-encoding reconstructs.

**Claimed:** that the predictive map contracts by `1/2`.

**Claimed now:** the rate is `resonanceRate K D τ = exp(-(K - K_c)τ/2)` with
`K_c = 2D`, read off the substrate. `1/2` was a fact about a map defined to
average with a baseline, not a claim about a substrate.

**Record:** `_archive/todo_2026-08-31_pre-composability-replan.md`, W5.

---

## 2026-08-31 — Derivation 5: the equilibrium hypothesis was assumed on every instance

**Claimed:** that a cover at thermodynamic equilibrium glues to one global
section, with `thermodynamic_equilibrium` an assumption every instance had to
make.

**Claimed now:** `ThermodynamicCover.ofConvergentTrajectory`
(`Phase5_EquilibriumBridge.lean`) derives it from a Kuramoto trajectory that
reaches the minimum, for initial data within a quarter turn and below the energy
threshold, and `Examples.lean` §17.1 is such a cover built from initial data that
is not phase-locked. The cover's couplings are read off the dynamics' own system,
so the system whose equilibrium is asserted and the system whose trajectory is
run are the same system. The cover's *other* physical hypothesis,
`section_agrees_of_phase_eq`, remains an assumption on every instance.

**Claimed:** that the gluing is an emergence theorem.

**The problem:** the class carried the global section as a field
(`phase_invariant_measure`) and declared the local sections to be its
restrictions, so the theorem could only rule out competitors to an object the
instance had already supplied.

**Claimed now:** both fields are gone. The global section is constructed by
`probability_glue_unique`, and the old field `sync_to_section_eq` is a theorem
about it.

**Record:** `_archive/todo_2026-08-31_pre-composability-replan.md`, W1; and the
O19 record in `_archive/todo_2026-08-30_pre-strategic-replan.md`.

---

## 2026-08-31 — Derivation 4: demoted from a derivation to a theorem plus a commitment

**Claimed:** that the continuous macroscopic electromagnetic field is *the
primary dissipative structure* interacting with the universe, and that the step
from the discrete system to the continuum is supported by the Renormalization
Group.

**The problem:** none of the cited work supports "primary". Anastassiou and Koch
report endogenous fields of 1–5 mV/mm shifting spike timing by 1–3 ms, which is
modulation. And no RG flow is constructed anywhere in the development, so the
appeal was decorative.

**Claimed now:** the section is *Macroscopic Scaling: A Theorem and a
Commitment*, deliberately not numbered as a derivation. The theorem is mesh
convergence; the commitment — that in mammalian cortex the field realizing the
coarse-grained coupling is the endogenous electromagnetic field — is stated as a
claim about biology, with four conditions that would falsify it. The field is
claimed to be modulatory in its effect on individual neurons and integrative in
its spatial reach, which is what the evidence supports.

**Record:** `_archive/todo_2026-08-31_pre-composability-replan.md`, W3.

---

## 2026-08-31 — frustration: a capacity claimed outside the regime the theorems cover

**Claimed:** that competing couplings give the field a memory capacity.

**The problem:** every "where does it land" theorem in the development carries
`∀ i j, A i j > 0` — an unfrustrated ferromagnet, whose potential has one minimum
up to global phase. Well-posedness, Lyapunov descent and the phase-locking
characterization all require it. The framework's account of content needs the
frustrated regime; its theorems describe the unfrustrated one.

**Claimed now:** the scope is stated rather than the capacity. This is the
deepest objection the framework faces and it is recorded as open, not closed.

**Record:** `_archive/todo_2026-08-31_pre-composability-replan.md`, W3, and the
standing note in `tasks/todo.md`.

---

## 2026-08-31 — Derivation 3: an invalid inference, replaced rather than weakened

**Claimed:** entropy production obeys `σ ≥ D_KL(P_ext ‖ Q_int)/Δt`, therefore a
system descending on `σ` drives `D_KL → 0`, therefore the internal model comes to
match the environment.

**The problem:** the rearranged bound `D_KL ≤ Δt · σ` is true and descending on
`σ` does lower the bound, but the limit does not follow. A driven system relaxes
to a non-equilibrium steady state at strictly positive `σ`, so the bound delivers
`D_KL ≤ Δt · σ_NESS`, a positive number, and never zero. The conclusion that buys
the framework predictive processing was read off an inequality that does not
support it.

**Claimed now:** Still, Sivak, Bell and Crooks, *Thermodynamics of Prediction*,
Phys. Rev. Lett. **109** (2012) 120604: dissipated work is bounded below by the
thermal cost of the *nonpredictive* information, `I(X_t;S_t) − I(X_t;S_{t+1})`.
The bracket's non-negativity is a theorem here
(`predictiveInfo_le_mutualInfo`, from the data processing inequality) rather than
a postulate, and no limit is required: any bound on the dissipation is
immediately a bound on the nonpredictive memory. This is weaker than the old
claim and it is what is true. The old KL bound is retained, since it is
consistent and yields `σ ≥ 0`; no limit may be read off it.

**Record:** `_archive/todo_2026-08-31_pre-composability-replan.md`, W4.

---

## 2026-08-30 and before — five axioms, three of them inconsistent

**Claimed:** five `axiom` declarations, presented as irreducible physical
postulates.

**The problem:** three of them each proved `False` on their own, from one shared
root cause — **an axiom that constrains a symbol it does not itself bind**.

* `spontaneous_symmetry_breaking_pointwise_min` took the potential-energy
  functional as an *implicit* argument occurring only in its hypothesis.
  Instantiating that functional with a constant map discharges the hypothesis by
  `rfl` and yields the conclusion for an arbitrary field; with `V(v) = v²`,
  `v₀ = 0` and `φ ≡ 1` it proves `1 = 0`.
* `landauer_heat_eq` equated the free class field `heat_dissipation` with a
  bath-entropy difference for *every* instance. An instance with zero heat
  dissipation and a bath gaining one bit gives `0 = log 2`.
* `kl_bound_axiom` asserted `σ ≥ D_KL(P‖Q)/Δt` for *all* `P` and `Q`, while `σ`
  is a single real fixed by a class field. `D_KL` is unbounded above.

The remaining two, `phase_invariant_periodic` and `sync_to_section_eq`, had the
same shape — global assertions pinning free fields of a class — and are refutable
as soon as the probability presheaf admits two distinct global sections.

None of the three was caught by reading. All three left the build green.

**Claimed now:** the development declares **no axioms**. `#print axioms` on any
result reports only `propext`, `Classical.choice` and `Quot.sound`. Every
physical postulate is a field of a class that each model discharges for itself,
and every such class is inhabited by an explicit witness in `Examples.lean`. The
general rule — a postulate about a symbol must bind that symbol, or it is a
constraint on every model including the ones that refute it — is stated in the
paper as a methodological finding, because it is one.

**Record:** `_archive/todo_2026-08-30_pre-strategic-replan.md`; the manuscript's
soundness section states the mathematics.

---

## 2026-08-30 and before — three further defects that survived prose review

**A false conjecture.** Mesh refinement convergence was stated for a single `δ`
good for all triangulations of small mesh, over a class that did not require the
edge regions to cover anything. The everywhere-empty triangulation refuted it.
`mesh_refinement_convergence` replaces it: a *sequence* of triangulations with
fineness tending to zero, required to be regular, over a named region.

**Two potentials never chained.** Lyapunov descent was proved for the full
Kuramoto potential; the characterization of the minimum, and everything
downstream including Derivation 5's gluing, concerned the coupling term alone.
`kuramoto_potential_unbounded_below` proves the full potential has no minimum as
soon as one natural frequency is non-zero, so "the phase-locked state minimizes
the Lyapunov potential" was false of the functional the descent theorem was
about. `Phase4_RotatingFrame.lean` closes it by the standard reduction, exactly
for identical frequencies.

**A threshold predicate sensitive to substrate mass.** `exhibits_phase_transition`
compared an unnormalized double integral against `2D`, so a constant kernel on a
substrate of mass `m` contributed `K m²` and any kernel could be pushed above
threshold by inflating `m`. Fixed by requiring the substrate's measure to be a
probability measure, which is the normalization the mean-field derivation uses.

**A witness that said nothing.** The first metric on `GlobalSection` was the 0/1
metric, under which `contracting_implies_const` proves every contraction is
constant. It is kept as `gsDiscreteMetric` together with that theorem, as the
record of why the earliest witness was empty. The Lévy–Prokhorov metric named in
`Phase6`'s header is *not* what is constructed: on a discrete substrate the
ε-thickening of a set is the set itself for ε < 1.

**Record:** `_archive/todo_2026-08-30_pre-strategic-replan.md`; the manuscript's
soundness section states the three mathematical findings.
