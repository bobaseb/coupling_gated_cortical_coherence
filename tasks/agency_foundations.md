# Agency foundations handoff — 2026-09-15

## Authorized scope

The user requested foundational Lean for **all remaining agency items**, with
completion by a later agent because the credit budget is short. This pass is a
Lean-only draft: publication alignment, rebuilt PDFs and final closure of the
research items are explicitly deferred. The pre-existing changes to `main.tex`,
`main.pdf` and `references.tex` belong to other work and must be preserved.

## Intent, constraints and success criteria

Build small independent foundations for:

1. Preparation, sharp charge transfer, installation/control work, reservoir
   identification and external refuelling: use actual state trajectories and
   energy observables; expose conservation and thermal identification as
   hypotheses, with concrete resource-transfer witnesses.
2. Broader state spaces: prove the trajectory resource bound without a finite
   state assumption and instantiate an unbounded state space. This is not yet
   countable/continuous stochastic thermodynamics or optimal control.
3. Weaker positivity: replace full support by forward/reverse support inclusion
   for finite entropy balance; retain infinite production when inclusion fails.
4. Local content: observation-driven overlap updates, a residual bound,
   preservation and an explicit readout/gluing condition. Neural interpretation
   and a bridge to the probability sheaf remain separate.
5. Longer learning horizons: derive a rate and limit for the **existing
   continuing observational learner's actual performance**, with the existing
   positive resource floor. Do not claim optimality or affordable infinite runs.

Success means retained concrete regression specifications, proved declarations
without placeholders or new axioms, root imports, a warning-free `lake build`
including `Audit`, and a precise record of remaining work. No Python,
dependencies, simulation runs or new references are required.

## Plan

- [x] Run failing Lean specifications before implementation.
- [x] Add resource/implementation foundations and nonfinite witnesses.
- [x] Add support-aware finite thermodynamics and irreversible counterexample.
- [x] Add local content dynamics and readout witnesses.
- [x] Add the actual learner's convergence/rate and resource obstruction.
- [x] Run the build/audit and applicable lightweight checks; record results.

Of the five parent roadmap items these serve, two — weaker positivity and
longer horizons — are closed against their own completion criteria and ticked in
`tasks/todo.md`. Broader state spaces and local content agreement are half
closed, with the open half named in each. Physical preparation and supply
remains open. The dated assessment is at the end of that ledger.

## Execution record — 2026-09-15

Two passes. The first drafted the five modules and the regression file; it
stopped before wiring them, so nothing it wrote was reachable from the root and
none of it had been compiled together. The second pass wired the modules,
compiled them, added the concrete witnesses the regression file's own docstring
promised, and repaired what compilation and the gates rejected.

### What is proved

`Phase3_ResourceFoundations` (13 declarations), upstream of the finite-state
store rather than downstream of it. `balance_sum`,
`draw_le_resources` and `horizon_bound` telescope a ledger and bound a horizon
on an **arbitrary** state type: no `Fintype`, no probability law, no channel.
`draw_eq_energy_heat_control` identifies the draw from a conserved boundary that
includes stored, bath and installation/control energy, and
`draw_eq_thermal_work` substitutes a thermal bath term **only** where that term
has been assumed. `transferCharge` is the reversible sharp swap on `ℕ × ℕ`
(involutive, conserving, `(n, 0) ↦ (0, n)`); `refuel` is a declared real-valued
trajectory whose ledger holds and which stays solvent forever when delivery
matches draw. `entropy_reduction_le_bathEntropy` is the bridge to the module
below. `Phase3_ContinuingAgent.horizon_le_of_cost` is now proved by specializing
`horizon_bound` to the expected-work ledger, which is what that bound is for:
the finite state space plays no part in it, and the pathwise store's own bounds,
which branch over reachable states, stay where they were.

`Phase3_Preparation` gains `PathwiseStore.withPreparation` and
`withPreparation_ledgered`, which attach the preparation stage to an existing
store so its draw is inside the resource boundary from the start of the run.
They live beside `FiniteProtocol.withPreparation`, the channel they wrap.

`Phase3_SupportedThermodynamics` (9 declarations). `ProbDist.SupportIncluded`
replaces full positivity by forward-into-reference support inclusion.
`KL_nonneg_of_support` is Gibbs under it; `ReversibleSupport` is the path-law
form and `reversibleSupport_of_positive` shows it is strictly weaker.
`entropyProduction_nonneg_of_support` and `entropy_balance_of_support` are the
second law and the exact balance in that regime. `ProbDist.extendedKL` keeps the
irreversible case honest in `ℝ≥0∞`: `extendedKL_toReal_of_support` recovers the
real divergence where support holds, and `extendedKL_top_of_missing` returns `⊤`
for a single unsupported forward atom rather than a finite real cost.

`Phase5_ContentDynamics` (10 declarations), upstream of `Phase5_GlobalSection`,
which it uses nothing from. `Compatible` is a pointwise overlap
mismatch bound; `update` mixes a local field with that patch's observation.
`update_residual` gives `(1-η)ε + ηδ`, `update_preserves` the exact-agreement
case, and `run_residual` the geometric decay `(1-η)^n ε` under compatible
observations. `readout` selects a patch per site; `readout_residual`,
`readout_agrees` and `readout_unique` are the approximate bound, the gluing at
zero residual and the uniqueness of any global extension.
`ApproximateGluing.compatible_pointwise`, added to `Phase5_GlobalSection`, reads
that section's finite nonnegative mass profiles as such a family at the same
tolerance: the two agreement predicates in this development are one predicate,
and the observation dynamics acts on the families the sheaf-side theorems
accept.

`Examples/ContinuingLimit` (5 declarations). `agreement_error` and
`performance_error` are the **exact** error of the existing learner's own
recurrence, `(65/127 - 65/128)(1/128)^m`; `performance_tendsto` is convergence
of its actual expected task performance to `65/127`, and
`performance_limit_lt_one` records that this is below perfect play.
`work_unbounded` reuses the existing per-cycle floor, reset included, to exceed
every finite expected allowance.

### Regressions

`Examples/AgencyFoundations` holds 22 specifications and 17 supporting witness
declarations. The 9 inherited specifications are the general statements; they
were re-run against the pre-implementation import set and failed with 16 errors,
every one an absent declaration, then passed unchanged once the modules were
wired. The 13 added are concrete, because the general statements alone are
vacuity-shaped:

- a real trajectory drawing one unit from ten, whose horizon `horizon_bound`
  bounds by 10 with no finite state space in the statement; a trajectory that
  stays solvent at every operation under matched delivery; the sharp transfer
  emptying a seven-unit source;
- `sparse`, a feedback step on `Bool × Bool` whose initial law is supported on
  one atom. `sparse_not_positive` and `sparse_reversibleSupport` are the two
  halves of the point: the entropy balance and the second law hold on it, and
  the earlier `entropy_balance` does not reach it;
- erasure of a definite bit onto the opposite definite bit, whose `extendedKL`
  is `⊤`, against the same bit read from uniform, whose extended divergence is
  finite and equals `log 2`;
- two patches on three sites sharing the middle one, carrying 5 and 7 away from
  it. The readout glues, is the unique global extension, and evaluates to
  `(5, 1, 7)`. A family disagreeing by one on the shared site is compatible at
  `ε = 1` and provably not at `ε = 0`, so the gluing premise is not automatic,
  and under constant observations its disagreement decays as `(1/2)^n`.

### Validation

`lake build`, including the default `Audit` target, completes with **zero
warnings**. The audit covers 4,126 declarations in 68 modules resting only on
`propext`, `Classical.choice` and `Quot.sound`; the 17 explicit `#print axioms`
headline checks in the new and moved declarations agree. `check_sorry` passes over 70 Lean
sources, and `check_leaves` passes with every new module carrying a real
consumer. No Python, dependency, reference, generated
macro, simulation result or publication source was touched, so the Python,
`.tex` and artifact gates have nothing in this change to read.

Four defects were found and fixed in the second pass, all in the first pass's
draft. `Phase5_ContentDynamics.run_residual` tripped the `unnecessarySeqFocus`
linter and had to be split into a combinator and a following `ring`. The five
modules were absent from `PhysicsOfConsciousness.lean` and
`PhysicsOfConsciousness/Examples.lean`, and `Examples/AgencyFoundations.lean`
imported the modules its predecessors live in rather than the ones it uses, so
nothing it specified was in scope.

The fourth was structural, and is the reason three modules moved. All three new
phase modules were leaves: their theorems were referenced by nothing outside
themselves and the witness file. `check_leaves` caught only
`Phase3_SupportedThermodynamics`, because it matches bare declaration names and
`withPreparation`, `update`, `readout` and `Compatible` are also names in seven
other modules — so two of the three passed spuriously. The repair was not to
invent consumers but to notice that all three were **placed** downstream of work
that should depend on them:

- `Phase5_ContentDynamics` imported `Phase5_GlobalSection` and used nothing from
  it. It now sits upstream, and `ApproximateGluing.compatible_pointwise` in the
  sheaf module reads that section's mass profiles through the general predicate.
- `Phase3_ResourceFoundations` imported `Phase3_Preparation`, which forced it
  below `Phase3_ContinuingAgent` — the module whose expected-work horizon bound
  is a special case of it. Moving `PathwiseStore.withPreparation` to
  `Phase3_Preparation`, beside the channel it wraps, freed it to sit above
  `Phase3_ContinuingAgent`, whose `horizon_le_of_cost` now specializes
  `ResourceTrajectory.horizon_bound` instead of re-proving the sum bound.
- `Phase3_SupportedThermodynamics` is consumed by
  `entropy_reduction_le_bathEntropy` in the resource module.

Every consumer is now a qualified reference in a real proof, verified against
the gate's own reference index rather than against its exit code.

### Remaining work

Closure of the parent roadmap items is still open; these are foundations for
their next reviewable changes.

Publication alignment was deferred by the authorized scope and has since been
done at the user's request, in a second commit. Four scope sentences were
rewritten rather than deleted: the article's and the supplement's statements of
the path-law premise, which said strictly positive masses and now say support
inclusion; the funded-memory sentence that placed external refuelling outside
the model; and the explanatory-gap paragraph, whose "preserve" half now has an
answer under a stated hypothesis while its "acquire" half does not. Table S1
gained three rows, the supplement a subsection on observation-driven contents
and the closed form of the continuing learner's recursion, and the primer that
closed form and a summary row. All three tracked PDFs and the arXiv submission
were rebuilt in the same commit. Details in `CHANGELOG.md`.

Owed by the foundations themselves:

- **Resources.** Gate fabrication and control work are charged to an observable
  (`C`) and never priced. Conservation and the thermal identification of the
  bath term are hypotheses, not theorems, and `draw_eq_thermal_work` will
  substitute any real number called `θ * log ratio`. `withPreparation_ledgered`
  supplies no microscopic implementation of the preparation it charges.
  External refuelling is an input `u`, not a modelled source.
- **State spaces.** The trajectory results carry no probability law, so this is
  not countable or continuous stochastic thermodynamics; `refuel` and
  `transferCharge` instantiate unbounded state, not unbounded dynamics. Optimal
  control is untouched.
- **Support.** `extendedKL` is a finite sum; equality with Mathlib's measure
  divergence is a separate bridge. Nothing here constructs a physical reverse
  protocol, and there is no continuous-state entropy balance.
- **Content.** The scalar contents are identified with nothing — not neural
  variables, not the probability sheaf of `Phase5_GlobalSection`. Observation
  compatibility is an input: no theorem derives it from task reward, phase
  coherence or a shared target. The gluing is of scalar fields and does not
  close the content-model gap at `main.tex:226`.
- **Horizons.** `performance_tendsto` is convergence in expectation along
  completed cycles of one fixed witness. It is not pathwise convergence, not
  optimality, and `work_unbounded` is the statement that the run it describes
  cannot be funded.
