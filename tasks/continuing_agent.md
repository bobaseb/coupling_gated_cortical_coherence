# One continuing physical agent — sequenced stages on one law, from a declared store, 2026-09-14

## Intent and constraints

Close the open modelling item **"One continuing physical agent"**: compose
learning, the subsequent action, the observation and the memory update on one
evolving joint law, include the policy register's actual influence on the
actuator, include preparation and the reset, declare the energy source, and
derive the total heat/work and entropy accounting for the executed process.

Three things are missing from the completed work and are what this change adds.

* `FiniteFeedbackStep.iterate` repeats **one** channel. A continuing agent runs
  *different* operations in sequence — it acts, then it reads, then it clears
  the workspace — so the accounting must telescope over a time-dependent
  protocol, not a repeated one. The existing docstring says as much: "Preparation
  and time-dependent protocols are absent."
* `FiniteObservationalLearner`'s world is memoryless: `world : W → A → ProbDist O`
  responds to the action and forgets it. Nothing in it carries a state the
  action changed into the next observation, so nothing in it needs clearing.
* Nothing anywhere in the development says where the work comes from.
  `sum_meanHeat_eq_energy_drop` funds cumulative heat from an energy drop and
  says, in its own docstring, that this "neither supplies a continuing power
  source nor accounts for preparing the initial distribution."

Out of scope, and to be fenced as such in the publication: the physical
mechanism of the store (it is declared, like every reservoir in this
development, and its depletion is bookkeeping on the same paths, not a derived
dynamics); **the store is a ledger of expected work, so it bounds every prefix
in expectation and promises nothing about a battery along an individual
trajectory**; the separate sensor memory a physical observation would need,
since the observation is marginalized inside the learning channel and local
detailed balance is then supplied for that composite; fabrication of the readout
and the actuator; the register ledger's own premises; optimal-policy
convergence; unbounded horizons; and any cortical identification. No new axiom, dependency, Python source, simulation, reference
or numerical macro is part of this change.

## Model

### The protocol

`FiniteProtocol X S` carries an initial law on `X × S` and a *sequence* of
channels `stage : ℕ → X → S → ProbDist S`. `step n` is the elementary
`FiniteFeedbackStep` whose initial law is the law reached after `n` stages and
whose transition is `stage n`; `law n` is that law. Every actual output is the
next input, so the parameter `X` is conserved and the process is one law.

The three existing balances lift to it without new physics, because each stage
is an ordinary `FiniteFeedbackStep`: `sum_entropy_balance` (telescoped KL
production), `sum_first_law` (one common energy, stage-dependent heat), and
`cumulative_entropy_budget` (Gibbs plus local detailed balance at one thermal
scale). `iterate` is the constant-stage case; nothing about it is superseded.

### The store

`ContinuingProcess X S` adds to a protocol: a common energy `energy`, a
stage-indexed heat observable `heat`, a thermal scale `temperature`, and
`stored`, the usable work available at the start. `stageWork n` is the pathwise
first law, `totalWork N` and `totalHeat N` are the sums over the executed
stages, and `remaining N = stored - totalWork N`. `Sustains N` says the store
is never overdrawn in expectation: `0 ≤ remaining k` for every `k ≤ N`.

Four consequences, each about the whole executed process:

1. `sustains_totalWork_le`: a sustained run has drawn at most its store.
2. `totalHeat_le_stored`: the heat delivered to the reservoirs over a sustained
   run is at most the store plus the energy the system itself gave up.
3. `entropy_reduction_le_stored`: the joint entropy reduction is bounded by
   the store **plus the system's mean energy drop**, divided by the thermal
   scale. The store alone suffices in the degenerate-energy witness.
4. `horizon_le_of_cost`: if every stage costs at least `c`, a sustained run of
   `N` stages satisfies `N * c ≤ stored`, so for positive `c` a finite store is
   finitely many operations. Sustained operation is a claim about
   replenishment, and the store makes none.

### The agent

`ContinuingAgent W R Env O A` carries the prior on `W × (R × Env)`, `readout :
R → A`, `actuate : W → A → Env → ProbDist Env`, `sense : Env → ProbDist O`,
`update : O → R → ProbDist R`, `reset : Env → ProbDist Env`, the two idle
channels that the coordinate not being driven undergoes anyway, and `reward`.
The fences are again signatures: `update` sees neither `W` nor the action,
`readout` and `sense` do not see `W`, and `reward` enters no channel. The
environment's state is what the action changed and what the observation reads,
so the actuator's influence is not a relabelling.

Its `stage` is three-periodic on one state space `R × Env`:

* `actStage` — the register's readout drives `actuate`, which moves the
  environment; the register drifts.
* `learnStage` — `sense` reads the environment the action moved, `update`
  writes the register; the environment drifts.
* `resetStage` — `reset` returns the environment to its standard state,
  preparing the next episode; the register drifts.

`protocol` is the `FiniteProtocol` of those stages from that prior, so every
result above applies to the composed process, and `performance` is read from
the same law.

## Success criteria

1. The three telescoped balances and the four store results above, for a
   heterogeneous protocol, with positivity and local detailed balance as
   hypotheses and no stationarity anywhere.
2. A witness on `W = R = Env = O = A = Bool`: an unknown rewarding action, a
   task flag the action sets and the reset clears, and a noisy flag readout.
   All primitive channel masses in `{1/4, 3/4}`, so every stage heat is a rational
   multiple of `log 3` or `log (5/3)`.
3. Exact accounting on the actual law: the mass form is preserved by each
   stage, the act, learn and reset heats have closed forms in the four masses,
   and the cycle map on the agreement parameter is exact.
4. **Persistence:** the register's agreement with the unknown parameter is at
   least `65/128 > 1/2` after every completed cycle, forever.
5. **The cost of persisting:** every cycle draws at least
   `(3/16) log 3 + (1/16) log (5/3)` of work from the store, for any law the
   agent can be in, so the declared store `4 log 3` cannot fund 22 cycles.
   The first cycle is funded exactly: `(15/32) log 3 + (1/16) log (5/3)`.
6. Regressions, each of which must fail without the premise it fences:
   * the actuator is actually driven by the readout — the post-action
     environment law differs between the two register values;
   * an uninformative `sense` channel collapses the cycle map to agreement
     exactly `1/2` and makes the learn stage free, so the acquired bias is
     bought by the observations and not by the update rule;
   * a non-erasing third stage (the idle channel in place of `reset`) fails
     to restore the standard flag law and reduces the second cycle's reward. It
     is *not* claimed to abolish learning or to make a set flag absorbing: the
     control still learns, and the comparison of the two rewards is the whole
     claim;
   * successive laws differ, and the reset's heat is strictly positive.
7. SDD/TDD, the axiom audit, zero-warning `lake build`, the publication and
   PDF-freshness gates, and `git diff --check`.

## Plan

1. [x] Recover the inherited specification and run failing specifications for
   the unfinished resource results, controls and active-bound integration.
   The generic protocol was already implemented on resumption.
2. [x] Add `Phase3_ContinuingAgent.lean` with the three structures and their
   derivations.
3. [x] Add `Examples/ContinuingAgent.lean` with the witness and regressions.
4. [x] Align article, supplement, Table S1, primer and ledgers. Rebuild the
   tracked PDFs and refresh the assembled arXiv submission.
5. [x] Pass the complete zero-warning build, the axiom audit, the applicable
   gates and `git diff --check`.

## Stop rule

Stop at one sequenced finite agent, its store and the accounting of both. Do
not generalize the state spaces, prove optimal-policy convergence, derive the
store from a microscopic battery model, or identify any variable with cortex.
If the composition cannot meet a criterion, record the obstruction before
designing an alternative.

## Resumption audit, 2026-09-14

The inherited generic module builds; the witness initially fails. Its
`learn_end_masses` first component has `-5at/32` where direct composition
requires `-3at/32`. Correcting that coefficient restores the planned cycle
map and cost; the remaining failures concern induction generalization and
simplification. A fresh specification in `/tmp/continuing-work/spec.lean`
fails on the missing resource and regression declarations before their
implementation; the inherited scratch specification also exists but has
outdated API signatures and no surviving red log.

The scope is expected work at every prefix, not a pathwise battery bound.
The prior and initial store are supplied resources. Executed resets prepare
subsequent episodes; preparing the initial law is not derived. The observation
is marginalized inside the learning channel, whose local detailed balance is
declared; a separate sensor-memory implementation and its erasure are absent.
These limitations must appear in both the docstrings and the publication.

The original reset-control wording was too strong. Exact rational composition
from the supplied prior gives flag probability `17/32` after one cycle without
reset (instead of `1/4`), and second-cycle agreement `4157/8192` (instead of
`8385/16384`). The control still learns. The regression therefore rejects
unchanged preparation and unchanged performance, not all learning without
reset. This is a correction to the proposed claim, not a redesign of the agent.
The proof bounds funded prefixes; the infinite protocol is only a mathematical
continuation beyond them.

## Completed result and verification — 2026-09-14

`Phase3_ContinuingAgent.lean` holds the three structures. `FiniteProtocol`
carries a stage sequence and reuses each stage as an ordinary
`FiniteFeedbackStep`, so `sum_entropy_balance`, `sum_first_law` and
`cumulative_entropy_budget` telescope over heterogeneous operations, and
`ofStep_step` identifies the constant protocol with the existing `iterate`, so
the repeated case is the same theory rather than a second one.
`ContinuingProcess` adds the energy, the stage heats, the thermal scale and the
store; `sustains_totalWork_le`, `totalHeat_le_stored`,
`entropy_reduction_le_stored` and `horizon_le_of_cost` are the four
consequences. `ContinuingAgent`'s three-periodic `stage` composes actuation,
observation-driven learning and preparation on one law, with `stage_act`,
`stage_learn` and `stage_reset` exposing it and `protocol_positive` lifting the
channel positivity the balances need. `Chain.activeBound_of_continuing` puts a
funded stage in the active node at its store allowance, and
`continuing_stage_activeBound` discharges it for the witness's first cycle —
without identifying that allowance with the register ledger's erasure heat.

`Examples/ContinuingAgent.lean` uses five bit-valued state types and a joint
state of three bits (parameter, register and flag). `masses` is the
four-parameter mass form; `law_zero_masses`, `act_masses`, `learn_masses`,
`reset_masses`, `learn_end_masses` and `cycle_masses` transport it through the
cycle and compose into the exact agreement map `a ↦ 65/128 + a/128` with the
flag returned to `1/4`. `act_heat_apply`, `learn_heat_apply` and
`reset_heat_apply` are the pathwise heats; `act_cost`, `learn_cost` and
`reset_cost` their expectations, the learning stage's being the law-independent
`(1/16) log (5/3)`. `performance_cycle`, `performance_persists` and
`agreement_strict` are criterion 4; `first_cycle_work`, `cycle_work_lower`,
`totalWork_cycles_lower`, `first_cycle_sustained` and `store_exhausted`
criterion 5; `entropy_budget` and `totalHeat_eq_work` the whole-run accounting.
`readout_changes_actuation`, `blind_performance`, `blind_learn_cost`,
`blind_cycle_uniform`, `noReset_first_law`, `noReset_second_law`,
`reset_changes_next_action`, `reset_changes_flag`, `reset_cost_pos` and
`successive_cycle_laws_differ` are the regressions.

Two of this task's conclusions are weaker than the ones first proposed, and the
weaker ones are what is proved. The store is a ledger of *expected* work: it
bounds every prefix in expectation and carries no battery state along a
trajectory. And replacing the reset by idle drift neither saturates the flag nor
abolishes learning; it leaves the flag at `17/32` instead of `1/4` after the
first cycle and lowers the second cycle's reward from `8385/16384` to
`4157/8192`. Both scopes are stated in the article, the supplement, the primer
and `tasks/lessons.md`.

The red specification failed before the declarations existed. The full
`lake build` has zero warnings; the default axiom audit covers 3,408
declarations in 55 modules with only `propext`, `Classical.choice` and
`Quot.sound`, and the explicit headline checks agree. Every pre-commit hook
passes at the repository root under `uv --project simulations`, including
`check-prose`, `check-tableS1`, `check-figures`, `check-pdf-freshness`,
`check-arxiv-freshness`, `check-leaves` and `check-sorry`; the 143 Python tests
pass unchanged. No Python, dependency, reference, macro or simulation result
changed.

The article gained one subsection paragraph with its budget equation and a
rewritten E34 row, the supplement one subsection with two displayed equations
and one Table S1 row, and the primer one subsection with a summary-table row.
The rebuilt article, supplement and primer have 45, 40 and 84 pages against 44,
39 and 82. Final logs have zero warnings and overfull boxes, with underfull
counts matching fresh baseline builds (2, 0 and 29). The changed result and
table pages were visually inspected. The 58-page arXiv submission compiles from
its unpacked archive and passes manifest freshness. `git diff --check` passes.

Still open after this change: preparation of the initial law, a microscopic or
pathwise model of the store and its replenishment, a separately implemented
sensor memory, the register ledger's own premises, fabrication of the readout
and the actuator, optimal-policy convergence, local content agreement, and every
cortical identification. The first of these is now its own ledger item.
