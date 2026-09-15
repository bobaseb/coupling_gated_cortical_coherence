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

## 2026-09-15 — Claims withdrawn when the last three agency items closed

**"Phase order cannot establish compatibility."** The article stated this
without qualification. It is true of descriptions that are free of the phase,
which is what the equal-phase counterexample exhibits: its two mass profiles are
chosen independently of the oscillators, so equal phases constrain them not at
all. It is false of contents that are a declared Lipschitz function of the local
phase, where `compatible_of_coherence` bounds overlap disagreement by a residual
read off the order parameter. The article now states both halves and the fence
between them.

**"The observations' own agreement is the input."** The Discussion said the
acquire half of the explanatory gap was untouched, and the supplement said no
theorem derived observation compatibility from task reward, phase coherence or a
shared target state. A theorem now derives it from phase coherence. The encoder
and its Lipschitz constant remain declared; the agreement does not.

**"The drawn unit is a declared reading, not the stage's heat."** The resource
ledger's thermal identification was a free hypothesis: `draw_eq_thermal_work`
substitutes any real number written `θ * log ratio`. `draw_eq_step_heat` ties it
to a named channel's mean heat, so the ledger's heat term is that step's own
`bathEntropy`. The claim that the identification is unavailable is withdrawn;
the claim that gate fabrication and control are unpriced stands, and is now
visible in the statement of `draw_ge_entropy_reduction`, where `C` is subtracted.

**"Equality with Mathlib's measure divergence is separate."** Recorded as an
open leftover under the weaker-positivity work. `extendedKL_eq_klDiv` and
`extendedKL_eq_klDiv_of_missing` close it on both branches, so the finite
convention is the measure-theoretic divergence restricted rather than a second
definition beside it.

**"The entropy balance remains finite-state."** Withdrawn in one direction and
retained in the other, which is why it is here rather than simply deleted. The
*divergence* form generalizes to an arbitrary measurable space
(`path_divergence_splits`). The *Shannon-entropy* form does not, and is not
claimed to: it needs a reference measure, and differential entropy relative to
Lebesgue measure is not entropy. The retained half is stated in the module
docstring, the ledger and Table S1 in the same words.

The full pass record is the dated section at the end of `tasks/todo.md`.

---

## 2026-09-15 — Four scope sentences the foundations narrow

The finite path-law balance is no longer stated with strictly positive masses
as its premise. The article said "strictly positive forward and reverse path
probabilities give" the entropy balance and its sign, and the supplement said
"the theorem assumes strictly positive initial masses and transition
probabilities". Both now state the condition the expansion actually uses: every
forward path of positive probability has positive reverse probability. Strict
positivity implies it and is not implied by it, and the gap is witnessed by a
step whose initial law sits on a single atom. Where a forward path has no
reverse, the divergence is infinite and is carried in the extended
nonnegatives, rather than as whatever finite number a totalized logarithm
returns.

Two sentences placed external refuelling outside the model. The pathwise store's
horizon bound needs no finite state space at all: it is a ledger on a trajectory,
and the expected-work horizon is that bound read on the sequence of allowances.
A real-valued reading whose delivery matches its draw is solvent at every
operation. The supply is still declared and still unconnected to any particular
agent's channels, which is what the rewritten sentences now say instead.

The explanatory-gap paragraph asked why cortical activity should "acquire or
preserve" compatibility and treated both as open. The second half is now
answered under a stated hypothesis: patch contents mixed with their own
observations preserve exact agreement and contract mismatch geometrically, with
an explicit residual floor when the observations themselves disagree. The first
half is untouched, and the paragraph says so — the observations' agreement is
the input to that result.

Specification and validation: `tasks/agency_foundations.md` and the dated
`tasks/todo.md` record.

## 2026-09-15 — Preparation enters the agent's law sequence

Preparation of a declared prior is no longer absent from every finite-agent
account. `FiniteProtocol.withPreparation` prepends a channel, identifies the
subsequent laws with the original run when it reaches the declared prior, and
reuses the existing balances. `Examples/Preparation.lean` prepares the
sensor-memory agent's uniform prior from a different positive hardware law and
includes it in the cumulative entropy bound. The parameter's uncertainty is
still supplied; a constant hardware channel cannot create parameter-system
correlation.

The interrupted draft described uniform preparation as free and its bit-family
divergence as excluding every sharp law from finite-cost preparation. Those
claims have been narrowed to the proofs: uniform preparation has zero mean
log-ratio heat; implementation and control work are unaccounted for. The
positive bit family is unbounded from uniform input at thermal scale one, and
its sharp endpoint fails the entropy identity's positivity premise. No universal
exact-preparation obstruction follows, and other modules do admit zero masses.

The article, supplement, Table S1 and primer now use that scope. Funding the
preparation, preparing the charge, gate implementation, reservoir identification
and external refuelling remain separate. Specification and validation:
`tasks/preparation.md` and the dated `tasks/todo.md` record.

## 2026-09-15 — The source that pays for the clearing

Four scope sentences are no longer written. The article, the supplement, Table
S1 and the primer each said that supplying the work the sensor memory's
operations draw, and connecting that memory to the finite source, were outside
the model. One coordinate of the agent's own world now carries the charge those
operations spend.

The generic half is that the store's reading bound now takes a cost that depends
on the stage, so an agent paying at one operation in four is describable at all:
`balance_le_of_stage_cost`, with the constant case derived from it rather than
proved twice, `sum_period_indicator` and `horizon_le_of_periodic_cost`. The
obstruction is recorded as a theorem in the same file:
`net_draw_eq_zero_of_positive` proves that a protocol whose channels all have
full support admits no net draw at all, so the funded witness's restricted
support is forced.

Two things the model does not do are stated in all three documents rather than
repaired. `erase : M → ProbDist M` reads only the memory — the fence that makes
its cost well defined — so it cannot be conditioned on the charge, and past the
funded horizon the agent keeps clearing, keeps costing at least `(3/16) log 3`
and draws nothing: the run is unfunded, not halted. And the unit drawn is a
declared reading of the state, not the stage's log-ratio heat; identifying them
needs the reservoir's own energy as a coordinate.

Specification and execution record: `tasks/funded_agent.md`.

## 2026-09-15 — A sensor memory, and what clearing it costs

Four scope sentences are no longer written. The article said the observation was
marginalized inside the learning channel and a separate sensor-memory
implementation was outside the model; the supplement and Table S1 said the same
in three places, and the primer's scope paragraphs said the learning channel's
local detailed balance derived no separate physical sensor memory or its
erasure. The measurement now has a register of its own.

`Phase3_SensorMemory.lean` proves the exact cost of clearing it: for an erasure
that lands on one declared law, the memory's heat is the entropy removed plus
the relative entropy of what the memory held from the state it is driven to.
Landauer's inequality is the Gibbs corollary of that identity, and the identity
says two things the inequality does not — a matched memory is free to clear,
and a memory more ordered than the standard state draws heat out of the
reservoir. `MemoryAgent` runs act, record, learn and clear as four stages of an
ordinary `FiniteProtocol`, so the existing cumulative balances charge the whole
run; the clear stage's heat is allocated to its three coordinates, and the
memory's share is identified with that identity on the agent's own paths.

The recurring cost is established from channel masses alone, with no joint law:
the memory's mass at every clearing lies in `[7/16, 9/16]`, so every cycle pays
between `(3/16) log 3` and `(5/16) log 3` whatever the agent has learned. A
blind measurement leaves the same marginal and pays the identical heat, so the
cost is set by the memory's marginal and not by what the memory is about.

Preparing the prior, fabricating the gates, supplying the work these operations
draw and connecting this memory to the finite source above remain open.
Specification and validation: `tasks/sensor_memory.md` and the dated
`tasks/todo.md` record.

## 2026-09-15 — A finite source behind replenishment

The resource discussion no longer leaves every microscopic supply model
outside the development. `PathwiseStore.SourceLedgered` identifies supply
with a finite source's actual energy loss; including the source in the resource
boundary cancels internal replenishment and bounds work by the initial combined
resources. A reversible source/buffer/load witness conserves total energy and
delivers a unit on only half its paths, so initial capacity is not delivery on
demand. The earlier unbounded charger cannot have a nonnegative finite source
coordinate satisfying that identity.

The pathwise horizon bound also has a weaker, realizable premise: positive
cost is required only before the chosen horizon. Requiring a uniformly
positive net draw at every natural-numbered stage is impossible for a finite
state coordinate. A one-stage depletion followed by idling instantiates the
bounded theorem and rejects the unbounded premise.

Preparation, gate-control costs, external refuelling and sensor memory remain
open. This finite source is not identified with the observational learner's
actuator or its heat reservoir. Specification and validation:
`tasks/finite_supply.md` and the dated `tasks/todo.md` record.

## 2026-09-15 — A store on the trajectory, and what replenishment buys

Two scope sentences are no longer written. The article said that the continuing
agent's accounting was in expectation and that no pathwise battery guarantee
followed; the primer's scope paragraph said the allowance was not a battery on
every sample path and left it there. A pathwise account now exists, so both
sentences point at it instead — and the thing they were fencing is now a
theorem in the other direction: an expected allowance that is never exceeded
does not imply solvency on the paths the process has, and there is a witness
where it fails at probability one quarter.

What changed is where the store lives. `ContinuingProcess.stored` is a number
outside the process, compared against a mean, so what it bounds is a mean.
`PathwiseStore` carries the store's reading as a coordinate of the state, which
makes `Solvent` a claim about the states the protocol reaches. Nothing about the
mean ledger is withdrawn: `mean_balance_eq` derives the expected identity from
the same pathwise one through `sum_energyTransfer`, and
`totalDraw_le_of_solvent` shows the pathwise claim implies the expected bound.
The refinement runs one way only, and the gambler witness is the proof that it
does.

The replenishment half was previously a fence in prose — "sustained operation is
a claim about replenishment, which the store does not make" — with nothing on
either side of it. It now has a sufficient condition, a necessary one, and a
witness strictly between them whose cumulative draw exceeds any declared
allowance while it stays solvent at every horizon.

Still not claimed: preparing the initial law, a microscopic or fluctuating model
of the supply itself, a separately implemented sensor memory and its erasure,
and every cortical identification. The supply is a declared input, exactly as
the initial store was.

Recorded in `tasks/pathwise_store.md`; two Lean lessons in `tasks/lessons.md`.

## 2026-09-14 — The register's bath, and what a map-indexed budget needs

Two scope sentences are no longer written. The article said that deriving the
register ledger's accounting identity from a microscopic bipartite dynamics was
a separate model, and the primer said the same in its ledger scope paragraph.
The model now exists, and what it establishes is a negative: a reversible
register/bath gate delivers the erasure heat and supplies neither of the
ledger's two physical inputs. Both sentences state that instead.

`Examples/RegisterBath.lean` carries each of the four maps of a register bit to
a permutation of register and bath that performs it on a bath prepared pure.
Heat is the bath's actual mean energy gain on the executed paths: `log 2` for
the two erasures, `0` for the two injective maps, at bath levels `0` and
`2 log 2`, degenerate register levels and thermal scale one. Those values
inhabit `StatisticalMechanics Bool` with the reachable bath supports, so the
instance is sharper than `Examples/Bit.lean`'s, which charges `log 2` for every
map including the identity. It is `local` to its file, and that witness and its
consumers are unchanged.

`FiniteProtocol.energyTransfer`, `sum_energyTransfer` and `reported_heat_eq`
(`Phase3_ContinuingAgent.lean`) give the bath's ledger for any finite protocol:
the stage transfers sum to the bath's endpoint gain, with no positive support
and no thermal identification, and a reported heat ledger differs from that gain
by the transfer it omits. No entropy inequality comes out of either.

Three results fence a heat budget indexed by the register's map. The same
erasing gate executed twice returns the `log 2` and restores the prepared law,
with shares `log 2` and `-log 2` about a total of zero, so an eraser is reusable
only if something prepares its bath again. A second reversible gate holds the
register fixed and excites its bath, performing the same register map as idling
at `2 log 2`; the work is `log 2` for one erasure, `2 log 2` for that drive and
zero for two erasures. And a swap is an involution, so the gate's transition
log-ratios vanish on every realized path while its bath gains `log 2`, and a
deterministic channel, which sends one state to one state, is not strictly
positive.

This constructs no `RegisterLedger` and weakens no result that consumes one.
Positivity, local detailed balance and the accounting identity remain the
physical inputs `Examples/RegisterBudget.lean` supplies. Preparing the bath,
supplying the work, fabricating the gate and identifying this bath with the
reservoir the ledger's operations exchange heat with are open, and no cortical
identification follows.

---

## 2026-09-14 — Sequenced episodes with a finite expected-work allowance

The open continuing-agent item is closed for a bounded finite model.
`FiniteProtocol` runs different stages on one evolving law and telescopes
their entropy and first-law balances. `ContinuingAgent` sequences an actual
register-driven actuator, observation-driven learning and reset.
`ContinuingProcess` bounds the whole run by a declared initial store plus
the system's mean energy drop. The witness learns above chance, pays for reset
and has a positive recurring work cost; its store funds the first cycle but
cannot fund 22 complete cycles. The same funded stages inhabit `ActiveBound`
without identifying their store with the register ledger's erasure heat.

The interrupted witness had an incorrect coefficient in its composed law;
direct composition fixes it without changing the channels or planned cycle
map. Its proposed reset-control claim was too strong: replacing reset by idle
drift reduces later reward but does not eliminate learning or create an
absorbing saturated flag. The proved control states that narrower result.

The store bounds expectations at every prefix, not batteries along individual
paths. Preparing the initial law, constructing or replenishing the store,
implementing a separate sensor memory and fabricating the hardware remain
outside the model. Local detailed balance is a physical input for each
composite stage. No general optimality, full active-chain physical realization
or cortical identification is claimed.

---

## 2026-09-14 — A register learns a task nobody told it about

Four sentences are no longer claimed. The article said that "learning unknown
rewards from observations" required additional accounting; Table S1's learning
row listed "learning unknown rewards" among the separate work; the supplement
said "learning unknown values" required further models; and the primer said
that "measuring unknown rewards" needed its own physical accounting. Each was
true of the policy-register model, whose energy landscape is built from rewards
that are already known. None of them is true of the repository any more.

`FiniteObservationalLearner` (`Phase3_ObservationalLearning.lean`) holds an
environmental parameter fixed and unknown, reads the register out as the
executed action, and updates the register from the observed outcome of that
action. The fences are signatures: `update : O → R → ProbDist R` and
`readout : R → A` have no `W` argument, so no channel can consult the parameter
and no precomputed policy value can be decoded into the action; `reward` enters
`performance` and nothing else. Act–observe–update composes into a single
`FiniteFeedbackStep`, so the existing entropy balance, local detailed balance,
first law and their telescoped sums apply to exactly the process the reward is
read from.

`Examples/ObservationalLearning.lean` witnesses it on a two-action task whose
rewarding action is an unknown bit: every mass of the joint law in closed form,
expected reward of the executed action rising strictly from `1/2` to `3/4`,
strict improvement over both a frozen register and an uninformative world under
one allowance, and cumulative heat `(log 3/4)[1 − (1/2)^N]`.

The result that makes this a different model rather than the previous one
relabelled is negative.
`zero_work_needs_parameter_independent_heat` proves that a register energy
giving zero path work forces the drive's heat to be the same at every parameter
value. A drive that behaves identically in both environments cannot be what
tells the register which one it is in, so the work spent here is irreducible:
an energy landscape that paid for this learning would be one that already
encoded the answer. Policy relaxation toward supplied values is free; learning
from experience is not.

What is still not claimed: preparing the prior, supplying that work, task
episodes beyond the declared updates, fabricating the readout, convergence to
an optimal policy, and any identification of these variables with cortical
ones. The learner also acquires no preference between the two actions — it
executes each half the time at every horizon — only a correlation with the
parameter.

---

## 2026-09-14 — A coupling kernel is constructed, not assumed

Two sentences are no longer claimed. The article's status table said "kernel
construction remains open" for E45/E45Active, and Table S1 said that a genuine
kernel limit "requires new architecture" before anything further could be
stated. The architecture now exists. `LocalActuator` gives finitely many
spatial response modes whose occupancies determine both a reciprocal kernel on
`M × M` and a stored installation energy, so an executed transition changes the
kernel through the modes it changes and pays for them; `KernelMesh` carries
cell *pairs* rather than edges, reconstructs the kernel throughout each pair,
and converges to its product-measure integral under shrinking sample error.
Both spatial edges are discharged on their named laws — the active one on an
executed step's final law, the passive one on a declared predictive system's
joint law — and the active chain composes through the result.

`Chain.lean` §9's negative result is not withdrawn and did not need to be. It
says that *triangulation* coarse-graining converges a scalar, that
`edge_region` offers no product structure, and that a vertex-sited kernel is
invisible on an atomless substrate. The cell-pair construction answers each of
those separately rather than repealing any of them, and the unit-interval
witness is atomless precisely so that this is checkable.

What replaced the gap is hardware, not a derivation from thermodynamics. Mode
profiles, prices, occupancy readout, the reservoir convention and the substrate
measure are declared; no heat bound supplies them, and neither does predictive
efficiency — two declared predictive systems differing by their whole
dissipated work install the same kernel and discharge the identical edge. One
prepared update is accounted for. Specification and verification:
`tasks/e45_kernel.md`.

## 2026-09-14 — A named feedback step sets a scalar coupling amplitude

The active chain's spatial energy sequence can now be constructed from its
named feedback process. `ActuatedCoupling` supplies the constitutive law
`density x = gain * [H(initial) - H(final)] * base x`. Mesh refinement proves
convergence of that sequence, and the same process's heat budget bounds its
continuum limit through the gain and profile integral. The noisy two-bit
witness has positive drive and changing grid energies; changing the process,
gain or profile changes the outcome. The active chain composes with the
actuated sequence after a stated calibration to the existing field witness.

This replaces the absence of a process-to-density relation with a specified
scalar model, not with a derivation of a microscopic coupling mechanism. The
gain, profile and use of ensemble entropy reduction remain constitutive inputs.
The budget does not cause spatial convergence, pay for a separate actuator, or
construct a kernel. The broader E45/E45Active task remains open with that scope.
Specification and verification: `tasks/e45_active.md`.

## 2026-09-14 — The active chain's heat allocation is derived, not assumed

The n3 → n4 edge's upper-budget allocation was a bridge assumption, discharged
on the witness by comparing an actuator's heat with an unrelated register's
Landauer heat. It is now a consequence of a named resource model. A
`RegisterLedger` holds one register's update, its operations as elementary
steps controlled by that register, local detailed balance for each at that
register's own temperature, and the identity that the register's dissipated
heat is the total its operations deliver to its reservoir. An operation that
does not increase the joint entropy has a nonnegative share by the path model's
own second law, so an operation whose companions all compress has a share no
larger than the register's dissipation.

The claim the supplement no longer makes is that this allocation is an
assumption of the composition. What it now names as assumptions are the
accounting identity and that compressiveness, both statements about one
register, and both fenced by regressions: a compressive operation of the
witness family exceeds the whole dissipation, and a second ledger whose other
operation draws heat out of the reservoir over-allocates its controlled one.
Sequencing the operations into one evolving law, a continuing power source and
the coupling-convergence assumption of the next edge remain separate. See
`tasks/e34_active.md`.

## 2026-09-14 — Finite policy selection at a supplied heat budget

The feedback development now selects among fixed deterministic policies for a
declared finite task. Reward and both substep costs use each policy's actual
L1 cycle. The lamp witness proves a unique feasible optimum that doubles
success over an equally costly baseline; a stronger policy exceeds the budget.
Equal final laws can have different heat costs, and budget feasibility alone
does not ensure the task target.

This closes L2's finite control result. The objective and budget remain model
inputs; learning, policy installation and switching, biological identification
and the active chain's resource and spatial bridges remain separate. The
article, supplement, primer and their tracked PDFs carry the result and its
scope. See `tasks/agency_control.md`.

## 2026-09-13 — Complete finite perception–action accounting

The generic feedback result now composes actuation and memory update using
the same intermediate joint law with an explicit coordinate swap. Its output
equals the composed perception–action channel law. Total entropy, heat and
mean-energy balances follow without assuming stationarity, and an upper budget
on total heat bounds the complete update's joint entropy decrease.

The reciprocal two-bit calculation specializes the theorem. A biased witness
exposes the swap, changes under sensing and rejects a positive but incompatible
second step. This closes L1, not the register-to-actuator allocation or the
coupling-convergence assumption of the active chain. Extra registers, protocols
and learning remain separate modelling tasks. See `tasks/agency_cycle.md`.

## 2026-09-13 — Scope of predictive thermodynamics for acting agents

The thermodynamic discussion distinguishes the passive predictive-memory bound
from feedback. The new channel construction makes policy, actuation, observation
and memory update explicit. A signed information identity recovers the passive
result when its feedback term vanishes and admits actions that create future
correlations. A finite path-law construction derives a joint entropy balance;
local detailed balance supplies the heat interpretation. Reciprocal two-bit
examples check information, heat, interaction energy and work on the same paths.

The passive composition retains its predictive fourth node. The follow-up
`chain_active` carries a specified feedback process, actual heat and budget
through an active fourth node; both branches share the downstream composition.
Its two new bridge predicates leave the physical budget allocation and the
connection to coupling convergence explicit. A noisy actuator witnesses the
branch, and zero-budget and incompatible-limit checks fence it. Neither branch
derives a cortical policy or thermodynamic selection of convergent couplings.
Details and verified references are in `tasks/agency.md` and
`tasks/agency_chain.md`.

## 2026-09-11 — Audit remediation, part F concluded: three claims of more than was measured

The follow-up audit's remaining wording corrections. Each is a place where a
correctly computed number was described as settling more than it settles: two
controls said to be matched by construction, a fit whose window was excluded as
a source of bias, and a grid refinement read as convergence.

Claims that were made and are no longer made:

- That the plasticity controls share the gradient arm's step size, and that the
  permuted arm reproduces its cumulative deformation. Every arm computes its
  direction from its own phases and couplings: the random arm is scaled to its
  own gradient and the permuted arm relabels its own gradient, so no control
  receives the gradient arm's contemporaneous step. The step sizes the shared
  rule produces are comparable, not equal — in the production replays the mean
  direction norm is about 43 on the gradient arm against about 35 on the random
  arm — and what supports the comparison is the observed overlap of the
  permuted and gradient arms' norm-growth and order ranges, which the work
  already reported, rather than an equality imposed by construction.
- That the growth-rate slope's shortfall from 1/2 "is therefore not a property
  of the fit window". The window's upper bound is half the stationary branch
  order rather than the extent of the linear regime, and a deterministic
  mean-field Fourier diagnostic with no finite population and no
  Euler--Maruyama integration returns 0.466531 under that bound against
  0.489995 under half of it. The step-size control apportions bias in the
  stationary order, not in this growth estimator; the window, finite size and
  the integrator all contribute and the sweep separates none of them.
- That the spatial-decay boundary is a property of the dynamics rather than of
  the discretisation, and that the finer sheet resolves it. What the one
  refinement shows is that the operational crossing barely moves: 1.01 times
  its coarse value, still only 1.81 cells wide. Two threshold interpolants
  agreeing is not convergence of the sheet near them — at 0.01467 mm, the
  shortest length from which both sheets stay coherent, steady order is 0.6176
  on the 128² sheet against 0.2687 on the 256² one.

What is unchanged: the two controls and every result read off them, the measured
production growth slope and the qualitative escape result, both reported spatial
crossings, the metastability qualification and the finding of coherence in the
sampled empirical band. Nothing was rerun; the two near-boundary steady orders
are new macros generated from the saved sweep summaries.

## 2026-09-10 — Audit remediation, part F: what the plasticity readout measures

Two bounded studies declared before execution in `tasks/f5_f6_design.md`, and
the sampling correction the first of them generalises. In the plasticity run,
diagnostics are sampled at the update cadence and the update acts first, so
every objective mean the work reported was a mean of the instant after an
update. Recording the objective at every integration step and averaging over
complete update intervals gives a different number, and F5 ran a declared grid
of six rate/cadence combinations to ask whether any regime holds the reduction.

Claims that were made and are no longer made:

- That these runs exhibit sustained minimisation of the squared-drift
  objective. The reduction is a property of the sampled instant. At the
  production rate and cadence the post-update second-half mean is 1118.95 where
  the complete-interval mean is 1383.87 against a frozen arm's 1383.06 — ratios
  of 0.998 and 1.003 in the two windows. What the update takes off, the interval
  that follows returns.
- That some declared plasticity regime is known to supply the antecedent of the
  strong counterexample: sustained reduction, coherence and loss of alignment at
  once. None of the six cases reaches the declared 5% sustained reduction; the
  best manages 1.22% and 1.36%. Coherence and the loss of alignment do appear
  across the grid, and the stop rule forbade widening it. A bounded grid that
  does not find such a regime does not show that none exists.
- That an awakening experiment could separate the recovery mechanisms from
  coherence traces. It cannot. The stationary density is von Mises with
  concentration K*r/D, so a coupling increase, a diffusion decrease and an
  uncoupled ensemble under a matched common drive agree on every stationary
  observable window for window — exactly, not approximately: over 18 ideal cases
  the three families return the same endpoint to within 8.9e-16 and no case
  identifies a unique generator. The protocol now says what is missing, which is
  the physical clock the phase increments carry, plus a measured drive or a
  controlled perturbation to separate endogenous coupling from common forcing.

What is unchanged: the observed coherence, the loss of alignment against the
frequency partition and against partitions drawn blind to it, the two controls
and their results, the conservation-law argument that fixes the direction of the
failure, and the fixed-phase descent theorem. The saved production numerals are
retained and nothing was rerun to reach any of this.

## 2026-09-10 — Audit remediation, part D concluded: what the descent moves against

A second partition of the same nodes, and the family it belongs to. The
plasticity result reported one pairing in which the template is literally the
frequency-cluster indicator and the objective provably anti-aligns with it, and
generalised from it. Two readings now separate the two things that pairing
confounds: an interleaved partition of the same group sizes, balanced against
the frequency clusters so that it carries no frequency information, and the
frequency partition's within-over-between ratio scored against 2000 relabellings
of itself. Both are diagnostics on saved kernels; neither enters the update.

Claims that were made and are no longer made:

- That the descent moves away from the environmental structure, full stop. It
  moves away from the partition the environment carries, and against partitions
  drawn blind to frequency the loss does not appear: at most 0.0495 of 2000
  blind relabellings give a lower ratio than the frequency partition does, on
  every seed, where the frozen arm's untouched kernel gives 0.0755 to 0.3480.
  The distinction is the one worth having — the descent is opposed to the
  environment's own structure rather than indifferent to structure — and it was
  asserted before it was measured.
- That descending the functional does not produce representational learning,
  without qualification. The abstract now attaches the claim to this pairing of
  objective and template, which is what the evidence covers.

Also recorded: a single alternative template is uninformative on its own here.
The gradient arm's interleaved ratio runs 0.807 to 3.022 across three seeds,
because concentrating a fixed resource onto few edges makes any ratio of block
means fluctuate widely; that value sits inside the blind family and is reported
with it rather than on its own.

## 2026-09-10 — Audit remediation, part D: a control matched on deformation

One new control arm. The plasticity run's specificity claim rested on a random
arm matched to the gradient arm on per-step Frobenius norm, and part B recorded
that this matches the step size without matching what the steps accumulate: the
random arm's fresh isotropic draws cancel, leaving it at a kernel norm growth of
about 1.3 where the gradient arm reaches 12.4 to 14.7. The fourth arm takes the
gradient step itself under a node relabelling drawn afresh at each update. A
relabelling is an isometry of the matrix and a bijection of the edges, so the
step keeps the gradient's norm and the whole multiset of its entries and changes
only which edges receive them.

Claims that were made and are no longer made:

- That a matched-norm random arm is the control the specificity of the descent
  needs. It is one of two. The permuted arm reproduces the gradient arm's
  cumulative kernel deformation (11.4 to 16.3 against 12.4 to 14.7) and its
  second-half order to three decimals, and neither descends the objective nor
  loses cluster alignment, so the two controls now separate the step's size, the
  deformation it accumulates and the direction it points in.

What the new arm shows, none of which reverses a published finding:

- A step of the gradient's magnitude and shape delivered to the wrong edges
  *raises* the squared-drift objective, by 16 to 33 per cent of the frozen arm's
  headroom above the drive floor. The random arm's isotropic steps leave it
  within 2 per cent of the frozen arm; the difference is that the permuted step
  is structured and consistently mis-targeted rather than self-cancelling.
- Within-over-between coupling under the permuted arm lands at 0.729 to 1.294,
  a range that contains the no-preference line and does not overlap the gradient
  arm's 0.351 to 0.614. Its typical value sits a little under one because with
  three clusters two thirds of the node pairs are between-cluster, so a dominant
  edge lands between more often than within.
- Against 2000 node relabellings the permuted arm's final kernel reaches 0.268
  to 0.841, at or below the frozen arm's 0.644 to 0.911, where the gradient arm
  reaches 0.951 to 1.000.

The nine pre-existing runs were reproduced bit-identically by the rerun, the new
arm drawing from the update stream that the gradient and frozen arms do not
touch. `tasks/todo.md` carries the prediction registered before the arm was
implemented, the two designs rejected for failing the matching criterion, and
the one prediction the run falsified.

## 2026-09-10 — Audit remediation, parts B and C: the reference and the cause

Eight corrections. Six read a derived quantity out of an artifact the repository
already had; two reran a sweep. As in part A, what moves is the reference a
number is measured against or the cause it is assigned to.

Claims that were made and are no longer made:

- That the onset estimator's target is the asymptotic exponent 1/2. The declared
  fit window reaches far enough past threshold that the estimator returns about
  0.44 on the exact stationary branch, whose exponent is 1/2 by construction.
  The measured exponents are now read against that generated reference, so the
  ramp effect and the window bias can be separated.
- That the four onset exponents are one quantity measured at four speeds. Each
  leg realises a different part of the declared window, and at the fastest ramp
  the ensemble mean never reaches the window at all, so the number returned
  there is a local log-slope rather than an onset exponent. Both documents now
  report the realised order range, coupling range and sample count per leg.
- That the shift parameter returning at its lower bound distinguishes the
  fastest fit. It is returned at the bound on every leg, and the count is
  generated rather than asserted.
- That the threshold delay's dependence on population size agrees with the
  predicted square-root-of-log law. Divided through, the three sizes do not
  collapse onto a constant; the spread is dominated by a fixed absolute escape
  criterion meeting a size-dependent critical fluctuation floor. Only
  monotonicity is claimed, and the control is reported as a demonstration of the
  measurement hazard the protocol warns about.
- That the spatial sweep's critical decay length lies about sevenfold below the
  empirical band. It is 0.90 lattice spacings on the sheet it was measured on,
  and the criterion is crossed entirely below one cell, so the boundary carries
  no resolution-independent content. What the sweep does show is now stated: the
  empirical band sits inside a plateau that runs out to four times the sheet's
  extent.
- That the frustration crossing is located to five significant figures. It is
  interpolated across one step of a geometric grid of ratio 1.136; the bracket
  that step spans contains the model's own mean-field threshold, so the run does
  not separate the crossing from the threshold. The quoted precision is cut to
  what the grid supports, and the fluctuation-amplification result in the same
  run is joined to it rather than left in an adjacent paragraph.
- That the matched-norm random arm controls for motion of a kernel at fixed
  resource. The arms are matched on the per-step direction norm, and successive
  isotropic steps cancel, so the random arm ends an order of magnitude less
  deformed and barely enters the sparsification channel the descent is explained
  by. The control's scope is stated, and the overlap between the reported seeds
  and the seed the learning rate was tuned on is disclosed.
- That the steady-order gap at K = 2.8 is a finite-size discrepancy. A
  step-size series at fixed duration assigns the bulk of it to Euler--Maruyama
  bias. The series has not converged at the finest step run, so the residual
  there bounds the finite-size part rather than measuring it, and it is reported
  as a bound.

Also changed, without a claim moving: the early-growth fit window is now defined
relative to the finite-size floor below and the static coherent branch above,
rather than as a fixed interval that opened on the noise floor and closed inside
the nonlinear regime. The refit leaves the slope short of 1/2. Because the sweep
still runs at the production step, the residual is not attributed to finite size
alone.

---

## 2026-09-10 — Audit remediation, part C concluded: two grids refined

Two reruns of existing sweeps at finer resolution. Each was run to decide a
question the coarser grid had left open, and one of them reverses a reading made
the same day.

Claims that were made and are no longer made:

- That the spatial sweep's boundary carries no resolution-independent content.
  It was withdrawn earlier today on the ground that it sits below one lattice
  spacing on the sheet that measured it, and therefore might be an artifact of
  the discretisation. Halving the spacing — a 256x256 sheet over the same 2.0 mm,
  everything else identical — leaves the boundary at 1.01 times its value in
  millimetres and twice its value in cells, where a discretisation artifact would
  have halved in millimetres. Reproducing the coarse sheet's lattice-spacing
  counts does not reproduce its boundary: every length in that set is incoherent
  on the finer sheet. The boundary is a physical length at this coupling,
  diffusion and frequency spread, and the finer sheet resolves it. The plateau
  statement that replaced the withdrawn margin is unaffected and remains the
  stronger claim about the empirical band.
- That the frustration crossing is located only to one step of a geometric grid
  of ratio 1.136. That step is now subdivided linearly into tenths and rerun on
  the same three seeds. The bracket the three seeds jointly support is
  [1.958, 2.009] in K_eff/D, and it still contains the model's own mean-field
  threshold K_c/D = 2. A tenfold finer grid does not separate the crossing from
  the threshold at N = 500, which is the result and not a failure of the run.

Also changed, without a claim moving: the refined spatial band carries two
lengths past the crossing. The criterion asks for a crossing above which every
larger sampled length stays coherent, and the band as it was first defined
ended at the crossing itself, leaving that clause resting on a single sample.

---

## 2026-09-09 — Audit remediation, part A: what the numbers were said to mean

Seven corrections to statements that were transcribed correctly and read wrongly.
No headline claim moves; in each case what changes is the reference a number is
measured against, the cause it is assigned to, or where an assumption lives.

Claims that were made and are no longer made:

- That $I_1/I_0$ and its tangent $a/2$ separate by more than 0.17 at $a = 1.5$,
  and that the curve departs from $a/2$ by at most 0.0094 over the observed
  concentration range. The separation at $a = 1.5$ is 0.154 and 0.17 is first
  reached at $a = 1.56$; the departure is 0.0095. These were the only
  hand-computed numerals in either document, and they are now generated by
  `empirical_collapse.tangent_separation` through `simulation_tex.py` with a
  drift test, so the mechanism that produced the error is gone with it.
- That the plasticity permutation percentile stands on its own. It is now read
  against the frozen arm's 0.6435--0.9110 on the same seeds, as the supplement
  already said it must be, and not against a null median of one half.
- That a *common* toy model satisfies the eight chain hypotheses. One witness
  satisfies all eight at once, assembled from a double well, a register, a
  uniform-grid mesh and a three-site cortex that remain distinct toy systems —
  which is what `Chain.lean`'s own docstring says.
- That `resonanceRate`'s exponent is the relaxation rate of the mean-field order
  parameter about the coherent branch. $(K-K_c)/2$ is the growth rate of the
  incoherent state's instability; the coherent branch relaxes at $(K-K_c)$,
  twice as fast. The error was conservative — the assumed Lipschitz constant is
  the larger of the two, so the hypothesis is weaker than it could be — and no
  theorem changes. Corrected in `main.tex`, the supplement, `Chain.lean`'s `E89`
  docstring, `Phase6_ReflexiveTopology.lean` and the primer.
- That `E78` supplies a cover carrying compatible local states. `E78` reads
  `Coherent K D → T.IsReachedByRelaxation K`: the cover is a separate argument of
  `chain` and its overlap-compatibility obligation is a class field, so the
  load-bearing assumption of the unity-is-not-synchrony argument sits outside
  the eight edges. Table 1, the figure note, Table S1 and the primer now say so,
  and the manuscript's "eight hypotheses it consumes" is qualified with the two
  structures the theorem also takes.
- That `fermi_params.tex` carries a `D`. Its parameter is the Lorentzian
  half-width of the frequency spread, read against the noiseless threshold
  $K_c = 2\gamma$; every macro is renamed accordingly, so nothing there can be
  divided into the identical-frequency noisy theory that `main.tex` forbids.

References: Townsend et al. (2015) and Xu et al. (2023) now resolve to verified
`\bibitem`s, the Kawai and Still citations are `\cite`s rather than inline
journal details, and `shenker2000` is recorded as the PhilSci-Archive preprint
that can be verified rather than a journal placement that cannot.

Also: `prepare_arxiv.sh` now boxes each citation group in the merged document.
A citation link broken across a page break aborts pdfTeX outright, and which
citation lands on a break depends on every word before it — so the prose edits
above were enough to make the submission unbuildable until this was fixed.

Reasoning and criteria: `tasks/todo.md`, section A.

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
