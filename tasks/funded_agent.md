# The source that pays for clearing, and how long it lasts — 2026-09-15

## Intent and constraints

Continue the agency ledger's **Physical preparation and supply beyond the
finite model** item with the piece its last two sentences name: *supplying the
work these operations draw*, and *connecting the finite source to the learning
agent's actual channels*.

`PathwiseStore` (2026-09-15) carries a store as a coordinate of the state and
`SourceLedgered` identifies replenishment with a source coordinate's loss, but
the protocol those run on is `Examples/FiniteSupply.lean`'s three-bit gate
chain: a separate witness, not the agent whose erasure `memoryHeat_const`
prices. `MemoryAgent` (2026-09-15) executes an erasure at every fourth stage
and charges it, but nothing in its state holds the energy that erasure draws.
The two accounts have never been run on one protocol. That is the gap.

Two obstructions are already visible in the existing statements and are part of
what this change has to record rather than route around.

- `horizon_le_of_net_cost` needs a positive net draw on *every* executed
  transition. A four-stage agent draws at one stage in four, so the existing
  bound applies to it only with `c ≤ 0`, which says nothing. The horizon result
  has to be generalized to a cost paid once per period before it can reach an
  agent at all.
- A protocol with `Positive` channels cannot run a ledgered store down. If every
  transition has positive mass then the ledger holds between *every* pair of
  states, in both directions, so the reading is constant and every net draw is
  zero. A fundable agent therefore cannot have full support, and the witness's
  failure to be `Positive` is a consequence rather than a convenience.

Reuse `FiniteProtocol`, `PathwiseStore` and `MemoryAgent`; add no axiom, no
dependency, no Python, no simulation and no reference.

This is one finite agent, one source coordinate and the horizon its charge
buys. It is not preparation of the source or the prior, not gate fabrication,
not an identification of the drawn work with the stage's own log-ratio heat,
and not a cortical identification. Keep those open.

## Model and success criteria

1. **A cost that is not paid every stage.** Generalize
   `PathwiseStore.balance_le_of_net_cost` from a constant `c` to a stage
   function `cost : ℕ → ℝ`, concluding `balance ≤ b - ∑ n ∈ range N, cost n` on
   every state reachable at `N`. Re-derive the existing theorem from it; do not
   leave two inductions in the file.
2. **Once per period.** For `cost n = if n % p = j then c else 0` with `j < p`,
   the sum over `range (p * m)` is `m * c`. State `horizon_le_of_periodic_cost`:
   a run solvent at `p * m` whose `j`-stages each draw at least `c` more than
   they supply, and whose other stages never return more than they draw, gives
   `m * c ≤ b`. State the same through `withSource`, so the bound is on the
   initial combined resources rather than on a store alone.
3. **The obstruction, as a theorem.** `net_draw_eq_zero_of_positive`: for a
   ledgered store on a `Positive` protocol, `draw = supply` on every transition
   of every stage. A positive protocol admits no net draw at all, so no
   full-support agent can be funded by a finite source.
4. **The bridge to the agent.** `MemoryAgent.sourceStore R` is the pathwise
   store whose reading is a declared source coordinate `R` of the agent's own
   state, whose draw is that coordinate's loss on the executed transition and
   whose supply is the same quantity — so it is `SourceLedgered` at `R` by
   construction and `withSource R` is its own combined boundary.
   `MemoryAgent.clearings_le_of_source`: a source that never rises on an
   executed transition, falls by at least `c > 0` at every clear stage, starts
   no higher than `b` and stays nonnegative through `m` complete cycles gives
   `m * c ≤ b`. **A finite source funds finitely many clearings.**
5. **Witness** in `Examples/FundedMemory.lean`, reusing `Examples/SensorMemory`'s
   memory channels so the thing funded is the thing already priced. The world is
   a task flag and a charge in `Fin 4`; the clear stage's world channel spends
   one unit while charged and the other three stages leave it alone. Required
   results:
   - the charge is nonincreasing on every executed transition and falls by one
     at every clear stage that the protocol can execute while charged;
   - `cycles_le_three`: instantiating criterion 4 at `c = 1`, `b = 3`;
   - the erasure's exact cost at every clear stage, from `clear_memoryHeat_const`
     and `Examples.Sensor.erase_cost`, and a recurring floor that holds at every
     cycle and uses no knowledge of the joint law;
   - `not_solvent`: the run is *not* solvent past the charge. The erasure's
     signature `M → ProbDist M` cannot see the world, so the agent cannot stop
     clearing when the source is empty. The model says a continuing run is
     unfunded, not that it halts — record this, do not repair it;
   - `not_positive`, with criterion 3 as the reason: a positive agent's draws
     are all zero.
6. Run failing Lean specifications before implementation and retain them in the
   witness file. Complete the zero-warning full build and axiom audit, the
   applicable gates, publication alignment (article, supplement, Table S1,
   primer), rebuilt tracked PDFs and a refreshed arXiv archive.

## Plan

- [x] Record the red regression run.
- [x] Generalize the cost bound and add the periodic and source horizons.
- [x] Prove the positivity obstruction and the agent-level bridge.
- [x] Build the witness, its horizon, its erasure cost and its two negatives.
- [x] Align publications and rebuild all linked artifacts.
- [x] Complete the build, checks and ledger record.

## Stop rule

Stop at this agent, the periodic horizon bound and the witness. Do not add
preparation of the charge, an external refuelling process, an identification of
the drawn work with the log-ratio heat, gate fabrication, continuous state
spaces or local content dynamics to this change.

## Execution

The working tree was clean at `4b03974`. Baseline tracked artifacts: 52/43/87
pages for article, supplement and primer, zero overfull boxes, underfull counts
2/0/29, and the already-recorded article Table 1 overflow of 22.86668 pt.

The 19 retained specifications were written from the criteria above and run
before any declaration existed: 33 errors, every one an absent declaration.

Two statements changed between the red run and the implementation, both because
the red version was false rather than unproved.

- `clearings_le_of_source` originally asked for the per-clearing cost at every
  stage congruent to three. A ledgered coordinate on a finite state space cannot
  pay a positive cost forever, which is the same non-vacuity trap
  `tasks/finite_supply.md` records for `balance_le_of_net_cost`. The hypotheses
  are restricted to `n < 4 * m`, matching the generic theorem they instantiate.
- `clear_spends_one` is likewise restricted to `n < 16`: past that the charge is
  empty and the clearing is free. That restriction is not a weakening to be
  repaired later — `clear_unfunded` states the same fact positively, and it is
  what the article's second new paragraph is about.

`positive_source_never_falls` also changed shape. Its first form took
`∀ s t, src t ≤ src s`, which already forces a constant reading and proves
nothing; the hypothesis is now monotonicity on the transitions the agent
executes, which is what the witness has and what `Positive` then collapses.

The witness avoids computing any joint law. `charge_invariant` is an induction
over `exists_pred_of_reachable`: the charge after `n` operations is exactly
`4 - n / 4`, because only the clear stage moves it and it moves it
deterministically. Solvency, the per-clearing draw and the sixteenth operation's
negative reading are three corollaries of that one invariant. The erasure's
recurring price needed one new generic lemma — `envLaw_act_sum_le` and its
lower companion — because a world with two coordinates has a flag marginal that
the existing pointwise bound on `envLaw` does not see.

## Completed result and validation

The full `lake build` passes with zero warnings. The default axiom audit covers
3,956 declarations in 61 modules using only `propext`, `Classical.choice` and
`Quot.sound`; twenty explicit `#print axioms` checks on the new declarations
agree. All 19 retained regression examples compile without warnings.

All fifteen pre-commit hooks pass under `uv --project simulations` at the
repository root, including prose, Table S1, figures, staged-PDF freshness, the
arXiv manifest, leaves and placeholder proofs; the Python hooks run and pass
although no Python changed. The 143 existing Python tests pass, with 6 subtests.
`git diff --cached --check` passes.

Two-pass builds give 53/44/88 pages against the baseline's 52/43/87, with zero
overfull boxes and unchanged underfull counts 2/0/29. The article's Table 1
overflow is unchanged at 22.86668 pt; Table 1 was not touched, and that separate
P-item remains open. The 66-page arXiv submission compiles from its unpacked
tarball and passes manifest freshness.

No Lean axiom, Python source, dependency, reference, generated macro or
simulation result was added or changed.

Remaining work in this thread: preparing the prior, the memory's initial law and
the charge itself; fabricating and controlling the gates; identifying the drawn
unit with the stage's own log-ratio heat; and external refuelling. Local content
agreement remains a separate agency task.
