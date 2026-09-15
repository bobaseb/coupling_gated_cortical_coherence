# A separately implemented sensor memory, and what clearing it costs — 2026-09-15

## Intent and constraints

Continue the agency ledger's **Physical preparation and supply beyond the
finite model** item with the piece it names first: a sensor memory that is an
actual coordinate of the agent's state, written by the observation, read by the
register update, and cleared by an executed operation whose cost is charged to
the same run.

`ContinuingAgent.learnStage` composes sensing and updating into one channel and
discards the observation between them (`Phase3_ContinuingAgent.lean:~`, "The
intermediate observation is not retained"). Nothing in the development
therefore carries a measurement outcome in a physical register, and nothing
pays to clear one. That is the gap.

Reuse `FiniteProtocol` and its telescoping accounting; add no positivity
assumption beyond the existing `Positive` pattern, no axiom, no dependency, no
Python, no simulation and no reference.

This is one finite four-stage agent and the cost of clearing its memory. It is
not preparation of the prior, not a cycle-cost composition with the store's
horizon bounds, not optimal-policy convergence, and not a cortical
identification. Keep those open.

## Model and success criteria

1. `MemoryAgent W R M Env A` in a new `Phase3_SensorMemory.lean`, on the joint
   state `R × (M × Env)` with the parameter `W` fixed. Four stages in order,
   four-periodically: **act** (the register's readout drives `actuate`),
   **record** (`record : Env → M → ProbDist M` writes the memory from the world
   the action moved), **learn** (`update : M → R → ProbDist R` writes the
   register from the memory alone), **clear** (`erase : M → ProbDist M` and
   `reset : Env → ProbDist Env` prepare the next episode). Every coordinate not
   being driven drifts. The fences are signatures: neither `record`, `update`
   nor `erase` takes `W`, and `update` does not take `Env`.
2. The fence as a theorem, not only a signature: the learn stage's register
   channel is `update m r` at every environment, so what the register can learn
   is exactly what the memory carries.
3. The memory's marginal `memoryLaw n`, and the one place it is autonomous:
   under the clear stage it evolves by `erase` alone, so
   `memoryLaw (n+1) = (memoryLaw n).bind erase` there. Under the record stage it
   does not — that asymmetry is the content.
4. The clear stage's log-ratio heat splits into the three coordinates' own
   shares. Name the memory's share and state it as an allocation, in the manner
   of `RegisterLedger.opHeat_le_dissipation`.
5. **The exact cost of clearing.** For a memory channel that lands on one
   declared law `ν` whatever it is given, the mean memory heat is
   `θ (H(μ) − H(ν)) + θ D(μ‖ν)`: the entropy removed plus the relative entropy
   of what the memory held from the state it is driven to. Gibbs then gives the
   Landauer inequality as a corollary, with the gap named rather than hidden.
   A memory already at `ν` is free to clear, and a memory more ordered than `ν`
   *absorbs* heat — clearing is not dissipative by construction.
6. Witness on bits, with channel masses `1/4` and `3/4`, so every heat is a
   rational multiple of `log 3`. Required results:
   - the agent is `Positive`, so the whole protocol's accounting applies;
   - bounds on the memory marginal that hold at *every* cycle and use no
     knowledge of the joint law, giving a positive recurring erasure cost
     independent of what the agent has learned;
   - the first cycle exactly, with its three numbers: total cost, entropy term
     and relative-entropy term, summing by the identity of criterion 5;
   - `H(uniform) > H(ν)` proved from `16 < 27`, not from a numeral.
7. Negative controls, each cheap and each fencing a distinct claim:
   - drift in place of erasure: zero memory heat, memory not cleared;
   - a blind `record` producing the same memory marginal: the same erasure cost
     with no information recorded, so the cost is set by the marginal and not by
     what the memory is about;
   - a memory already at the standard state: zero cost;
   - a memory more ordered than the standard state: negative cost.
8. Run failing Lean specifications before implementation and retain them in the
   witness file. Complete the zero-warning full build and axiom audit, the
   applicable gates, publication alignment (article, supplement, Table S1,
   primer), rebuilt tracked PDFs and a refreshed arXiv archive.

## Plan

- [x] Record the red regression run.
- [x] Prove the generic erasure cost and the agent's stage structure.
- [x] Build the bit witness, its recurring floor and the four negative controls.
- [x] Align publications and rebuild all linked artifacts.
- [x] Complete the build, checks and ledger record.

## Stop rule

Stop at this agent, the erasure identity and its witness. Do not add the
cycle-cost horizon composition, initial-law preparation, an external refuelling
source, local content dynamics or continuous state spaces to this change.

## Execution

The working tree was clean at `667ae36`. Baseline tracked artifacts: 50/42/86
pages for article, supplement and primer, zero overfull boxes, underfull counts
2/0/29, and the already-recorded article Table 1 overflow of 22.86668 pt.

The 27 retained specifications were written from the criteria above and run
before any declaration existed: 38 errors, every one an absent declaration
(`/tmp/sensor-memory-red.log`). One of them was a syntax error in the
specification itself — a projection written with a pipeline — and was corrected
in the retained suite; no criterion changed.

The generic module was built in three parts, each compiled before the next:
the erasure cost on a declared memory law, the agent and its stage structure,
then the marginals and the heat bridge. Three points needed more than the first
attempt. Collapsing a product channel's unused coordinates must not expand the
inner product, or `sum_one` no longer applies. `simp_rw` reaches a fixpoint, so
a repeated rewrite in the same list fails as "no progress" rather than helping.
And `prod_collapse_weighted` cannot infer its `Fintype` instances from the goal
through `_`, because the collapsed coordinates appear only under the sum.

The recurring floor is proved without the joint law. `envLaw_act_le` and
`le_envLaw_act` bound the world's marginal by the actuator's own masses through
`joint_le`, and `memoryLaw_record` pushes that bound through a measurement that
overwrites. Both hold at every cycle, so the floor does not depend on what the
agent has learned — which is the point of the item and also what keeps the
witness small.

## Completed result and validation

The full `lake build` passes with zero warnings. The default axiom audit covers
3,871 declarations in 60 modules using only `propext`, `Classical.choice` and
`Quot.sound`; seventeen explicit `#print axioms` checks on the new headline
results agree. All 27 retained regression examples compile without warnings.
Log: `/tmp/sensor-memory-build.log`.

All fifteen pre-commit hooks pass under `uv --project simulations` at the
repository root, including prose, Table S1, figures, staged-PDF freshness, the
arXiv manifest, leaves and placeholder proofs; the Python hooks run and pass
although no Python changed. The 143 existing Python tests pass.
`git diff --cached --check` passes. Report: `/tmp/sensor-memory-hooks.log`.

Two-pass builds give 52/43/87 pages against the baseline's 50/42/86, with zero
overfull boxes and unchanged underfull counts 2/0/29. The article's Table 1
overflow is unchanged at 22.86668 pt; Table 1 was not touched, and that
separate P-item remains open. The new article paragraphs, supplement
subsection, Table S1 row and primer subsection were rendered and read. The
64-page arXiv submission compiles from its unpacked tarball and passes manifest
freshness.

No Lean axiom, Python source, dependency, reference, generated macro or
simulation result was added or changed.

Remaining work in this thread: preparing the prior and the memory's initial
law, fabricating and controlling the gates, supplying the work these operations
draw, and identifying this memory with the finite source's load or with the
learning agent's actual channels. Local content agreement remains a separate
agency task.
