# Learning from experience — observational learning that changes the next action, 2026-09-14

## Intent and constraints

Close the ledger item **"Learning from experience"** and the roadmap's
highest-value bounded next step: an observed outcome changes the policy, and
the changed policy controls the next actual action, on one evolving joint law.

The decisive difference from the completed `PolicyLearning` item is the source
of the bias. There the register's energy was set from *known* expected task
values, so the answer was supplied before the first update. Here the rewarding
action is an unknown environmental parameter, the register never sees it, and
every change of the register is driven by a realized noisy outcome of the
action it actually took.

Type-level fences, not prose ones:

* the register update has signature `O → R → ProbDist R`. It has no `W`
  argument, so it structurally cannot read the unknown parameter;
* the readout has signature `R → A`. It has no `W` argument, so no policy value
  can be decoded into it;
* the reward appears only in `performance`, never inside any channel.

Out of scope, and to be fenced in the publication as such: preparing the prior,
a continuing power source, repeated task episodes beyond the declared updates,
physical fabrication of the readout, general reinforcement-learning
convergence, arbitrary horizons, and any cortical identification. No new
simulation, reference, axiom or numerical macro is part of this change.

## Model

`FiniteObservationalLearner W R A O` carries `prior : ProbDist (W × R)`,
`readout : R → A`, `world : W → A → ProbDist O`, `update : O → R → ProbDist R`
and `reward : W → A → ℝ`. Its composite register channel is

    transition w r = (world w (readout r)).bind (fun o => update o r)

which is exactly a `FiniteFeedbackStep W R` with the parameter `W` held fixed,
so `iterate` supplies the evolving law and the existing telescoped entropy and
first-law balances apply to the same process that `performance` is read from.

**Witness — a two-action choice task with an unknown rewarding action.**
`W = R = A = O = Bool`. The parameter `w` names the rewarding action; the
readout is the identity, so the register's value *is* the action executed. The
prior is uniform and independent: `1/4` on each `(w, r)`, the declared initial
uncertainty. The world returns success with probability `3/4` when the executed
action matches `w` and `1/4` when it does not. The update is win-stay,
lose-flip-a-coin: on success the register is unchanged; on failure it is
resampled uniformly. The reward is `1` when the executed action matches `w`.

The composite channel is then, with rows the current register value and columns
the next, at `w = true`

    T = [[5/8, 3/8], [1/8, 7/8]]

and its mirror image at `w = false`; every entry is positive. Writing
`a_n = Pr(r_n = w)`:

    a_{n+1} = 3/8 + a_n/2,   a_0 = 1/2,   a_n = 3/4 - (1/4)(1/2)^n
    J_n = a_n  (expected reward of the action actually executed at update n)

so `J_0 = 1/2`, `J_n` is strictly increasing and `J_n → 3/4 < 1`.

Heat, at thermal scale one, is the transition log-ratio of the same composite
channel: `q(w, r, r') = ±log 3` for the two register flips and `0` otherwise.
On the actual evolving laws

    <Q_n> = (log 3 / 8)(1/2)^n,   sum_{n<N} <Q_n> = (log 3 / 4)[1 - (1/2)^N]

bounded by `budget = (log 3)/4` at every horizon.

## Success criteria

1. **Nothing is learned for free.** The register is energetically degenerate, so
   every dissipated quantum is externally supplied work. This is not a modelling
   convenience: prove generically that a parameter-independent register energy
   with zero path work forces the composite channel's heat to be independent of
   the parameter, and exhibit that this witness's heat is not. An energy
   landscape that made learning free would be one that already encoded the
   answer.
2. **One joint law.** `law (n+1)` is the *actual* final law of update `n`.
   Successive laws differ; a reset to the prior is rejected.
3. **The observation moves the policy and the policy moves the world.**
   `update true r ≠ update false r`, and `world w (readout r)` differs between
   register values.
4. **Strict improvement over baselines under a common allowance.** Against a
   frozen register (never updates: constant `1/2`, zero heat) and against an
   uninformative world channel (success probability `1/2` regardless of the
   action: constant `1/2`, zero heat, and still positive), `J_n > 1/2` for every
   `n ≥ 1`, with cumulative heat within the same `budget`.
5. **Fences.** Observations carry task information conditionally, not
   marginally: `Pr(o | w, r)` differs across `w` at fixed `r` while the outcome's
   marginal at the uniform prior does not. A reward-decreasing transition keeps
   positive probability `1/8`, so expected improvement is not pathwise
   improvement. The limit `3/4` is below the optimum `1`.
6. **Whole-process accounting.** Cumulative heat, cumulative work and the
   telescoped entropy budget are derived for the same iterated process, with
   the entropy drop strictly smaller than the work spent.

## Plan and execution

1. [x] Red: failing Lean specifications for the structure, the recurrence, the
   improvement, the baselines, the costs and every negative check.
2. [x] `ProbDist.bind` and `ProbDist.dirac` beside `ProbDist.swap`; the new
   module `Phase3_ObservationalLearning.lean` with the structure, its composite
   step, the law/performance readers, the zero-work obstruction and the
   cumulative entropy budget.
3. [x] `Examples/ObservationalLearning.lean`: the witness, its exact values and
   its regressions. Wire both index files.
4. [x] Align article, supplement, Table S1 and the primer with the exact result
   and its resource boundary. Rebuild the tracked PDFs and refresh the arXiv
   submission.
5. [x] Zero-warning `lake build`, the axiom audit, applicable pre-commit gates
   and `git diff --check`. Update `tasks/todo.md` and `CHANGELOG.md`.

**Stop rule.** Stop at this one finite task, its whole-process accounting, the
improvement theorem and its negative checks. If the model cannot meet a
criterion, record the obstruction here before designing an alternative.

## Completed result and verification — 2026-09-14

Every proposed equality and every success criterion above is proved. The full
`lake build` has zero warnings; the axiom audit covers 3,154 declarations in 53
modules resting only on `propext`, `Classical.choice` and `Quot.sound`. All
pre-commit hooks pass, as do 143 Python tests; no Python, dependency, reference,
macro or simulation result changed. The rebuilt article, supplement and primer
have 44, 39 and 82 pages with no overfull boxes, and the 57-page arXiv
submission compiles from its unpacked archive. The completion record in
`tasks/todo.md` names every declaration.

The stop rule held: no obstruction was recorded, and nothing beyond the declared
finite task was implemented. Preparing the prior, supplying the drive's work,
task episodes beyond the declared updates, fabricating the readout, optimal
policy convergence and cortical identification remain separate open work.
