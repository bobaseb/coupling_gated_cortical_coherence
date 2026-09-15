# A store on the trajectory, and what replenishment buys — 2026-09-15

## Intent and constraints

`ContinuingProcess.stored` subtracts cumulative *expected* work from a declared
number. `tasks/lessons.md` records what that does not do: it carries no battery
through the transition law, and it does not stop an individual trajectory from
overdrawing the store. `tasks/register_bath.md` closes with "a pathwise or
replenished store" still open, and the ledger's open item **Physical
preparation and supply beyond the finite model** names the same two things.

Close the pathwise and replenishment halves of that item. Leave the other two
halves — preparation of the initial law, and a separately implemented sensor
memory with its own erasure — open and unclaimed.

The store's reading is a **coordinate of the state**, so a statement about it is
a statement about the actual path, and the existing `FiniteProtocol` law
recursion is the only sequencing machinery needed. No positivity hypothesis: a
pathwise ledger must admit the deterministic gates `Examples/RegisterBath.lean`
uses. Add no axiom, Python, reference, simulation, dependency or universal
physical postulate. Replenishment is a *declared* supply, exactly as `stored`
is; nothing here derives a power source.

## Model and success criteria

1. Declare a store over an arbitrary finite protocol: a reading `balance` on
   the state, a `draw` and a `supply` per executed transition. Define
   reachability as positive mass under the protocol's own law, `Ledgered` as
   the reading falling by the draw and rising by the supply on every
   transition the protocol can actually execute, `Funded` as the draw not
   exceeding what is there plus what arrives, and `Solvent N` as no reachable
   state up to `N` having a negative reading. Every predicate quantifies over
   the support only.
2. Prove that a reachable state at `n+1` has a reachable predecessor at `n`
   with positive transition mass, and from it that an initially solvent,
   ledgered, stagewise funded protocol is solvent at every horizon. No
   positivity, and the draw may be random.
3. Prove the expectation identity for the same store — mean reading after `N`
   equals mean reading before, less the drawn work, plus the supplied work —
   from the existing `sum_energyTransfer` rather than a second calculation,
   and derive from it that pathwise solvency implies the expected bound the
   mean ledger asserts. The refinement must go one way only.
4. Prove the two replenishment results. A supply that covers each executed
   draw sustains **every** horizon, with no bound on cumulative work. A net
   draw bounded below by `c > 0` on every executed transition bounds the
   horizon by the initial reading over `c` — the pathwise form of
   `horizon_le_of_cost`, and this one does constrain each trajectory.
5. Witnesses. *(a)* A store whose expected allowance is nonnegative at every
   prefix and which a realized path overdraws: the mean ledger's `Sustains`
   holds and `Solvent` fails, so the converse of criterion 3 is false and the
   recorded lesson becomes a theorem. Identify the stage whose funding
   condition fails. *(b)* A deterministic spend/recharge cycle that is solvent
   at every horizon while its cumulative draw grows without bound, so no
   finite store bounds the work a replenished agent draws. Show the same
   protocol without its supply is not ledgered by the same reading — a store
   coordinate that does not record the draw is not a ledger.
6. Follow SDD/TDD, the axiom audit, and the publication/PDF alignment rules.
   Align article, supplement, Table S1, primer and ledgers; rebuild and inspect
   the tracked PDFs and the assembled arXiv submission; run the applicable
   gates and `git diff --check`.

## Stop rule

Stop at the pathwise ledger, its two replenishment theorems and the two
witnesses. Preparing the initial law, a microscopic or fluctuating model of the
supply itself, a separately implemented sensor memory, optimal-policy
convergence and every cortical identification stay out. If the pathwise
statement cannot be had without positivity, record the obstruction instead of
weakening the definitions.

## Execution

- [x] Red specifications fail before implementation.
- [x] Generic pathwise ledger and solvency pass.
- [x] Expectation identity, refinement and replenishment results pass.
- [x] Both witnesses pass.
- [x] Publication and built artifacts agree.
- [x] Required verification passes.

Six red specifications named `PathwiseStore`, `FiniteProtocol.Reachable`,
`exists_pred_of_reachable`, `solvent_of_funded`, `mean_balance_eq`,
`totalDraw_le_of_solvent`, `solvent_forall_of_replenished` and
`horizon_le_of_net_cost`; all failed on the absent declarations and pass
unchanged afterwards.

Criterion 1 is `PathwiseStore` with `Ledgered`, `Funded` and `Solvent`, each
quantified over `FiniteProtocol.Reachable` — positive mass under the protocol's
own law — rather than over the state type. Criterion 2 is
`exists_pred_of_reachable`, `solvent_succ` and `solvent_of_funded`, with no
positivity hypothesis and a possibly random draw. Criterion 3 is
`meanHeat_congr_support`, `mean_balance_eq` — which is `sum_energyTransfer` at
the store's own coordinate — `meanBalance_nonneg_of_solvent` and
`totalDraw_le_of_solvent`; the converse is refuted by criterion 5's first
witness rather than asserted to fail. Criterion 4 is
`solvent_forall_of_replenished` and `horizon_le_of_net_cost`, the sufficient and
necessary fences, the second via `balance_le_of_net_cost`.

Criterion 5(a) is the gambler: `gamblerProcess_totalWork` identifies its draw
with the existing mean ledger's work, so `gambler_mean_sustains` is that
ledger's own predicate and not a restatement; `gambler_totalDraw_two` is `1`
against a declared store of `1`; `gambler_not_solvent` exhibits the overdrawn
reading, reachable at probability `1/4`; `gambler_not_funded` locates the
failure at the second stage; and `sustained_not_solvent` states the three
together. Criterion 5(b) is the charger: `charger_reach` proves the overdrawn
reading unreachable, `charger_solvent` comes from the generic theorem and
`charger_funded`, `charger_totalDraw` gives `m` units drawn over `m` cycles and
`charger_draw_unbounded` exceeds any allowance at a solvent horizon.
`charger_not_covered` and `charger_no_uniform_cost` place it outside both
fences; `unsupplied_not_ledgered` removes the supply and loses the ledger.

Criterion 6: the full `lake build` has zero warnings and the default axiom audit
covers 3,590 declarations in 57 modules with only `propext`, `Classical.choice`
and `Quot.sound`. Every applicable pre-commit hook passes at the repository root
under `uv --project simulations`, and the 143 Python tests pass unchanged. No
Python, dependency, reference, macro or simulation result changed. The article,
supplement and primer rebuild to 49, 42 and 86 pages against 48, 41 and 85, with
zero overfull boxes and the baseline underfull profile; the 62-page arXiv
submission compiles from its unpacked archive.

Article Table 1 was left unchanged: its float already overflows the page at
`HEAD` by 36.47pt and a sentence in the E34 row grew that to 77pt. The content
is carried by the new paragraph and by Table S1, which is a longtable. The
pre-existing overflow is a separate defect.

Still open after this change: preparing the initial law, a microscopic or
fluctuating model of the supply itself, a separately implemented sensor memory
and its erasure, optimal-policy convergence, unbounded-horizon convergence
results, local content agreement, and every cortical identification.
