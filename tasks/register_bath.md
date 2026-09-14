# Register-ledger premises — a finite microscopic bath, 2026-09-14

## Intent and constraints

Resolve the ledger's open request to derive its accounting from a specified
bipartite dynamics, or exhibit where it fails. Follow one register and one
finite bath through executed operations. Heat into the bath is its actual
energy increase; externally supplied work changes the combined energy. The
existing `RegisterLedger` and its positive-channel thermal allocation theorem
keep their hypotheses. A reversible microscopic gate is not automatically a
strictly positive reduced channel satisfying local detailed balance.

Use the existing `FiniteProtocol` for sequencing. Add no new axiom, Python,
reference, simulation, dependency or universal physical postulate. Preserve
the original Bool witness and its consumers by keeping the sharper
`StatisticalMechanics Bool` instance local to its witness file. Preparation of
the initial bath, fabrication, a work supply, cortical identification and the
local-content-agreement item remain separate.

## Model and success criteria

1. Derive an arbitrary finite protocol's cumulative bath-energy transfer from
   the final minus initial expected bath energy. Identify the correction when
   reported stage heat omits part of that transfer. No positivity is needed
   for this first-law statement; it supplies no new entropy inequality.
2. Implement all four deterministic bit maps by reversible permutations of
   register and bath, realizing the requested map on a bath prepared false.
   Injective maps leave the bath alone; erasures transfer the register bit to
   it. Start with a uniform register and a pure bath, bath energies zero and
   `2 log 2`, and a degenerate register energy at temperature one. Compute
   mean heat from the actual paths. It must be zero for injective maps and
   `log 2` for erasure, and inhabit `StatisticalMechanics` with the actual
   reachable bath supports. The energy gap and prepared bath are model inputs;
   the resulting heat/entropy equality is specific to this preparation.
3. Execute two swaps on the same law. The first erases and delivers `log 2`;
   the second returns that energy and restores the original register instead
   of erasing it again. Derive the zero total from the generic ledger and
   exhibit the negative second share and first share exceeding the total.
4. Exhibit a different reversible protocol that leaves the register unchanged
   but excites its bath. It has the same logical update as idle and different
   heat. Thus a register map alone does not identify a protocol's cost, and
   reversibility does not establish the ledger's thermal allocation premises.
   Account explicitly for work and the prepared bath; reject a free drive or
   reusable unprepared eraser.
5. Keep generic and concrete Lean regression specifications, observe their
   failure before implementation, then pass the zero-warning full build and
   axiom audit. Align article, supplement, status tables, primer and ledgers;
   rebuild and inspect all tracked PDFs and the assembled arXiv submission;
   run applicable publication/freshness gates and `git diff --check`.

## Execution

- [x] Red specifications fail before implementation.
- [x] Generic accounting and correction identity pass.
- [x] Reversible register instance and counterexamples pass.
- [x] Publication and built artifacts agree.
- [x] Required verification passes.

The generic half is in `Phase3_ContinuingAgent.lean`: `energyTransfer` is a
declared subsystem's gain on an actual transition, `sum_energyTransfer` sums the
stage transfers to that subsystem's endpoint gain with no positivity hypothesis,
and `reported_heat_eq` exhibits the correction by which a reported heat ledger
differs from it. Both were red in `Examples/RegisterBath.lean` before they
existed, and criterion 1 asked for nothing else: no entropy inequality follows.

The witness is `Examples/RegisterBath.lean`. `lift` carries each of the four
maps of a register bit to a permutation of register and bath —
`lift_injective` — that performs the requested map on a bath prepared `false`
— `lift_realizes`; `lift_of_injective` and `lift_of_const` are the two shapes,
and `lift_erase` identifies the eraser with the swap. `prepared` is a uniform
register and a pure bath, `bathEnergy` has levels `0` and `2 log 2`, the
register's levels are degenerate (`bathEnergy_register_degenerate`), and the
thermal scale is one. `operationHeat` is the bath's mean energy gain on the
executed paths, computed through `meanHeat_gate`, and `operationHeat_formula`
evaluates it as `log 2` for the two erasures and `0` for the two injective maps
(`idle_heat`, `negate_heat`, `erase_heat`, `set_heat`). `bathThermo`, `bathEnv`
and `bathStatMech` inhabit `StatisticalMechanics Bool` at those values, with the
reachable bath supports as `final_bath`; `idle_dissipation` is the sharpening
over `Examples/Bit.lean`, whose bath charges `log 2` for every map. The three
instances are `local`, so that file's witness and its consumers are unchanged —
checked by a scratch module importing `Examples`, where
`heat_dissipation (id : Bool → Bool) = Real.log 2` still holds by `rfl`.
Criterion 2 is met.

Criterion 3: `erase_law_one` clears the register and leaves the bath uniform,
`erase_law_two` proves the second execution of the same gate restores
`prepared`, and `erase_not_erased` reads the restored uniform register off it.
`erase_first_heat` is `log 2`, `reused_bath_heat` is `-log 2`, `two_stage_heat`
derives the zero total from `sum_energyTransfer` rather than recomputing it, and
`shares_exceed_total` states both comparisons.

Criterion 4: `driveGate` holds the register at its value
(`driveGate_register`, `driveGate_realizes`) and excites its bath, so
`drivenIdleHeat_eq` is `2 log 2` and `same_update_different_heat` separates it
from idling. `suppliedWork` charges the bath's gain to an external drive,
because the register's levels are degenerate: `erase_work` is `log 2`,
`driven_work` is `2 log 2` and `driven_work_pos` rejects a free drive, while
`reuse_work` is zero for two erasures, which erase nothing. The two ledger
premises fail on the gate itself: `gate_channel_zero` and `gate_not_positive`
(a deterministic channel sends one state to one state, so the reduced step is
not strictly positive) and `erase_stageHeat_zero`, since a swap is an
involution, so its log-ratio heat vanishes on every realized path while the bath
gains `log 2` (`erase_stageHeat_not_bath_heat`), the whole of which the reported
ledger omits (`erase_reported_correction`).

Nothing here constructs a `RegisterLedger`, and the stopping point stands: a
microscopic realization of the positive-channel ledger would need premises this
model shows reversibility does not supply.

The red specifications failed before the declarations existed. The full
`lake build` has zero warnings; the default axiom audit covers 3,488
declarations in 56 modules with only `propext`, `Classical.choice` and
`Quot.sound`, and the explicit headline checks agree. Every pre-commit hook
passes at the repository root under `uv --project simulations`, including
`check-prose`, `check-tableS1`, `check-figures`, `check-pdf-freshness`,
`check-arxiv-freshness`, `check-leaves` and `check-sorry`; the 143 Python tests
pass unchanged. No Python, dependency, reference, macro or simulation result
changed.

The article gained one paragraph with the two-identity bath ledger equation and
a rewritten E34 row, the supplement one paragraph set with one Table S1 row, and
the primer one subsection with a summary-table row. The rebuilt article,
supplement and primer have 46, 41 and 85 pages against 45, 40 and 84. Final logs
have zero warnings and overfull boxes, with underfull counts matching fresh
baseline builds from `HEAD` (2, 0 and 29). The changed pages were visually
inspected. The 60-page arXiv submission compiles from its unpacked archive and
passes manifest freshness. `git diff --check` passes.

Still open after this change: preparing the bath and the register's law,
supplying the work, fabricating the gate, identifying this bath with the
reservoir the ledger's operations exchange heat with, a pathwise or replenished
store, local content agreement, and every cortical identification.

Stop at this finite derivation and obstruction result. A microscopic realization
of the existing positive-channel `RegisterLedger` is a separate, narrower
follow-up if the counterexamples show that the proposed identifications need
additional assumptions; do not label that realization complete.
