# 2026-09-16 — Repairing the leaf detector's false consumers

## Intent, constraints and success criteria

`tasks/n_manuscript_review.md` recorded that `simulations/check_leaves.py`
matched unqualified tokens across the whole Lean tree rather than resolved
constants, so two modules escaped its leaf report through references that Lean
would never have resolved. Repair the detector so that consumption means an
actual module-and-declaration dependency, then classify the leaf set the
repaired detector reports.

Constraints, all from the review note and `AGENTS.md`: failing regressions
first; preserve the existing exclusions (prose, witnesses, aggregator, the
`NOT_CHECKED` modules); do not repair the report by widening the baseline
before classifying the results; change no Lean statement, publication file or
axiom allowlist. Success is a detector whose false consumers are gone, a
regression suite that fails on each of them, and a baseline in which every
entry states why that module is terminal.

## The defect

The old check asked whether any file in the tree contained a token spelling one
of the module's declarations. Three things made that weaker than it looked, and
all five modules below were credited with consumers because of them.

| Shape | Example |
| --- | --- |
| Shared final segment | `Network.run` (`Phase6_Locality`) credited to `run` in `Phase5_ContentDynamics`, and `ball` to `Phase8_CriticalExponent`. Neither imports Locality. |
| Namespace prefix taken for the declaration | `PredictiveDissipation.ofLandauer` (`Phase3_LandauerBridge`) truncated to `PredictiveDissipation`, the structure declared in `Phase3_PredictiveThermodynamics`; likewise `FiniteObservationalLearner.ofPhaseSensor` truncated to the learner `Phase3_PhaseSensor` imports. |
| Field and projection names | `final`, `forward`, `performance` (`Phase3_MeasureFeedback`) and `snd` (`Phase3_Preparation`), matched in a dozen unrelated files. |

## The repair

A reference now has to be a constant that would resolve:

* **only an importer can consume.** A file references a constant of `A` only if
  it imports `A`, directly or transitively. This also disposes of the reverse
  direction — the module `A` imports cannot be consuming `A`.
* **a declaration carries its namespaces.** `Widget.ofThing` inside
  `namespace Pkg` is `Pkg.Widget.ofThing`, so a file mentioning the structure
  `Widget` has not mentioned it.
* **a spelling that does not resolve uniquely resolves to nothing.** A constant
  is reachable by its full name or any trailing segment, which is also how dot
  notation on a term reaches it; where two constants visible in the same file
  share a spelling, that spelling credits neither.

The remaining inaccuracies are all in the strict direction: a lemma reached
through the `simp` set leaves no token, and an ambiguous spelling is refused
rather than credited. The gate can therefore ask for a decision about a module
that is used; it can no longer report a dead module as used, which is the
failure C1 was.

`simulations/test_check_leaves.py` carries a regression for each of the three
shapes, for the real consumers that must keep counting (direct import,
transitive import, qualified reference, dot notation), and for the exclusions
that must survive the rewrite (prose, witnesses, declaration-free modules,
`NOT_CHECKED`). The last test runs the gate on the Lean tree itself.

## The leaf set, classified

The repaired detector reports eight leaves: the three already recorded and the
five the false consumers had hidden. Each of the five was read against the
module it bounds and against `Chain.lean` before being recorded, and none is
wired into the chain by this change.

- **`Phase3_LandauerBridge`.** The discharge route for the chain's n3 → n4
  edge, and the edge stays a named hypothesis: `PredictiveDissipation.
  ofLandauer` derives Still's bound from `landauer_bound`, but only under the
  physical identification `(nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t`,
  which nothing derives and `nonpredictive_eq_zero_of_injective` shows is not
  free. `E34`'s docstring already names the module as what would discharge the
  edge; `Examples/Phase3.lean` §18 discharges it on the one-bit eraser, where
  the inequality is an equality. Routing the constructor into `chain` would
  assert the identification for every dissipating register. **This is the one
  entry to delete if the identification is ever supplied.**
- **`Phase3_MeasureFeedback`.** A generalization. It carries the path law to an
  arbitrary measurable space and states `extendedKL_eq_klDiv` over the finite
  development it imports, so the dependency runs outward from it and cannot run
  back. The chain's thermodynamic edges are stated on finite state spaces.
- **`Phase3_PhaseSensor`.** Limitative. `channel_eq_of_phase_eq` and
  `channel_ne_iff_fiberCount_ne` say what a phase-derived channel can and
  cannot separate, and that the condition is on the readout's fibre counts
  rather than on the order parameter. A consumer would be a result deriving
  learning performance from coherence — the implication `Examples/PhaseSensor.
  lean` §27 exhibits failing in both directions.
- **`Phase3_Preparation`.** It prices a stage the rest of the development
  leaves supplied, and prices it through the existing machinery:
  `withPreparation` prepends the preparation to a `FiniteProtocol` and to a
  `PathwiseStore` so the telescoped balance and store bounds already cover it.
  The results are applied where an agent is built, in
  `Examples/Preparation.lean`. Charging every `prior` in the chain would assert
  that each agent's preparation is the constant channel this module prices.
- **`Phase6_Locality`.** Limitative, in the shape `Phase7_FiniteRegion`
  already has: `not_reconstructs_of_outside_past` says `Phase6_Reconstruction`'s
  bound applies to a site outside the causal past of an intervention, so no
  report read off that site can track it. Routing it into `chain` would add a
  temporal requirement to edges whose hypotheses are snapshots.

## Validation and deliverables

- `simulations/check_leaves.py` rewritten; `simulations/test_check_leaves.py`
  added with 19 tests, red before the rewrite and green after.
- Full Python suite: 162 passed. `ruff`, `ruff format`, `mypy --strict`,
  `bandit`, `vulture`, `xenon` (`--max-absolute B`) and `tach` all pass.
- `python simulations/check_leaves.py` exits 0: eight recorded leaves, all
  still leaves.
- No Lean file, publication source, tracked PDF, figure, reference or axiom
  allowlist is touched, so no rebuild is required and no chain edge, R-item or
  P-item changes status.
