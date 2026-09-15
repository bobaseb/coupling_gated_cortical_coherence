# Closing the last three agency items — 2026-09-15

## Authorized scope

The user asked for all open agentic items in `tasks/todo.md` to be closed, at
the agent's discretion, under deadline. Two discretionary calls were delegated
explicitly and are recorded here: the content encoder is a general Lipschitz map
on circle points with the identity-style projection as its witness, and the two
residues that a proof cannot discharge are to be rewritten as standing
modelling obligations rather than left as open agency work.

The three items are the ones the preceding assessment left open: *physical
preparation and supply*, *local content agreement* (acquire half), and *broader
state spaces for agency thermodynamics and control*.

## Intent and success criteria

Each item closes only where a theorem can close it. Where the item's own
criteria cannot be met, the obstruction is proved and recorded rather than
narrated, and the residue is filed where it belongs.

1. **Supply.** Identify the ledger's drawn unit with a named channel's own
   reservoir heat rather than a free real. Answer the sharp charge. Answer
   external refuelling in both directions.
2. **Content.** Derive observation compatibility from phase coherence, with a
   quantified residual and the exact case as its endpoint. Fence it against the
   equal-phase counterexample, which must survive unchanged.
3. **State spaces.** Carry the path law to an arbitrary measurable space with a
   probability law on it; discharge integrability and existence assumptions
   rather than assuming past them; generalize the control result off finite
   state.

## What was built

**`Phase3_ResourceFoundations`.** `draw_eq_step_heat`,
`draw_ge_entropy_reduction`; `ProbDist.eq_zero_of_eq_one`,
`FiniteFeedbackStep.sharp_preparation_not_reversibleSupport`,
`sharp_preparation_extendedKL_top`; `ResourceTrajectory.SourceDelivery`,
`totalDelivery_eq_source_loss`, `delivery_le_source`,
`horizon_le_of_sourced_delivery`, `no_finite_source_sustains`.

**`Phase4_KuramotoDynamics` §6.** `order_parameter_r_sq_eq_mean_cos`,
`cos_gap_le_of_coherence`, `circlePoint`, `chord`, `chord_sq_eq`,
`chord_nonneg`, `chord_le_of_coherence`, `chord_eq_zero_of_phase_locked`.

**`Phase5_ContentDynamics`.** `LipschitzEncoder`, `compatible_of_coherence`,
`compatible_of_phase_locked`, `run_residual_floor`, `run_residual_of_coherence`.

**`Phase3_MeasureFeedback`** (new module). `MeasureFeedbackStep` and its
`forward`/`final`/`reversePath`/`reverse`/`entropyProduction`;
`entropyProduction_nonneg`, `entropyProduction_eq_top`,
`entropyProduction_eq_zero_iff`, `path_divergence_splits`,
`entropyProduction_map_le`, `initial_divergence_le_entropyProduction`,
`entropyProduction_self`; `ProbDist.toMeasure_ac_of_support`,
`extendedKL_eq_klDiv`, `extendedKL_eq_klDiv_of_missing`;
`MeasureControlProblem` with `exists_optimal` and `exists_optimal_compact`.

**`Examples/AgencyFoundations.lean`.** Namespaces `Ledger`, `SharpCharge`,
`Supply`, `Broad`, and the coherence witnesses in `Content`.

## What it does not establish

Gate fabrication and control work are charged to an observable and never priced;
`withPreparation_ledgered` supplies no microscopic implementation of the
preparation it charges. Both are R7 in the ledger, because pricing them means
declaring a hardware model with prices, which relocates the input rather than
discharging it.

The encoder and its Lipschitz constant are declared hardware. The scalar
contents are identified with no neural variable and with no section of the
probability sheaf; that identification is R6.

The Shannon-entropy form of the entropy balance is not generalized off finite
spaces and is not claimed to be. The divergence form is what survives.

The coherence bound is not tight: two antiphase oscillators give a residual of
`2√2` where the actual disagreement is `2`. The `N²` factor is inherent to
extracting a pointwise statement from a population mean.

## Verification

`lake build` clean, zero warnings. Axiom audit: 4293 declarations in 69 modules
on `propext`, `Classical.choice`, `Quot.sound` only, from 4126 in 68. Red
regression specifications ran before the declarations existed. Publication,
Table S1, primer, `CHANGELOG.md` and the ledger updated in the same pass, with
PDFs rebuilt and the arXiv submission refreshed.
