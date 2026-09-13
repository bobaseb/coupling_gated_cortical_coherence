# L1 — Complete finite perception–action update, 2026-09-13

## Intent and constraints

Compose actuation with a memory update whose initial joint law is constructed
from the actuation's final law by exchanging internal/world coordinates. Keep
the existing finite autonomous-channel model, strict positivity, one common
thermal scale and one energy observable. Action and observation alias the
existing state variables. No stationarity, extra register, protocol, learning
rule, register-to-actuator allocation or coupling convergence is assumed.

The previous agency/chain/primer work was uncommitted at the start of this task
(HEAD b4e12af). Preserve it while adding this bounded extension.

## Plan and success criteria

1. Write failing Lean regression specifications before implementation.
2. Add coordinate-swap identities for finite laws and a bare cycle data type
   in the existing thermodynamics module. Construct its sensing step from the
   actual intermediate law; do not carry an independently chosen second law.
3. Identify its final distribution with the existing `Agency.cycle` channels.
   Sum the two entropy balances and first laws, cancelling the same intermediate
   entropy and expected energy. Derive a whole-update heat-budget consequence.
4. Specialize to the existing reciprocal two-bit model. Also use a biased
   initial law to expose the coordinate swap and a changing sensing law.
   Reject incompatible supplied substeps and a zero whole-update heat budget.
5. Update publication scope, primer and ledgers; rebuild tracked PDFs and the
   assembled arXiv submission. Pass the full Lean build, axiom audit, explicit
   headline axiom checks and relevant publication/freshness gates.

## Execution

- [x] Red regression specifications fail before implementation.
- [x] Generic channel identification and balance/budget theorems pass.
- [x] Reciprocal and asymmetric witnesses/regressions pass.
- [x] Publication sources and rebuilt artifacts agree.
- [x] Required verification passes.

Stop after these criteria. E34Active's allocation and E45Active's convergence
remain independent modelling assumptions.

## Completed result and verification

`FiniteFeedbackCycle.sensing` constructs the intermediate law with
`ProbDist.swap`; `cycle_transition` and `cycle_law` identify the complete
perception–action channel output. `entropy_balance`, `heat_balance`,
`mean_first_law` and `entropy_budget` use the actual substeps and cancel their
shared intermediate entropy and energy. These are derived results, not fields
assuming a desired inequality. Channel identification and the first law do
not require the positivity needed by the entropy theorem.

`Examples/AgencyCycle.lean` checks the generic statements and specializes them
to `ThermalAgency.reciprocalCycle`, including the prior heat, entropy-production
and zero-work energy calculations. `biasedCycle` has a nonstationary sensing
law and positive actuation heat. Its unequal intermediate masses detect an
omitted swap even though both coordinates have type Bool. The incorrectly
initialized step is positive, but `mismatched_intermediate_rejected` proves no
cycle can compose it with that actuation. The reciprocal cycle rejects a zero
whole-update budget and is not stationary over the complete update.

The initial regression check failed on the absent cycle declarations. Final
`lake build` passes without warnings; the default axiom audit checks 2,404
declarations in 43 modules using only the three permitted axioms. Explicit
`#print axioms` checks cover every headline balance, channel identification and
the mismatch regression. All pre-commit hooks pass, including the inherited
Python changes, and the 31 PDF/arXiv/figure unit tests pass.

Two-pass PDF builds produce a 38-page article, 32-page supplement and 74-page
primer with no LaTeX warnings or overfull boxes. New equations, text and tables
were visually inspected. A separate check against the entire working-tree
diff and dependency timestamps confirms freshness, beyond the staged-file gate.
`prepare_arxiv.sh` compiles the unpacked archive at 47 pages and its freshness
gate passes. `git diff --check` passes. No production sweep ran, and L1 adds
no Python source, numerical simulation result or reference.

The user requested a combined commit of the inherited agency/chain/primer work
and L1 on 2026-09-13. All L1 criteria are complete; the independent
allocation/convergence assumptions and the explicitly excluded modelling
extensions remain open.
