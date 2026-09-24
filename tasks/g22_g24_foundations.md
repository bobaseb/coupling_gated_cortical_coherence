# G22–G24 first increment — 2026-09-23

## Intent and acceptance criteria

Prioritize Lean foundations for the three research proposals in `tasks/todo.md`,
then add small Python analytical checks. Manuscript and publication artifacts
are outside this increment by explicit user instruction. Preserve existing
uncommitted work. Acceptance: new formal results compile without warnings, are
reachable from the root import, and pass the axiom audit; numerical helpers have
analytical regression tests and reject inputs outside their stated domain.

## Formal scope

- G22: retain the observable second moment in weighted current
  Cauchy–Schwarz; derive the directional sine-current bound with factor one
  minus squared cosine mean. This is a spatial functional inequality for a
  positive continuous normalized density and continuous current, valid for any
  angular direction. It requires neither stationarity nor spatial periodicity
  until the integration-by-parts bridge to a time derivative is made.
- G23: compose installed register readout, phase evolution, phase sensor and
  register update into a normalized joint transition, retaining phase state.
  Supply a two-phase feedback witness and blind-sensor comparison. Telescope a
  declared work-store account and prove a finite-prefix exhaustion obstruction.
  `Phase3_FeedbackLedger.lean` couples declared sensing, reset and installation
  prices to expected costs on that transition's joint law, charges preparation
  once, and records replenishment. It proves eventual work-store exhaustion
  when expected net cost has a positive floor and replenishment is absent.
- G24: extend the existing projection proof to nonnegative input second-moment
  weights. Sort by weighted squared eigenvalue. A two-dimensional witness has
  eigenvalues (3,1), input second moments (1,16), and rank-one error floor 9;
  the preferred retained mode reverses relative to isotropic inputs.

## Open proof and model obligations

G22 now has `Phase8_OrderSpeed.lean`: it identifies the real first-harmonic
magnitude with the norm of `circularOrderParameter`, derives cosine and sine
moment rates from a pointwise continuity equation under periodic spatial
regularity and explicit differentiation-under-the-integral hypotheses, proves
the positive-order magnitude speed bound, and integrates it to the arcsine
endpoint cost floor. The endpoint theorem assumes globally smooth order and
cost, and 0 < r < 1 throughout its domain. It does not construct a PDE
solution. Zero-order instants, the approach to unit order, and the weaker
absolute-continuity formulation remain open; so does quantitative numerical
validation across the full protocol grid. The formal bound is about
probability-current cost, without heat or metabolic conversion.

G23 now has an executed-law ledger in `Phase3_FeedbackLedger.lean`. It uses
supplied mode prices, sensing and reset path prices, a one-time preparation
charge and an explicit replenishment sequence. The Bool witness exhibits a
nonzero signed installed-energy change. It still needs calibrated physical
prices, a controller stop rule, a specified replenishment mechanism and an
actual reservoir model. Thermal claims require local detailed balance and path
support. The deterministic witness is not a heat model or a performance
benchmark. Matched noisy/blind/shuffled controls and held-out task scoring
remain open.

G24 now has `Phase6_SampledRank.lean`: for a declared probability law that
samples eigenbasis vectors, expected squared reconstruction error has the
weighted spectral-tail floor, and spectral truncation attains it. The two-mode
witness gives a normalized anisotropic input law and exact floor 9/17.
A distribution-level identity for general inputs with diagonal second moments
and a general covariance treatment remain open, as do the shared intervention
task, fixed train/test families, nonlinear transformer and phase candidates,
measurement rules,
and a CPU runtime budget. The weighted theorem alone establishes none of these
empirical comparisons.

All three parent checklist items remain open. No publication claim is added.

## Python checks

`simulations/followup_foundations.py` evaluates periodic current quadrature,
composes finite feedback channels, and computes diagonal weighted spectral tails.
Nine tests cover the exact uniform zero-current control, a manufactured evolving
cosine density with its continuity current, invalid densities/diffusion/channels,
the Lean feedback witness and blind control, the anisotropic mode reversal,
zero/full rank, and random rank-one competitors (seed 22). These are analytical
checks, not saved simulation results, onset experiments or benchmark outcomes.

The tests were observed failing on the absent module before implementation.
They now pass, together with targeted Ruff, strict mypy, Bandit, Vulture, Xenon
and the repository architecture gate. Radon reports maximum complexity 8.
The textual no-sorry gate passes on 104 Lean sources.

## G22 Python pilot — 2026-09-24

`simulations/g22_current_sim.py` now evolves a positive periodic density on a
conservative finite-volume grid. The same edge current advances the density and
enters the numerical `∫ J²/(Dρ)` account. The saved five-protocol pilot at 64
cells, D = 0.5 and duration 1 includes uniform zero current, ordered diffusion
relaxation, and early/linear/late coupling schedules from 0.4 to 2.0. Every
artifact records time, density, edge current, order, coupling, accumulated cost,
duration, diffusion, initial order and grid resolution. The report generator
`simulations/g22_current_report.py` reads those `.npz` files only and writes
`simulations/figures/g22_pilot/summary.json`; it never runs the solver.

At initial order 0.2, early/linear/late final orders are approximately
0.24546/0.21669/0.19087, with measured current costs
0.01902/0.00975/0.00838 and endpoint lower bounds
0.00435/0.00058/0.00017. The corresponding cost-to-bound ratios are about
4.37/16.75/48.36. All five trajectories have positive density and mass error
at floating-point precision. The exact uniform path has zero current and cost.
For zero-coupling ordered relaxation, the cost is about 0.02599 versus a bound
of 0.01274. These computed values are in this working record only; no
publication numerals or macros were changed.

The finite-volume calculation is a homogeneous numerical pilot. Grid tests at
32, 64 and 128 cells converge toward the exact diffusion relaxation order.
A quantitative continuum error estimate and sweeps across diffusion, ramp rate
and heterogeneity remain open. In particular, heterogeneity changes the model
premise and cannot be used as a direct test of the homogeneous formal bound.
There is no operational onset in this small fixed-duration pilot; its loose
slack does not yet make a main-text claim useful. Current cost remains separate
from heat, work and metabolic power.
