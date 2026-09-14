# Learning dynamics — thermal adaptation of a policy register, 2026-09-14

## Intent and constraints

Specify a policy update, the objective driving it and its actual resource
accounting after L2. Use a finite autonomous policy bit: false decodes to the
lamp baseline, true to copy. Both policies satisfy L2's complete-task heat
budget. The register relaxes under a fixed channel whose energy favours the
policy with higher expected lamp reward. Expected rewards are known model
inputs; this is model-based policy adaptation, not estimation from observations.

Keep the learning clock separate from task execution and spatial refinement.
The register's distribution weights L2's actual-cycle performance and heat for
a prospective task with L2's prepared initial law. Task episodes, preparation,
reward evaluation, and implementing the register's readout in an actuator are
not executed by the learning channel. Their resource costs cannot be inferred
from its heat. No continuing energy source, E34Active allocation, E45Active
convergence, cortical identification, new axiom, reference or simulation is
part of this change.

## Model and success criteria

At thermal scale one, set register energy to
`E(b) = 4 log(3) (R(copy) - R(policy(b)))`, hence `E(false)=log(3)` and
`E(true)=0`. The autonomous channel, with rows/columns false then true, is
`[[5/8, 3/8], [1/8, 7/8]]`. Its forward/backward log-ratio must equal the
outward heat `E(before)-E(after)` on every transition; path work is zero.
The initial probability of copy is 1/4. No monotonicity or convergence is
assumed as a structure field.

Prove from successive channel outputs that
`p_n = 3/4 - (1/2)(1/2)^n`, so expected prospective task reward is
`7/16 - (1/8)(1/2)^n`. It strictly increases and converges to 7/16, below
copy's 1/2. Each prospective task still has expected heat `log(3)/4` and
zero expected work under L2's initial law. Register update heat is
`(log(3)/4)(1/2)^n`; cumulative heat over N updates is
`(log(3)/2)(1-(1/2)^N)`, funded by the register's initial energy decrease.
These are proposed exact Lean equalities, not numerical simulation claims.

The generic iteration must carry each final law into the next initial law,
preserve positivity, and telescope the first-law and entropy balances over
any finite number of updates. The witness must instantiate these results.
Regressions must detect a frozen/reset initial law, retain positive probability
of a reward-decreasing individual update, show that the limiting mixture is
not the optimum, and exhibit expected reward decrease when initialized above
the stationary copy probability. Improvement is conditional on the declared
initial preparation, not guaranteed by a heat bound or for every trajectory.

## Plan and execution

1. [x] Run failing Lean specifications for iteration, reward, heat, convergence
   and the negative cases before adding their implementation.
2. [x] Add reusable autonomous iteration and finite balance theorems beside
   `FiniteFeedbackStep`; prove the policy-register witness and regressions.
3. [x] Align article, supplement, status tables, primer and ledger with the
   exact result and its resource boundary. Rebuild and inspect tracked PDFs
   and refresh the assembled arXiv submission.
4. [x] Pass the zero-warning Lean build, axiom audit, explicit headline axiom
   checks, applicable publication/freshness gates and `git diff --check`.

Stop at the specified finite model and its limiting distribution. Learning
unknown rewards, repeated task execution, policy installation and coupled
controller/world learning require separate process models and accounting.

## Completed result and verification — 2026-09-14

All proposed equalities above are proved. `FiniteFeedbackStep.iterate` and its
finite entropy/first-law sums live in `Phase3_AgencyThermodynamics.lean`.
`Examples/PolicyLearning.lean`, imported through the witness index, instantiates
them with the thermal policy bit. `energy_objective` ties energy to L2 reward;
`local_balance` and `zero_work` check all physical transitions.
`probability_recurrence` derives the scalar recurrence from the iterated law,
and `copy_probability` solves it. `performance_improves`, `performance_limit`,
`stationary_law` and `law_limit` prove the positive distributional results.
`update_heat`, `cumulative_heat`, `cumulative_heat_budget` and
`entropy_accounting` use the same evolving path laws and energy observable.

`task_heat` and `task_work` are prospective expectations of L2's actual task
cycles under the learned policy mixture. `reward_decreasing_path_positive`,
`limit_below_optimum`, `overprepared_reward_decreases` and
`successive_laws_differ` delimit the improvement and iteration claims. The red
specifications failed before the declarations existed and pass with the proofs.

The full `lake build` has zero warnings. The default axiom audit covers 2,568
declarations in 45 modules with only `propext`, `Classical.choice` and
`Quot.sound`; explicit headline axiom checks agree. All applicable pre-commit
hooks and 39 existing publication/macro tests pass. No Python, dependency,
reference or simulation result changed. The initially attempted hook command
used `uv --directory simulations`, which made root-relative file arguments
miss every hook; the verified run uses `uv --project simulations` at the
repository root, and its publication and Lean hooks actually execute.

The rebuilt article, supplement and primer have 39, 34 and 76 pages. Their
final logs have no warnings or overfull boxes, as in the baseline. Changed
text, equations and status tables were visually inspected. The 49-page arXiv
submission compiles from its unpacked archive and passes manifest freshness.
The working-tree check confirms that every changed document has its changed
PDF and that all three PDFs are newer than every resolved source dependency.
`git diff --check` passes.

The bounded learning-dynamics item is complete. Learning unknown values from
observations, preparing resources, implementing the policy readout and
coupling adaptation to actual task execution are explicitly separate open
work. The model establishes no cortical identification or active-chain
resource/spatial bridge.
