# L2 — Finite policy selection under a heat budget, 2026-09-13

## Intent and constraints

Select a deterministic policy for a declared finite task using the reward and
heat of its actual `FiniteFeedbackCycle`. Share the initial distribution, world
channel, memory channel, thermal scale and energy across all comparisons.
Action is a function of the existing internal state and observation is the
world state; neither has a separate physical register. Selection compares
fixed autonomous models before one update. It does not model the cost of
implementing, switching or learning a policy.

The thermal interpretation of transition log-ratios remains the local detailed
balance modelling assumption. Work is the energy change plus outward heat on
each actual transition. No arbitrary scalar policy cost, new axiom, production
simulation, register-to-actuator allocation or spatial convergence is added.

## Model and success criteria

The task is to make a lamp true after one complete update. Internal state `X`
is a uniform bit; the independent initial lamp `S` is true with probability
1/4. A fixed world channel sets `S` equal to action `a` with probability 3/4.
The fixed memory channel sets the new `X` equal to the new `S` with probability
3/4. All initial masses and transition probabilities are positive. The common
interaction energy is zero for agreement and `log 3` for disagreement, at
thermal scale one.

All four deterministic bit policies are permitted: constant false (baseline),
copy, invert and constant true. The objective is the final probability of a
true lamp, with task target at least 1/2. At budget `log 3 / 4`, the anticipated
unique optimum is copy: performance 1/2 versus the baseline's 1/4. Both have
total mean heat `log 3 / 4` and mean work zero. Invert and constant true have
total mean heat `3 log 3 / 4` and mean work `log 3 / 2`; constant true reaches
performance 3/4 but is infeasible. These are exact proposed Lean equalities,
not simulation estimates; the proofs must confirm or correct this calculation.

## Plan

1. Write and run failing Lean specifications for the generic finite comparison
   and the model's performance, heat/work, optimality and negative cases.
2. Add bare task data and actual-cycle reward/cost definitions beside the L1
   construction. Prove deterministic policy/channel identification, the common
   first law, the entropy-budget consequence and existence of a finite feasible
   maximizer. Keep physical assumptions separate from optimization.
3. Prove the complete four-policy table and characterize the feasible policies.
   Construct the unique optimum; prove strict improvement and attainment of
   the stated target. Prove the baseline is feasible but misses the target,
   the stronger constant-true policy is infeasible, and the copy/invert pair
   has identical final laws but different heat. Check real action and memory
   changes and retain the shared intermediate law by construction.
4. Align article, supplement, status tables, primer and ledgers. Rebuild and
   inspect tracked PDFs and refresh the assembled arXiv submission.
5. Pass the complete zero-warning Lean build and axiom audit, headline axiom
   checks, publication/freshness gates and `git diff --check`.

## Execution

- [x] Red specifications fail before implementation.
- [x] Generic finite-control results and channel identification pass.
- [x] Explicit witness, optimum and regressions pass.
- [x] Publication sources and rebuilt artifacts agree.
- [x] Required verification passes.

Stop at this finite control result. Learning, additional registers, policy
switching protocols, biological identification, E34Active and E45Active remain
separate tasks.

## Completed result and verification — 2026-09-14

`FiniteControlProblem` lives beside `FiniteFeedbackCycle` in
`Phase3_AgencyThermodynamics.lean`. `cycle_law` identifies the explicit policy's
composed channel law with the distribution used for both reward and cost.
`first_law` and `entropy_budget` consume the L1 results on that cycle;
`exists_optimal` maximizes reward over the nonempty finite feasible set.

`Examples/AgencyControl.lean` proves all expectations specified above exactly.
Its `performance_formula`, `actuation_heat_formula`, `memory_heat_formula` and
`work_formula` cover every deterministic bit map. `feasible_iff` admits exactly
baseline and copy. `budgeted_improvement` and `unique_optimum` select copy,
while `feasible_failure`, `stronger_policy_infeasible` and
`equal_output_different_heat` fence the roles of reward, budget and path law.
The selected action depends on memory, both substeps permit bit changes and
the selected process satisfies the whole-update entropy-budget theorem.

The red specification run failed before the declarations existed. The full
`lake build` now passes with zero warnings, including the default axiom audit:
2,497 declarations in 44 modules, resting only on `propext`, `Classical.choice`
and `Quot.sound`. Explicit headline axiom checks and all applicable pre-commit
hooks pass. Python hooks correctly skip this change, which adds no Python.
The 39 existing PDF, arXiv, figure and numerical-macro tests pass; macro
regeneration reads the saved artifacts and does not invoke integrators.

The article, supplement and primer PDFs have 39, 33 and 75 pages. Their final
LaTeX logs have no warnings or overfull boxes, matching the clean pre-change
baseline. Changed text, equations and tables were visually inspected. The
48-page arXiv submission compiles from its unpacked tarball and passes the
manifest freshness check. A separate working-tree check confirms that all
three PDFs are changed alongside their sources and newer than every resolved
source dependency. `git diff --check` passes.

The comparison proves finite control under its declared objective and physical
model. It does not account for policy installation, switching or learning,
additional registers, a continuing power source, cortical identification or
the active chain's resource and spatial bridges. L2 is complete; L3 and L4
and the separate modelling and submission tasks remain open. No dependency,
reference, Python source or simulation result was added.
