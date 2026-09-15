# Preparing the declared prior, and what it costs — 2026-09-15

## Intent and constraints

Continue the agency ledger's **Physical preparation and supply beyond the
finite model** item with the piece it has named first since it was opened:
*preparing the initial law*.

Every finite agent in this development starts from a `prior` whose docstring
says its preparation is supplied, not derived --- `FiniteProtocol.initial`,
`ContinuingAgent.prior`, `MemoryAgent.prior`. The run is charged from that law
onward and nothing is charged for reaching it. That is the gap, and it is the
one place where a declared resource enters every agency result at once.

The tool is already here and was built for the other end of the run.
`memoryHeat_const` prices a channel that lands on one declared law whatever it
is given. Preparation *is* such a channel: it drives the hardware to a law
without reading what the hardware held. So preparation and erasure are the same
operation, and the identity that prices one prices the other.

Two things this has to state rather than assume.

- A preparation that reads nothing cannot create a correlation. The prepared
  law is a product of whatever the parameter's marginal already was with the
  law the preparation lands on, so the agent's uncertainty about the world is
  an input and not something it prepares.
- A sharp target falls outside the positive-target entropy identity. The
  specified bit preparation family has unbounded mean log-ratio heat from
  uniform input at thermal scale one. This does not price the sharp endpoint
  or every implementation of exact preparation; the real logarithm is
  totalized at zero.

Reuse `FiniteProtocol`, `memoryHeat` and the existing agents; add no axiom, no
dependency, no Python, no simulation and no reference.

This is the preparation of one declared law, its cost and its two fences. It is
not gate fabrication, not preparation of the charge of `tasks/funded_agent.md`
(whose target is sharp and so is outside the identity), not an identification of
the preparation's work with a source, and not a cortical identification.

## Model and success criteria

1. `ProbDist.uniform` on a nonempty finite type, and `KL_uniform`:
   `D(μ‖uniform) = log|V| - H(μ)` for every `μ`, with no positivity of `μ`.
2. **Uniform preparation has zero mean heat.** `memoryHeat_uniform`: the two terms of
   `memoryHeat_const` cancel identically, at every starting law and every
   thermal scale. Gate construction, control work and a funding source remain
   outside this identity; the reservoir interpretation uses local detailed balance.
3. `FiniteProtocol.withPreparation P blank prep`: the protocol that executes
   `prep` once from `blank` and then runs `P`. `withPreparation_law_succ` shows
   the shifted run is `P`'s own, given that the preparation's final law is
   `P.initial`; the whole thing is an ordinary `FiniteProtocol`, so the
   telescoped entropy balance, first law and store bounds cover the preparation
   without a second theory.
4. `preparation_meanHeat`: for a state-blind preparation the stage-0 mean
   log-ratio heat is `memoryHeat θ` of that channel on the blank law's system
   marginal. The constant-channel identity prices a product prior when the
   parameter marginal is already correct and the hardware target is positive.
5. The two fences as theorems. `preparation_parameter_marginal`: the
   preparation leaves the parameter's marginal exactly as it found it, for any
   `prep`. `preparation_product`: a state-blind preparation's output is a
   product, so a prior correlating parameter and register is not its output.
6. **Witness** on the sensor-memory agent of `Examples/SensorMemory.lean`, whose
   prior is uniform on four bits. Required results:
   - the agent's prior is the uniform law, and a state-blind preparation from a
     skewed hardware law with full support and the parameter already uncertain
     lands on it; the initial and target laws are proved different;
   - the prepared protocol's run after the preparation is the agent's own run,
     at every horizon;
   - that preparation has zero mean heat, and the whole run including it is charged by the
     existing cumulative bound;
   - the contrast: preparing the agent's own standard state `(3/4,1/4)` from
     uniform costs `(1/4)log 3`, by the existing `erase_cost`;
   - the divergence: the cost of preparing a bit law biased to `ε` from uniform
     is `(1/2-ε)log((1-ε)/ε)` and is unbounded over the positive bit family;
   - the parameter fence and the correlation fence on concrete laws, and
     rejection of the sharp bit target from the positivity premise.
7. Run failing Lean specifications before implementation and retain them in the
   witness file. Complete the zero-warning full build and axiom audit, the
   applicable gates, publication alignment (article, supplement, Table S1,
   primer), rebuilt tracked PDFs and a refreshed arXiv archive.

## Plan

- [x] Record the red regression run.
- [x] Add the uniform law, its divergence identity and the free-preparation
      theorem.
- [x] Add the prepended protocol, its shifted run, its cost and its two fences.
- [x] Build the witness, the contrast and the divergence.
- [x] Align publications and rebuild all linked artifacts.
- [x] Complete the build, checks and ledger record after resumption.

## Stop rule

Stop at one preparation stage, its cost identity and its fences. Do not add
preparation of a sharp law, funding the preparation from a source, gate
fabrication, continuous state spaces or local content dynamics to this change.

## Initial execution (inherited record)

The working tree was clean at `906afe2`. Baseline tracked artifacts: 53/44/88
pages for article, supplement and primer, zero overfull boxes, underfull counts
2/0/29, and the already-recorded article Table 1 overflow of 22.86668 pt.

The 13 retained specifications were written from the criteria above and run
before any declaration existed: 30 errors, every one an absent declaration.

One statement changed between the red run and the implementation.
`correlated_not_preparable` was first written with the candidate law on the
whole joint state rather than on the system coordinate, which does not typecheck
against the product form `preparation_product` proves. The corrected form is the
one that says what was intended.

Three points needed more than the first attempt. `positivity` cannot see through
a `ProbDist`'s own nonnegativity field, so `blank`'s obligation is discharged
from `skew.nonneg` instead. `simp only` on a definition used as a structure
field made no progress, so `prep_lands` computes the final law from `final`'s
own definition rather than through `preparation_product`; the generic theorem is
still exercised by the retained specifications. And `ProbDist.uniform` needed
`Nonempty`, which the existing `uniformDist` of `Phase1_PhaseSpaceCapacity` also
requires; the two are separate because that one is a bare function and the
information API here takes a `ProbDist`.

The unbounded-cost proof picks `ε = exp(-4c)/4` with `c = max B 0`. Then
`1/2 - ε ≥ 1/4` and `(1-ε)/ε ≥ 3 exp(4c) ≥ exp(4c)`, so the product is at least
`c ≥ B`. No limit is taken and no filter is needed.

## Validation before resumption (inherited record)

The full `lake build` passes with zero warnings. The default axiom audit covers
4,017 declarations in 63 modules using only `propext`, `Classical.choice` and
`Quot.sound`; fifteen explicit `#print axioms` checks on the new declarations
agree. All 13 retained regression examples compile without warnings.

All fifteen pre-commit hooks pass under `uv --project simulations` at the
repository root. The 143 existing Python tests pass, with 6 subtests.
`git diff --cached --check` passes.

Two-pass builds give 54/45/89 pages against the baseline's 53/44/88, with zero
overfull boxes. Underfull counts are 2/0/30 against 2/0/29: the extra box is the
new `\raggedright` cell of the primer's summary table at `docs/primer.tex:5373`,
the same kind as the twenty-odd boxes the rest of that table already
contributes. The article's Table 1 overflow is unchanged at 22.86668 pt. The
arXiv submission compiles from its unpacked tarball at 66 pages --- the same
count as before, because the merged NeurIPS layout absorbs the two added
single-column pages --- and carries the new passages.

No Lean axiom, Python source, dependency, reference, generated macro or
simulation result was added or changed.

## Resumption review — 2026-09-15

The implementation and PDFs were staged at `906afe2`, with only this task's
completion record unstaged. `tasks/todo.md`, `tasks/lessons.md` and
`CHANGELOG.md` had not been updated. The inherited build passes; the recovered
`prep-axioms.log` and `prep-hooks.log` support the headline and hook records
above. The original red log was not recovered.

The review corrected two claims that exceeded the statements. Zero
`memoryHeat` is zero mean log-ratio heat under a declared channel and reservoir
convention, not zero implementation or control cost. `sharp_prep_unbounded`
quantifies over strictly positive bit targets with a uniform input and thermal
scale one; it proves no infinite endpoint value and no impossibility theorem
for every exact-preparation implementation. The repository also contains laws
with zero masses. Publications and docstrings now state those scopes.

The witness uses a skewed law with full support, rather than the definite
hardware state first proposed. The cumulative entropy theorem requires the
initial law to be positive; the zero-heat identity itself does not. This keeps
the complete-run witness inside that theorem's actual hypotheses.

Three additional specifications failed on absent declarations in
`/tmp/preparation-resume-red.log` before implementation and pass in
`/tmp/preparation-resume-green.log`: `blank_ne_prior` makes the preparation
nontrivial, `known_parameter_not_preparable` rejects creating the parameter's
uncertainty even with a channel allowed to read it, and
`sharp_target_not_positive` rejects the exact bit target from the support
premise. They are retained beside the original 13 specifications. The new phase
is also explicitly imported by the root aggregator.

Remaining work: funding preparation from a source; preparation of the sharp
charge or other exact targets under an appropriate model; gate construction and
control; identifying a drawn unit with the stage's own reservoir heat; external
refuelling; and local content agreement as a separate agency task.

## Final validation — 2026-09-15

The completed `lake build` has zero warnings. The default axiom audit covers
4,022 declarations in 63 modules, using only `propext`, `Classical.choice` and
`Quot.sound`. Eighteen explicit headline axiom checks agree. All 16 retained
Lean specifications compile, including the three added through a red/green run
on resumption. All 143 existing Python tests pass.

All fifteen pre-commit hooks pass with `uv run --project simulations pre-commit
run --all-files`, including publication prose, Table S1, figures, staged-PDF
freshness, the arXiv manifest, leaves and placeholder proofs. The staged diff
passes `git diff --cached --check`. No Python source, dependency, reference,
generated macro or simulation result changed.

Final two-pass PDF builds have 54/45/90 pages for the article, supplement and
primer, against fresh builds of `906afe2` at 53/44/88. They have zero overfull
boxes and underfull counts matching that baseline (2/0/29). The inherited
primer's extra underfull box was fixed by making the new row's label ragged
right. Table 1's existing 22.86668 pt overflow is unchanged; its E34 row now
mentions the preparation account without changing the bridge's status.
The changed passages and summary rows were visually inspected. The 67-page
arXiv submission compiles from its unpacked tarball and passes freshness.

The bounded initial-prior item is marked complete in `tasks/todo.md`, with a
dated result record. Its broader physical-preparation and supply parent remains
open for the separate modelling work listed above.
