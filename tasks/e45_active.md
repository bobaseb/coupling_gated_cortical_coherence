# E45Active — an actuated scalar coupling model, 2026-09-14

## Intent and constraints

Finish the interrupted `Phase3_ActuatedCoupling.lean` change. A named finite
feedback step sets the amplitude of a specified spatial density through the
model law `density x = gain * drive * base x`, where `drive` is its actual joint
entropy reduction. The gain and profile are physical inputs; the mesh index is
spatial and is independent of learning time. This is an ensemble-level
constitutive law, not a microscopic actuator or a kernel on a product space.

The saved module fails on the mesh vertex universe and has no witness or chain
consumer. Preserve its intended separation: mesh regularity proves convergence,
and the named process's heat budget bounds its limit when the profile integral
is nonnegative. Do not claim the budget alone proves convergence or closes the
general E45/E45Active kernel-construction task. No new axiom, Python source,
simulation, dependency or citation is required.

## Success criteria and plan

1. [x] Run failing Lean specifications before completing the implementation.
2. [x] Compile the scalar model without warnings and connect its refinement
   theorem and budget bound to `Chain.E45Active` with the same process data.
3. [x] Exhibit a positive-drive noisy actuator on changing uniform grids.
   Test process dependence, gain dependence and profile dependence; reject a
   wrong limit and a heat-only cap that omits the gain/profile conversion.
   Compose the active chain with this actuated energy sequence.
4. [x] Align the article, supplement, status tables and primer; rebuild all
   three tracked PDFs and the assembled arXiv submission. Compare LaTeX warnings
   with HEAD and inspect the changed pages.
5. [x] Pass the full Lean build, axiom audit, explicit headline axiom checks,
   applicable repository gates and `git diff --check`. Record the completed
   scalar result and keep the microscopic/kernel question open in the ledger.

## Scope boundary

The fixed spatial profile and conversion gain are supplied constitutive data.
The step entropy is computed from the executed channel's initial and final
laws, but nothing derives this constitutive law from local actions, accounts
for a separate actuator's work, or constructs the cortical coupling kernel.
The passive edge, repeated learning and biological identification remain open.

## Completed result and verification — 2026-09-14

The interrupted module is complete. Its mesh vertex universe is explicit;
`ActuatedCoupling.actuated_coarseGrains` proves spatial convergence and
`Chain.e45Active_of_actuatedCoupling` supplies the active edge for exactly that
process and density. `Chain.actuated_limit_le_budget` separately consumes the
named process's entropy/heat bound. The eight hypotheses of the general chain
remain unchanged.

`Examples/ActuatedCoupling.lean` supplies the noisy two-bit actuator with
strictly positive drive, the profile `1 + |x - 1/2|`, and the same uniform
meshes used by the existing refinement witness. `energy_moves` checks the
first two energies differ; `idle_density`, `gain_matters` and `profile_matters`
fence the process and constitutive inputs. A gain calibrated to limit three
composes through `chain_active_actuated_jointly_satisfiable` using the existing
thermal-actuator heat comparison. This witness is separate from the
register-ledger witness; it does not combine all operations into one agent.
`actuated_wrong_limit_rejected` rejects target zero for that very sequence,
and `actuated_no_gain_free_budget_cap` rejects a scalar cap that omits the
conversion factors.

Verification:

- Failing specifications were run before implementation (`/tmp/e45-red.log`).
  The witness existential was annotated at vertex universe zero, matching its
  `Fin` vertices; the mathematical assertions then passed together
  (`/tmp/E45Spec.lean`, `/tmp/e45-green.log`) and remain as examples in the
  library. No admitted declaration remains.
- Full `lake build`: zero errors or warnings. The default audit covers 2,859
  declarations in 48 modules, using only `propext`, `Classical.choice` and
  `Quot.sound`; fourteen explicit headline axiom checks agree.
- All 39 existing PDF, figure, arXiv and publication-macro regression tests
  pass. All eight applicable pre-commit hooks, including the advisory hedging
  report, pass. Python hooks skip because no Python source changed. Hooks ran
  from the repository root: invoking pre-commit with `uv --directory simulations`
  and root-relative filenames skips those files, so the final invocation uses
  `uv run --project simulations pre-commit run --files ...`.
- Article, supplement and primer rebuilt and visually inspected: 41, 37 and
  79 pages. All final standalone logs have zero warnings and zero overfull
  boxes, matching freshly compiled HEAD; existing underfull counts are
  unchanged (2, 0, 26). Each changed source has its rebuilt PDF in the working
  tree, and all transitive source timestamps precede their PDFs.
- `prepare_arxiv.sh` rebuilt the 53-page submission and compiled it from the
  unpacked archive. Its source manifest passes freshness. `git diff --check`
  passes. No source or result was published.

The open ledger retains the full microscopic/kernel problem. A supplied
ensemble-level law connecting entropy reduction to scalar density is the
bounded result here; the constitutive law, physical installation cost and
coupling kernel have not been derived from the executed local actions.
