# E45 / E45Active — finite microscopic actuator and kernel limit

## Intent and constraints — 2026-09-14

Close the remaining E45 mathematical modelling item with an explicit finite
actuator, its executed state changes, installation work and a product-space
kernel reconstruction. Keep the scalar model and its negative results intact.
The general chain keeps its eight hypotheses: this is a constructive discharge
for a declared mechanism, not a deduction of a mechanism from a heat bound.

The hardware consists of finitely many spatial response modes. A microscopic
configuration specifies their occupancies; the same occupancies determine the
kernel and stored installation energy. Local changes change only the affected
mode products. An executed finite feedback channel pushes the configuration
law forward. Its expected kernel change is the average of those actual path
changes; work includes installation-energy change and reservoir heat. Profiles,
installation prices, channel and reservoir are physical model inputs.

Finite measurable spatial partitions reconstruct each sampled weight throughout
its cell pair. On a compact substrate, continuity and shrinking sample error
give kernel convergence and convergence of the cell-mass weighted energy.
The spatial index is independent of the number of executed control updates.
The passive branch uses a declared predictive system's actual joint law with
the same hardware; predictive efficiency alone selects no hardware or mesh.

No new axiom, dependency, simulation, Python source or reference is needed.
Cortical identification, field trajectory convergence, fabrication of the
fixed substrate, a continuing energy supply and observational learning are
separate tasks, not requirements of this finite microscopic model.

## Success criteria and execution plan

1. [x] Run failing Lean specifications for the new model and its regressions.
2. [x] Derive pathwise/local and expected kernel updates and installation work
   from the same microscopic occupancy and executed process.
3. [x] Construct finite cell-pair kernels and prove their kernel and scalar
   energy limits under spatial refinement, with explicit hypotheses.
4. [x] Witness a noisy physical switch on the atomless unit interval. Prove
   nonzero continuous coupling, action dependence, changing approximations,
   positive installation work, and rejection of zero-work/wrong-limit claims.
   Exercise passive and active E45 consumers on their named laws.
5. [x] Align the manuscript, supplement, status tables and primer. Rebuild all
   tracked PDFs and the assembled arXiv artifact; inspect changed pages and
   compare warnings against HEAD.
6. [x] Pass the full Lean build, axiom audit, headline checks and applicable
   publication/pre-commit gates. Complete the todo item in place and append a
   dated execution record with the model's scope.

## Completed result and verification — 2026-09-14

The finite microscopic model is complete. `Phase3_LocalActuator.lean` defines
`LocalActuator`: mode occupancies on configurations, fixed spatial profiles and
installation prices. The same occupancies give `kernel`, a reciprocal kernel on
`M × M`, and `storedEnergy`. `kernel_update` computes a transition's kernel
change from its changed occupancies; `kernel_update_local` leaves a pair
untouched when every changed mode has zero profile at one of its points;
`kernel_symmetric` and `kernel_nonneg` record reciprocity and positivity.
`pathWork` is the transition's external work and `installation_first_law`
evaluates its mean on the executed step as the expected stored-energy change
plus that step's mean heat. `expected_kernel_update` derives the ensemble
kernel change as the mean of those same pathwise changes, so an unrelated final
law does not substitute for the executed one.

`Phase2_KernelMesh.lean` defines `KernelMesh`, a finite measurable partition
with one sample per cell, whose reconstruction extends each sampled weight
throughout the whole cell pair. `energy_eq_integral` proves the cell-mass
weighted finite energy to be exactly that reconstruction's product-measure
integral, needing finite mass and measurable cells and neither continuity nor
refinement. `kernel_tendsto` and `energy_tendsto` give the kernel and energy
limits on a compact second-countable substrate of finite mass, and
`snap_tendsto_of_dist` reduces the sample hypothesis to a shrinking distance
bound. `KernelArrangement` bundles hardware, configuration law, substrate
measure and partition sequence; `coarseGrains` is its spatial limit.

`Chain.e45Active_of_localActuator` discharges the active spatial edge for an
arrangement holding a named step's final law, and `Chain.e45_of_localActuator`
discharges the passive edge for one holding a declared `PredictiveDissipation`'s
own joint law. Neither proof consults its premise: the refinement data supplies
convergence, which is the recorded content of both edges.

`Examples/MicroscopicCoupling.lean` witnesses one response mode on the unit
interval with profile `(4/3)(1 + x)` and unit price, switched by the existing
two-bit thermal channel. `action_changes_kernel` raises the installed kernel
from `(8/9)(1+x)(1+y)` to `(4/3)(1+x)(1+y)`; `closure_changes_kernel` takes the
pathwise value at the origin from `0` to `16/9`; `after_continuous` and
`after_pos` fence degeneracy. `work_formula` and `installation_work_positive`
give mean external work `(1 + log 3)/4 > 0`, and `zero_work_rejected` refuses a
zero-work claim on the same paths. `mesh_error` bounds the sample error of the
clamped left-endpoint partitions by `1/(n+1)`; `mesh_energy_zero`,
`mesh_energy_one` and `mesh_energy_changes` give `4/3` and `25/12`, and
`continuumEnergy_eq` gives limit three. The unit interval is atomless, so these
are cell masses rather than vertex weights. `remembered` reads the declared
predictive law on the same hardware, installing `(16/9)(1+x)(1+y)` with limit
four (`law_matters`), and `efficiency_selects_nothing` records that the two
declared systems differ by their whole dissipated work.

In `Chain.lean`, `microscopic_e45Active`, `microscopic_e45` and
`microscopic_e45_scrambled` exercise both consumers on their named laws;
`microscopic_wrong_limit_rejected` and
`microscopic_passive_wrong_limit_rejected` reject wrong targets for those same
sequences, the passive one against an inhabited `PredictiveBound`; and
`chain_active_microscopic_jointly_satisfiable` composes the active branch
through a product-space kernel at the existing field witness's coupling three.

Verification:

- Failing specifications were run before completing the implementation
  (`/tmp/E45KernelSpec.lean`, `/tmp/e45-kernel-red.log`); the same file passes
  with no errors afterwards (`/tmp/e45-kernel-green.log`).
- Full `lake build`: zero errors and zero warnings. The default audit covers
  3,028 declarations in 51 modules, resting only on `propext`,
  `Classical.choice` and `Quot.sound`; the added headline `#print axioms`
  checks agree. `check_sorry` reports no `sorry` in 53 Lean sources.
- All 143 publication, figure, arXiv and macro regression tests pass, as do
  every applicable pre-commit hook including the advisory hedging report.
  Python hooks skip because no Python source changed.
- Article, supplement and primer rebuilt and inspected: 43, 38 and 81 pages.
  Each final log has zero warnings and zero overfull boxes, and the underfull
  counts (2, 0, 26) match a freshly compiled HEAD. `prepare_arxiv.sh` rebuilt
  the 56-page submission and compiled it from the unpacked tarball; its
  manifest passes freshness.

## Scope boundary

Mode profiles, prices, occupancy readout, the reservoir convention and the
substrate measure are declared hardware data, which no heat bound supplies.
One prepared update is accounted for: fabricating the hardware, preparing its
initial configuration law and supplying continuing power are separate. The
spatial refinement index is independent of the number of executed updates.
`Chain.lean` §9's negative result stands unchanged — it is an obstruction to the
triangulation architecture, which carries no product structure and sites its
weights on a null set, and the cell-pair construction answers each point
separately rather than repealing it. Nothing identifies the substrate with
cortex or the modes with a physical field, and no argument makes predictive
efficiency select this hardware. Field trajectory convergence, observational
learning and the general chain's eight hypotheses are unchanged.
