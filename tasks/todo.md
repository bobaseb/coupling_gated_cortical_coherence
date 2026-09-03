# Physics of Consciousness — simulation work plan

**Replanned 2026-09-03.** The preceding ledger is archived unchanged at
`_archive/todo_2026-09-03_pre-simulations-replan.md`. It closed every scheduled
formalization, manuscript, audit and witness item through T5. Earlier ledgers
remain at `_archive/todo_2026-08-31_pre-composability-replan.md` and
`_archive/todo_2026-08-30_pre-strategic-replan.md`.

This pass is numerical. The detailed execution specifications live beside this
file under `tasks/`; this ledger records their order, gates and closure criteria
without duplicating them.

## Scope and success criteria

The six planned simulations provide **heuristic numerical evidence**. They do
not discharge `E45`, `E56`, `E67`, propagation of chaos, dynamical selection or
any other Lean obligation. A finite run exhibits behaviour at its sampled
parameters; it does not prove a general statement. Preserve that distinction in
script docstrings, captions, manuscript prose and pass records.

For every simulation:

1. State the intended claim, controls, parameter regime and failure condition
   before implementation. Follow red-green-refactor: add deterministic unit or
   regression tests before the production run.
2. Use `uv` and the existing `simulations/pyproject.toml`; do not create another
   environment or dependency file. Seed every RNG explicitly.
3. Reuse the Bessel-ratio implementation in `simulations/bifurcation.py` and the
   physical constants in `simulations/fermi_params.tex` or
   `simulations/fermi_estimate_check.py`.
4. Never apply linear statistics directly to wrapped phases. Use circular means
   and the Fisher–Lee/Jammalamadaka circular correlation where appropriate.
5. Draw the finite-size floor `1/sqrt(N)` on every order-parameter plot. Runs
   compared with the identical-frequency von Mises theory must use `omega = 0`.
6. Store only required summaries and snapshots, not full phase histories. Run a
   reduced deterministic smoke configuration before the full sweep.
7. Pass `ruff`, `ruff format --check`, `mypy --strict`, `bandit`, `vulture`,
   `xenon`, `tach`, the three repository check scripts, and relevant numerical
   tests. Compile any changed manuscript and compare warnings against `HEAD`.
8. Record parameters, seed, runtime, numerical result, negative result or failed
   assumption, generated artifacts, and what the run does **not** establish.

The shared corrections and measured Raspberry Pi 5 budgets are canonical in
`tasks/simulation_shared_notes.md`; read that file before taking any S item.

## Completed baseline — do not rerun without a reason

- The public-data collapse pipeline is implemented in
  `simulations/empirical_collapse.py`. Its independent log-density estimator and
  SOS bandpass correction are complete; the remaining protocol question is C1.
- The field-magnitude arithmetic is implemented in
  `simulations/fermi_estimate_check.py` and its constants are generated in
  `simulations/fermi_params.tex`.
- Existing illustration scripts—`bifurcation.py`, `kuramoto.py`,
  `mesh_refinement.py`, `structural_resonance.py` and
  `hardware_comparison.py`—remain baselines. S6 must revise
  `structural_resonance.py`, not create a near-duplicate.
- `pre-commit` is installed at `.git/hooks/pre-commit` and all ten hooks pass on
  the whole tree. **Five of them judge the whole tree rather than the staged
  files: `mypy --strict`, `bandit`, `vulture`, `xenon` (absolute B, modules B,
  average A) and `tach`. They fire whenever any Python file is staged, and then
  read every Python file in the repository.** So a new script that is
  unannotated, carries a C-rank block, or leaves a name unused blocks *any*
  later Python commit, not only the commit that adds it. Write new simulation code annotated and factored from
  the start; a `main` that both parses arguments and prints a report will be
  C-rank.
- `check-leaves` runs on any `.lean` change and fails two ways: on a module that
  has become a leaf, and on an `ALLOWED_LEAVES` entry that has acquired a
  consumer. The second is not a nuisance — it is how the baseline is kept
  truthful, and wiring `Phase3_MeasureThermodynamics` into the chain is what
  removed its entry.

## Work items — simulations, in order

Take one item at a time. Do not begin a lower-ranked full sweep while a
higher-ranked item is incomplete; reduced test runs may be shared where that
removes duplicated infrastructure.

### S1 — Dynamic sleep-inertia ramp and critical slowing down

- [ ] Implement and run `tasks/dynamic_ramp.md`.

Quantify bifurcation delay while `K(t)` crosses `K_c = 2D`; estimate the maximum
ramp speed for which the adiabatic curve remains accurate, compare it with the
astrocytic/CSF rate, and fit the early-foot exponent. This is first because it
tests the validity range of the paper's sole distinctive prediction. Run the
four ramp speeds one process per core only after reduced tests pass.

### S2 — Spatially decaying two-dimensional ephaptic kernel

- [ ] Implement and run `tasks/spatially_decaying_kernel.md`.

Use FFT convolution on a periodic 128×128 sheet and row-normalize the exponential
kernel so total coupling is fixed across the length-scale sweep. Measure global
order, winding-defect density and the critical decay length in millimetres. This
is the simulation most able to count against the framework: fragmentation in the
empirical 0.1–0.3 mm band must be reported rather than tuned away.

### S3 — Dynamical selection of the coherent branch

- [ ] Implement and run `tasks/dynamical_selection.md`.

Measure escape from the finite-N fluctuation floor below, at and above threshold;
compare steady states with the static self-consistency curve; and fit the early
growth rate against `(K - 2D)/2`. Keep the manuscript's “not dynamically
selected by theorem” statement unchanged.

### S4 — Finite-N evidence around propagation of chaos

- [ ] Implement and run `tasks/propagation_of_chaos.md`.

Sweep `N`, measure circular cross-correlation, matched-sample joint-versus-product
distance and stationary-density error. Use sliced Wasserstein or the specified
subsample/bootstrap scheme—never the cubic exact multidimensional solver at
`N = 1000`. Describe the result as convergence evidence, not a proof of
propagation of chaos.

### S5 — Frustration rescue and physical-unit consistency

- [ ] Implement and run `tasks/overcoming_geometric_frustration.md`.

Build a row-balanced Dale-law baseline, verify it remains at the finite-N floor,
then sweep the uniform modulatory term around `2D/N`. The useful result is the
conversion of the threshold to mV/mm at decay lengths 0.1, 0.2 and 0.3 mm—not
the analytically expected fact that a sufficiently strong positive term wins.

### S6 — Joint phase/plasticity dynamics

- [ ] Revise and run `tasks/joint_phases_plasticity.md`.

Extend `simulations/structural_resonance.py` with explicit fast/slow separation,
the full symmetric gradient, total-coupling renormalization, `r(t)` and a shuffled
control. Use the resolved genuine-NESS design: clustered frequencies with a
non-zero grand mean. Do not label `sum(v_i^2)/D` entropy production unless the
implemented drive supports that interpretation; otherwise label it a dissipation
function. This remains last because it overlaps existing code and does not
discharge `E45`.

## Carried forward — resolve alongside the simulation pass

### C1 — Make the empirical phase-estimation protocol internally consistent

- [x] Decide and document whether `(a,r)` is estimated instantaneously across
      at least 100 sites or by pooling the available 62 EEG channels over a
      stated short time window.

`main.tex` describes an instantaneous spatial distribution, while
`compute_ar_trace` pools 62 channels over 100 ms because the estimator requires
100 samples. Existing sensitivity checks find the residual stable from 5–100 ms,
but the estimand must still be named honestly. Prefer a protocol clarification
and explicit window-sensitivity panel over changing the result.

### C2 — Decide whether the E78 and E89 covers must coincide

- [x] Decide whether `chain` should require the cover reached by relaxation in
      `E78` to be the cover whose glued section becomes the fixed point in `E89`.

The current theorem remains correct because `UnifiedSelf` concerns the section
named by `E89`, but the types do not establish that the unity witnessed by E78
is the unity made reflexive by E89. Treat this as a separate formal change; do
not smuggle it into a simulation item or strengthen the edge merely to close it.

### C3 — Decide whether the phase-action module is ever to have a consumer

- [x] Decide whether `Phase5_TwistedGluing`'s results are to be reachable from
      the chain, which requires enlarging the local state so that phase — or an
      independent transition datum — is part of it.

Decided: no. The module is terminal by content, not merely unwired, and its
`ALLOWED_LEAVES` entry now says which. Enlarging the local state remains an open
modelling question and is recorded below, not scheduled.

## Recorded, not scheduled

- A dynamical mean-field limit/propagation-of-chaos theorem remains a research
  programme; S4 cannot close it.
- Enlarging the local state space so that phase, or an independent transition
  datum, is part of it would give `Phase5_TwistedGluing` a non-vacuous consumer.
  That is a physical modelling choice about what a local state is, with the
  presheaf, Derivation 5 and the frustration argument downstream of it. It is
  not to be undertaken to close a leaf gate; see the C3 record below.
- Overlap compatibility remains an explicit physical hypothesis. The existing
  equivalence and counterexample explain its content; do not schedule another
  attempt to derive it from the current class fields.
- The formalization paper and audit paper remain viable separate publications.
  Neither belongs in this numerical pass.
- PRX Life presubmission was explicitly declined. Direct submission, if any, is
  a later author decision rather than a repository task.
- Three of the four recorded leaf modules are terminal and are not to be
  re-litigated per pass; C3 settled that `Phase5_TwistedGluing` is the third of
  them rather than a deferred decision. `Phase3_KLBound` is superseded in part by
  `Phase3_PredictiveThermodynamics`, and its own header says which inference it
  no longer supports. `Phase5_PhaseLifts` proves the discrete winding
  obstruction and the chain has no winding node to consume it.
  `Phase5_TwistedGluing` proves that phase frustration produces no obstruction to
  glue around, so there is nothing for the chain to consume.
  `Phase8_CriticalExponent` ends in a prediction the manuscript consumes and
  Lean does not. The gate will say so if any of them acquires a consumer.
- The `.venv` console scripts embed an absolute interpreter path, so renaming
  the repository or moving the checkout makes `vulture`, `bandit`, `xenon`,
  `radon` and `tach` fail to spawn — which reads as a broken hook rather than a
  failing gate, and is how six red gates stayed invisible. After any such move
  run `uv sync --reinstall` in `simulations/` before trusting a green run.

## Pass records

Append one dated record per completed item: red test, implementation, reduced
run, full run, numerical findings, artifacts, manuscript changes, scope limits
and gates. Keep raw drafting history here or in the next archive, never in
`main.tex` or `supplementary.tex`.

### 2026-09-03 — C1 and C2

C1 names the EEG estimand as a pooled spatiotemporal distribution over 62
channels and 100 ms. The cached sensitivity run generated
`simulations/figures/window_sensitivity.png`; residuals at 5, 10, 20, 50 and
100 ms were -0.0261, -0.0079, +0.0017, -0.0019 and +0.0001, supporting
20--100 ms stability but not equivalence to an instantaneous distribution.

C2 requires the covers to coincide. `E89` now consumes the reached cover from
`E78`, and `chain` returns it in `UnifiedSelf`. The witness proves reachability
with a constant synchronized trajectory; this does not prove selection from an
incoherent state.

### 2026-09-03 — C3

Decided that `Phase5_TwistedGluing` is not to be reachable from `chain`, and
recorded the reason in `ALLOWED_LEAVES` in place of the previous one-line
"not wired into `chain`".

The premise the item was written on was too strong. It said no consumer is
constructible. One is: `gluesUpToPhase_of_isCoboundary` and
`gluesUpToPhase_of_phaseField` require a `PhaseAction`, not a free one, and
`probabilityPresheaf` admits the trivial action. But under the trivial action
`TwistedFamily.agrees_up_to_phase` reduces to exact overlap agreement, so that
consumer restates `Phase5_GlobalSection` and the chain link would carry no
information. Freeness — `IsFreeOn`, which the module's own docstring says fails
at the uniform phase distribution and for any structureless local state — is
what a non-vacuous consumer needs, and it is unavailable without enlarging the
local state.

The decisive point is content, not constructibility. `isCoboundary_of_phaseField`
and `gluesUpToPhase_of_phaseField` show that any Kuramoto configuration, twisted
or splay, supplies absolute patch phases whose differences are automatically a
coboundary, so the family glues. `gluesUpToPhase_of_isFreeOn` bounds the rest: a
non-zero class needs a hole in the cover. The module therefore ends in a negative
result — phase frustration creates no gluing obstruction — which is what
`supplementary.tex` already states, and a negative result has nothing downstream
to consume it. This places it with `Phase5_PhaseLifts` and
`Phase8_CriticalExponent`, not with `Phase3_KLBound`.

The 405 lines are the price of that negative result, and are not reduced by this
decision. What changes is that the exemption now records a closed judgement
rather than an open one.

Also de-referenced "the C1 shape" in the `Phase3_KLBound` entry: it pointed at
the previous ledger's C1 (`Chain.lean` composition, archived), not this ledger's,
which is the EEG estimand. A gate comment that cites a ledger label ages badly;
it now describes the shape instead.

Artifacts: `simulations/check_leaves.py`, `tasks/todo.md`. No Lean, manuscript or
simulation change. Gates: all ten hooks green.

One observation from running them, since it confirms the whole-tree hook hazard
recorded above. While S1's `test_dynamic_ramp.py` existed without its
`dynamic_ramp.py`, `mypy --strict` read the untracked test and failed on the
missing import, which blocked this commit although C3 touches no Python that
mypy objects to. A red test therefore blocks unrelated commits for as long as it
is red — the red phase of red-green-refactor is not commit-neutral here. S1's
module has since landed and the gates are green; the lesson is to close a red
test in the same sitting it is written.
