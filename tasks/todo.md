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

- [x] Implement and run `tasks/dynamic_ramp.md`.

Quantify bifurcation delay while `K(t)` crosses `K_c = 2D`; estimate the maximum
ramp speed for which the adiabatic curve remains accurate, compare it with the
astrocytic/CSF rate, and fit the early-foot exponent. This is first because it
tests the validity range of the paper's sole distinctive prediction. Run the
four ramp speeds one process per core only after reduced tests pass.

### S2 — Spatially decaying two-dimensional ephaptic kernel

- [x] Implement and run `tasks/spatially_decaying_kernel.md`.

Use FFT convolution on a periodic 128×128 sheet and row-normalize the exponential
kernel so total coupling is fixed across the length-scale sweep. Measure global
order, winding-defect density and the critical decay length in millimetres. This
is the simulation most able to count against the framework: fragmentation in the
empirical 0.1–0.3 mm band must be reported rather than tuned away.

### S3 — Dynamical selection of the coherent branch

- [x] Implement and run `tasks/dynamical_selection.md`.

Measure escape from the finite-N fluctuation floor below, at and above threshold;
compare steady states with the static self-consistency curve; and fit the early
growth rate against `(K - 2D)/2`. Keep the manuscript's “not dynamically
selected by theorem” statement unchanged.

### S4 — Finite-N evidence around propagation of chaos

- [x] Implement and run `tasks/propagation_of_chaos.md`.

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

### 2026-09-04 — S1 dynamic sleep-inertia ramp

Red tests fixed the numerical contract before the production run: deterministic
Euler--Maruyama evolution, exact checkpoint/resume equivalence, decimated
per-replica summaries without phase history, the independent log-density slope
estimator, post-critical sustained escape detection, finite-size controls and
known synthetic power-law/onset fits. `dynamic_ramp.py` implements the run and
atomic checkpoints; `dynamic_ramp_analysis.py` and `dynamic_ramp_report.py`
implement the declared analyses.

The full sweep used seed 20260903, 32 replicas, N=2000, D=1, dt=0.01 and
v in {0.1, 0.01, 0.001, 0.0001}. It completed 1,111,000 integration steps per
replica, with approximately two hours of elapsed compute across resumable
sessions. The N-dependence control added N=500 and 8000 at v=0.01; those legs
took about 16 seconds and four minutes respectively. Checkpoints store only the
current 32-by-N phase state, RNG state and decimated summaries.

Escape was operationalized as the first of three consecutive samples at
r >= 0.2, after K_c. All replicas escaped for the three slower ramps; only 5/32
did so at v=0.1 before the window ended, making that leg right-censored. Mean
delays were 0.1947, 0.0684 and 0.0253 for v=0.01, 0.001 and 0.0001, giving a
log--log exponent 0.443 against the predicted 1/2. At v=0.01 the delay increased
from 0.0619 through 0.1947 to 0.2341 across N=500, 2000 and 8000, qualitatively
matching the predicted sqrt(log N) dependence, though three sizes do not
establish that law.

Early-foot fits over 0.1 <= r <= 0.4 gave beta_eff = 0.964, 0.898, 0.471 and
0.417 from fastest to slowest: the square-root foot is recovered only in the
slow regime and moves toward the linear falsifier as the ramp accelerates. The
independent (a,r) traces stayed close to I1(a)/I0(a). Their post-critical RMS
deviations were 0.00245, 0.00599, 0.00689 and 0.00705; taking the slowest value
as Dev_0, no leg reached 2 Dev_0=0.01410. The specified v* is therefore not
bracketed, a negative result rather than grounds for extrapolating a number.

Artifacts are the six per-replica checkpoint files, four PNG panels and
`simulations/figures/DYNAMIC_RAMP_REPORT.md`. The result is finite-N heuristic
evidence. It proves no trajectory theorem, does not discharge adiabaticity or
dynamical selection, and does not turn the physical-unit conversion into a
measurement. The focused tests and the full ruff, formatting, strict mypy,
bandit, vulture, xenon, tach, prose, table and leaf gates pass.

### 2026-09-04 — S2 spatially decaying ephaptic kernel

Red tests fixed the numerical contract before implementation: the periodic
exponential kernel excludes self-coupling and has row sum exactly `K_0`; FFT
convolution agrees with an explicit periodic sum; wrapped plaquette circulation
detects balanced vortices and antivortices; the shared 0.1--0.3 mm constants
convert correctly to grid units; and seeded smoke trajectories are reproducible,
endpoint-inclusive and retain only decimated summaries plus one final snapshot.

The reduced 24-by-24 smoke sweep completed before production. The full sweep
used a periodic 128-by-128 sheet of extent 2.0 mm, seed 20260904, `K_0=8`,
thermodynamic diffusion 0.5 rad2/s, quenched Gaussian frequency spread 1.5
rad/s, `dt=0.01`, and 20,000 steps at each of 22 decay lengths. Its saved
integration runtime was 1,152 seconds. Seven transition-local controls were
added after the original 15-point sweep showed that a coarse two-point
interpolation would give false precision. Each length is independently
resumable; files contain decimated `r(t)` and defect density, the final phase and
winding maps, and configuration metadata, never a phase history.

With coherence operationalized as steady `r > 0.2`, the smallest interpolated
length above which every larger sampled length remained coherent was 0.0140 mm.
The transition region was metastable rather than monotone in a single seeded
trajectory: `r` ranged from 0.040 to 0.238 between 0.0085 and 0.0140 mm, before
jumping to 0.618 at 0.01467 mm. Defect density declined from 0.00157 at 0.0078125
mm to about 0.00001 at 0.01467 mm. In the empirical band, steady `r` was 0.9424,
0.9427 and 0.9427 at 0.1, 0.2 and 0.3 mm, while defect density was at most
2.5e-6. The declared finite model therefore did not fragment in the empirical
band; its operational boundary lay roughly seven times below the 0.1 mm lower
bound.

Artifacts are `spatial_kernel.py`, its six deterministic tests, 22 compact NPZ
runs, a JSON summary, the order/defect sweep figure and the cyclic final-phase
maps under `simulations/figures/spatial_kernel/`. The result is one finite-N,
single-seed parameter sweep. It does not establish a phase transition, exclude
metastability or seed dependence, measure cortex, validate the Fermi arithmetic,
or discharge any Lean obligation. The focused tests and the full repository
gates pass.

### 2026-09-04 — S3 dynamical selection of the coherent branch

Red tests fixed the numerical contract before implementation: the O(N)
mean-field reduction agrees with the explicit pair sum; seeded Euler--Maruyama
trajectories are reproducible and endpoint-inclusive; only decimated ensemble
order summaries are retained; the theoretical rate is exactly `(K-2D)/2`; and
a synthetic log-linear trace recovers its known rate while an underspecified
fit window is rejected. The first reduced sweep exposed an overly short
post-transient fit window at N=64; the corrected N=128 near-threshold smoke sweep
passed without relaxing the required `r < 0.3` cap.

The full run used seed 20260904, 500 replicas, N=1000, identical frequencies,
D=1, dt=0.01 and 5,000 steps at K in {1.6, 2.0, 2.8}. The early-growth sweep
used 1,000 steps at ten couplings from 2.2 through 3.1. Saved integration runtime
was 1,383.97 seconds. The three trajectory files are about 10 KB each and contain
configuration, decimated ensemble mean and standard deviation, the finite-size
reference and runtime, never phases or per-replica histories.

Steady ensemble-mean r was 0.06266 below threshold, 0.16049 at threshold and
0.67735 above threshold. The static coherent value at K=2.8 is 0.68270, a
residual of -0.00535. The nonzero subcritical value and the enhanced critical
value are finite-N fluctuations, not coherent fixed points, and are reported
alongside the 1/sqrt(N)=0.03162 reference rather than relabelled as selection.

All growth fits over t>=1 and r<0.3 had R-squared from 0.9738 to 0.9968. Rates
rose from 0.14398 at K=2.2 to 0.52282 at K=3.1. Their fitted law was
`lambda = 0.43240 K - 0.82318`, against the exact infinite-N prediction
`0.5 K - 1.0`: the slope was 13.5% low and the inferred zero crossing was 1.904.
The run therefore exhibits escape toward the coherent branch and nearly linear
early growth, while retaining the quantitative finite-size/time-window
discrepancy as a negative result.

Artifacts are `dynamical_selection.py`, its six deterministic tests, three
compact NPZ summaries, JSON metadata, three PNG figures and
`simulations/figures/dynamical_selection/DYNAMICAL_SELECTION_REPORT.md`.
`main.tex` remains unchanged and continues to state that dynamical selection is
not proved. This single-N, single-seed finite simulation establishes neither a
trajectory theorem nor propagation of chaos and discharges no Lean obligation.
The focused tests and the full repository gates pass.

### 2026-09-04 — S4 finite-N propagation-of-chaos diagnostics

Red tests fixed the numerical contract before implementation: circular pair
correlation is branch-cut invariant and rejects degenerate samples; seeded
sliced Wasserstein distance on a torus embedding detects dependence; the von
Mises density is normalized and even; and seeded Euler--Maruyama snapshots are
reproducible and retain only two oscillator samples plus one aligned density
sample. The reduced deterministic sweep completed before production.

The full run used seed 20260904 with deterministic per-leg offsets, 1,000
ensembles, identical frequencies, D=1, dt=0.01, 5,000 steps, K in {1, 3}, and N
in {10, 50, 100, 500, 1000}. The joint-versus-product statistic used a torus
embedding, 64 seeded sliced-Wasserstein projections and 30 matched bootstrap
resamples of 250 observations, avoiding the cubic exact multidimensional solver.
Saved integration runtime was 1,622.35 seconds.

The subcritical control showed finite-size convergence: mean r declined from
0.3726 to 0.0402 and absolute circular pair correlation from 0.0458 to 0.0010.
The sliced distance declined only from 0.0468 to 0.0419, exposing its
matched-sample estimator floor, while co-rotating density L1 error fell from
0.2640 to 0.1286.

The supercritical run produced a negative result for the specified
unconditional 1/N claim. Mean r stabilized near 0.72, while lab-frame pair
correlation remained between 0.459 and 0.525 across the full N sweep. The sliced
distance decreased from 0.1042 to 0.0812 but remained about twice the
subcritical floor. The unpinned coherent ensemble retains dependence through
its random collective orientation; conditional propagation of chaos modulo
that orientation is a different estimand and was not silently substituted.

The co-rotating density check did agree with the stationary target. At K=3 and
N=1000, measured r=0.7208 gave a=2.1624, density L1 error 0.1291 and Bessel
self-consistency residual 0.00191. Artifacts are `propagation_of_chaos.py`, seven
deterministic tests, ten compact NPZ snapshots, a JSON summary, one PNG figure
and `PROPAGATION_OF_CHAOS_REPORT.md`. `supplementary.tex` reports S3 and S4
alongside the existing S1 and S2 controls through `simulation_results.tex`,
which `simulation_tex.py` regenerates from their saved summaries and checkpoints
without rerunning production. Its drift test and the corresponding `AGENTS.md`
rule make that the standard publication path for computed simulation results.
This single-seed finite sweep proves
neither unconditional nor symmetry-quotiented propagation of chaos, and closes
no Lean or manuscript obligation. The focused tests and all repository gates
pass.
