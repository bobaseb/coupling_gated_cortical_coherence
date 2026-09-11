# F5 and F6: designs fixed before execution

Declared 2026-09-10, before implementing the estimators or inspecting new runs.
The studies are separate changes in scientific scope. F5 runs first. Neither
study expands R1--R5 into an empirical programme or identifies an EM mechanism.

## F5: sustained squared-drift reduction and anti-alignment

**Intent.** Determine whether one bounded design supplies coexistence of lower
time-averaged squared drift, coherent phases and loss of alignment with the
frequency-cluster template. This is a finite-run question, not monotone descent
or a thermodynamic entropy-production claim.

**Fixed substrate.** Reuse `structural_resonance.Config` and its dynamics,
initialization, frequencies, projection and objective `sum(v**2)/D`. N=100,
D=0.1, total coupling=400, physical duration=400, dt=0.01. Only the learning rate
and physical update interval vary: the Cartesian product of rates
`[0.01, 0.05, 0.2]` and intervals `[0.05, 0.5]`. A paired frozen arm has the same
initial state and phase-noise stream. No additional matching controls are needed
to decide the stated coexistence question.

**Estimator and criteria.** At every integration step, measure squared drift
and order on the state used for that step, after any update at its left endpoint.
Average those measurements within complete physical update intervals; exclude
the terminal endpoint. Retain the existing immediate post-update readout too.
The two assessment windows are `[200,300)` and `[300,400)`. Each must have an
objective mean at least 5% below the paired frozen arm and mean order at least
0.8. Anti-alignment requires the second-half time mean of within/between
coupling to be at most 0.8 and at least 0.1 below frozen, and the final frequency
partition to have percentile at most 0.05 among 2000 size-preserving random
partitions. The kernel is constant between updates, so its left-endpoint interval
value supplies its exact time weighting. Every condition is conjunctive.

**Selection and confirmation.** Tuning seed: `20260910`. Held-out seeds:
`20261910, 20262910, 20263910`; none is an existing production seed. Among tuning
cases meeting objective/coherence criteria, select the smallest worst-quarter
objective/frozen ratio, breaking exact ties by learning rate then interval.
Selection receives no alignment values. Confirm that one choice on every held-out
seed at dt=0.01 and dt=0.005, keeping duration and physical update interval fixed.
Run these confirmations even if tuning alignment fails. Coexistence is confirmed
only if every held-out run at both steps meets all criteria. If no tuning case
meets objective/coherence criteria, stop without confirmation. Do not try a
second candidate or expand the grid after inspecting alignment or confirmation.

**Budget and validation.** One reduced N=12, duration=2 check is outside inference.
At most 19 full trajectories, 1,000,000 integration steps, and 30 minutes of
simulation wall time, with one BLAS thread. A budget overrun is incomplete, not
a negative scientific result. Tests first: expose post-update sampling bias,
check complete-interval endpoints and time weighting, preserve the original
dynamics, pin alignment-blind selection and fixed physical cadence at smaller dt.
Save every tuning and confirmation outcome, compact interval checkpoints and a
summary. Report and TeX generation read those artifacts without integration.

## F6: mechanism recovery from ideal stationary phase observations

**Intent and observation scope.** Test the distributional arm of the proposed
protocol first: successive equilibrated phase distributions, their independent
log-density concentration estimate and circular order. Ideal means the density
is known exactly in each window, with physical window order retained, no noise,
no filtering and no sampling uncertainty. Individual paths and within-window
increments are not observed; no independent K or D measurement has been supplied.
This does not test an ideal continuously observed phase-trajectory protocol.

**Analytic families.** In the identical-frequency rotating frame compare:

1. Coupling increase: `K=q(s), D=1`, where `q(s)=1.5+(b-1.5)*s`.
2. Diffusion decrease: `K=b, D=b/q(s)`.
3. Independent oscillators under a common phase-restoring drive:
   `dtheta=-h(s)*sin(theta-psi) dt + sqrt(2)*dW`, with
   `h(s)=q(s)*r(q(s))`, and no inter-oscillator coupling.

Here s is the declared window coordinate in `[0,1]`, b ranges over `[2.6,4]`,
and r(q) is the stationary coherent branch, zero for q<=2. The shared drive
uses a single prescribed amplitude schedule, not a force inferred from each
oscillator. It is an observationally matched alternative, not a claim that every
shared drive has that schedule. Its stationary concentration is h, which equals
the other families' K*r/D. Absolute orientation is a nuisance shared by all
families. Analyze this equivalence before numerical recovery.

**Finite ideal feasibility cases and fitting.** Use nine equally spaced windows,
4096 periodic phase-grid points, b=`[2.6,3.2,4]`, and psi=`[0,0.7]`: six cases per
family. Fit b within `[2.6,4]` using least-squares concentration trajectories, with
concentration estimated by regression of log density on cosine and sine;
estimate r independently by the circular density integral. Inference receives
only the observed densities and declared window coordinates, never true b, K, D
or generating labels. The same parameter range and predicted concentration
curve is used for each model, as required by their analytic equivalence.
Report all model scores and the confusion matrix, splitting ties within 1e-10
equally and reporting that fraction as an expected tie allocation, not random
classification successes. Require a unique correct model on at least 80% of
cases in each family to proceed.

**Stop rule and budget.** At most 18 ideal cases and two minutes of computation.
If analytic equivalence and the ideal test prevent unique recovery, stop: add no
noise model, larger sample, temporal filter or new model family. Report the
ambiguity and the missing observation. Resolved phase increments can in principle
estimate diffusion from quadratic variation and drift from conditional means;
separating endogenous coupling from common forcing also needs a measured drive
or a controlled perturbation. These are proposed next measurements, not validated
by the stationary pilot. If unique discrimination unexpectedly survives, inspect
that conflict with the analytic calculation before considering the conditional
held-out simulation stage; do not treat numerical noise as mechanism evidence.

## Deliverables and completion

- Tests before implementation; reduced checks before full runs.
- Saved design, scripts, all compact results, reproducible reports and macro
  drift tests. Report generation never runs the studies.
- Present-tense publication claims scoped to the actual observations/results;
  retain fixed-phase mathematics and do not claim finite runs prove impossibility.
- Rebuild every affected tracked PDF and the assembled arXiv submission.
- Run the full Python test suite and repository quality/publication gates.
- Close F5 and F6 with outcome records in `tasks/todo.md` and `CHANGELOG.md`.
  Other audit tasks are not silently marked complete.
