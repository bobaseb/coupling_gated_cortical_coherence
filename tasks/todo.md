# Physics of Consciousness — scheduled extensions and research

**R-items triaged 2026-09-16.** Every R-item was assessed for whether it is
reachable in this repository and for what closing it would buy. Three tractable
aspects move into the scheduled bucket as N7–N9; the R-items they came from stay
open on the residues that need measurements this repository does not have. The
triage, and the reason each of the other nine stays unscheduled, is recorded in
the R preamble. This pass changes no claim, proof, numeral or deliverable.

**Follow-up scheduled 2026-09-16.** N1–N6 below are bounded extensions of the
current results; R8–R12 record the broader research directions. None is a
prerequisite for publishing the present conditional framework. K1–K5 remain
complete, R1–R7 retain their scope, and the two existing P-items are unchanged.
Scheduling these extensions does not report them as proved or implemented.

**Completed and documented 2026-09-16.** N1–N6 are proved and witnessed in
`7833bbf`; the manuscript, supplement, primer and rebuilt PDFs now reflect
them. The commit review and publication checks are recorded in
`tasks/n_manuscript_review.md`. The leaf-checker correctness finding there is
a separate gate-repair task; no R- or P-item has been closed.

**N7–N9 measured 2026-09-16.** The three numerical items are run, saved and
reported in `tasks/numerical_extensions.md`; N1–N9 are all closed. Their **publication alignment is deliberately not part of that pass**:
no numeral has reached `main.tex` or `supplementary.tex`, no macro has been
generated and `simulation_results.tex` is unchanged, so the four sentences the
measurements bear on are listed at the end of that file, and are tracked as
open work in **section M** below. R2, R4 and R6 keep the residues the
2026-09-16 triage left them.

**R8 triaged 2026-09-16.** N8's regime statement was the input R8's reduction
criterion waited on, so R8 was assessed the way R2, R4 and R6 were. Four
reachable aspects are registered below as N10–N13 — two Lean, two numerical —
and R8 is narrowed to the residue. That triage pass scheduled and changed no
claim, proof, numeral or deliverable; the four items were closed later the same
day and their pass records are at the end of this file.

**N10–N13 closed 2026-09-16.** The two Lean items are proved and witnessed in
`Examples/FundedCoupling.lean` (§29) and `Examples/EvolvingCoupling.lean` (§30),
with their general statements in `Phase9_InstalledCoupling.lean`; the two
numerical items are run, saved and reported in
`tasks/coupling_rate_extensions.md`. Every N-item is now closed. As with N7–N9,
**publication alignment is deliberately not part of either pass**: no numeral has
reached `main.tex` or `supplementary.tex`, no macro has been generated, and the
sentences the measurements bear on are listed at the end of that file. Together
with N7–N9's, they are now **section M** below — eight sentences, open and
actionable here, so that two deferrals are tracked rather than merely explained.
R8 keeps the residue the 2026-09-16 triage left it.

**Replanned 2026-09-15.** The preceding ledger is archived unchanged at
`_archive/todo_2026-09-15_pre-coupling-budget-replan.md`. It closed A1–A7,
B1–B6, C1–C4, D1–D2, E1–E4, F1–F6, L1–L4, the five agency items, the three
agency stretch items, the steady-state section and both actionable P-items, and
left R1–R7 and two author/journal P-items open; those carry forward below
without change of content. Earlier ledgers are
`_archive/todo_2026-09-09_pre-simulation-audit-replan.md`,
`_archive/todo_2026-09-03_pre-simulations-replan.md`,
`_archive/todo_2026-08-31_pre-composability-replan.md` and
`_archive/todo_2026-08-30_pre-strategic-replan.md`.

This file replaces the old one because **the agency extension built two-thirds
of a bridge into the coherence model and stopped, and the missing third is a
theorem rather than a research programme.**

## The gap at the 2026-09-15 replan

The following motivation records the state before the K pass; its completion
and the precise scope of the installed-energy result are recorded below.

Section 5 is 42% of the article and the abstract does not mention it. The one
result that would justify that share does not exist yet, and both halves of it
are already proved.

**The half with the budget has no kernel.** `Chain.actuated_limit_le_budget`
gives `A.continuumLimit ≤ A.gain * (budget / A.temperature) * ∫ base`: an
agent's heat allowance caps the coupling amplitude it can actuate.
`Phase3_ActuatedCoupling.lean` calls this "the relation that was missing", and
it is the only arrow in the development pointing from a thermodynamic resource
into the coupling model. But its limit is a **scalar** energy `∫ f_A dμ`. The
Discussion already records the no-go: coarse-graining the discrete couplings
"converges a scalar energy and produces no kernel". A scalar never becomes a
coupling constant, so this bound never reaches a threshold statement.

**The half with the kernel has no budget.** `KernelArrangement` installs a
genuine product-space kernel and `KernelArrangement.coarseGrains` converges its
cell-pair energies to
`continuumEnergy = ∫ z, kernel z.1 z.2 ∂(volume.prod volume)`.
`Phase3_LocalActuator.lean:150` says it outright — "no field of this structure
is a budget" — and line 202 repeats it for the convergence hypotheses. Nothing
bounds that limit by anything the agent spends.

**They are the same quantity.** `Phase8_ContinuousField.mean_field_coupling sys`
is `∫ x, ∫ y, sys.K x y`, and `IsEMFieldCoupling.coupling_is_mean_field` makes
that *equal to* the `K` of `critical_coupling D = 2 * D`. So the microscopic
branch's continuum limit is, up to Fubini, exactly the coupling constant that
sets the synchronization threshold. The composition has never been made.

**What it would buy.** A statement of the form *a substrate whose installation
prices and allowance are such-and-such cannot reach `K_c = 2D`* — a minimum
installed energy for coherence, with `Phase8`'s subcritical uniqueness on the
other side of the contrapositive. That would be the first result in which
thermodynamics **predicts** something about coherence rather than accompanying
it, and it is the result that makes Section 5 earn its length and gives the
abstract something to say about it.

**What it would not buy, and why that is a finding rather than a defect.** The
honest theorem is about *installed energy*, not dissipated heat.
`Examples/RegisterBath.lean` is the reason: a deterministic reversible gate is
not a strictly positive reduced channel, its transition log-ratios vanish on
every realized path, and local detailed balance assigns it none of the heat its
bath receives. A reversible installation moves energy at zero entropy
production. So the fence already proved explains the shape the positive result
has to take, and K5 below is where that is recorded rather than glossed.

## How this ledger is ordered

**K1–K5 completed 2026-09-15.** K1 identifies the
coupling by Fubini, K2 bounds it by installed energy, K3 composes the threshold
and stationary-density consequences, and K4 supplies the witnesses and
rejections. K5 aligns the publication, primer and rebuilt deliverables.
The pass is recorded in `tasks/k_completion.md`.

**Editorial follow-up completed 2026-09-16.** The main article now integrates
the installed-energy condition with coherence and the scalar content bounds
with compatibility, while the detailed agency models have separate technical
sections in the supplement. Main source length is 5,841 whitespace words
(including TeX), and the rebuilt main PDF is 39 pages. Scope clarifications,
preservation checks and rebuilt deliverables are recorded in
`tasks/structural_rewrite.md`. This pass changes no R- or P-item status.

N-items are the scheduled follow-up: each has a concrete result, witnesses and
a stopping point. N1–N6 are Lean extensions and are complete. N7–N9 were added
2026-09-16 and are numerical: they are the aspects of R4, R2 and R6 that need no
measurement this repository lacks. They are complete as measurements and their
publication alignment is outstanding; they were run in one pass rather than in
the ascending-effort order they were written in, because none consumed another's
output. N10–N13 were added 2026-09-16 from R8 — N10 and N11 Lean, N12 and N13
numerical, each pair being a result and the fence that keeps it honest — and are
complete, with the same publication alignment outstanding.
M-items are the publication alignment N7–N9 and N12–N13 both deferred: eight
sentences, actionable here, and the only open work that changes what the
publication says. R-items require broader theory, new physical identifications
or empirical work. P-items are submission mechanics and are blocked on someone
else. The N- and R-items do not reopen publication readiness; the M-items are
where their findings reach it.

Take one item at a time. N3 consumes N2's specified observation mechanism; N6
can reuse N5's indistinguishability bound. N1, N4 and N5 can be completed
independently. Among the numerical items N7 is independent, N8 produces the
regime statement R8's reduction criterion would consume, and N9 may use N1's
normed-space extension for its content model but does not require it. The
completed K pass followed K1 before K2 because the latter names the quantity the
former identifies.

## Standing constraints for the completed K pass

- **This is theory work with a stopping point.** The 80/20 constraint carries
  forward from the archived ledger: correct unsupported claims and retain
  supported results, without expanding into incremental sweeps. If K2 turns out
  to need a hardware model richer than one declared constant, stop and record
  that in K5 rather than building the richer model.
- **No new empirical results are required, and none may be invented.** Nothing
  in K1–K5 needs a simulation, a sweep or a reference. If an item appears to,
  it has been misread.
- **No Lean axioms.** `Audit.lean` is a default `lake` target and every new
  headline result carries an explicit `#print axioms`.
- **Red first.** Each K-item gets a regression that fails before the
  declaration exists (AGENTS.md §1).
- **The publication is not a changelog** (AGENTS.md §5) and **a tracked PDF is a
  deliverable** (AGENTS.md §6): the K5 prose change and its rebuilt PDFs go in
  one commit.

## K — An installed-energy bound on coherence

### K1 — Identify the installed kernel's energy with the mean-field coupling

- [x] Prove `KernelArrangement.continuumEnergy A = mean_field_coupling sys`
      whenever the arrangement's installed kernel is the field's kernel and the
      substrate carries a probability measure.

**Why it is first.** `continuumEnergy` integrates against `volume.prod volume`
and `mean_field_coupling` is the iterated `∫ x, ∫ y`. These are the same number
and the development never says so, which is why the microscopic branch's limit
has never been read as a coupling constant.

**What it costs.** `MeasureTheory.integral_prod` or `integral_integral`, whose
side conditions are already fields: `KernelArrangement.kernel_continuous` gives
joint continuity, `volume_finite` gives finiteness, and
`IsEMFieldCoupling.domain_probability` gives the normalization in which the
mean-field derivation of `K_c = 2D` is carried out. Integrability on a compact
substrate with a continuous kernel and a finite measure should be immediate.

**Scope to state in the docstring.** The identity is about the two integrals and
nothing else. It does not assert that any physical field's kernel *is* the
installed one; that identification is `E56` and stays a physical commitment.

**Completion.** The identity is proved, a regression exhibits it on the existing
`Examples/MicroscopicCoupling.lean` arrangement, and Table S1 records it.

### K2 — Bound the installed coupling by the installation energy

- [x] Prove `KernelArrangement.continuumEnergy A ≤ κ * storedEnergy`, for a
      declared hardware constant `κ` relating each mode's spatial mass to its
      price.

**The shape of it.** `LocalActuator.kernel z x y = ∑ i, occupancy z i * profile i
x * profile i y`, so the double integral factorizes:
`∬ kernel = ∑ i, occupancy z i * (∫ profile i)²`. And
`storedEnergy z = ∑ i, price i * occupancy z i`. So the bound holds termwise
under exactly one declared hypothesis — `(∫ profile i)² ≤ κ * price i` for every
mode — plus nonnegative occupancies. **`κ` is coupling installed per unit
installation energy, and it is hardware data, not something a heat bound
supplies.** Name it as a field and fence it with a regression, in the manner of
`ActuatedCoupling`'s `gain` and `base`.

**The expectation step.** `KernelArrangement.kernel` is
`expectedKernel A.law`, the average of `kernel z` over the configuration law, so
the bound has to pass through that average. `expected_kernel_update` is the
existing statement of how the executed step moves it. Bound the mean by the mean
of the bounds; the inequality is preserved because the law is a probability
distribution.

**What must not happen.** Do not let `κ` absorb the threshold. A constant chosen
after seeing `2D` makes the K3 statement vacuous. `κ` is declared from the
profiles and prices alone and the regression must reject a `κ` read off the
target.

**Completion.** The inequality is proved, the declared hypothesis is a named
field, a regression rejects negative occupancy and a `κ` that fails the mode
condition, and the scope paragraph says `κ` is hardware data.

### K3 — A minimum installed energy for coherence

- [x] Compose K1 and K2 with `critical_coupling` to conclude that an
      arrangement whose installed energy satisfies `κ * storedEnergy ≤ 2 * D`
      does not exhibit the phase transition, and carry that to the incoherent
      stationary state.

**The statement.** From K1 and K2, `mean_field_coupling sys ≤ κ * U`.
`Phase8_ContinuousField.exhibits_phase_transition sys` is
`mean_field_coupling sys > critical_coupling sys.D`. The contrapositive is
immediate: `κ * U ≤ 2 * D` excludes the phase transition.
Then `Phase8_SelfConsistency`'s subcritical side gives that the incoherent
solution is the only stationary one, and
`Phase8_Linearization.incoherent_instability_iff` already says a mode of
positive index grows exactly above `2D`, so the excluded regime is the one
where nothing grows.

**Say it in the direction it holds.** This is a **no-go**: insufficient
installed energy forbids the coherent branch. It is *not* a claim that
sufficient energy produces coherence: `κ * U > 2D` bounds the coupling from the
wrong side, and K2's inequality does not reverse. State the sufficient direction
nowhere.

**Completion.** The theorem is proved, `#print axioms` is clean, the one-sided
scope is in the docstring and in Table S1, and a regression rejects the
converse.

### K4 — A witness with numbers

- [x] Discharge K1–K3 on a concrete arrangement, reusing
      `Examples/MicroscopicCoupling.lean`'s hardware rather than building new.

**What it must exhibit.** Declared profiles, prices and a `κ` satisfying K2's
mode condition; a configuration whose installed energy falls below `2D/κ` and
which the K3 theorem excludes from coherence; and a second configuration above
that line which the theorem says **nothing** about, so the one-sidedness is
visible in the witness and not only in the prose.

**Rejections to carry**, in the manner of the existing active witnesses: a
negative price, a mode whose spatial mass exceeds its budgeted share, a `κ`
fitted to the threshold, and a configuration where the claimed exclusion fails
because the occupancies are not nonnegative.

**Completion.** Every declaration is checked, the witness is referenced from
Table S1 and `check_leaves` still passes.

### K5 — What the bound is about, in the manuscript

- [x] State K3 in the thermodynamic composition section and in the abstract, and record in the same pass
      what it is not.

**The prose change.** Section 5 currently reaches `E45Active` through two models
and lets the reader discover that only one carries a budget and only the other
carries a kernel. After K3 it should say the composed thing: the installed
kernel's mean-field coupling is bounded by the installation energy, and below
`2D/κ` the coherent branch is unavailable. This is also the clause the abstract
is missing — it presently says nothing about the thermodynamic half of the paper
at all.

**Three limitations go in with it, in the same paragraph, not in a later one.**

1. **Installed energy is not dissipated heat.** `Examples/RegisterBath.lean`
   exhibits a reversible gate that installs at zero entropy production, so no
   version of K3 licenses reading `U` as a dissipation. The manuscript already
   says positivity and local detailed balance are inputs of the resource model
   rather than consequences of microscopic reversibility; K5 is where that
   sentence acquires a consequence.
2. **`κ` is declared hardware data.** Changing the prices or the profiles at
   fixed process changes the bound, exactly as changing `gain` or `base` changes
   Eq. (17). No heat bound supplies `κ`.
3. **One direction only.** Per K3, and it must be said where the result is
   stated rather than in the scope list at the end of the Discussion.

**What this does not close.** `E56` remains a physical commitment: that a
cortical field's kernel is the installed one is not a Lean question, and K3
constrains a declared arrangement rather than cortex. Say so in the same place.

**Completion.** Section 5 and the abstract carry the result and its three
limits, Table 1 and Table S1 agree with `Chain.lean`, `check_prose`,
`check_hedging`, `check_tableS1`, `check_figures` and `check_pdf_freshness`
pass, and the rebuilt PDFs are in the same commit as the sources.

## N — Scheduled follow-up, not publication prerequisites

**Intent and acceptance rule for N1–N6.** Connect existing constructions or
remove an unnecessary restriction. A completed item must supply a new
consequence or discharge a previously separate modelling obligation for a
declared mechanism; renaming an assumed conclusion or adding an unused
structure is insufficient. Write failing Lean specifications first, retain
nondegenerate witnesses and rejection cases, and require the warning-free build
and axiom audit. Changes to published claims include the matching prose, tables
and rebuilt tracked PDFs. No production sweep or new empirical result is
required by these items.

**Intent and acceptance rule for N7–N9.** These are numerical and each needs a
new design, so each gets a written specification before any run. A completed
item must supply a saved summary, a generated macro for every numeral that
reaches the publication, and at least one rejection case the estimator or
comparison is required to fail. None may be closed on a specification —
publishing what an observable must satisfy already failed to close R6 once. A
negative result closes its item: if the quantity does not separate at the stated
sensitivity, the reportable finding is that it does not. Regenerating a macro
must never rerun a production sweep (AGENTS.md §3) and no new hand-typed
numerals enter the publication.

### N1 — Content agreement for vector-valued observations

- [x] Generalize `Phase5_ContentDynamics` from real outputs to a real normed
      vector space, with finite-dimensional vectors as the principal example.
      Use distance for encoder agreement and the norm triangle inequality for
      the convex observation update. Recover the existing scalar results as
      specializations and retain the same coherence-derived residual and
      finite-horizon error floor.
- [x] Permit a shared encoder for each shared spatial quantity, with a uniform
      Lipschitz bound, rather than requiring every site to report the same
      scalar. The encoder at an overlap must still be the same for both
      patches; identify that obligation explicitly.
- [x] Supply a nonconstant two-component witness, a rejection of inference
      from agreement of one scalar projection to agreement of the whole vector,
      and a phase-locked example whose independent content coordinates disagree
      when the encoder hypothesis is removed.

**Win and stop.** Scalar output is an implementation restriction of the current
proof, not an impossibility result for richer content. Prove the normed-space
extension, including its consumer in the observation update, and stop there.
Do not infer arbitrary vector agreement from phase order, identify neural
embeddings, or claim that the probability-measure sheaf has been replaced by a
vector sheaf. Different local coordinate systems belong to R11.

### N2 — A phase-derived observation channel used by a finite learner

- [x] Construct one finite-output sensor channel from a declared phase readout
      and phase law, and feed those observations to the existing
      `FiniteObservationalLearner` or `MemoryAgent`. The hidden environmental
      parameter enters only the world/sensor law; the learner's update and
      action readout must not read it or supplied task values.
- [x] Prove a finite-horizon information or task-performance comparison from
      the actual composed law. Include an informative case and a control with
      the same phase coherence but observations independent of the unknown
      parameter. Keep phase order, overlap agreement, environmental information
      and reward distinct; correlation between internal observations need not
      be information about the world.
- [x] Derive the observation probabilities from the chosen readout instead of
      postulating that greater coherence improves accuracy. State which
      phase-to-world relation makes any positive comparison work, and keep
      phase-independent content as a rejection case.

**Win and stop.** The agent actually consumes an observation produced by the
phase construction, and the comparison exposes the assumptions connecting
coordination to useful information. One finite sensor and one learner suffice.
A stationary phase law is a supplied regime, not a proof of dynamical
selection. Continuous phase dynamics, automatic truth learning and a universal
monotonic relation between coupling and performance are outside this item.

### N3 — Learning, installed coupling and work on the same executed process

- [x] Attach the existing `LocalActuator` occupancy readout to the register or
      configuration changed by N2's learner. Compute the before/after expected
      kernel, installed energy and installation work from the same executed
      laws, using `expected_kernel_update` and `installation_first_law`.
- [x] Give a bounded, nondegenerate witness in which observation-driven updates
      change the subsequent installed coupling relative to a frozen or
      uninformative controller. State the common resource allowance and the
      actual work of both processes; reject substitution of an unrelated final
      law or a free installation claim.
- [x] Apply `PricedArrangement` to that hardware and law, obtaining its
      necessary energy condition for the identified scalar coherent branch.
      Preserve the distinction between installed energy, external work and
      reservoir heat. Neither a heat allowance nor the upper bound
      `K ≤ κ U` supplies a sufficient condition for coherence.

**Win and stop.** The learning and coupling claims concern one mechanism and
one account of its work, rather than compatible examples with independently
chosen laws. A finite sequence of updates is enough. This does not establish
that the resulting coupling dynamically produces N2's next phase law. A full
feedback loop, maintenance/leakage costs and a finite source that actually
halts the process on exhaustion belong to R8.

### N4 — A resource-matched finite-region hardware comparison

- [x] Extend the Phase 7 comparison to finitely many measurable cells of finite
      positive measure, using `KernelMesh` where possible. For disjoint cells
      with masses `m_i > 0`, embed a symmetric, nonnegative, zero-diagonal
      coupling matrix by setting
      `K(x,y) = A_ij / (m_i m_j)` on cell pair `(i,j)` and make phase constant
      on each cell, with zero coupling outside the cell pairs. Prove that the
      continuum kernel integral and phase
      correlation equal their respective discrete sums. The matched resource
      here is total coupling weight; identifying it with joules needs priced
      hardware separately.
- [x] Use this identity to delimit `fieldCorrelation_sited_eq_zero`: ordinary
      point-supported functions under an atomless measure vanish, whereas
      finite-region reconstructions need not. Retain the genuine fixed-support
      rigidity gap at matched coupling resource, with a control whose allowed
      support includes the best distinct pair and hence has no forced gap.
- [x] Align the standalone `simulations/hardware_comparison.py` description and
      plot labels with its actual fixed-versus-adaptive finite matrices. Its
      current GPU/biology and continuous/rigid labels do not describe measured
      devices. Do not reuse that illustration as empirical hardware evidence;
      update its generated figure if the script is corrected.

**Win and stop.** Separate a physical support constraint from an artefact of
representing finite sites with the wrong continuum measure. The result concerns
an explicitly defined observable, not consciousness or computational power;
the piecewise-constant embedding also supplies no continuous-field dynamics.
Neither GPU emulation of a kernel nor the absence of a particular native
coupling settles physical realization of the proposed conscious mechanism.
Device calibration and architectural exclusion claims belong to R9.

### N5 — Self-reconstruction limits from indistinguishable encodings

- [x] Define bounded-error reconstruction on a declared family of relevant
      macrostates, with a metric, encoder `E`, readout `R` and tolerance
      `ε ≥ 0`. For `E(s) = E(t)`, prove
      `d(s,t) ≤ d(s,R(E(s))) + d(t,R(E(t)))`, hence at least one reconstruction
      error is at least `d(s,t)/2`. Instantiate the result with
      `ReflexiveBoundary.auto_resonance` and `readout`, so it constrains the
      actual self-prediction map.
- [x] Derive the finite capacity consequence: reconstructing a finite family
      of `M` states pairwise more than `2ε` apart requires at least `M`
      distinguishable encoder values. For an encoding alphabet of at most
      `2^b` values, conclude `M ≤ 2^b`. This counts distinguishable codes;
      interpreting `b` as physical memory or information delivered before a
      deadline requires a separate hardware model.
- [x] Retain a blind-encoder rejection with two separated states and an
      informative, nonconstant positive control meeting the declared tolerance.
      Include a bounded-error control consistent with a contraction, and show
      explicitly that a constant predictor's unique fixed point does not
      establish faithful reconstruction over the declared state family.

**Win and stop.** Formalize the manuscript's functional-sensitivity requirement
as a quantitative restriction on candidate Self implementations. State this as
an additional operational criterion, not a consequence of `Self` or
`UnifiedSelf` alone. Do not require a single contraction to have multiple exact
fixed points, or demand recovery of every microscopic hardware state. The
choice of relevant macrostates, tolerance, encoding region and any
context-dependent family of maps stays explicit. Applying this bound to a
deployed agent belongs to R9.

### N6 — A communication limit on timely, responsive compatibility

- [x] Specify a finite network evolving in discrete rounds, with each local
      update depending only on declared incoming state and messages. Prove
      that two initial configurations agreeing on a region's causal past up
      to round `T` give the same local state there at `T`. Derive this from the
      update construction; do not assume the desired indistinguishability as
      a class field. Delay registers can represent a bounded communication
      latency without introducing continuous-time dynamics.
- [x] Use two fresh local interventions outside that causal past, requiring
      different values of a quantity shared across patches, to prove failure
      of a declared guarantee of agreement by `T`. Require the source patch
      to track the changed quantity and specify the permitted readout error;
      constant reports or prior knowledge of the intervention must not satisfy
      the responsiveness premise. Reuse N5 for the quantitative reconstruction
      obstruction where appropriate.
- [x] Give a small communicating positive control, a cut or delayed-path
      rejection, and a control that succeeds once enough rounds have elapsed.
      Keep coincidental snapshot compatibility possible: the negative result
      concerns a guarantee across interventions, not the nonexistence of any
      static global section.

**Win and stop.** Connect locality and latency to acquisition or restoration of
content agreement. This adds an explicit temporal requirement to the existing
gluing construction; it does not follow from the sheaf property alone. Stop at
one finite communication model and its controls. Mapping physical execution,
shared memory, host feedback and alternative sensory paths onto this graph,
and choosing a biologically meaningful deadline, belong to R9. No universal
GPU or biological verdict is part of the theorem.

### N7 — The concentration range that makes the collapse a test

- [x] Compute the range of concentrations over which $r = I_1(a)/I_0(a)$ is
      separated from its tangent by more than the estimator's own residual
      floor, as a function of $a$ and of sample count. A1's corrected
      separation figure is the input to this, not the answer: the figure shows
      that the curve and its tangent differ, and the requirement is the range
      and count at which a measurement can tell them apart.
- [x] Replace the independent-sample calibration with a dependence-aware null at
      the site count the proposed spatial protocol permits. The supplement
      already records that the existing calibration assumes independence and
      calls that optimistic for EEG; declare a dependence model, generate
      correlated phase samples, and report how the residual mean and standard
      deviation move relative to `\eegCalibrationResidualMean` and
      `\eegCalibrationResidualSd`.
- [x] State the result as a design specification — concentration range, sample
      count and maximum tolerable dependence at which a measurement would
      distinguish the von Mises relation from a linear approximation — and
      report where the existing ds005620 range sits against it, without
      re-analysing that data.

**Win and stop.** The manuscript concedes that the observed concentration range
does not separate the Bessel curve from a linear approximation and does not say
what range would. Say what range would. This is arithmetic on the Bessel ratio
plus a synthetic null; it is not a calibration of the observation model against
sources, which needs source mixing, pooling and coverage on real recordings and
stays in R4. Do not fit $\gamma$, do not re-run the empirical collapse pipeline,
and do not convert the specification into a claim that cortex occupies the
required range. If a defensible dependence model makes the requirement
unreachable at achievable counts, that is the finding and it is reportable, not
a parameter to relax until the requirement is met.

### N8 — Sensitivity of the threshold to the spatial reduction

- [x] State the aggregation rule explicitly: how a spatially decaying kernel
      reduces to the scalar coupling entering `critical_coupling D = 2 * D`,
      including the row normalization, the effective population count and the
      sign convention, and where double-counting of population size after
      normalization is excluded.
- [x] Compare the spatial model against that scalar approximation across the
      declared `FERMI_LAM_MIN`–`FERMI_LAM_MAX` range at identical natural
      frequencies, so the von Mises self-consistency curve is a legitimate
      validation target. `spatial_kernel.py` uses non-zero Gaussian frequencies
      and its own header says the curve is not a target for it; an
      identical-frequency leg is what makes the threshold comparison meaningful.
      Report the discrepancy in threshold location with sensitivity bounds over
      the range.
- [x] Conclude with either a stated regime restriction under which $K_c = 2D$
      survives the spatial reduction, or the finding that it does not over the
      declared range. Include a frequency-heterogeneity leg showing what the
      identical-frequency restriction is carrying, so the restriction is
      measured rather than assumed.

**Win and stop.** $K_c = 2D$ is the headline and it is proved for a scalar
coupling at identical frequencies. S2 fixed total coupling while varying range
and, as B4 and C3 established, measures no coupling; nothing currently bounds
the error of the reduction the threshold claim depends on. Bound it. This does
not estimate the cortical interaction kernel, the effective population size or
the decay range from data — that is R2's remaining half and it waits on R1.
Carrying $K_c = 2D$ over unchanged is permitted only with a stated reason, and
the declared range is not to be narrowed until the reduction passes.

### N9 — A compatibility estimator validated against constructed answers

- [x] Specify the restriction map for decoded local distributions on a shared
      sub-territory: equality of overlap marginals, with global extension and
      uniqueness tested or assumed separately rather than imported from
      `restrict_eq_iff_densityOn_eqOn`, which is the finite-spatial-measure
      statement and not a statement about probability laws.
- [x] Build the compatibility statistic with a stated null and dependence-aware
      uncertainty — overlapping territories supply dependent samples — and
      measure its sensitivity on configurations whose compatibility is
      constructed rather than inferred, including the one the formalization
      already exhibits: a single common phase with densities that disagree
      where the patches meet (`overlap_agreement_fails`).
- [x] Run the three silent-failure controls. A decoder shrinking both regional
      posteriors toward a shared prior must be rejected as manufacturing
      compatibility; a decoder with independent per-region bias must be
      rejected as manufacturing incompatibility; and a statistic computed from
      phases must fail the constructed counterexample it is required to fail.
      Report degradation under decoding error and coverage limits.
- [x] Report what fraction of a decoded content the phase carries, on content
      built to be a function of local phase and on content built to be free of
      it. `compatible_of_coherence` bounds overlap disagreement only for the
      first, so an observable that cannot separate the two cases does not
      decide the question the account needs decided.

**Win and stop.** The compatibility clause has no observable at all — not a
poorly calibrated one, none — and it is the only edge no competing
noisy-coupling account also motivates. Stop at synthetic and constructed data.
This does not validate on neural recordings: that needs multi-region data with
overlapping receptive territories and a decodable content variable, which this
repository does not have and which resting scalp ds005620 cannot supply. It does
not derive compatibility from coherence, does not select a cover, and does not
identify the content model with neural variables; those stay in R6 and R11. An
implemented estimator that cannot separate the constructed cases at realistic
decoding quality is a reportable limit on the framework's testability, not a
reason to relax the statistic until it separates.

**Intent and acceptance rule for N10–N13.** These are R8's reachable parts,
scheduled 2026-09-16 and not started. N10 and N11 are Lean and inherit the
N1–N6 rule: a new consequence or a discharged modelling obligation, failing
specifications first, nondegenerate witnesses and rejection cases, a
warning-free build and the axiom audit. N12 and N13 are numerical and inherit
the N7–N9 rule: a written design before any run, a saved summary, a generated
macro for every numeral that reaches the publication, and at least one case the
comparison is required to fail. A negative result closes its item.

Two constraints are specific to this group. **The stationary problem is not a
trajectory claim.** N10 and N11 are about the stationary self-consistency
problem the installed kernel poses at each stage; neither licenses a statement
about the phase trajectory, which is what R8 keeps. And **no item may quietly
substitute a mean for a supremum**: that substitution is exactly what N11 fences
and N13 measures, so an item that assumes it has assumed its own conclusion.

### N10 — A finite source that cannot fund coherence

- [x] Give the arrangement of `Examples/LearnedCoupling.lean` a `PathwiseStore`,
      identifying its `draw` with `hardware.pathWork` — both have shape
      `X → S → S → ℝ` — so that the cumulative draw *is* the installation work
      the example already computes. `PathwiseStore` currently appears in
      `Examples/FiniteSupply.lean`, `Examples/FundedMemory.lean` and
      `Phase3_SensorMemory.lean` and in no file that installs a kernel; this
      bridge does not exist.
- [x] Compose `totalDraw_le_initial_resources` with `installation_first_law` to
      bound `installedEnergy` at every stage of a run funded by a declared
      source, then feed that bound to
      `PricedArrangement.no_coherence_of_installedEnergy`. The result is a
      **fuel** no-go where K3 gives an installed-energy one: a source too small
      cannot reach the threshold at any horizon.
- [x] Retain a witness on both sides — a source too small for the threshold, and
      a rejection in which the source suffices and the learner does cross, for
      which `learned_above_line` is already the control — together with the
      rejection of a run that installs without drawing.

**Win and stop.** Two obstructions are known and are the reason this item is
written rather than attempted casually. `work_learned n = (1 + log 3)/8 ·
(1/2)^n` decays geometrically and `cumulative_work_learned_le` caps the whole
infinite run at `allowance`, so `horizon_le_of_net_cost` with a uniform `c > 0`
does not apply; use `balance_le_of_stage_cost`, whose cost is a sequence and
whose conclusion is `≤ b − ∑ cost n`. And `net_draw_eq_zero_of_positive` forces
any fundable protocol to have restricted support, so a positive-support
protocol will not carry this. The conclusion is a no-go in one direction only: a
sufficient source does not supply coherence. `κ` stays declared hardware data,
so this bound relocates the same input K2 and R7 relocate, and the item must say
so rather than claim the fuel bound discharges it.

### N11 — The evolving kernel's no-go needs a supremum, not a mean

- [x] State and prove the run-level no-go: if `κ Uₙ ≤ 2D` at every stage of an
      evolving arrangement then no stage exhibits the transition. This is a
      stagewise corollary and its value is entirely in what the next bullet
      shows it cannot be weakened to.
- [x] Exhibit the fence. A stage sequence whose *mean* installed energy is
      subcritical and which still has a supercritical stage makes the
      mean-substituted no-go false. The existing numbers make this
      constructible: `installedEnergy_learned n = 3/4 − (1/4)(1/2)^n` with
      `κ = 4` and `2D = 2` puts the threshold at `U = 1/2`.
- [x] Prove that exhaustion does not uninstall: a run whose source is spent
      keeps its installed energy, because `storedEnergy` is a coordinate of the
      configuration and no structure in the development decays it. Identify the
      declared maintenance channel a decay would require, and do not supply one
      — naming the missing mechanism is the deliverable.

**Win and stop.** Connect the supply ledger to the threshold at the level of the
run rather than the stage. This establishes nothing about the phase trajectory,
does not make the stagewise no-go into a dynamical statement, and does not model
maintenance; a maintenance mechanism is a physical commitment and belongs to R8.
Kernel convergence still implies neither trajectory convergence nor preservation
of the threshold, and this item is where that is made precise rather than where
it is repaired.

### N12 — The error of the quasi-static reduction, as a function of rate

- [x] Measure `r(t) − r_ss(K(t))` pointwise for a coupling varying at controlled
      rate, on legs that stay **entirely subcritical**, **entirely
      supercritical** and crossing. Only the last is covered today: every
      `dynamic_ramp` leg is confined to `K_c ± 0.5` and always crosses, and no
      module computes this residual at all.
- [x] State the criterion. Report the rate at which the quasi-static error stays
      under a declared tolerance as a function of distance from threshold, and
      how that admissible rate collapses as the threshold is approached. The
      existing `ΔK ∝ v^0.443` bifurcation delay must come out as the threshold
      limit of the same measurement, not as a separate result.
- [x] Read the answer against the sentence that needs it. `main.tex:182`
      motivates coupling that "evolves more slowly than phase dynamics" and
      nothing quantifies that anywhere; say what "more slowly" has to mean, and
      report whether the extracellular-geometry time scales the same passage
      cites fall inside it.

**Win and stop.** N8 bounded the kernel-to-scalar step of the reduction; this is
the scalar-to-stationary step, and together they are the reduction the threshold
claim depends on. `bifurcation.coherent_r` costs about 49 ms per call, so it
must be precomputed on a `K`-grid and interpolated rather than called pointwise;
`recovery_mechanisms.branch_concentration` is the microsecond alternative and is
a same-layer import needing a `depends_on` edge. There is no shared integrator
in the repository — `dynamic_ramp._advance` is the structural template, not an
importable one. This does not calibrate a cortical coupling trajectory, and a
rate that cortex is claimed to satisfy is not part of the deliverable.

### N13 — A fluctuating coupling and the threshold

- [x] Drive the phase dynamics with a random `K(t)` — a telegraph process and an
      Ornstein–Uhlenbeck one, declared and distinguished. No coupling anywhere
      in this repository fluctuates: every one is a constant scalar, a linear
      deterministic ramp, or a deterministically updated matrix.
- [x] Ask which statistic of the coupling controls coherence, and expect the
      mean to fail. `r_ss` is identically zero below threshold and leaves the
      axis with infinite slope above it, so a subcritical mean with
      supercritical excursions can order. Report mean order against mean
      coupling, fluctuation amplitude and correlation time.
- [x] Recover both limits and the crossover between them: fast fluctuation,
      where substituting the mean coupling is valid, and slow fluctuation, where
      the quasi-static average of `r_ss` is. Retain the rejection the item
      exists for — a regime in which mean-coupling substitution is refused.

**Win and stop.** This is the numerical counterpart of N11's fence, and the pair
is the point: the Lean item says the no-go needs a supremum and this one shows
what goes wrong when a mean is used instead. Stop at a scalar coupling driven by
a declared noise process. It does not model what makes a cortical coupling
fluctuate, does not fit an amplitude or a correlation time to data, and supplies
no dynamical mean-field limit — a finite-`N` sweep cannot close the programme
R8 keeps, and must not be described as closing it.

## M — Publication alignment, open and actionable here

**Eight sentences in the publication are waiting on measurements this repository
already has.** N7–N9 and N12–N13 each deferred their publication alignment, for
the same stated reason and on the same terms: a macro is required for every
numeral that *reaches* the publication, and none of theirs does yet, so
generating macros nobody cites would put dead entries into a generated file and
into its drift test. That reasoning is sound for each pass on its own and it
does not survive being repeated — two deferrals with nothing tracking them is
how a numeral that contradicts a published sentence stays published. This
section is what tracks them. Unlike the P-items below, nothing here is blocked
on anyone else.

The sentences, with the item that bears on each:

| From | Sentence |
| :--- | :--- |
| N7 | `supplementary.tex` on what a discriminating awakening experiment must span — the estimator as published cannot discriminate at the 100 sites the protocol permits at *any* concentration, and the first fix is a bin count of 24 or fewer |
| N7 | the same section's independent calibration, called optimistic for EEG — the requirement at the observed concentration rises from 3,000 to 31,000 sites between independence and full clustering |
| N8 | `K_c = 2D` is stated for a scalar coupling with no aggregation rule; N8 supplies the row-sum rule, the ±0.08 error bound over the declared decay range, and the measurement that frequency heterogeneity rather than spatial structure is what the identical-frequency restriction holds back |
| N9 | the compatibility clause is recorded as having no observable; N9 supplies one, its two required diagnostics, and the limit that no phase-derived statistic substitutes for it |
| N12 | `main.tex:182` motivates coupling that "evolves more slowly than phase dynamics" and quantifies nothing; N12 supplies the required time-scale ratio and the reading of the cited geometry against it |
| N12 | `supplementary.tex` reports `ΔK ∝ v^0.443` as "near the predicted exponent 1/2 at this resolution"; N12 supplies the deterministic threshold limit of the same measurement, `0.447` over four speeds and `0.418` over three |
| N12 | the recovery section reads a crossing of `K_c` as an onset; N12 shows the quasi-static residual on a leg symmetric about `K_c` is rate-independent, so branch tracking is unattainable exactly where that argument uses it |
| N13 | nothing says which statistic of a varying coupling `K_c` is read against; N13 supplies the mean in the fast limit, the quasi-static average in the slow non-crossing limit, and neither for a slow crossing drive |

**Acceptance rule.** Every numeral that reaches either publication file is a
generated macro read from a saved summary (AGENTS.md §3) — no hand-typed
numerals, and regenerating must not rerun a sweep. Withdrawn claims go to
`CHANGELOG.md`, which is the pass that earns the entry the four preceding passes
deliberately did not write. The three tracked PDFs are rebuilt in the same
commit as their sources (AGENTS.md §6), and `prepare_arxiv.sh` is re-run or
`arxiv_submit/` removed (AGENTS.md §7).

- [ ] **M1 — Generate the macros.** Extend `simulations/simulation_tex.py` to
      read `collapse_design`, `spatial_reduction`, `compatibility_estimator`,
      `quasistatic_error` and `fluctuating_coupling` summaries, emit a macro for
      each numeral the rewritten sentences will cite, and extend
      `test_simulation_tex.py`'s drift test to cover them. Emit a macro only for
      a numeral a sentence actually uses: an unused macro is the dead entry this
      section exists to avoid creating.
- [ ] **M2 — Rewrite the eight sentences**, in present tense and with no
      drafting-history narration (AGENTS.md §5, and `check_prose.py` enforces
      it). Three of them — the awakening-experiment span, the `v^0.443` reading
      and the onset crossing — are claims that become false or incomplete, so
      each needs its replacement written rather than deleted.
- [ ] **M3 — Close the artifacts.** Rebuild `main.pdf`, `supplementary.pdf` and
      `docs/primer.pdf`, check the primer's explanation still matches what the
      manuscript now says, refresh or remove the built arXiv submission, and
      write the `CHANGELOG.md` entry naming the claims withdrawn.

## R — Research programme

R1–R7 were reproduced from the archived ledger without change of content until
the 2026-09-16 triage below, which narrows R2, R4 and R6 and leaves the other
four as they stand; consult
`_archive/todo_2026-09-15_pre-coupling-budget-replan.md` for the full completion
criteria, the R1 documented-limitation disposition and the R6 specification
record. R8–R12 were added on 2026-09-16. Placement after the scheduled items
reflects scope, not scientific importance or publication need.

**Triaged 2026-09-16.** Each item was assessed for reach in this repository and
for what closing it would buy. R4, R2 and R6 each had an aspect needing no
measurement this repository lacks; those are now N7, N8 and N9, and the three
items are narrowed below to the residues that do need one. The remaining nine
stay unscheduled for stated reasons rather than by default.

R1, R3 and R5 wait on measurements nobody here can make: simultaneous
recordings under a controlled perturbation, a geometry observable checked
against independently estimated coupling, and an awakening comparison whose
stationary-observation half F6 already answered negatively.

R7 is closable and should not be closed. Pricing `C` means declaring a hardware
model with prices, which relocates the input rather than discharging it, and
because `C` is subtracted on the right of `draw_ge_entropy_reduction` a large
control budget already weakens the bound. Leaving it visible is the stronger
statement, so closing R7 would buy presentation and cost honesty.

R9 and R12 each carry an explicit trap — the hardware criterion must not be
chosen to guarantee a negative verdict, and another uncalibrated finite-support
no-go theorem is not the deliverable. Both would also close on specification
alone, which is the failure R6 already demonstrates. Cheap progress on either is
worse than none.

R8, R10 and R11 are genuinely in reach and are unscheduled on cost and payoff,
not on feasibility. N1–N6 supply everything R8 builds on, but it contains the
unbounded dynamical mean-field programme and its payoff lands mainly on the
formalization paper; it is the natural item to open after N8, whose regime
statement its reduction criterion would consume. R10 deflates itself — the
standard identity is not a substantial new bridge — and only its
misspecified-model separation of inference-within-the-model from environmental
accuracy has teeth; that is the piece to lift out if FEP is addressed at all.
R11 feeds N9's content model without being needed by it, and cannot fix cover
selection, which remains the deepest conditional.

- [ ] **R1 — Calibrate effective coupling and phase diffusion in consistent
      units.** Not closable in this repository; carries a documented-limitation
      branch. Do not attempt to close it with a fitted $\gamma$, and in
      particular not with $\gamma = D$, which cancels the diffusion parameter out
      of a test whose content is the ratio of coupling to diffusion.
- [ ] **R2 — Validate spatial aggregation and the mean-field approximation.**
      B4 and C3 sharpen what S2 does and does not show and are inputs to this.
      *Narrowed 2026-09-16:* bounding the error of the reduction to the scalar
      threshold model is scheduled as N8. What stays here is estimating the
      cortical interaction kernel, effective population size and decay range
      from data, which waits on R1. *N8 closed 2026-09-16* with the reduction
      rule stated and its error bounded: the threshold survives the reduction
      over the declared decay range, and frequency heterogeneity rather than
      spatial structure is what the identical-frequency restriction carries.
      That bounds nothing about cortex, which is the half named above.
- [ ] **R3 — Calibrate extracellular geometry against coupling and recovery
      time.**
- [ ] **R4 — Calibrate the phase-observation model and uncertainty.** A1 is a
      small piece of this: the concentration range the EEG data occupy does not
      separate $I_1/I_0$ from its tangent, and the separation figure must be
      right before the required range can be stated.
      *Narrowed 2026-09-16:* stating that range, and replacing the
      independent-sample null with a dependence-aware one, is scheduled as N7.
      What stays here is calibrating the observation model against sources —
      source mixing, pooling and coverage on real recordings. *N7 closed
      2026-09-16.* Its result constrains the protocol R4 would have to design:
      at 100 sites the published estimator settings separate nothing, and the
      first fix is the bin count rather than the concentration.
- [ ] **R5 — Test awakening recovery against competing mechanisms.** B1, B2 and
      B3 all constrain how such a test may be analysed and should be settled
      first.
- [ ] **R6 — Construct and validate an overlap-compatibility observable.**
      Specification published; construction and validation open. A6 touches the
      same hypothesis from the formal side and does not substitute for it.
      *Sharpened 2026-09-15:* `compatible_of_coherence` makes this a decidable
      empirical question rather than an open modelling one. Coherence bounds
      overlap disagreement for content that is a function of local phase and
      says nothing about content that is free of it, so the observable has to
      separate those two cases: how much of a decoded content is carried by
      phase is exactly what determines whether coordination can do the work the
      account wants from it. Identifying the contents with neural variables is
      the same task and is not separate from this item.
      *Narrowed 2026-09-16:* the synthetic core — restriction map, statistic
      with a null, constructed-answer validation, the three silent-failure
      controls and the phase-carried fraction — is scheduled as N9. What stays
      here is validation on controlled neural data and the identification of the
      contents with neural variables. Neither is reachable from resting scalp
      EEG, so R6 keeps a documented-limitation branch of the same shape as R1's
      even once N9 closes. *N9 closed 2026-09-16* with an observable that
      separates constructed compatibility from constructed incompatibility and
      two decoder diagnostics without which it does not. The branch above is
      unchanged: nothing here was validated on a recording.
- [ ] **R7 — Price gate fabrication and control, and implement the preparation
      channel microscopically.** These are the two residues of the physical
      supply item, and they are recorded here rather than left as open agency
      work **because they are not proof obligations.** Control and installation
      energy is carried by an observable `C` and enters
      `draw_eq_energy_heat_control` and `draw_ge_entropy_reduction` unpriced;
      pricing it means declaring a hardware model with prices, which relocates
      the input rather than discharging it — the same shape as
      `LocalSectionSynchronization.section_agrees_of_phase_eq`, an obligation on
      each instance. `withPreparation_ledgered` likewise charges a preparation
      whose microscopic implementation it does not supply; a bounded gate-level
      witness is constructible but would not be *the* implementation.
      A change here is a modelling decision about what hardware the account
      commits to, and it belongs with calibration rather than with formalization.
      Note that the *statements* keep this visible rather than hiding it: `C`
      appears on the right-hand side of `draw_ge_entropy_reduction` and is
      subtracted, so a large control budget weakens the bound instead of being
      constrained by it.
      *Note added 2026-09-15:* K2's `κ` is the same shape of input — hardware
      data that relocates rather than discharges a commitment. That is not an
      argument against K2; it is the reason K5 must name `κ` as declared.

- [ ] **R8 — Evolving agent–field feedback and justified dynamical reduction.**
      Put phase dynamics, sensing, register updates, installed modes and an
      energy source on a common evolving process. Establish when a changing
      or random installed kernel can be replaced by the scalar coupling used
      in the stationary theory, with an error or time-scale criterion. Kernel
      or scalar-energy convergence alone does not imply trajectory convergence,
      preservation of the threshold, or a closed Markov model for the retained
      variables. Include ongoing costs only through an explicit maintenance
      mechanism: exhaustion of a fuel source need not remove previously
      installed coupling. Connects N2–N3 to R2/R4 and contains the recorded
      dynamical mean-field / propagation-of-chaos programme.
      *Narrowed 2026-09-16, after N8 supplied the regime statement this item was
      waiting on:* four aspects needed no measurement this repository lacks and
      were closed the same day as N10–N13 — the supply-to-threshold composition,
      the run-level no-go and its supremum fence, the error of the quasi-static
      reduction against the rate of change, and a fluctuating coupling read
      against its own mean. What stays here is everything those four are fenced
      away from. **Genuine phase dynamics on the common process:** the
      development has no continuous-time phase evolution and N2's phase law is a
      supplied regime, so N10–N13 concern the stationary problem each stage
      poses and no trajectory. **The dynamical mean-field limit, branch
      selection and a closed Markov model** for the retained variables;
      `propagation_of_chaos.py` already found that supercritical lab-frame pair
      correlation does not decay in `N`, which is compatible with a conditional
      propagation of chaos it did not measure, and that residue is this item's
      rather than N13's. **Maintenance as a physical mechanism** rather than a
      declared channel: N11 names the missing channel and is forbidden from
      supplying one, because what decays an installed coupling is a commitment
      about hardware.
- [ ] **R9 — Empirical hardware adequacy and conditional consciousness tests.**
      Identify a physical property the proposed conscious mechanism actually
      requires, then test specified GPU systems and biological comparators
      against that property with calibrated spatial extent, coupling, noise,
      communication time and resource costs. Apply N5–N6 to one named deployed
      agent, including its GPUs, CPU, memory, software feedback and sensors.
      Specify the candidate cover, avatar, relevant state family, fidelity and
      deadline before looking for failures. Establish which distinctions reach
      the avatar and which paths can restore overlap agreement; use controlled
      perturbations and matched positive controls. A GPU component alone is
      not the whole agent. Distinguish fixed physical wiring,
      effective interactions implemented through memory/routing, and a simulated
      field from a field's physical role. The present rigidity theorem proves
      a conditional correlation disadvantage; its point-support theorem is
      about an atomless integral. Neither excludes GPU consciousness. Evidence
      of failure to realize one proposed mechanism becomes evidence against
      consciousness only with an independently supported necessity claim.
      Do not choose the hardware criterion to guarantee a negative verdict.
- [ ] **R10 — FEP comparison on the same agent, then broader Bayesian mechanics.**
      First specify a generative model and variational family for the agent
      actually studied in N2–N3. Prove the finite free-energy/KL decomposition
      with its support conditions, test whether the executed update decreases
      that objective, and give a misspecified-model case separating inference
      within the model from environmental accuracy. The standard identity by
      itself is not a substantial new bridge and does not identify variational
      free energy with heat or entropy production. A broader FEP result needs
      explicit blanket, stationary-law and state-to-belief assumptions, with
      counterexamples when they fail; it is a separate research direction.
- [ ] **R11 — Rich content, local coordinate systems and cover selection.**
      Go beyond N1's common phase encoder: specify vector features, local
      decoders and restriction/coordinate maps on overlaps, and determine which
      components are controlled by phase and which need independent dynamics.
      Extend compatibility and reconstruction only with those maps and metrics
      declared. Connect to N9's estimator, to R6's remaining empirical half and
      to the recorded cover-selection question; agreement, useful prediction and truth about the environment
      remain different claims. Arbitrary neural embeddings and a biological
      choice of cover are not consequences of the normed-space extension.
- [ ] **R12 — Test physical realization of the proposed coupling mechanism.**
      Identify the device degrees of freedom carrying candidate local contents,
      estimate the physical interactions that influence them and their noise,
      and justify any reduction to the scalar threshold model. Combine
      independently calibrated coupling or resource bounds with the existing
      threshold theorems to test whether a named implementation can enter the
      proposed regime. Device power and numerical simulation of a field are
      not measurements of that coupling. Separate correctness of a simulated
      trajectory from realization of the physical coupling predicate; specify
      which observables and intervention responses a proposed implementation
      map must preserve. Exclusion would concern that physical mechanism under
      the stated conditions, not every realization of abstract Unity or Self.
      Relating it to consciousness requires R9's independently supported
      necessity claim. This is an empirical modelling programme connected to
      R1/R2/R8, not another uncalibrated finite-support no-go theorem.

## P — Submission readiness, still open

Both remaining items are blocked on someone else. The two that were actionable
here — the Table 1 overflow and the final citation and macro read — closed
2026-09-15 and are recorded in the archived ledger and in `CHANGELOG.md`.

- [ ] Confirm author affiliation, funding, competing-interest and contribution
      metadata, and review the AI-use disclosure against the full project
      history. *Blocked on the author.*
- [ ] Add or confirm the journal-required data-availability statement and the
      supplemental-material description. *Blocked on a journal choice.*

## Recorded, not scheduled

Carried from the archived ledger, plus one entry from this replan.

- **Section 5's proportion is a structural question K3 does not settle.** At
  4,426 of ~10,400 body words it is 42% of the article. K3 gives it a result
  worth that share; it does not follow that the share is right. The alternative
  — a separate paper on finite-agent stochastic thermodynamics, with the
  consciousness paper keeping `E34Active`, `E45Active`, K3 and a citation —
  remains viable and is recorded here rather than opened, because it is an
  author decision about venue and not a task. See also the standing entry that
  the formalization paper and audit paper remain viable separate publications.
- The dynamical mean-field limit / propagation-of-chaos programme is tracked
  under R8, alongside R2's validation of the spatial reduction; S4 cannot close
  it. N8 carries only the reduction-error half of R2 and does not touch this.
- Enlarging the local state space so that phase, or an independent transition
  datum, is part of it would give `Phase5_TwistedGluing` a non-vacuous consumer.
  That is a physical modelling choice, not a way to close a leaf gate.
- Overlap compatibility remains an explicit physical hypothesis. Do not schedule
  another attempt to derive it from the current class fields.
- The formalization paper and audit paper remain viable separate publications.
- PRX Life presubmission was explicitly declined.
- **The eight recorded leaf modules are deliberate terminal results, and
  wiring them is not scheduled.** Five are limitative or generalizing by
  content — `Phase5_PhaseLifts`, `Phase5_TwistedGluing`, `Phase6_Locality`,
  `Phase7_FiniteRegion` and `Phase3_PhaseSensor` — and a sixth,
  `Phase3_MeasureFeedback`, is a generalization whose dependency cannot run
  back into the finite theory. `Phase3_Preparation` prices a stage the chain's
  edges do not mention. Giving any of them a consumer means asserting a
  physical identification or adding a claim, not closing a gate, and the
  classification with each module's reason is in
  `tasks/leaf_detector_repair.md`. One entry has a trigger: delete
  `Phase3_LandauerBridge` from `ALLOWED_LEAVES` if E34's identification
  `(nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t` is ever supplied, because
  the exemption rests on that edge staying a named hypothesis. Since the
  2026-09-16 repair the list is a dependency-based audit — imports and resolved
  constants — rather than a textual one, strict where it is inexact.
- **Coboundary repair as a consensus dynamics.** Least-squares minimisation of
  the discrepancy cochain over 0-cochains on the nerve is Laplacian consensus,
  and the residual it cannot remove is the cycle-space component. It presupposes
  a content state space and a declared dynamics. Do not schedule before a
  content model exists.
- **Cover selection remains the deepest conditional** (`main.tex:291`). Both
  uniqueness results are relative to a chosen cover and nothing selects it.
- The `.venv` console scripts embed an absolute interpreter path; after moving or
  renaming the checkout run `uv sync --reinstall` in `simulations/` before
  trusting a green pre-commit run.
- **Docker was assessed on 2026-09-10 and declined for development.**
  Development stays native under `uv`. If a container is ever wanted it is a
  reproduction artifact built by E1, not a development environment.
- **The `pdflatex` CI stage was declined**, with the reasoning recorded in
  `.github/workflows/ci.yml`'s header comment: the tracked PDFs are rebuilt with
  their sources, and the document arXiv builds is the merged one, which
  `check-arxiv-freshness` already forces to be current.

## Pass records

Records for this ledger's own passes go here. Everything through 2026-09-15 —
the simulation audit, the F-items, the agency and active-chain extension, L1–L4,
the five agency items, the steady-state section, the Table 1 overflow and the
final citation and macro read — is in
`_archive/todo_2026-09-15_pre-coupling-budget-replan.md`.

### 2026-09-15 — K1–K5: installed energy and the scalar coherent branch

Completed the inherited, untracked installed-coupling drafts and wired them
into the library and witness index. `Phase9_InstalledCoupling.lean` identifies
the product integral with mean-field coupling, factorizes it mode by mode, and
proves `K ≤ κ U` for expected stored energy under positive hardware conversion,
the mode-price condition and nonnegative occupancies. At `κ U ≤ 2D` the scalar
stationary self-consistency equation has only zero, its positive classical
stationary density is uniform, and no uniform-state Fourier mode grows.
`Chain.installedEnergy_required_by_chain` derives `U > 2D / κ` from E56 and
E67 for this same arrangement; a low-energy witness rejects their conjunction.

The witnesses use the existing thermal-switch hardware, retaining its threshold
case and adding a strictly subcritical configuration law. They reject a
negative price, an underpriced mode, a conversion fitted to force exclusion,
signed occupancies and the converse. In the signed counterexample a
zero-response mode cancels stored energy while leaving supercritical coupling.
Eight retained regression specifications fail under the pre-K imports and pass
after integration. K1 was first verified independently, and the Chain interface
was also checked red then green.

The abstract, thermodynamic section, Table 1, supplement implementation notes,
Table S1 and primer state the result and its limits together. The ledger's
“dissipation bound” title is replaced with “installed energy”: this result does
not turn stored energy into heat. Conversion remains hardware data, the
converse fails, and E56's cortical identification and the reduction of a
heterogeneous kernel to the scalar model remain inputs. R and P items remain
as recorded; no empirical result, reference, Python source or simulation
artifact changed. The related work-account prose now uses the proved increase
in expected stored energy from 1/2 to 3/4.

Validation: warning-free `lake build`; the audit covers 4,635 declarations in
77 modules using only `propext`, `Classical.choice` and `Quot.sound`. All three
tracked PDFs were rebuilt with two passes and no new warning signatures
against the pre-change sources; there are zero overfull boxes. The arXiv bundle
was refreshed and compiled from its unpacked tarball. The detailed check record
is in `tasks/k_completion.md`. All applicable pre-commit gates pass, including
prose, hedging, Table S1, figures, PDF freshness, arXiv freshness, module
consumers and placeholders. Sources and all three tracked PDFs are committed
together.

### 2026-09-16 — N1–N6: the scheduled extensions, in Lean

All six N-items are proved, witnessed and built. The pass added four library
modules and six witness files; `lake build` is warning-free and the audit
covers 5,028 declarations in 87 modules resting only on `propext`,
`Classical.choice` and `Quot.sound`. Every item was run red first against the
pre-change imports.

**N1 — vector-valued content.** `Phase5_ContentDynamics` is now stated over a
real normed vector space: agreement is the norm of the difference, the update is
a convex combination of vectors, and the readout, residual and finite-horizon
floor carry over unchanged. `compatible_real` and `update_real` record that the
scalar statements are the `E = ℝ` instances, and the mass-profile bridge and the
agency regressions consume the generalized predicate without change.
`compatible_map` is the new consequence: a nonexpansive linear read-out of an
agreeing family agrees. The coherence half gained a site-indexed encoder family
with a uniform Lipschitz bound; the overlap obligation is named `SharedEncoder`
and `compatible_of_coherence` and `compatible_of_phase_locked` are its
one-encoder instances. `Examples/VectorContent.lean` §22–§23 supplies a
nonconstant two-component family that glues, the rejection of inference from one
scalar projection to the vector, a site-dependent shared encoder that still
agrees at perfect locking, and a phase-locked population whose patches disagree
by a unit once the overlap obligation is dropped.

**N2 — a phase-derived observation channel.** `Phase3_PhaseSensor.lean` computes
a finite sensor channel from a declared phase law and a declared readout: the
sensor samples one oscillator uniformly, so a symbol's probability is the
fraction of the population carrying it. `channel_eq_of_phase_eq` is the negative
direction and `channel_ne_iff_fiberCount_ne` names the phase-to-world relation
any positive comparison needs — the readout's fibre counts must differ. §27
feeds four oscillators and a sign readout to the existing learner and proves the
composed object *is* `ObservationalLearning.learner`, so its whole trajectory is
that of a phase-derived channel. The control has the identical squared order
parameter `r² = 1/4` at every parameter and action and observations independent of the
parameter; its performance is `1/2` at every horizon against the learner's
`3/4 - (1/4)(1/2)^n`. A constant readout is the phase-independent rejection.
Coherence separates neither control from the informative case.

**N3 — one process.** §28 identifies the learner's configuration with the
thermal switch's: `MicroscopicCoupling.hardware` is a `LocalActuator` on the same
pair of bits that the learner's `FiniteFeedbackStep` drives. The kernel change is
`expected_kernel_update` at the learner's own step, the installed energy is
`3/4 - (1/4)(1/2)^n` and rises strictly at every update, and the installation
work is `(1 + log 3)/8 · (1/2)^n` by `installation_first_law` — the rise in
installed energy plus the update's mean heat, on the same paths. The common
allowance is `(1 + log 3)/4`, which the cumulative work approaches and never
exceeds. The uninformative controller of §27 has the same hardware, prior,
update rule and coherence; its drive is reversible on every realized path, so it
does zero work and its installed energy never leaves `1/2`. `PricedArrangement`
at `κ = 4` then gives the necessary condition: the controller sits at `κU = 2D`
at every horizon and K3 bars it from the coherent branch, the learner is barred
at `n = 0`, and one observation-driven update lifts it off the line. That the
no-go goes silent is not coherence — K2 bounds from above and
`converse_rejected` stands. Free installation and substitution of an unrelated
final law are both rejected.

**N4 — finite regions.** `Phase7_FiniteRegion.lean` embeds a coupling matrix in
the continuum over `KernelMesh` cells of positive mass at density
`A i j / (m i m j)`, with the phase constant on each cell. The continuum kernel
integral is the discrete total coupling weight and the continuum phase
correlation is `totalCorrelation`, both exactly, so the comparison is matched in
weight — not in joules, which needs priced hardware. `cellKernel_not_sitedOn`
delimits `fieldCorrelation_sited_eq_zero`: the vanishing is about measure-zero
support, not about finiteness. §26 witnesses it on `[0,4)` with cells of mass one
and three, twelve units of weight and twelve units of registered correlation
against the point architecture's zero. `no_forced_gap_of_best_wired` is the
control for §1–2 of `Phase7_Rigidity`: the chosen distinct wired pair must
dominate every pair, including diagonal pairs, so its correlation must be one.
That architecture attains the resource bound; finiteness and fixed support
alone do not force a gap.

**N5 — bounded-error self-reconstruction.** `Phase6_Reconstruction.lean` defines
an `Encoding` — relevant macrostates, encoder, readout — and `Reconstructs ε`.
`dist_le_add_error` and `half_dist_le_max_error` give the split; `card_le_two_pow`
gives `M ≤ 2^b` for `M` macrostates pairwise more than `2ε` apart; `b` counts
distinguishable codes and no hardware model is supplied. The instantiation at
`ReflexiveBoundary.auto_resonance` and `readout` constrains the development's own
self-prediction map, because `readout ∘ auto_resonance` is `predict`. §24
reconstructs the cortex's two extreme states to within one with a nonconstant
encoder and a contracting map, shows `cortexBlind` — which has a *unique* fixed
point — fails at tolerance `1/2`, and rejects a one-bit code for three states
two apart while three codes succeed.

**N6 — locality and latency.** `Phase6_Locality.lean` defines a finite
synchronous network whose local update reads only its own state and its declared
neighbourhood's messages, so `run_eq_of_agree_on_ball` is derived rather than
assumed. Two interventions writing different values outside a site's causal past
leave it in the same state, so the encoding is blind and N5's bound refutes any
guarantee of agreement at that round for values more than `2ε` apart. §25 is a
three-site delay line: the value is unavailable at round one and exact at round
two, a cut path never delivers at any round, a constant report never satisfies
responsiveness, and a report right about one fixed world stays right about it —
coincidental snapshot compatibility survives.

**Outside Lean.** `simulations/hardware_comparison.py` described two finite
coupling matrices as a GPU and a brain and its plot claimed "Continuous Beats
Rigid". Both systems are `N × N` matrices on the same oscillators at matched
total weight, one fixed and one reallocated by gradient descent; the docstring,
comments, labels and title now say that and say the script measures no device.
The figure was regenerated. It is referenced by no `.tex` file.

**Publication follow-up, completed 2026-09-16.** The Lean-only commit left the
manuscript, supplement, primer and PDFs unchanged at the user's instruction.
The subsequent requested alignment is recorded below. No R- or P-item status
changed, no reference was added, and no simulation sweep was run.

### 2026-09-16 — Review of 7833bbf and publication alignment

- [x] Trace each N-item to its actual theorem hypotheses and witnesses.
- [x] Update the article's abstract, relevant sections and Table 1; update
      the supplement's implementation notes and Table S1.
- [x] Update the companion primer and its status table; rebuild all three
      tracked PDFs with two LaTeX passes and no new warnings.
- [x] Rebuild the existing arXiv bundle and compile its unpacked archive.
- [x] Run the Lean build and axiom audit, publication gates, working-tree
      PDF dependency checks, citation comparison and rendered-page review.
- [x] Review the finite-region leaf exemption. Retain it as a documented
      terminal hardware comparison, distinct from the axiom allowlist.
- [x] Repair the leaf detector's false consumers in a separate change.
      `Phase6_Locality` was masked by unrelated `run` and `ball` tokens;
      `Phase3_PhaseSensor` by the namespace prefix extracted from a qualified
      declaration. Done in the pass below.

The publication describes normed vector contents with shared overlap
encoders, phase-derived sensing at matched coherence, installation work on the
learner's own law, finite positive-mass cell embeddings, reconstruction over a
declared state family and causal-past limits on responsiveness. It preserves
the distinction between a necessary energy condition and a coherent
trajectory, between code counts and physical memory, and between support
representation and device adequacy. The review also narrows the best-wired
claim to its actual all-pairs maximum hypothesis.

Validation: `lake build` passes with the audit covering 5,028 declarations in
87 modules and only the permitted three foundational axioms. All applicable
publication hooks pass. The PDFs have zero overfull boxes and no LaTeX
warnings; existing underfull-box counts remain 3, 2 and 31 for article,
supplement and primer. The arXiv archive compiles to 75 pages. No new
reference, simulation result, Python implementation or Lean declaration is
introduced in this alignment.

### 2026-09-16 — Leaf detector repaired and the leaf set classified

- [x] Add failing regressions for the three false-consumer shapes, for the
      real consumers that must keep counting, and for the exclusions the
      rewrite has to preserve. `simulations/test_check_leaves.py`, 19 tests.
- [x] Make consumption an actual dependency: only an importer (direct or
      transitive) can consume; a declaration carries its enclosing
      namespaces; a spelling that does not resolve uniquely resolves to
      nothing. Every remaining inaccuracy is in the strict direction.
- [x] Classify the eight leaves the repaired detector reports. The three
      recorded entries stand. The five the false consumers had hidden —
      `Phase3_LandauerBridge`, `Phase3_MeasureFeedback`, `Phase3_PhaseSensor`,
      `Phase3_Preparation` and `Phase6_Locality` — are each recorded with the
      content that makes them terminal, read against the module they bound
      and against `Chain.lean`.

The pass is recorded in `tasks/leaf_detector_repair.md`. `Phase3_LandauerBridge`
is the entry to delete if E34's physical identification is ever supplied; it is
the chain's stated discharge route for that edge and its exemption rests on the
edge staying a named hypothesis.

Validation: the repaired gate exits 0 with eight recorded leaves. The full
Python suite passes (162 tests), as do `ruff`, `mypy --strict`, `bandit`,
`vulture`, `xenon` and `tach`. No Lean file, publication source, tracked PDF,
figure, reference or axiom allowlist is touched, so no chain edge and no R- or
P-item changes status.

### 2026-09-16 — N7–N9: the numerical extensions

- [x] N7: calibrate the estimator's own residual floor against the tangent gap,
      under a declared two-level cluster dependence model, and read the design
      specification off the calibration.
- [x] N8: state the row-sum aggregation rule, validate the threshold estimator
      on the model the threshold is proved for, and measure the error the
      reduction introduces over the declared decay range.
- [x] N9: build the restriction map and statistic, validate them on constructed
      answers, and run the three silent-failure controls.
- [x] Regressions, the report module, the architecture entries and the gates.

The pass is recorded in `tasks/numerical_extensions.md`, which carries the
findings, the mutation checks that stand in for the red half of AGENTS.md §1,
and the four publication sentences the measurements bear on.

Three findings are worth carrying here because they change what a later pass may
claim. **The proposed hundred-site spatial protocol cannot discriminate the
Bessel relation from its linear approximation at any concentration** with the
estimator as published; the first fix is a bin count of 24 or fewer, not a
larger concentration, and the observed ds005620 ceiling needs 3,000 independent
sites rising to 31,000 under full clustering. **`K_c = 2D` survives the spatial
reduction** across 0.1–0.3 mm — a two-sheet crossing puts the mean-field
threshold at 0.956 × 2D and the three spatial legs at 0.850, 1.013 and 0.940,
while a 1.5 rad/s frequency spread moves it to 3.0 × 2D, so heterogeneity rather
than spatial structure is what the identical-frequency restriction holds back.
**A compatibility observable exists and needs two diagnostics to be trusted**: a
per-region bias mild enough to keep the modal label passes both the information
and the accuracy floors while manufacturing incompatibility, and only a
calibration check catches it.

Validation: `ruff`, `ruff format`, `mypy --strict`, `bandit`, `vulture`, `xenon`
and `tach` pass over 60 source files; the Python suite passes at 214 tests, 52
of them new. No Lean file, publication source, tracked PDF, reference or axiom
allowlist is touched, so no chain edge changes status, and the two P-items are
unchanged. The publication alignment for these three items remains open and is
the only outstanding part of them; `CHANGELOG.md` gets its entry in that pass
rather than this one, because the sentence N7 shows to be incomplete —
`supplementary.tex` on what a discriminating awakening experiment must span — is
still being made and has not yet been withdrawn.

### 2026-09-16 — R8 triaged and its reachable parts scheduled

- [x] Assess R8 against what this repository can reach, now that N8 has
      supplied the regime statement its reduction criterion was waiting on.
- [x] Register the reachable aspects as N10–N13 with acceptance rules, the
      obstructions already known, and the stopping point of each.
- [x] Narrow R8 in place to the residue and say what each remaining part is
      waiting on.

**Nothing was proved, run or measured.** No Lean file, Python module,
publication source, tracked PDF, figure, reference, macro or axiom allowlist is
touched; this pass adds four unstarted items to the ledger and rewrites one
research item's scope note.

Three findings from the assessment are recorded in the items themselves because
they would otherwise be rediscovered at cost. **The supply-to-coherence bridge
does not exist:** `PathwiseStore` appears in `Examples/FiniteSupply.lean`,
`Examples/FundedMemory.lean` and `Phase3_SensorMemory.lean`, and in no file that
installs a kernel, so the composition from a finite source through cumulative
draw and installed energy to K3's no-go is absent rather than merely unstated.
**Two obstructions block the obvious route to it:** `work_learned` decays
geometrically and `cumulative_work_learned_le` caps the whole infinite run, so
the uniform-cost horizon bound does not apply and `balance_le_of_stage_cost` is
the one that does; and `net_draw_eq_zero_of_positive` forces any fundable
protocol to have restricted support. **The quasi-static reduction error has
never been measured:** every `dynamic_ramp` leg is confined to `K_c ± 0.5` and
always crosses threshold, nothing computes `r(t) − r_ss(K(t))` pointwise, and no
coupling anywhere in the repository fluctuates — so `main.tex:182`'s "evolves
more slowly than phase dynamics" is unquantified by anything, which is what N12
exists to fix.

R1, R3, R5, R7 and R9–R12 keep the dispositions the earlier triage gave them,
the two P-items are unchanged, and no chain edge moves.

### 2026-09-16 — N10–N11: the supply-to-coherence bridge, in Lean

- [x] N10: identify a `PathwiseStore`'s draw with `LocalActuator.pathWork`,
      compose the cumulative draw with `installation_first_law` and feed the
      result to K3, with witnesses on both sides.
- [x] N11: state the run-level no-go, exhibit the fence that stops it being
      weakened to a mean, and say what a decay of an installed coupling would
      require.
- [x] The axiom audit, the leaf gate and the `sorry` gate.

**The bridge that did not exist now does.** `PathwiseStore` appeared in no file
that installs a kernel; `PathwiseStore.totalDraw_eq_installation` is the
identification, and it is an identification rather than a construction — a
store whose `draw` at every stage *is* the actuator's path work has a cumulative
draw that `FiniteProtocol.sum_first_law` already telescopes into the
installed-energy change plus the run's heat.
`PathwiseStore.installedEnergy_le_resources` reads
`totalDraw_le_initial_resources` backwards, and
`PricedArrangement.no_coherence_of_funded_source` is the fuel no-go: a run
funded by a declared finite source cannot reach the threshold at any horizon its
resources could not have paid for. `Examples/FundedCoupling.lean` §29 discharges
every hypothesis on a three-level installation funded by a source of `3/8`,
where the threshold needs `1/2`, and the cap is attained exactly at the second
stage, so the bound is not loose by a margin it invented.

**Three findings are worth carrying here.** First, **the learner of §28 cannot
be funded by any finite source at all.** `net_draw_eq_zero_of_positive` forces
its supply to match every draw, which the triage had predicted; what the triage
had not predicted is that `SourceLedgered` is unsatisfiable outright —
`no_source_funds_learner` shows the two readings of `R true - R false` differ by
`2 (1 + log 3)`, because closing the switch costs `1 + log 3` when the register
comes to match the parameter and returns as much when it comes to differ. The
fuel no-go is therefore silent about the learner, which is the right outcome and
not a gap: `learned_above_line` puts it above the threshold from its first
update, and a bound whose hypotheses it satisfied would contradict that.

Second, **the identification of draw with path work is what carries the bound.**
`free_installation_rejected` exhibits a store that is ledgered, solvent at every
horizon and carries a source ledger, and whose run installs `3/8` out of initial
resources of zero. It fails exactly one hypothesis.

Third, **a decay of an installed coupling has a named mechanism and this
development has none of it.** `LocalActuator.storedEnergy_mono_of_stage` says an
installed energy cannot fall across a stage none of whose executed transitions
lowers an occupancy, and
`LocalActuator.exists_lowering_of_installedEnergy_lt` is the contrapositive: a
decay identifies a stage that *uninstalls*. `KernelArrangement.installedEnergy_congr`
says a store's reading is not an argument of `installedEnergy`, which is the
sense in which exhaustion does not uninstall. Naming the maintenance channel and
not supplying one is the whole of the claim; supplying one is a physical
commitment and stays in R8.

**The fence.** `Examples/EvolvingCoupling.lean` §30 carries both sides.
`approach` is an arrangement whose installed energy rises strictly at every
stage towards the threshold and never reaches it, so `no_coherence_of_run`
applies at every horizon. `fence` is four stages of the same hardware whose mean
installed energy is `47/128` — `κ` times it is `47/32` against a threshold of
`2` — and whose first stage exhibits the transition, at mean-field coupling
`23/8`. A no-go with a mean substituted for the supremum would prove a falsehood
on that sequence. Neither says anything about the phase trajectory.

Validation: `lake build` completes warning-free and the axiom audit reports
5,149 declarations in 89 modules resting only on `propext`, `Classical.choice`
and `Quot.sound` — 121 declarations and 2 modules more than before. The leaf
gate reports the same eight recorded leaves and the `sorry` gate covers 93
sources. No publication source, tracked PDF, figure, reference, macro or axiom
allowlist is touched, so no chain edge moves and no R- or P-item changes status.

### 2026-09-16 — N12–N13: the rate and the fluctuation of an evolving coupling

- [x] N12: measure the quasi-static residual on subcritical, supercritical and
      crossing legs, state the admissible-rate criterion, recover the published
      bifurcation-delay exponent, and read the answer against `main.tex:182`.
- [x] N13: drive the same equation with a telegraph and an Ornstein–Uhlenbeck
      coupling, recover both limits and the crossover, and retain the regime in
      which mean-coupling substitution is refused.
- [x] Regressions, the report module, the architecture entries and the gates.
- [x] Open **M1–M3** for the publication alignment this pass and the N7–N9 pass
      both deferred, so that two deferrals are tracked as work rather than
      explained twice in prose.

The pass is recorded in `tasks/coupling_rate_extensions.md`, which carries the
findings, the controls that stand in for the red half of AGENTS.md §1, and the
four publication sentences the measurements bear on. Those four and N7–N9's four
are now section M of this ledger.

Four findings are worth carrying here because they change what a later pass may
claim. **At the threshold itself there is no admissible rate**: on a leg
symmetric about `K_c` the terminal quasi-static residual is `0.3934` at every
one of nine speeds spanning four decades, because the exponential suppression below
threshold and the amplification above cancel exactly. A slower ramp does not
help, so "slowly enough to track the branch" is unattainable precisely where the
recovery argument uses it. **Away from the threshold the criterion is a required
ratio of coupling to phase time scales** — `2000` at `|K-K_c| = 0.05` above
threshold, `632` at `0.2`, `200` at `0.8`, and three to ten times less demanding
below threshold at the same distance — and the geometry and phase time scales
`main.tex:182` cites give a ratio between `600` and `60,000`, which meets every
scanned leg from `0.8` at the slow end and `0.05` at the fast end. **The
published `ΔK ∝ v^0.443` is the threshold limit of this same measurement**: the
deterministic run seeded at threshold at the finite-`N` fluctuation floor fits
`v^0.447` over the four published speeds and `v^0.418` over the three the
published fit used. **Mean-coupling substitution is refused in 25 of 168
drives**, but the refusal is a finite-horizon effect and saying so is part of the
result — the long-run growth rate of a small order is linear in `K`, so the
asymptotic onset threshold is at the mean after all, and at four times the
measured horizon the strongest rejection falls from `0.0924` to `0.0392`. What
the mean fails to predict is the order on a horizon, and a recovery measurement
is made on a horizon.

Validation: `ruff`, `ruff format`, `mypy --strict`, `bandit`, `vulture`, `xenon`
and `tach` pass over `simulations/`; the Python suite passes at 257 tests, 43 of
them new. No Lean file, publication source, tracked PDF, reference or axiom
allowlist is touched, so no chain edge changes status and the two P-items are
unchanged. `CHANGELOG.md` gets no entry: it lists claims that were made and are
no longer made, and the eight sentences these measurements bear on are still
being made. The entry belongs to M3, which withdraws them.
