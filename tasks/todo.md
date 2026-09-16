# Physics of Consciousness — scheduled extensions and research

**Follow-up scheduled 2026-09-16.** N1–N6 below are bounded extensions of the
current results; R8–R12 record the broader research directions. None is a
prerequisite for publishing the present conditional framework. K1–K5 remain
complete, R1–R7 retain their scope, and the two existing P-items are unchanged.
Scheduling these extensions does not report them as proved or implemented.

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
a stopping point. R-items require broader theory, new physical identifications
or empirical work. P-items are submission mechanics and are blocked on someone
else. The N- and R-items do not reopen publication readiness.

Take one item at a time. N3 consumes N2's specified observation mechanism; N6
can reuse N5's indistinguishability bound. N1, N4 and N5 can be completed
independently. The completed K pass followed K1 before K2 because the latter
names the quantity the former identifies.

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

**Intent and acceptance rule.** Connect existing constructions or remove an
unnecessary restriction. A completed item must supply a new consequence or
discharge a previously separate modelling obligation for a declared mechanism;
renaming an assumed conclusion or adding an unused structure is insufficient.
Write failing Lean specifications first, retain nondegenerate witnesses and
rejection cases, and require the warning-free build and axiom audit. Changes to
published claims include the matching prose, tables and rebuilt tracked PDFs.
No production sweep or new empirical result is required by these items.

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

## R — Research programme

R1–R7 are reproduced from the archived ledger without change of content;
consult `_archive/todo_2026-09-15_pre-coupling-budget-replan.md` for the full
completion criteria, the R1 documented-limitation disposition and the R6
specification record. R8–R12 were added on 2026-09-16. Placement after the
scheduled items reflects scope, not scientific importance or publication need.

- [ ] **R1 — Calibrate effective coupling and phase diffusion in consistent
      units.** Not closable in this repository; carries a documented-limitation
      branch. Do not attempt to close it with a fitted $\gamma$, and in
      particular not with $\gamma = D$, which cancels the diffusion parameter out
      of a test whose content is the ratio of coupling to diffusion.
- [ ] **R2 — Validate spatial aggregation and the mean-field approximation.**
      B4 and C3 sharpen what S2 does and does not show and are inputs to this.
- [ ] **R3 — Calibrate extracellular geometry against coupling and recovery
      time.**
- [ ] **R4 — Calibrate the phase-observation model and uncertainty.** A1 is a
      small piece of this: the concentration range the EEG data occupy does not
      separate $I_1/I_0$ from its tangent, and the separation figure must be
      right before the required range can be stated.
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
      declared. Connect to R6's observable and to the recorded cover-selection
      question; agreement, useful prediction and truth about the environment
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
  under R8, alongside R2's validation of the spatial reduction; S4 cannot close it.
- Enlarging the local state space so that phase, or an independent transition
  datum, is part of it would give `Phase5_TwistedGluing` a non-vacuous consumer.
  That is a physical modelling choice, not a way to close a leaf gate.
- Overlap compatibility remains an explicit physical hypothesis. Do not schedule
  another attempt to derive it from the current class fields.
- The formalization paper and audit paper remain viable separate publications.
- PRX Life presubmission was explicitly declined.
- The three recorded leaf modules are terminal and are not re-litigated per pass.
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

All six N-items are proved, witnessed and built. The pass added five library
modules and five witness files; `lake build` is warning-free and the audit
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
that of a phase-derived channel. The control has the identical order parameter
`1/4` at every parameter and action and observations independent of the
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
control for §1–2 of `Phase7_Rigidity`: an architecture whose support contains the
best distinct pair is optimal at its resource, so the gap `rigid_gap` exhibits is
forced by the missing wire alone.

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

**Not done, and deliberately.** The manuscript, supplement and primer are
unchanged at the user's instruction, so Table 1, Table S1 and the implementation
notes do not yet mention any N-item result, and no PDF was rebuilt. That is the
remaining work for this pass under AGENTS.md §8. No R- or P-item status changed,
no reference was added, and no simulation sweep was run.
