# R — Research programme

The unscheduled research items, restored from `tasks/todo.md` as it stood at
`dde1a36`. Commit `0505cac` replaced that ledger wholesale with a
property-testing plan; these items were open then and are open now, so they live
here rather than in git history alone.

`tasks/todo.md` carries the scheduled work and its pass records. This file
carries what is deliberately not scheduled, with the reason beside each item —
the triage below is the point of the file, not the list. An item that is merely
hard is not the same as an item whose cheap closure would be worse than none,
and three of these are the second kind.

Two further sections of that ledger are not restored here and remain in
`dde1a36:tasks/todo.md`: **P — Submission readiness** (two open items on author
affiliation and the journal data-availability statement) and the **Pass records**,
whose substance is in `CHANGELOG.md` and the `_archive/` ledgers.

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
