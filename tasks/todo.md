# Physics of Consciousness — a dissipation bound on coherence

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

## The gap this ledger is about

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

**Current priority: K1, then K2.** K1 is a Fubini identity that costs an
afternoon and is a prerequisite for everything after it. K2 is the substantive
inequality. K3 composes them into the threshold statement, K4 is the witness,
K5 is the scope record and the manuscript change. K-items are the reason this
file exists and come first.

R-items are the carried-forward research programme and are unbounded. P-items
are submission mechanics and are blocked on someone else.

Take one item at a time. Do not start K2 before K1 is proved: K2's statement
names the quantity K1 identifies.

## Standing constraints for this pass

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

## K — The dissipation bound on coherence

### K1 — Identify the installed kernel's energy with the mean-field coupling

- [ ] Prove `KernelArrangement.continuumEnergy A = mean_field_coupling sys`
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

- [ ] Prove `KernelArrangement.continuumEnergy A ≤ κ * storedEnergy`, for a
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

- [ ] Compose K1 and K2 with `critical_coupling` to conclude that an
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

- [ ] Discharge K1–K3 on a concrete arrangement, reusing
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

- [ ] State K3 in Section 5 and in the abstract, and record in the same pass
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

## R — Carried forward unchanged

R1–R7 are reproduced from the archived ledger without change of content;
consult `_archive/todo_2026-09-15_pre-coupling-budget-replan.md` for the full
completion criteria, the R1 documented-limitation disposition and the R6
specification record. They are after the K-items because they are unbounded
research, not because they rank below them.

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
- A dynamical mean-field limit / propagation-of-chaos theorem remains a research
  programme; S4 cannot close it.
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
