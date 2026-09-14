# Physics of Consciousness — simulation audit remediation

**Replanned 2026-09-09.** The preceding ledger is archived unchanged at
`_archive/todo_2026-09-09_pre-simulation-audit-replan.md`. It closed S1–S6,
C1–C3 and P1–P3, and left R1–R6 and three P4 items open; those carry forward
below without change of content. Earlier ledgers are
`_archive/todo_2026-09-03_pre-simulations-replan.md`,
`_archive/todo_2026-08-31_pre-composability-replan.md` and
`_archive/todo_2026-08-30_pre-strategic-replan.md`.

This file replaces the old one because **the bottleneck changed from producing
the numerical pass to trusting what the pass is reported to show.** An audit on
2026-09-09 re-derived every published numeral from the saved artifacts and ran
two controls the repository does not have. The bookkeeping is sound: 100/100
tests pass, `check_prose`, `check_tableS1` and `check_figures` pass, and the
macro-drift test confirms every `\ramp*`, `\selection*`, `\spatial*`,
`\frustration*` and `\plasticity*` numeral matches its summary file. What the
audit found is a different class of defect: **numbers that are correctly
transcribed and incorrectly interpreted.** Three are attributed to the wrong
cause, three are compared against the wrong reference, one control does not
control for the thing it is cited for, and one hand-computed numeral is simply
wrong.

None of the September 9 findings overturns a headline claim. Every one is a
place where a referee who recomputes will find the manuscript saying more than
the artifact supports, which is precisely the failure mode the whole project
is organised against.

**Follow-up audit, 2026-09-10; closed 2026-09-11.** F1–F6 below are all done.
F1 changes that assessment for the plasticity headline: sampling immediately
after updates shows descent that the mean over all integration steps does not.
F2–F4 are narrow wording corrections. F5 and F6 were optional, bounded studies
that could have changed a central conclusion; both ran and both reported
negative answers, which the publication now carries.

## How this ledger is ordered

**Current manuscript priority:** the third P-item, the final read of every
citation and every generated macro. Its prerequisites A1, A2 and F1–F4 are
closed, and the other two P-items require author or journal decisions.
**The publication audit is on hold at the user's request, 2026-09-14.**
The agency/active-chain extension is complete; its primer alignment and the
complete finite-update theorem are recorded in the dated sections at the end
of this ledger. L2's goal-directed policy selection under a finite budget is
complete; its witness and scope are recorded below. Further theoretical
modelling does not require new empirical results. The bounded learning-dynamics
model is complete: thermal adaptation of a policy register with known task
values, expected improvement, a stationary limit and explicit update heat.
Its specification and scope are in `tasks/learning_dynamics.md`.
The agency roadmap at the end of this ledger records the remaining modelling
gaps and stretch work. Agency has reached the 80/20 stopping point for the
current manuscript; those extensions are not submission prerequisites.
The 80/20 constraint remains to correct unsupported claims and retain supported
results, without expanding into incremental sweeps.

**The preceding pass is ordered by effort, ascending.** A-items are prose or
reference edits against numbers already in the repository. B-items add a
derived quantity to an existing report script and read it from a saved summary
— no production sweep reruns. C-items
need a rerun of an existing sweep at new parameters. D-items need a new design.
E-items are repository infrastructure: they change no number, proof or claim,
and sit after D because none of them blocks the manuscript. R-items are the
carried-forward research programme and sit after E because they are unbounded,
not because they rank below it. P-items are submission mechanics
and are last only because two of the three are blocked on someone else; the
third was gated on A1, A2 and F1–F4, which are now closed.

Take one item at a time. A- and B-items may be batched into one commit each if
they touch the same file; do not start a C-item while an A- or B-item is open.

## Standing constraints for this pass

1. **Regenerating a macro must never rerun a production sweep** (AGENTS.md §3).
   Every B-item reads `figures/*/summary.json` or an existing `.npz` and emits a
   macro through `simulation_tex.py`. If an item seems to need a rerun, it is a
   C-item and is misfiled.
2. **No new hand-typed numerals in the publication** (AGENTS.md §3). A1 exists
   because that rule was not followed once; do not add a second instance while
   fixing the first.
3. **The publication is not a changelog** (AGENTS.md §5). Every correction below
   becomes a present-tense statement of what is true. "The gap we previously
   attributed to finite size" fails `check-prose` and would deserve to.
4. **A source change and its rebuilt PDF belong in the same commit**
   (AGENTS.md §6), and `arxiv_submit/` is refreshed or removed in the same
   commit (AGENTS.md §7).
5. Five pre-commit hooks judge the whole tree whenever any Python file is
   staged. A B-item that adds an unannotated helper blocks every later Python
   commit, not only its own.
6. **Correct only what the evidence requires.** Retain supported findings and
   distinguish a wrong interpretation from a wrong numerical implementation.
   F1 is a substantive exception to the preceding pass's conclusion that every
   headline survives: sustained plasticity descent is not supported by the
   production replay. Do not weaken other conclusions by association or
   strengthen one because a correction turned out to be small.

---

## F — Follow-up audit and consequential simulations (2026-09-10)

**Scope and evidence.** The audit read the simulation implementations, saved
artifacts and manuscript claims. Forty-nine targeted tests, the
`simulation_results.tex` drift check, and direct numerical equation checks
passed. In-memory replays reproduced all twelve production plasticity final
kernels exactly. The audit changed no repository files; the new diagnostic
numbers below were printed during the audit and are not committed simulation
summaries. If any enters the publication, first preserve its compact source
summary, generator and drift test under AGENTS.md §3.

F1–F4 are necessary corrections. F5–F6 are optional studies whose outcomes could
change the argument, with completion defined by answering the stated question
either way. Existing A–E completion records remain historical records; they
must not be used to dismiss these follow-up findings.

### F1 — Correct the plasticity sampling and claim of sustained descent

- [x] Distinguish the immediate post-update objective from its mean throughout
      the intervals between updates, and correct the claims that depend on
      sustained reduction.

**Evidence.** In `structural_resonance.simulate`, `update_every` and
`sample_every` are both 50. Diagnostics run after the coupling update, so
`metrics.tail_dissipation` averages only the instant at which the update has
just acted. Recording the drift objective at every integration step in an
otherwise unchanged replay gives the following second-half means:

| Seed | Gradient: reported post-update mean | Gradient: mean over all steps | Frozen: mean over all steps |
|---|---:|---:|---:|
| 20260906 | 1115.4 | 1429.1 | 1381.9 |
| 20261906 | 1110.6 | 1398.7 | 1380.8 |
| 20262906 | 1116.6 | 1422.3 | 1383.7 |

The all-step diagnostic covers t in [200, 400) at dt = 0.01; the saved
post-update readout includes the final t = 400 sample. All twelve final kernels
match the saved production kernels bit-for-bit. The reported 67.7–69.1%
headroom removal belongs to the post-update readout. On every seed the mean
over all steps exceeds the frozen baseline.

**Completion.** The abstract, introduction, plasticity argument and figure
caption in `main.tex`, the corresponding supplement and run report, and the
primer wherever it repeats the claim, consistently name the measured quantity.
Retain the observed coherence and loss of alignment and the fixed-phase
mathematics. Remove the inference that these runs exhibit sustained objective
minimization, including the claim that they thereby establish the antecedent of
the strong counterexample. Keep squared drift distinct from thermodynamic
entropy production. A prose correction can retain the saved post-update
numbers if they are identified accurately.

If the reporting code is extended to measure the mean over complete update
intervals, write a regression test first that distinguishes it from samples
taken only after an update. Preserve the dynamics, record both readouts, and
save compact summaries of the replay separately from macro generation. The
saved decimated objective alone cannot reconstruct the omitted intervals.
F5 is the separate question of whether a different declared regime supplies
the stronger counterexample; it is not a prerequisite for correcting F1.

### F2 — Describe the plasticity controls' actual matching

- [x] Replace claims of equal step size, cumulative deformation and coherence
      with the matching implemented and the comparable ranges observed.

**Evidence.** `structural_resonance.step_direction` computes the gradient from
each arm's own evolving phases and couplings. The random direction is scaled to
that local gradient; the permuted arm relabels its own gradient. Neither is fed
the contemporaneous step from the gradient arm. In the production replays,
mean direction norms were about 43 for the gradient arm and 35 for the random
arm. The gradient and permuted arms' final norm-growth and order ranges
overlap; they are not equal by construction.

**Completion.** Correct the abstract and control descriptions in `main.tex`,
the sentence beginning “The comparison the two controls jointly support” in
`supplementary.tex`, and corresponding report/docstring descriptions. State
local gradient normalization and empirical overlap of the reported ranges.
Retain the controls and their observed results. This is a wording correction;
it does not require another control arm or a redesigned matching procedure.

### F3 — Remove the exclusion of growth-fit window bias

- [x] Correct the supplement's statement that the shortfall of the growth-rate
      slope from 1/2 “is therefore not a property of the fit window”.

**Evidence.** C2's relative bounds do not establish an unbiased estimator.
A deterministic mean-field Fourier diagnostic, with no finite population or
Euler–Maruyama integration, returned a slope of 0.466531 using the declared
upper bound of half the stationary branch. Halving that bound returned
0.489995. The 0.466531 result agreed between 30 modes with DOP853 and 15 modes
with Radau. The diagnostic used D = 1, the production coupling grid 2.2–3.1,
samples every 0.05 over t in [0, 10], lower bound 2/sqrt(1000), and initial
first Fourier moment sqrt(pi)/(2 sqrt(1000)), with higher moments zero.

**Completion.** Preserve the measured production slope and the qualitative
escape result. State that the finite fit window can contribute to the residual;
the stationary-order step-size control does not apportion bias in this growth
estimator. Do not assign the whole remaining discrepancy to finite N or the
integrator. Removing the unsupported exclusion is sufficient; no production
rerun or new published diagnostic numeral is required.

### F4 — Scope the spatial refinement to the comparison actually made

- [x] Replace the claim that the boundary is independent of discretization and
      resolved on the finer sheet with the observed stability of the operational
      crossing under this one refinement.

**Evidence.** The interpolated crossing changes by a factor of about 1.01
between the 128² and 256² sheets. At the same nearby decay length,
0.014670795479089165 mm, the saved steady order changes from 0.617556 to
0.268704. Agreement of the threshold interpolants is not convergence of the
near-boundary dynamics; the refined crossing is only about 1.81 cells wide.

**Completion.** In the “Finite-sheet spatial-decay control” subsection of
`supplementary.tex` and any repeated interpretation, say that the operational
crossing was nearly unchanged under this one refinement. Keep the reported
crossings, the metastability qualification and the finding of coherence in the
sampled empirical band. No additional spatial resolution is needed to make this
wording correction.

### F5 — Bounded study: sustained objective reduction with loss of alignment

- [x] Optional, first study to consider: determine whether a declared
      plasticity regime exhibits sustained objective reduction, coherence and
      anti-alignment together.

**Why this could change the paper.** A positive result would supply the missing
antecedent of the strong plasticity counterexample exposed by F1. A negative
result would support keeping the corrected, narrower account. This study is
about the squared-drift objective and this objective/template pairing; it
does not establish a result for thermodynamic entropy production.

**Design before execution.** Specify a small finite set of learning rates and
physical update intervals, the resource budget and duration, and quantitative
criteria for sustained improvement against the frozen arm, maintained
coherence and loss of alignment. Use the objective throughout complete update
intervals. Declare tuning and held-out seeds separately; do not select a rate
on its favorable alignment outcome. Confirm any candidate coexistence on the
held-out seeds and at a smaller integration step while keeping physical
duration and update cadence fixed. Describe any additional controls according
to what they actually match, as in F2.

**Completion and stop rule.** Write the estimator tests first, run a reduced
check, then execute the declared design and report every outcome. Preserve
compact summaries and generate any publication numbers from them. Stop after
the declared design and confirmation checks; do not expand the grid or keep
tuning to rescue the headline. Failure to find coexistence in that design
is not a proof that no such regime exists. Completing the study means reporting
its answer and adjusting the claim accordingly, not obtaining a positive result.

### F6 — Bounded study: recovery-mechanism discrimination under common observation

- [x] Optional, after F5 if a substantive addition is wanted: test whether the
      proposed measurements can identify the mechanism generating recovery.

**Why this could change the paper.** The stationary self-consistency equation
depends on K/D. Increasing coupling and decreasing phase diffusion can
therefore give the same stationary concentration and coherence. A model-recovery
study could show which temporal information or independent parameter measurements distinguish
them, or demonstrate precisely which additional measurement the proposed
protocol needs. This develops R4/R5 without claiming to complete their
empirical programme.

**Design before execution.** Declare the candidate families: increasing
coupling, decreasing phase diffusion, and a simple shared-drive alternative.
Specify parameter ranges, observations available to the analysis, fitting
procedures and success criteria before inspecting outcomes. Examine analytic
equivalences first and use ideal observations for a small feasibility study.
If distinguishability survives, apply the same observation noise, filtering,
pooling and estimators to data from each mechanism, and measure recovery of the
generating model on held-out simulations. The inference must not receive
unobserved true K, D or model labels; independent parameter estimates count
only when the measurement protocol supplies them.

**Completion and stop rule.** Report model recovery and confusion across the
declared cases, including failures. If the mechanisms are indistinguishable
under ideal observations, record the ambiguity and the additional observable
needed, and stop before adding observation complications. Retain a successful
protocol only within the tested observation assumptions. Neither outcome
identifies the coupling as electromagnetic; that requires independent physical
measurements. Do not turn a failed pilot into an open-ended search over models.

**Method reference, verified online during the review:** Robert C. Wilson and
Anne G. E. Collins (2019), “Ten simple rules for the computational modeling of
behavioral data”, *eLife* 8:e49547,
[doi:10.7554/eLife.49547](https://elifesciences.org/articles/49547).

**Not scheduled under the 80/20 constraint.** Further spatial resolutions,
frustration grids, population-size sweeps or alternative templates would mostly
refine existing illustrations. Skip them unless a specific result shows they
are necessary to decide a central claim. Keep the supported finite-run findings
and existing scope qualifications; do not broaden the corrections into a
simulation redesign. F5 and F6 are optional additions, not submission blockers
once F1–F4 have been addressed.

---

## A — Prose and reference corrections (no computation)

**Closed 2026-09-09.** All seven items are done; the entry in `CHANGELOG.md`
records what each one changed. Two things the section did not anticipate. A1's
numerals are now generated rather than typed, which required a new
`tangent_separation` in `empirical_collapse.py` and four macros in
`simulation_results.tex`. And the prose edits repaginated the merged arXiv
document onto a citation link split across a page break, which aborts pdfTeX
rather than warning; `prepare_arxiv.sh` now boxes citation groups in the merged
document only, the standalone article being unable to take the same edit without
overfilling a line by 164pt.

### A1 — Correct the Bessel-tangent separation figure

- [x] `supplementary.tex:580`: "recordings that reach $a \gtrsim 1.5$, where the
      two separate by more than 0.17". The separation between $I_1/I_0$ and its
      tangent $a/2$ at $a = 1.5$ is **0.154**, not 0.17; 0.17 is first reached
      near $a \approx 1.57$. In the same sentence, "departs from the naive
      linear form $a/2$ by at most 0.0094" over $a \in [0.302, 0.542]$ is
      **0.00949**, which rounds to 0.0095.

**Completion:** both numerals generated, not typed. Add a small function to
`empirical_collapse.py` that computes the max deviation of `bessel_ratio` from
`a/2` and from `tanh(a/2)` over the observed concentration range, and the
concentration at which a stated separation is reached; emit them as macros
through `simulation_tex.py` with a drift test. This section is the only place in
either document where computed numbers are hand-entered, which is why this is
the only arithmetic error the audit found. Fixing the number without fixing the
mechanism leaves the mechanism.

### A2 — Resolve the citation gaps

- [x] `supplementary.tex:95` cites "Townsend et al. (2015)" and "Xu et al.
      (2023)" by author-year. Neither has a `\bibitem` in `references.tex`, so
      neither resolves for a reader.
- [x] `kawai2007` has a `\bibitem` and no `\cite`; the supplement cites it inline
      in prose with full journal details instead. Pick one form.
- [x] Re-verify `shenker2000` (Shenker, "Logic and Entropy", given as
      *Philosophy of Science* 67, S146–S152). The audit could not confirm that
      venue and page range; the widely available version is a PhilSci-Archive
      preprint.

**Completion:** every author-year mention in either document resolves to a
`\bibitem`, and every `\bibitem` is cited. Each added or changed entry is
verified online for authors, title, year and venue before commit (AGENTS.md §4).
Do not add an entry from memory.

### A3 — Report the frozen-arm baseline beside the permutation percentile

- [x] `main.tex:198` gives the gradient arm's permutation percentile
      (`\plasticityPercentileMin`–`\plasticityPercentileMax`, 0.951–1.000) with
      no reference distribution. `supplementary.tex:370` states the rule the
      main text does not follow: "the gradient arm is read against the frozen
      arm and not against the null median". The frozen arm sits at 0.644–0.911
      across the same three seeds, so the increment is smaller than the bare
      figure suggests, and the two ranges nearly touch at n = 3.

**Completion:** `main.tex` carries `\plasticityFrozenPercentileMin` and
`\plasticityFrozenPercentileMax` in the same sentence. Both macros already
exist; no computation is required. State the comparison as the increment over
the frozen arm, and do not present the percentile as if the null were 0.5.

### A4 — Stop calling the joint witness "a common toy model"

- [x] Abstract (`main.tex:48`), introduction (`main.tex:60`) and §5.2
      (`main.tex:357`) say "a common toy model satisfies all eight" / "A common
      toy witness satisfies all eight".
      `chain_hypotheses_jointly_satisfiable` instantiates a `Bool` double well,
      a `Bool` register, a uniform-grid mesh and a three-site cortex, and
      `Chain.lean`'s own docstring says these "remain deliberately distinct toy
      systems".

**Completion:** the manuscript says what the Lean docstring says — a single
simultaneous witness assembled from distinct toy components, establishing that
the conjunction is inhabitable and not that one mechanism realises it. Keep the
non-vacuity claim; drop the implication of a shared model.

### A5 — Correct the `resonanceRate` physical description

- [x] `supplementary.tex:237` calls $\exp(-(K-K_c)\tau/2)$ "the linear
      relaxation factor of the mean-field order parameter over an interval
      $\tau$", and `Chain.lean`'s `E89` docstring calls it "the linearisation of
      the mean-field dynamics about the coherent branch". Neither is right.
      $(K-K_c)/2$ is the growth rate of the *incoherent* state's instability;
      linearising $\dot r = \tfrac12(K-2D)r - cr^3$ about the coherent fixed
      point gives a relaxation rate of $(K-K_c)$, twice as large.

**Completion:** the rate is described as what it is. Note that the error is
conservative — the assumed Lipschitz constant is larger than the true relaxation
factor, so the hypothesis is weaker than it could be and no theorem changes.
Say that rather than silently substituting the correct rate, which would
strengthen an instance obligation the framework does not need strengthened.

### A6 — Align the E78 row of Table 1 with `Chain.lean`

- [x] Table `tab:summary` and the `E78` edge note in `fig:chain` say "Coherence
      supplies a cover ... carrying compatible local states". In Lean,
      `E78 K D T := Coherent K D → T.IsReachedByRelaxation K`: the cover `T` is a
      separate argument of `chain`, its overlap-compatibility obligation lives in
      the `LocalSectionSynchronization` field it extends, and `n8` is derived by
      `unity_of_cover ⟨T⟩` rather than from `n7`. So coherence does not supply
      the cover, and the compatibility hypothesis — the load-bearing assumption
      of the whole unity-is-not-synchrony argument — sits outside the eight
      arrows.
- [x] `Chain.lean`'s `E78` docstring opens with the same stale claim ("Asserts
      that a substrate with a coherent order parameter carries a
      `ThermodynamicCover`"), which its own closing paragraph then contradicts.
      A second stale line in the same docstring says `cortexCover` "meets no
      relaxation condition at all", while `chain_hypotheses_jointly_satisfiable`
      discharges the edge with `cortexCover_reachedByRelaxation_three`.

**Completion:** Table 1 and the figure note state what `E78` consumes, and the
manuscript's "isolating the eight hypotheses it consumes" is qualified to say
that the theorem also takes structures — a `ThermodynamicCover` and a
`ReflexiveBoundary` — whose class fields carry physical content. Do not attempt
to fold compatibility into `E78`; that is the derivation the standing
prohibition below forbids. The point is to name where the assumption is, not to
move it.

### A7 — Fix the latent unit trap in `fermi_params.tex`

- [x] `fermi_estimate_check.py:9` documents `D` as "Lorentzian half-width of
      intrinsic frequency spread (rad/s)", `\fermiD` inherits that comment, and
      `\fermiKD` divides by it. `main.tex:80` states the opposite rule: "a
      frequency-spread width cannot be substituted for `D` when applying the
      identical-frequency stationary theory." Nothing published is currently
      wrong — only `\fermiFieldMin` and `\fermiFieldMax` are used in either
      document — but every other macro in that file is one `\fermiKD` away from
      making the substitution the manuscript forbids.

**Completion:** either the comment and macro names say which threshold they
belong to (noiseless Lorentzian $K_c = 2\gamma$ versus identical-frequency noisy
$K_c = 2D$), or the unused macros are removed. Both are defensible; a silent
`\fermiD` that means neither is not.

---

## B — Derived quantities from saved artifacts (no reruns)

### B1 — State the onset estimator's stationary-branch reference

- [x] `supplementary.tex:469` says "the slow ramps recover the square-root
      foot", comparing $\beta_{\rm eff}$ against 1/2. Applying
      `fit_onset_exponent` — the paper's own estimator, window $0.1 \le r \le
      0.4$, `K0` bounded below by 2 — to the **exact stationary branch** on each
      leg's own coupling grid returns $\beta_{\rm eff} = 0.443$ (v = 1e-2, 1e-3
      grids) and $0.448$ (v = 1e-4 grid). The estimator carries a systematic
      downward bias of about 0.05 from fit-window curvature, independent of ramp
      speed: the window reaches $K - K_c = 0.19$, well outside the asymptotic
      regime where $\beta = 1/2$ is defined. The slowest ramp's 0.417 is
      therefore at, and slightly below, the adiabatic reference rather than
      recovering 1/2.

**Completion:** `dynamic_ramp_report.py` computes the reference exponent by
running `fit_onset_exponent` on `bifurcation.coherent_r` sampled on the same
coupling grid, and emits it as a macro. The supplement compares the measured
exponents against that reference and not against 1/2. The headline conclusion is
unaffected — 0.96 against a 0.44 adiabatic reference is a large effect — and
must not be softened; what changes is that a reader can separate the ramp effect
from the estimator bias, which at present they cannot.

### B2 — Report the fit window each onset exponent was measured over

- [x] The four $\beta_{\rm eff}$ values are presented as one quantity at four
      speeds (`main.tex:166`, `supplementary.tex:469`). They are not. For
      v = 0.1 the ensemble mean never exceeds $r = 0.152$, so the nominal window
      $r \in [0.1, 0.4]$ truncates to $[0.100, 0.151]$ at $K - K_c \in [0.32,
      0.50]$ — 19 points, far past threshold — and `curve_fit` returns `K0`
      pinned exactly at its lower bound 2.00000. The slower legs fit over
      $K - K_c \in [0.01, 0.20]$. The fast number is the local log-slope of a
      strongly delayed trajectory, not an onset exponent.

**Completion:** the report emits per-leg macros for the realised $r$ range, the
realised $K - K_c$ range, the sample count and whether `K0` hit its bound; the
supplement states them. The right reading is available and is stronger than the
current one: at the fastest ramp the trajectory does not reach the fit window at
all within the simulated interval, which is a sharper statement of "the
stationary branch is not a universal time course" than an incomparable exponent.

*(A mixture artifact was suspected here and ruled out: ensemble mean and median
replica track each other to within 0.01 at every speed, so the ensemble mean is
representative of a typical trajectory. The defect is the truncated window
alone.)*

### B3 — Withdraw or qualify the $\sqrt{\log N}$ agreement

- [x] `supplementary.tex:464` reports delays 0.0619, 0.1947, 0.2341 at
      $N = 500, 2000, 8000$ and calls them "qualitatively agreeing with the
      predicted $\sqrt{\log N}$ dependence". Dividing through:
      `delay / sqrt(log N)` = 0.0248, 0.0706, 0.0781 — a factor of 2.8 spread,
      all of it in the $N = 500$ point. The mechanism is in the data: at
      $N = 500$ individual replicas reach $r = 0.436$ **before** $K_c$ (against
      0.106 at $N = 8000$), so the size-independent escape level $r \ge 0.2$
      fires almost immediately at the small size. The measured $N$-dependence is
      dominated by a fixed absolute criterion meeting a size-dependent critical
      fluctuation floor — the exact failure mode item 5 of the manuscript's own
      protocol warns experimenters about.

**Completion:** the report emits `delay / sqrt(log N)` per size and the maximum
pre-threshold replica order per size, and the supplement claims monotonicity
only. The self-referential point is worth making in print rather than burying:
the control demonstrates the protocol hazard it was not designed to test.

### B4 — Report the spatial sweep in lattice units and name the plateau

- [x] `supplementary.tex:427` reports a critical decay length of 0.0140 mm and
      says "its boundary lies about sevenfold below the band's 0.1 mm lower
      limit". Grid spacing is $2.0/128 = 0.015625$ mm, so 0.0140 mm is **0.90
      lattice spacings**, and every sampled point in the transition region
      (0.0078–0.0147 mm) is below one cell. The boundary is set by the choice
      `side=128, extent=2.0` and would halve on a 256² sheet, so the sevenfold
      margin has no resolution-independent content.
- [x] The same summary shows steady order **0.9427 to four decimals at every
      $\lambda \ge 0.1$ mm out to $\lambda = 8$ mm** — four times the sheet
      extent, i.e. effectively all-to-all coupling. The empirical band sits deep
      in a saturated plateau, which is the actual finding and is not stated.

**Completion:** the report emits the decay lengths in lattice units alongside
millimetres, and emits the plateau range. The supplement states the decay length
in cells wherever it states it in millimetres, drops the sevenfold margin or
attaches the resolution caveat to it, and says that coherence in the 0.1–0.3 mm
band is indistinguishable from the global-coupling limit. The negative claim the
simulation was run for — no fragmentation in the empirical band — survives
unchanged and is what matters.

### B5 — Report the frustration crossing as its bracket

- [x] `main.tex:183` gives an operational crossing at $K_{\rm eff}/D$ between
      1.8994 and 1.9387, five significant figures. The saved bracket is
      $[1.857, 2.110]$ with order 0.165 → 0.314 across it, from a geometric
      $\varepsilon$ grid of ratio 1.136; the point estimate is a straight-line
      interpolation of a near-critical power law across a 14%-wide gap, which
      biases it low. The bracket contains $K_c/D = 2$, so the run provides no
      evidence that the crossing differs from the mean-field threshold.

**Completion:** the bracket is reported beside or instead of the interpolant,
with the grid ratio stated, and the precision of the quoted range is cut to what
the grid supports. Add the observation the supplement is one sentence from
already making: the crossing sits below the model's own $K_c$, and the same run's
$N\langle r^2 \rangle > 1$ result — signed coupling amplifying finite-size
fluctuations — is why. The two facts are currently in adjacent paragraphs and
never joined.

### B6 — Expose the limitation of the matched-random plasticity control

- [x] `main.tex:196` rests the specificity of the descent on a random arm "of
      the same Frobenius norm", concluding that the descent belongs to the
      gradient "and not to motion of a kernel at fixed resource". The saved
      summary shows the arms are matched on the *per-step* direction norm only:
      `kernel_norm_growth` is **12.41–14.70** for the gradient arm and
      **1.29–1.31** for the random arm. Successive isotropic steps cancel, so
      the random arm ends an order of magnitude less deformed. The manuscript's
      own explanation for the Frobenius-distance growth — clip-and-rescale
      concentrating mass onto fewer edges — is a channel the random arm barely
      enters, so the control does not separate the gradient direction from
      comparable cumulative deformation.
- [x] The learning rate 0.2 was selected by a one-seed sweep on seed 20260906,
      which is also one of the three reported seeds: its `tail_dissipation`,
      1115.4313857261145, appears identically in `sweep.json` and
      `summary.json`. Disclosed in the supplement as a one-seed sweep; the
      overlap is not.

**Completion:** the random arm's `kernel_norm_growth` is emitted as a macro and
reported, and the supplement states what the control does and does not rule out.
Note the tuning-seed overlap in the same paragraph. This is a scoping fix, not a
retraction: the effect is large, consistent across three seeds, and the
conservation-law argument is independent of the control. D1 is the item that
would close the gap properly.

---

## C — Reruns of existing sweeps

### C1 — Attribute the dynamical-selection residual correctly

- [x] `main.tex:177` reports that at $K = 2.8$ the steady mean order is 0.67735
      against a static 0.68270 and calls the gap a **finite-size** discrepancy.
      An independent step-size series on the same system (`K=2.8, D=1, N=1000`,
      64 replicas, tail-quarter mean) gives:

      | dt | 0.02 | 0.01 | 0.005 | 0.0025 | static |
      |---|---|---|---|---|---|
      | steady $r$ | 0.67145 | 0.67674 | 0.68041 | 0.68103 | 0.68270 |

      dt = 0.01 reproduces the published value to within noise; the residual is
      monotone in dt and about 70% of it is gone by dt = 0.0025. Roughly
      $-0.004$ of the reported $-0.0054$ is Euler–Maruyama bias and only about
      $-0.0016$ is attributable to $N$.
- [x] `dynamical_selection.py`, `dynamic_ramp.py` and `propagation_of_chaos.py`
      all run at a fixed dt = 0.01 with no step-size control. Only
      `geometric_frustration` has a half-step check.

**Completion:** a step-size control is added to `dynamical_selection.py` on the
pattern of the existing frustration half-step control, its result saved as a
compact summary and emitted as macros, and the manuscript attributes the
residual to the integrator with the finite-size part stated separately. Write
the deterministic test first. Do not re-tune dt to make the residual vanish and
then report the smaller number without the control — the control is the result.

**Scope:** this does not change any conclusion. The finding is that the
finite-$N$ system agrees with the stationary branch *better* than the manuscript
claims, which strengthens the escape-toward-the-coherent-branch statement while
removing a finite-size claim the data do not support.

### C2 — Refit the growth rate outside the fluctuation floor

- [x] `estimate_growth_rate` fits $\log \bar r$ from `transient = 1.0` up to
      `saturation_cap = 0.3`. At $N = 1000$ the noise floor is $\approx 0.028$
      and the fit window opens while the trace is still on it, which biases the
      slope down; the cap at 0.3 truncates inside the nonlinear regime at larger
      $K$. The reported slope 0.4324 against a theoretical 1/2
      (`main.tex:177`) is partly a window artifact, and the same integrator bias
      as C1 contributes.

**Completion:** the window is defined relative to the finite-size floor rather
than absolutely — a stated multiple of $1/\sqrt{N}$ at the low end, a stated
fraction of the static branch value at the high end — the fit is repeated, and
the supplement reports the window with the slope. If the slope moves toward 1/2,
say so; if it does not, the residual is then a real finite-$N$ statement and can
be reported as one for the first time.

### C3 — Grid-refinement control for the spatial sweep

- [x] B4 establishes that the reported critical decay length is 0.90 lattice
      spacings. Whether that is a lattice artifact or a coincidence is decidable
      by running the transition region at `side = 256, extent = 2.0` (halved
      spacing) and asking whether the boundary in millimetres halves.

**Completion:** the transition-region decay lengths rerun at one refined
resolution, with the result reported either way. If the boundary scales with the
lattice, the supplement says the sweep bounds fragmentation from below only in
the resolved band and states no critical length; if it does not, the number
becomes meaningful for the first time. Reduced smoke run first;
`tasks/simulation_shared_notes.md` carries the Pi 5 budget for the 128² sweep and
a 256² sheet is four times the work per step.

### C4 — Refine the frustration crossing grid

- [x] B5 establishes that the crossing bracket $[1.857, 2.110]$ contains $K_c/D
      = 2$. A linear refinement of `epsilon_grid` between those two points on the
      three existing seeds would either separate the crossing from 2 or show it
      is not separable at this $N$.

**Completion:** the refined sweep is run and the crossing is reported with a
bracket the grid supports. A result indistinguishable from $K_c$ is the more
interesting one and must not be presented as a failure of the run.

---

## D — New design required

### D1 — A plasticity control matched on cumulative deformation

- [x] B6 records that the matched-norm random arm ends 10× less deformed than
      the gradient arm, so it does not control for the sparsification channel.
      A control that does would fix a random symmetric direction once per seed
      and take persistent steps along it, or rescale the random step so that
      cumulative `kernel_norm_growth` tracks the gradient arm's.

**Completion:** a third control arm sharing the same phase-noise stream, with
its `kernel_norm_growth`, `alignment_ratio` and `permutation_percentile`
reported beside the existing arms. The prediction under the conservation
argument is explicit and should be written down before the run: a persistent
random direction should sparsify like the gradient arm and *not* drive the
within-over-between ratio below 1, because only the gradient direction is
correlated with the drift-equalising structure. If it does drive the ratio down,
the published claim narrows to a statement about sparsification under a fixed
resource total, and that must be reported rather than absorbed.

**Prediction registered 2026-09-10, before the arm was implemented or run.**
Whatever the fourth arm's direction, under the conservation argument:

1. `kernel_norm_growth` lands with the gradient arm's 12.4--14.7 and not with
   the random arm's 1.29--1.31. That is the matching criterion the arm exists
   to meet, and an arm that misses it is the wrong arm.
2. `descent_fraction` stays near zero, as the random arm's -0.017--(-0.010)
   does. Only the gradient direction lowers the objective.
3. `tail_alignment_ratio` stays at 1 within fluctuation, and does **not** fall
   to the gradient arm's 0.35--0.61. A direction drawn independently of the
   labels is uncorrelated with the cluster indicator, so sparsifying along it
   removes within- and between-cluster mass in proportion.
4. `permutation_percentile` sits at or below the frozen arm's 0.64--0.91 band
   rather than at the gradient arm's 0.95--1.00.

The discriminating prediction is 1 together with 3: same deformation, no loss of
alignment. If 3 fails — if a label-blind direction of the same cumulative
deformation also drives the ratio below 1 — then the published claim narrows to
sparsification under a fixed resource total, and the manuscript says so.

**Scope:** this does not bear on the conservation-law argument
($\sum_i v_i$ is conserved under symmetric coupling, so minimising $\sum_i v_i^2$
equalises drift, which rewards between-cluster coupling), which is analytic and
independent of every control. The manuscript's strongest form of the negative
result rests on that argument and on the within-over-between ratio, not on the
random arm.

### D2 — Scope the generality of the plasticity negative result

- [x] The abstract's "away from the structure it is asked to learn" and
      §4.3's "Descending a squared-drift functional does not produce
      representational learning" generalise from one pairing in which the
      template is literally the frequency-cluster indicator and the objective
      provably anti-aligns with it. `supplementary.tex:388` states the limit
      ("a property of this pairing of objective and template"); the abstract does
      not.

**Completion:** either the abstract carries the pairing qualification, or a
second template not aligned with the frequency clusters is run and the result
reported. The second is the stronger paper and is a real experiment: a template
built from a latent structure orthogonal to the frequency clustering would show
whether the descent is merely indifferent to environmental structure or actively
opposed to it, and those are different claims. The manuscript currently makes the
second while the evidence supports the first for one adversarial pairing.

---

## E — Repository infrastructure

Added 2026-09-10 from a structural review of the repository layout. None of
these changes a number, a proof or a claim; they are recorded here so that the
reasoning does not have to be redone. The review's conclusion on the two
refactors that prompted it was **not to do them**: the Lean development's flat,
phase-ordered `PhysicsOfConsciousness/` is the Mathlib convention and its DAG is
already enforced by `check_leaves.py` and by `PhysicsOfConsciousness/AGENTS.md`
section 7, and moving `simulations/` itself would touch twelve `pre-commit`
hooks, `\graphicspath`, seven `\input` paths, ten path sites in
`prepare_arxiv.sh`, three gate scripts and the `BUILD_MANIFEST` digests, in
exchange for a shorter `ls`. What the review did find is below.

### E1 — Continuous integration, off this machine

**Done 2026-09-10, two stages of the three.** `.github/workflows/ci.yml` runs
two independent jobs on every push to `master`, on every pull request and on
demand. The Python job syncs `simulations/` with `uv`, runs `uv run pytest`, and
then runs `pre-commit run --all-files` — the whole twelve-hook gate set, which
is the thing nothing outside this machine verified. The Lean job installs elan
with the toolchain left to `lean-toolchain`, fetches Mathlib's prebuilt cache
and runs `lake build` on an x86 runner. Checkouts are pinned shallow.

**The `pdflatex` stage is not there, and that is the decision the item left
open.** The tracked PDFs are rebuilt and committed with their sources
(`AGENTS.md` §6), so a `.tex` file that does not compile cannot reach `master`
in the first place; and the document arXiv builds is neither `.tex` file but the
merged one `prepare_arxiv.sh` assembles and compiles from its own tarball, which
`check-arxiv-freshness` already forces to be current before an upload. A TeX
Live install on every push would exercise neither. The reasoning is recorded in
the workflow's own header comment, where the next person to want the job will
look.

**What is verified and what is not.** `pre-commit run --all-files` was run
against the whole tree here and exits 0, and the venv-relative invocation the
workflow uses is the one that was run. The pinned Mathlib revision was checked
to be an ancestor of `mathlib4` master, so the prebuilt cache the Lean job
fetches exists for it. The runner setup itself — `astral-sh/setup-uv`, the elan
install, `lake exe cache get` — could not be exercised from here, and
`lake exe cache get` must not be run on this machine: the local `.lake` was
built from source for aarch64, and Mathlib's cache is per platform.

**The first run passed, both jobs, on the first push.** The Python job takes 1m
37s; `lake build` takes 35m 36s, of which nearly all is the Mathlib cache
fetch — well inside the 90-minute timeout, but it is the reason the two jobs are
independent rather than staged, since a Python failure should not wait on it.

There is no `.github/`. All twelve gates run only under `pre-commit`, on one
machine, and `git commit -n` skips every one of them. Nothing verifies
`lake build`, `uv run pytest` or `pre-commit run --all-files` anywhere else, so
"reproducible" presently means "reproducible on this Pi" — which is the one
claim the repository cannot check.

Stage it: the Python gates and the test suite first, since they need only `uv`
and a checkout; `lake build` second, with `lake exe cache get` on an x86 runner,
where the Mathlib cache exists; a `pdflatex` compile last and only if the PDF
gates are worth the TeX Live install. Note that the checkout is not small — 248
tracked `.npz` — so pin a shallow clone.

This is the item that Docker was the wrong answer to; see *Recorded, not
scheduled*.

### E2 — Split `Examples.lean`

**Done 2026-09-10.** Ten files under `PhysicsOfConsciousness/Examples/`, one per
phase plus two shared substrates, and `Examples.lean` keeps the coverage
docstring and becomes their index — including the map from each section number
to the file that now holds it, because the section numbers are what the
supplement cites and they are unchanged. `lake build` is green: every witness
still elaborates. No code line was lost, which is checkable — the split is a
slice of contiguous line ranges, and the only lines the new tree adds are
headers, imports and `end` markers.

**The substrates are the part the plan did not predict.** Three files' witnesses
stand on the three-site cortex of §4 and two on the one-bit eraser of §1, so
those two sections are files of their own (`Examples/Cortex.lean`,
`Examples/Bit.lean`) and the witnesses that need them import them. §19's
dependence on §1 is invisible to any reading of the text: it needs the
`Thermodynamics Bool` *instance* and names no declaration from it. It surfaced
as a `failed to synthesize` on the first build, which is the only way it could
have surfaced. `section TrioDynamics` also spanned §17 and §17.1, which sit in
different files now; it holds nothing but a redundant `open`, so §17 closes it
and §17.1's own `section TrioCover` carries the rest.

**`check_leaves.py` now recognises the witnesses by path**, not by the name
`Examples.lean`: `Examples.lean` plus everything under `Examples/` is neither
checked for consumers nor counted as one. A name-based exemption would have
silently stopped covering the witnesses the moment they moved into a directory —
and worse than silently, since counting a witness file as a consumer makes every
phase module look non-leaf and defeats the gate.

**The publication cites the witnesses, not a file.** The supplement already
spelled the citation both ways — `\texttt{Examples.lean}~\S11` in the prose and
`\texttt{Examples}~\S18` in Table S1 — and every site is now the second form.
That is the form that stays true through a layout change, which is the point:
a reader is pointed at §11, and the index says which file §11 is in. Same in
`docs/primer.tex`. Both PDFs were rebuilt and `arxiv_submit/` repacked in the
same commit.

4,976 lines, thirty per cent of the 16,777-line development, and it is the sink
that imports every phase, so the witness for a given phase is findable only by
search. Per-phase files under `Examples/` would fix that.

It is a Lean-semantics change and not a file move: instance visibility and
`open` scopes decide whether each witness still elaborates, `check_leaves.py`
special-cases the name `Examples.lean` and would need to learn the new shape,
and verifying the result needs a full `lake build` against an 8.4 GB `.lake`.
Do it as its own change or not at all — it must not be folded into a tidy-up,
because a witness that stops elaborating is a soundness-relevant regression
(`PhysicsOfConsciousness/AGENTS.md` section 2) and a tidy-up is not read as
though it could cause one.

### E3 — Hoist the in-run report calls out of `geometric_frustration`

**Done 2026-09-10, and not in the shape sketched below.** Passing the summary
and the in-memory legs out to `main()` would have left the import where it is:
`main()` lives in the sweep module, so a report call there is still a simulation
reaching a report, and the `tach.toml` exception would have had to stay. The
sweep now writes `summary.json`, the legs and — on a failed gate — the noise
control, and returns the summary; `geometric_frustration_report.py` carries its
own `--output` entry point, reads those files, dispatches on the run's own
status and integrates nothing. It is the pattern `dynamic_ramp` and
`structural_resonance` already use, at the cost of a second command.

What this buys beyond the layer label: the figures and the readout of a finished
run were previously reachable only by rerunning the sweep, because the legs the
plots need existed only in memory. All six tracked run directories now
regenerate their `FRUSTRATION_REPORT.md` byte-for-byte from their saved files,
and `test_geometric_frustration_report.py` asserts it.

`geometric_frustration.py` imports `geometric_frustration_report` inside two
function bodies (lines 224 and 253) and calls it, so the sweep writes its own
report as it finishes. That is the one layer inversion in the package, and it is
recorded rather than hidden: `tach.toml` places `geometric_frustration_report`
in the `simulation` layer instead of `report`, with a comment saying why. Every
other report module reads artifacts a finished run left behind.

The clean form returns the summary and legs to `main()` and lets `main()` call
the report writer; the module then moves to the `report` layer and the exception
in `tach.toml` goes. It changes signatures that `test_geometric_frustration.py`
calls directly, so it is a real refactor with test updates, not a config edit.
Deferred because the sweep behind it is expensive to re-run for reassurance.

### E4 — `paper_assessment.md` is at the repository root

**Done 2026-09-10.** Moved to `tasks/paper_assessment.md` with `git mv`; no
reference anywhere in the tree needed updating, because there was none.

Nothing links it — no `.md`, `.tex`, `.html`, `.py` or `.sh` file in the tree
mentions it. The root is otherwise manuscript sources, Lean scaffolding and the
three tracked deliverables that `README.md` and `index.html` link. `tasks/` is
its place. Trivial, and deferred only because it is cosmetic and moving a file
someone opens by habit is not worth doing as a side effect of something else.

## R — Carried forward unchanged

R1–R6 are reproduced from the archived ledger without change of content; consult
`_archive/todo_2026-09-09_pre-simulation-audit-replan.md` for the full completion
criteria, the R1 documented-limitation disposition and the R6 specification
record. They are last in this file because they are unbounded research, not
because they rank below the A–D items.

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

## P — Submission readiness, still open

- [ ] Confirm author affiliation, funding, competing-interest and contribution
      metadata, and review the AI-use disclosure against the full project
      history. *Blocked on the author.*
- [ ] Add or confirm the journal-required data-availability statement and the
      supplemental-material description. *Blocked on a journal choice.*
- [ ] Final read of every cited reference and every generated numerical macro
      after the last prose edit. **On hold at the user's request, 2026-09-14.**
      **A1, A2 and F1–F4 were prerequisites and are
      closed**, so this item is now the open one; it is no longer a formality: the audit found one wrong numeral and two
      unresolvable citations by doing exactly this read. Do not submit while any
      source/PDF, estimator or public-description inconsistency remains.

## Recorded, not scheduled

Carried from the archived ledger; unchanged by the audit.

- A dynamical mean-field limit / propagation-of-chaos theorem remains a research
  programme; S4 cannot close it.
- Enlarging the local state space so that phase, or an independent transition
  datum, is part of it would give `Phase5_TwistedGluing` a non-vacuous consumer.
  That is a physical modelling choice, not a way to close a leaf gate.
- Overlap compatibility remains an explicit physical hypothesis. Do not schedule
  another attempt to derive it from the current class fields. A6 corrects where
  the manuscript says the assumption lives; it does not reopen the derivation.
- The formalization paper and audit paper remain viable separate publications.
- PRX Life presubmission was explicitly declined.
- The three recorded leaf modules are terminal and are not re-litigated per pass.
  The agency extension consumes `Phase3_KLBound.KL_nonneg` in its path-law
  entropy proof and finite-measure bridge (2026-09-13).
- The `.venv` console scripts embed an absolute interpreter path; after moving or
  renaming the checkout run `uv sync --reinstall` in `simulations/` before
  trusting a green pre-commit run.
- **Docker was assessed on 2026-09-10 and declined for development.** The Python
  half is already reproducible from `uv.lock` and `.python-version`; the barrier
  a container would address is the Lean half, and there it is a bad trade on this
  machine — an image means either a second multi-gigabyte `.lake` or a bind mount
  that defeats the isolation, and Mathlib's prebuilt cache is per toolchain and
  per platform, so an aarch64 image risks a full Mathlib build. Development stays
  native under `uv`. If a container is ever wanted it is a reproduction artifact
  built by E1, not a development environment.

## Verified correct by the 2026-09-09 audit

Recorded so the next pass knows what was covered and does not re-audit it.

- **Analysis.** $r^2/(K-K_c) \to 1/D$; the $E''(0) = -1/8$ Taylor step and the
  $E(a) - (\tfrac12 - a^2/16) = o(a^2)$ expansion; $R(a) = aE(a)$ from the
  integration-by-parts identity; $K_c = 2D$ and the $E(a) < 1/2$ argument behind
  it; the Łojasiewicz estimate $2a^2W \le (\sum_{ij}A_{ij})\sum_i \dot\theta_i^2$
  and the forward invariance of the quarter-turn region; the data-processing
  direction in Eq. (5).
- **Implementations.** The exact mean-field drift $Kr\sin(\psi - \theta_i)$ in
  `dynamic_ramp`, `dynamical_selection` and `propagation_of_chaos`; the
  sine-difference factorisation in `geometric_frustration`; the FFT toroidal
  convolution and plaquette winding in `spatial_kernel`; the symmetric-edge
  derivative $(v_i - v_j)\sin(\theta_j - \theta_i)$; the shared phase-noise
  stream across the three plasticity arms; the non-ML log-density concentration
  estimator and the argument for it.
- **Numerals.** The conserved-drift floor $N\langle\omega\rangle^2/D = 990.025$
  (cluster sizes 34/33/33 give $\langle\omega\rangle = 0.995$); the delay
  exponent fit 0.443 from the three uncensored legs; the Fermi conversion, which
  reproduces 0.5668 / 0.0709 / 0.0210 mV/mm at $f = 40$ Hz; the static
  $r(2.8) = 0.68270$; the gradient arm's descent fractions against the frozen
  arm's headroom; the plasticity, ramp, spatial and frustration macros against
  their summary files.
- **A confirmation worth promoting to print.** The supercritical pair
  correlation is not merely "substantial": for a uniformly distributed collective
  phase it should equal $r^2 = 0.7208^2 = 0.5196$, and the measured range is
  0.459–0.525. The observation confirms the unpinned-orientation diagnosis
  quantitatively, and saying so is stronger than the present qualitative
  statement. Similarly, the propagation-of-chaos density $L^1$ error of 0.1291 is
  consistent with pure binning noise at $n = 1000$ and 40 bins, which is what
  makes it uninformative rather than bad.
- **Gates.** 100/100 tests, `check_prose`, `check_tableS1`, `check_figures`,
  macro-drift test. `Axioms.lean` declares no live axioms — all three `axiom`
  blocks are commented out — so the manuscript's no-additional-axioms claim
  stands. The Lean build artifacts are current with respect to the sources.

## Pass records

Append one dated record per completed item: red test, implementation, reduced
run, full run, numerical findings, artifacts, manuscript changes, scope limits
and gates. Keep raw drafting history here or in the next archive, never in
`main.tex` or `supplementary.tex`.

### 2026-09-09 — simulation audit (this replan)

Re-derived every published simulation numeral from `figures/*/summary.json` and
the saved `.npz` checkpoints; ran two controls not in the repository (the
step-size series in C1 and the stationary-branch estimator reference in B1) using
the repository's own `bifurcation.coherent_r` and `fit_onset_exponent`. No
repository file was changed by the audit itself. Findings are A1–A7, B1–B6,
C1–C4 and D1–D2 above; coverage is in "Verified correct" above. The audit's
one-line summary: the numbers are right and three of them are assigned to the
wrong cause, three are compared against the wrong reference, one control does not
control for what it is cited for, and one hand-entered numeral is wrong.

### 2026-09-10 — B-items (B1--B6)

Six derived quantities read out of saved artifacts; no sweep rerun.

- **B1.** `adiabatic_onset_exponent` in `dynamic_ramp_report.py` runs
  `fit_onset_exponent` on `bifurcation.coherent_r` sampled on each leg's own
  coupling grid. It returns 0.443 on the three faster grids and 0.448 on the
  slowest, reproducing the audit. Emitted as `\rampOnsetReference*`; the
  supplement reads the measured exponents against it and not against 1/2.
- **B2.** `OnsetFit` carries the window it realised — order range, coupling
  excess, sample count, and whether the shift returned at its lower bound.
  Emitted per leg. The shift is pinned on all four legs, so it is reported as a
  count over legs (`\rampOnsetPinnedCount` of `\rampLegCount`) rather than as a
  property of the fastest fit, which is what the first pass at this item said.
- **B3.** `SizeMetrics.scaled_delay` and `precritical_order_max`. The ratios do
  not collapse; at N = 500 replicas reach 0.436 before threshold against 0.106
  at N = 8000. The supplement claims monotonicity only and names the protocol
  hazard.
- **B4.** Decay lengths in lattice spacings beside millimetres, plus the plateau
  the empirical band sits in. The criterion is crossed between 0.90 and 0.94
  spacings — entirely below one cell — and steady order spans 0.00038 from the
  band's lower limit out to four times the sheet extent. The sevenfold margin is
  gone from `supplementary.tex` and from `docs/primer.tex`.
- **B5.** The bracket is converted with the run's own N and D rather than a
  literal, and the grid ratio is read from the epsilon grid rather than from the
  bracket, which agree only while the bracket is one grid step wide. The
  interpolant's precision is cut to two decimals. Both documents state that the
  bracket contains K_c/D = 2, so the run does not separate the crossing from the
  threshold; the fluctuation-amplification result is joined to it in the same
  sentence rather than left in an adjacent paragraph.
- **B6.** The random arm's `kernel_norm_growth` is emitted and reported beside
  the gradient arm's. The main text states what the control does not rule out,
  and discloses that the learning-rate sweep ran on one of the three reported
  seeds.

**Scope.** B5 reports the crossing as a bracket; C4 is what would resolve it.
B4 establishes that the boundary is unresolved; C3 is what would decide whether
it is a lattice artifact. B6 scopes the control; D1 is what would close it.

**Gates.** 111/111 tests, `ruff`, `ruff format`, `mypy`, `bandit`, `vulture`,
`xenon`, `tach`, `check_prose`, `check_tableS1`, `check_figures`,
`check_pdf_freshness`, `check_arxiv_freshness`, `check_leaves`, and the
macro-drift test in `test_simulation_tex.py`.

### 2026-09-10 — C-items (C1, C2)

**C1.** `dt_control_configs` refines the production step at fixed physical
duration and fixed tail sampling, so the only thing that changes across the
series is the step. The production step opens the series and is not re-run: the
regime sweep has already integrated it at that coupling. Red test first
(`test_dt_control_refines_the_base_step_at_fixed_duration`, which fails against
a control whose step list and step count are literals rather than derived from
`base.dt`). Full sweep rerun; the regime and growth legs reproduce bit-for-bit
because every config seeds its own generator.

The series at K = 2.8, D = 1, N = 1000, 500 replicas, tail-quarter mean:

| dt | 0.01 | 0.005 | 0.0025 | static |
|---|---|---|---|---|
| steady $r$ | 0.677352 | 0.680206 | 0.681681 | 0.682705 |
| residual | -0.00535 | -0.00250 | -0.00102 | --- |

The residual is monotone in dt and 81% of it is gone by dt = 0.0025, so the
bulk of the published gap is Euler--Maruyama bias, as the audit found. What the
series does **not** do is measure the finite-size part: the last refinement moves
the steady order by 0.00147, which is larger than the 0.00102 it leaves, so the
series has not converged and the remainder is consistent with zero. Both
documents report -0.00102 as a bound on the finite-$N$ part and say that it is a
bound. This is the one place where the first pass at C1 overstated: a two-point
series was read as a decomposition.

The audit's independent 64-replica series reached 0.68103 at dt = 0.0025; at 500
replicas the same step gives 0.68168. The two agree on the attribution and not on
the fourth decimal, which is what 64 against 500 replicas predicts.

**Artifacts.** `selection_dt_control_dt0.005.npz`,
`selection_dt_control_dt0.0025.npz`, and `dt_control_dt` / `dt_control_order` /
`dt_control_coupling` in the summary. `selection_dt_control_dt0.01.npz` is
deleted: the production step opens the series, and the supercritical regime leg
already is that run, bit-for-bit.

**C2.** `estimate_growth_rate` takes bounds instead of a transient and a cap:
the window opens at twice the finite-size floor and closes at half the static
branch order, so it follows the trace rather than a fixed interval. The value
mask is restricted to its first contiguous block, which is what the discarded
transient argument was protecting against — a saturated trace that fluctuates
back into the band would otherwise contribute samples from the wrong regime.
The upper bound moves with the coupling, so the supplement reports the range it
takes across the sweep rather than one leg's window.

The window at N = 1000 opens at $2/\sqrt{N} = 0.06325$ and closes at half the
static branch order, which runs from 0.20669 at K = 2.2 to 0.37050 at K = 3.1 --
one bound per leg, not one window for the sweep, and the supplement reports the
range rather than the first leg's value. The refit gives
$\lambda = 0.41505\,K - 0.78619$ against the infinite-$N$ linearization
$0.5K - 1$: the slope moves away from 1/2, not toward it.

Per C2's completion criterion that makes the shortfall a real residual rather
than a window artifact. It does not make it a pure finite-$N$ statement, because
the sweep integrates at the production step whose bias C1 has just measured, and
both documents say so rather than claiming finite size alone.

The first-contiguous-block restriction is a guard, not a correction: it leaves
the slope unchanged to $10^{-15}$ on this data, because none of the ten traces
re-enters the window after saturating. It is there because the value-only mask
that replaced the transient argument had nothing stopping one that did.

**Gates.** 113/113 tests, `ruff`, `ruff format`, `mypy`, `bandit`, `vulture`,
`xenon`, `tach`, `check_prose`, `check_tableS1`, `check_figures`,
`check_pdf_freshness`, `check_arxiv_freshness`, `check_leaves`, and the
macro-drift test.

**Scope.** Neither item changes a conclusion. C1 removes a finite-size claim the
data do not support and replaces it with a bound; C2 removes the window as an
explanation for the growth-rate shortfall without establishing that finite size
is the whole of what remains, because the sweep runs at the production step.
C3, C4, D1 and D2 stay open.

### 2026-09-10 — C-items (C3, C4)

**C3.** `transition_band` reads the unresolved part of a saved sweep — the
lengths up to the first sustained crossing, plus the two above it that make the
"stays ordered" half of the criterion mean anything — and `refined_decay_lengths`
samples it twice on the finer sheet: once at the same millimetre values, once at
the millimetre values carrying the same lattice-spacing counts. That is the whole
design: a boundary fixed in millimetres falls in the first set and one fixed in
cells falls in the second, so the two hypotheses are two runs rather than two
readings of one run. The two sets are disjoint and span 0.50 to 6.62 spacings
contiguously. Red test first, on the spacing ratio rather than on a literal half.

The refinement is a $256^2$ sheet over the same 2.0 mm, everything else
identical to production, 22 lengths, 1.4 h across four cores.

| | side 128 | side 256 |
|---|---|---|
| boundary (mm) | 0.014026 | 0.014126 |
| boundary (spacings) | 0.90 | 1.81 |

**The boundary does not move with the spacing.** It is 1.01 times its coarse
value in millimetres and twice it in cells, so it is a property of the dynamics
at this coupling, diffusion and frequency spread, not of the discretisation —
and the finer sheet resolves it, where the coarse sheet put it below its own
spacing. Every length in the fixed-cell-count set (0.0039 to 0.0073 mm, 0.50 to
0.94 spacings) is incoherent on the refined sheet, so reproducing the coarse
sheet's cell counts does not reproduce its boundary.

The first assembly of this control put the boundary on one sample above the
criterion: the band as B4 defines it ends at the first sustained crossing, and
the coarse sheet's own coherent side was outside it. A crossing whose "all larger
sampled lengths stay ordered" clause rests on a single length is a clause no
rerun tests, so the band carries two lengths past the crossing and the coherent
side is now 0.269, 0.899, 0.909 and 0.940 across four of them.

This reverses the reading B4 left in place. B4 withdrew the sevenfold margin
because the boundary sat below one spacing; the ground for that was that an
unresolved boundary could be a lattice artifact, and it is not one. Both
documents now say the boundary is physical and resolved on the finer sheet. The
plateau argument B4 introduced is untouched and remains the stronger statement
about the empirical band.

**C4.** `refinement_grid` subdivides the step a crossing was found in, excluding
the two ends the sweep has already integrated, with the step read off the bracket
rather than fixed. `run` continues leg indices past the coarse grid, so all 20
cached coarse legs per seed load unchanged and keep the noise streams they were
saved with; nine legs per seed are new. The summary carries the merged grid and,
separately, the coarse grid the ratio is read from and the coarse bracket that
was refined. `aggregate` refuses to average across seeds that refined different
grids.

Nine interior points give steps of 0.025 in $K_{\mathrm{eff}}/D$, a tenth of the
geometric step $[1.857, 2.110]$:

| seed | 20261905 | 20262905 | 20263905 |
|---|---|---|---|
| refined bracket | [1.983, 2.009] | [1.958, 1.983] | [1.958, 1.983] |
| interpolated crossing | 1.987 | 1.962 | 1.973 |

**The refinement does not separate the crossing from the threshold.** The union
of the three seeds' brackets is $[1.958, 2.009]$ and contains $K_c/D = 2$. All
three interpolated crossings fall below 2 and two of the three brackets do, but
the third contains it and the grid does not resolve the difference at $N=500$.
This is the outcome C4 named as the more interesting one and it is reported as
a result, not as a failure of the run. The conditional field values move with
the sharpened crossing (0.586--0.593 mV/mm at 0.1 mm against 0.567--0.579
before) and stay below the 1--5 mV/mm comparison band.

**Artifacts.** `figures/spatial_kernel_refined/` (22 legs, summary, sweep and
phase-map figures, and its own report); `leg_20` through `leg_28` in each of the
three `weak_seed*` directories; `coarse_epsilon`, `coarse_bracket` and
`refinement_step` in the frustration summaries. `\spatialRefinedSide`,
`\spatialRefinedCriticalDecay`, `\spatialRefinedCriticalDecayCells`,
`\spatialRefinedBoundaryRatio`, `\frustrationCoarseMin`, `\frustrationCoarseMax`
and `\frustrationRefinementStep` are new macros.

**Gates.** 119/119 tests, `ruff`, `ruff format`, `mypy`, `bandit`, `vulture`,
`xenon`, `tach`, `check_prose`, `check_tableS1`, `check_figures`,
`check_pdf_freshness`, `check_arxiv_freshness`, `check_leaves`, and the
macro-drift test.

**Scope.** Neither item changes a conclusion. C3 turns a number the manuscript
was reporting as possibly a discretisation artifact into a physical length, and
C4 sharpens a bracket tenfold without separating it from the mean-field
threshold. Both sheets in C3 run one seed, so seed dependence at the boundary is
still open. D1 and D2 stay open.


### 2026-09-10 — repository structure review

Prompted by a question about whether the folder layout should be tidier and
whether `simulations/` or the Lean development should be refactored. The answer
to both refactors was no, for the reasons recorded at the head of section E. The
review found four things that were worth doing and were done, and four that were
not done and are E1--E4.

**`tach` now enforces something.** It was reporting `✅ All modules validated!`
directly after `[WARN] No first-party imports were found` — a single `<root>`
module with every file inside it has no edges to check. `tach.toml` now declares
each file as its own module across six layers, so the boundaries are enforced
without a directory tree to carry them, and `exact = true` fails a commit on an
import no rule permits *and* on a rule no import uses. The two rules that
motivate the ordering — no gate imports a simulation, nothing imports
`simulation_tex` — were each verified by inserting a violating import and
confirming the failure. On its first real run it found the `geometric_frustration`
inversion that is now E3; that inversion is recorded in `tach.toml`'s layer
comment rather than hidden by widening a rule.

**Output paths are anchored on the module file.** Sixteen sites across six
modules defaulted to a working-directory-relative `figures/...` while three other
modules already anchored on `__file__`. The failure mode is silent: a sweep
started from anywhere else writes a fresh empty tree beside itself and the
report generator that reads the real one afterwards finds nothing. Verified by
importing all six with the working directory set elsewhere.

**Two implicit policies are now written down** in `simulations/README.md`: every
artifact under `figures/` is tracked, so `git status` is the record of whether a
sweep finished; and output paths are addressed from the module file. Its test
count was stale at 80 and is now 119.

**Four stale build artifacts untracked.** `main.bbl` and `supplementary.bbl` were
zero bytes and the two `.blg` files were logs of a BibTeX run that produced
nothing. `references.tex` is an inline `thebibliography` and no script, gate or
source file referenced any of them; `.gitignore` covered `*.aux`, `*.log` and
`*.out` but not these.

**Artifacts.** `simulations/tach.toml` (rewritten); `FIGURES` constants in
`dynamic_ramp.py`, `dynamic_ramp_report.py`, `dynamical_selection.py`,
`propagation_of_chaos.py`, `spatial_kernel.py` and `empirical_collapse.py`;
`simulations/README.md`; `.gitignore`; section E and this record.

**Gates.** 119/119 tests, `ruff`, `ruff format`, `mypy`, `bandit`, `vulture`,
`xenon`, `tach`, `check_prose`, `check_tableS1`, `check_figures`,
`check_pdf_freshness`, `check_leaves`. `check_arxiv_freshness` was failing before
this pass began, on `main.tex` and `references.tex` changes this pass did not
make; `./prepare_arxiv.sh` was rerun and it compiled cleanly from the unpacked
tarball at 44 pages.

**Scope.** No number, figure, proof or claim changes. No production sweep was
rerun and none needed to be.

### 2026-09-10 — D1 (a plasticity control matched on deformation)

**Prediction first.** The four numbered predictions above were written into this
file and committed before any arm was implemented. Result: 1, 3 and 4 hold; 2 is
false in a direction worth reporting.

**Three designs, screened on the matching criterion.** The criterion is
`kernel_norm_growth`, which the gradient arm carries to 12.4--14.7 and the
existing random arm to 1.29--1.31. Screening measured deformation and order
only.

1. *One symmetric Gaussian direction fixed per seed, stepped at the gradient's
   norm.* Reaches 1.66 at the production seed and stops there. A single
   direction can zero only the edges it points at once; after that the clip is
   already saturated and the kernel sits at a fixed point. Rejected.
2. *The isotropic random step rescaled* — the ledger's own second suggestion.
   There is no scale that works: at gains 2, 5 and 20 the arm reaches 1.389,
   1.500 and 1.605. The additive isotropic family has a deformation ceiling near
   1.6 regardless of step size, so matching deformation requires a different
   step family and not a different step size. Rejected.
3. *The gradient step under a node relabelling drawn afresh at each update.*
   Accepted. A relabelling is an isometry of the matrix and a bijection of the
   edges, so the step carries the gradient's Frobenius norm and its entire entry
   multiset onto edges the gradient did not select; nothing is rescaled and no
   gain is tuned. A multiplicative variant (`noise * coupling`, matched norm) was
   also measured and reaches the target deformation, but at 0.20--0.44 order it
   destroys the coherence the comparison needs, and its step scale is a knob.

Screening ran at three seeds, so the alignment numbers of design 3 were visible
before the production run was written. The production module reproduces them.

**Red test first.** `test_permuted_step_relabels_the_gradient_without_rescaling_it`
pins the isometry contract (equal norm, equal sorted entries, symmetric, hollow,
not the gradient); `test_permuted_arm_tracks_the_deformation_the_random_arm_cancels`
pins the point of the arm at 24 nodes; the shared-stream test now covers four
arms. 121/121 tests pass, from 119.

**Run.** Full production sweep, 3 seeds x 4 arms, 2m32s on this Pi. The nine
pre-existing runs came back bit-identical — the new arm draws from the update
stream, which the gradient and frozen arms never touch and which is fresh per
`simulate` call — so `summary.json` gained three records and changed nothing
else, and `sweep.json` is unchanged.

**Findings.** Permuted arm against gradient arm across the three seeds:
deformation 11.418/12.805/16.330 against 12.409/13.836/14.696; second-half order
0.9184--0.9189 against 0.9167--0.9222; descent fraction -0.332/-0.205/-0.161
against 0.677/0.679/0.691; within-over-between 0.729/0.765/1.294 against
0.351/0.416/0.614; permutation percentile 0.268/0.763/0.841 against
0.951/0.975/1.000. So at the gradient arm's own deformation and its own
coherence, a step carrying the gradient's entries to the wrong edges neither
descends the objective nor loses cluster alignment. The two ratio ranges do not
overlap.

**The falsified prediction.** Prediction 2 said the arm's descent fraction would
sit near zero as the random arm's does. It does not: the permuted arm *raises*
the objective by 16--33% of the frozen arm's headroom. The random arm's isotropic
draws cancel, so it stays within 2% of the frozen arm; a permuted gradient step
is structured and consistently mis-targeted, and a step of descent magnitude in a
wrong direction ascends. Reported in both documents rather than absorbed.

**On the ratio's tilt.** Two of the three permuted values sit near 0.75. That is
not a weak version of the gradient arm's effect but a property of the statistic
under concentration: with three clusters, two thirds of node pairs are
between-cluster, so a dominant edge lands between more often than within and
pushes a ratio of block means under one. The supplement says so where it reports
the range.

**Artifacts.** `structural_resonance.py` (fourth mode, `step_direction`
docstring and module docstring); `structural_resonance_report.py` (fourth line
style, a norm-growth column, the two-control paragraph); `simulation_tex.py`
(five permuted macro pairs); `test_structural_resonance.py` (two new tests, one
extended); three new `.npz`; `summary.json`; `REPORT.md`; `joint_dynamics.png`;
`simulation_results.tex`; `main.tex` (abstract, introduction, §4.3, caption);
`supplementary.tex`; `docs/primer.tex`; `CHANGELOG.md`; all three PDFs;
`arxiv_submit/`.

**Scope.** The conservation-law argument is untouched and was never at issue —
it is analytic. D2 stays open: the negative result is still demonstrated on one
pairing of objective and template, and this arm says nothing about a second
template.

**Gates.** 121/121 tests, `ruff`, `ruff format`, `mypy`, `bandit`, `vulture`,
`xenon`, `tach`, `check_prose`, `check_hedging`, `check_tableS1`,
`check_figures`, `check_pdf_freshness`, `check_arxiv_freshness`, `check_leaves`.
The merged arXiv document compiles from the unpacked tarball at 44 pages.

### 2026-09-10 — D2 (the generality of the plasticity negative result)

**Both branches, not either.** The item offered a choice: qualify the abstract,
or run a second template. The second was run and the first done anyway, because
the run answers a different question than the qualification does. The run settles
whether the descent is indifferent to structure or opposed to the environment's
own; the qualification is about other objectives and other environments, which no
run in this repository reaches.

**The second template, and why it is not enough alone.** `interleaved_labels`
partitions the nodes as `i % 3` against the frequency clusters' contiguous
`i * 3 // n`, so each interleaved group draws equally from all three clusters and
the partition carries no frequency information; a kernel with only frequency
structure scores 0.9375 under it at N = 99, an O(1/N) leak that the test pins.
The gradient arm's interleaved ratio came back 0.807, 1.640, 3.022 across the
three seeds — wildly scattered, and on its own it supports nothing. A probe over
200 frequency-blind partitions on the same three kernels explained why: the ratio
of block means has a 5--95% spread of roughly [0.42, 2.1] once the kernel is
concentrated onto few edges. One alternative template is one draw from that.

**The calibrated reading.** `partition_percentile` scores the frequency
partition's ratio against `permutations` relabellings of itself, each keeping the
group sizes and losing the correspondence with frequency. Gradient arm: 0.0000,
0.0245, 0.0495 — the frequency partition is in the bottom twentieth on every
seed. Frozen: 0.0755, 0.3480, 0.2425. Random: 0.4305, 0.6645, 0.7270. Permuted:
0.1475, 0.7250, 0.2360. Under exchangeability the six control values are
consistent with uniform; three gradient values all below 0.05 are not.

**Red test first.** `test_interleaved_labels_carry_no_frequency_information`
pins the balance, the group sizes, the exact neutrality of a uniform kernel and
the O(1/N) leak; `test_partition_percentile_brackets_the_frequency_partition`
pins the null at both ends; `test_metrics_score_both_templates_on_the_same_kernel`
pins that the second partition is a readout and never an input. 124/124 tests
pass, from 121.

**Run.** Two full production sweeps, 2m37s and 2m39s. The first added the
interleaved diagnostic, the second replaced the crossed-template permutation
percentile with the blind-partition null. All twelve runs reproduced
bit-identically both times: neither readout consumes randomness from the
dynamics streams, and the null draws from `seed + 5`.

**Manuscript.** The abstract carries the pairing qualification and the
blind-partition result; the introduction adds the blind reading to the list of
references the loss is measured against; §4.3 and the supplement report both
partitions, with the supplement stating plainly that a single alternative
template is uninformative here and why. The supplement also says what is not
claimed: which structure a different objective would move against is not settled
by one pairing.

**Artifacts.** `structural_resonance.py` (`cluster_labels`, `interleaved_labels`,
`gram`, `partition_percentile`, a crossed diagnostic series, two metrics);
`structural_resonance_report.py` (two columns and the reading);
`simulation_tex.py` (three macro pairs); `test_structural_resonance.py` (three
new tests); twelve `.npz`; `summary.json`; `REPORT.md`; `simulation_results.tex`;
`main.tex`; `supplementary.tex`; `docs/primer.tex`; `CHANGELOG.md`; all three
PDFs; `arxiv_submit/`.

**Scope.** The negative result still rests on one objective and one environment.
What the run removes is the weaker reading of it — that the descent degrades any
structure scored against it — not the limits of the pairing.

**Gates.** 124/124 tests and every hook. The merged arXiv document compiles from
the unpacked tarball at 45 pages.

### 2026-09-10 — E-items (E1--E4)

Repository infrastructure, in four commits. No number, figure, proof or claim
changes, and no production sweep was rerun.

**E4** moved `paper_assessment.md` to `tasks/`. Nothing in the tree referenced
it, so nothing else had to change.

**E3** hoisted the frustration report out of the sweep, and not in the shape the
item sketched: returning the legs to `main()` would have kept the import, since
`main()` is in the sweep module. `geometric_frustration.py` now writes
`summary.json`, the legs and the noise control and returns the summary;
`geometric_frustration_report.py` has its own `--output` entry point, dispatches
on the run's own status and integrates nothing. The gain is not the layer label:
a finished run's figures and readout were previously reachable only by rerunning
the sweep, because the legs the plots need lived in memory. All six tracked run
directories now rebuild their `FRUSTRATION_REPORT.md` byte-for-byte from saved
files, and a new test asserts it for each.

**E1** added `.github/workflows/ci.yml`: a Python job (`uv sync`, `pytest`,
`pre-commit run --all-files`) and a Lean job (elan, Mathlib cache, `lake build`)
on an x86 runner. The `pdflatex` stage the item left conditional was declined,
with the reason in the workflow header. What could be verified here was: the
whole hook set exits 0 on this tree by the same invocation the workflow uses,
and the pinned Mathlib revision is an ancestor of `mathlib4` master, so the cache
the Lean job fetches exists. The runner setup is first exercised by the first
push.

**E2** split `Examples.lean` into ten files under `Examples/` and taught
`check_leaves.py` to recognise witnesses by path. Two shared substrates came out
of it, and one dependency that only a build could find. The publication's
citations of the witnesses were normalised onto the form Table S1 already used.

**Artifacts.** `.github/workflows/ci.yml`; `simulations/geometric_frustration.py`,
`geometric_frustration_report.py`, `frustration_diagnostics.py`, `tach.toml`,
`test_geometric_frustration.py`, `test_geometric_frustration_report.py`;
`simulations/check_leaves.py`; ten new `PhysicsOfConsciousness/Examples/*.lean`;
`PhysicsOfConsciousness/Examples.lean`; `PhysicsOfConsciousness/AGENTS.md`;
`README.md`; `simulations/README.md`; `supplementary.tex`; `docs/primer.tex`;
`supplementary.pdf`; `docs/primer.pdf`; `arxiv_submit/`;
`tasks/paper_assessment.md`.

**Gates.** 125/125 tests and every hook, `lake build` green, and the merged arXiv
document compiles from the unpacked tarball at 45 pages. Both CI jobs then passed
off this machine on the first push, which is the E1 claim actually being checked
rather than asserted.

**One thing the push found that was not an E-item.** `git push` was rejected:
the `GITHUB_TOKEN` this machine authenticates with is a classic PAT scoped
`repo` only, and GitHub refuses any push that touches `.github/workflows/`
without `workflow` scope. `gh auth refresh` cannot fix a token supplied through
an environment variable. The remote is now `git@github.com:` over SSH with a new
ed25519 key on this machine, which is not subject to that check at all and needs
no scope decision the next time a workflow file changes.

### 2026-09-11 — F-items (F2, F3, F4)

The audit's three remaining wording corrections, batched into one commit as the
ledger's ordering asks. All of F1--F6 is now closed; nothing was rerun and no
production numeral changed.

**F2.** `step_direction` is called with the calling arm's own phases and
couplings, so the random arm is scaled to its own gradient and the permuted arm
relabels its own gradient; neither is handed the gradient arm's step. A replay
of the three production seeds recording direction norms confirms the audit's
figures: mean direction norm about 43 on the gradient arm against about 35 on
the random arm, a ratio of 0.81 on every seed. The manuscript, supplement,
primer, `structural_resonance.py` docstrings and the run report now say that the
controls follow the gradient arm's rule rather than being equated to it, and
rest the comparison on the overlap of the permuted and gradient arms' reported
norm-growth and order ranges. Those ranges were already published; no macro
changed.

**F3.** The supplement's exclusion of fit-window bias is gone from both
publication files. The window's upper bound is half the stationary branch order
rather than the extent of the linear regime, so it can contribute to the
shortfall; the step refinement is a control on stationary order and apportions
no bias in this growth estimator. Both files now name the window, finite size
and the integrator together and say the sweep separates none of them. The
primer does not carry the claim.

**F4.** The supplement and primer no longer call the boundary a property of the
dynamics rather than the discretisation, nor say the finer sheet resolves it.
What replaces it is the observed stability of the operational crossing under
this one refinement, with the reason that is not convergence stated beside it:
three new macros, generated from the two saved sweep summaries through
`simulation_tex.py`, report the shortest length from which both sheets stay
coherent and each sheet's steady order there — 0.01467 mm, 0.6176 against
0.2687. `_shared_coherent_length` and its two unit tests were written before
the generator emitted them.

**Also done.** F1 asked for the readout correction in the run report as well as
the publication, and that one site had been missed; `REPORT.md` now names the
post-update readout, regenerated from the saved summaries.

**Artifacts.** `main.tex`, `supplementary.tex`, `docs/primer.tex` and the three
rebuilt PDFs; `simulations/simulation_tex.py`, `simulation_results.tex`,
`test_simulation_tex.py`; `structural_resonance.py`,
`structural_resonance_report.py` and `figures/structural_resonance/REPORT.md`;
`CHANGELOG.md`; `arxiv_submit/`.

**Gates.** 140/140 tests, every hook green, and the merged arXiv document
compiles from the unpacked tarball at 48 pages.

### 2026-09-10 — F-items (F1, F5, F6)

The two bounded studies of `tasks/f5_f6_design.md`, and the sampling correction
they generalise. F2, F3 and F4 remain open: they are wording corrections to
other subsections and nothing here touches them.

**F5** ran the declared grid — rates 0.01, 0.05, 0.2 crossed with physical
update intervals 0.05 and 0.5, on the substrate of the production plasticity
run, each case against a frozen arm on its own initial state and phase-noise
stream. The estimator records objective and order at every integration step, on
the state driving that step, and averages within complete update intervals with
the zero-duration terminal endpoint excluded; a regression test pins it against
sampling only after updates, since that difference is the whole point of the
measurement. None of the six cases met the declared 5% sustained reduction, so
the design selected no candidate and the held-out confirmation did not run. The
best worst-quarter ratio, at rate 0.05 and interval 0.05, reaches 1.22% and
1.36%. Coherence and loss of alignment appear across the grid; the sustained
reduction does not appear anywhere in it. Seven trajectories, 94 s.

**F6** stopped at the analytic stage, as the design allowed. In the
identical-frequency rotating frame the stationary density is von Mises with
concentration `K*r/D`, so a coupling increase `K=q(s)`, a diffusion decrease
`D=b/q(s)` and an uncoupled ensemble under a prescribed drive of amplitude
`q(s)*r(q(s))` share every stationary density window for window. The ideal
feasibility check confirms the coincidence is exact rather than close: over 18
cases the three families return the same endpoint to within 8.9e-16 at squared
errors of at most 5.2e-14, and no case identifies a unique generator. The 80%
unique-recovery gate fails for every family, so no noise, filtering or pooling
stage was added. The missing observable is the physical clock: increments carry
`2D` in their quadratic variation, and separating an endogenous coupling from a
common drive needs a measured drive or a controlled perturbation on top of that.

**F1** is closed as the publication half of F5. The production run samples
diagnostics at the update cadence, immediately after each update, so its
reported objective means are that post-update readout; the manuscript, the
supplement and the primer now name it wherever they report it, and the
inference that these runs sustain a minimisation is gone. The saved production
numerals are retained, none was recomputed and nothing was rerun. F5's grid
contains the production rate and cadence, and that cell carries the contrast the
publication now prints: a post-update second-half mean of 1118.95 against a
complete-interval 1383.87, beside a frozen 1383.06.

**Where the studies enter the publication.** A supplement subsection for each —
"Sustained reduction over complete update intervals" with the full six-case
table, and "What successive stationary phase distributions cannot separate"
under the alternative-models section. In the article: the abstract, the third
contribution, the plasticity subsection and the figure caption carry the
readout correction and the F5 outcome, and protocol items 1 and 6 carry F6. The
resonance figure dropped from 0.62 to 0.60 `\textheight` so the longer caption
does not enlarge a float overflow the page already had.

**Artifacts.** `simulations/plasticity_study.py`, `recovery_mechanisms.py`,
`followup_report.py` and their tests; `structural_resonance.py` and
`test_structural_resonance.py` for the interval estimator; `simulation_tex.py`,
`simulation_results.tex`, `test_simulation_tex.py`; `tach.toml`;
`simulations/figures/plasticity_study/`, `simulations/figures/recovery_mechanisms/`;
`tasks/f5_f6_design.md`; `main.tex`, `supplementary.tex`, `docs/primer.tex` and
the three rebuilt PDFs; `arxiv_submit/`.

**Gates.** 138/138 tests, every hook green, and the merged arXiv document
compiles from the unpacked tarball at 46 pages.

## 2026-09-13 — Agency and finite feedback thermodynamics

- [x] Specify policy, world, observation and memory-update channels and verify
      their composition on deterministic and noisy finite agents.
- [x] Prove the signed conditional-information identity, conditional terms'
      nonnegativity, finite-law support theorem and exact passive recovery.
- [x] Derive a feedback entropy balance from normalized forward/reverse laws,
      with local detailed balance and the first law stated independently.
- [x] Check reciprocal two-bit actuation and sensing against the same path
      laws, with nonzero correlations, heat and entropy production, explicit
      energy consumption and zero external work during relaxation.
- [x] Add the active heat-budget interface, update the publication and rebuild
      the tracked PDFs and assembled arXiv submission; pass the Lean audit and
      publication/tooling gates.

Specification and validation are in `tasks/agency.md`. The proof modules are
`Phase3_Agency`, `Phase3_FiniteInformation` and `Phase3_AgencyThermodynamics`,
with two witness files under `Examples/`. The no-axiom audit covers all of them.

The passive composition carries a predictive structure at `n4`. The extension
supplies the feedback-compatible joint-entropy budget used by the active branch
recorded below.
Open physical identifications: a sufficient cortical/environment state, policy
and action readout, learning dynamics, biological objective and reservoir
calibration. These are not inferred from coherence or from the second law.

## 2026-09-13 — Active branch of the conditional composition

- [x] Add `ActiveBound`, retaining the named process's initial/final law, heat
      observable, thermal scale and upper budget.
- [x] Add `E34Active` and `E45Active`: physical transition/budget premises and
      the distinct modelling implication to the specified coupling-energy limit.
- [x] Factor `chain_from_coarseGrains`; preserve `chain` and compose
      `chain_active` through the same cover and fixed state, with eight edges
      in each branch. Remove unused predictive carrier parameters from `E56`.
- [x] Supply the nontrivial thermal-actuator joint witness and regressions
      rejecting zero heat budget and an incompatible energy limit.
- [x] Rebuild publication artifacts and complete the full audit/freshness gates:
      2,320 declarations in 42 modules, only the three permitted axioms;
      two-pass article/supplement/primer PDFs and a fresh 47-page arXiv archive.

Specification and validation: `tasks/agency_chain.md`. The active substep holds
the controller fixed and requires strictly positive finite path data and local
detailed balance. Its controller uses the register's state type, and its heat
fits the register's named budget. This allocation is assumed, not inferred
from Landauer's lower bound, and erasure is not identified with actuation.
The witness supplies mesh convergence independently. Open: the physical
relation among register, actuator and coupling dynamics, a complete protocol's
costs and the biological identifications already listed above.

## 2026-09-13 — Primer alignment and the next Lean modelling decision

- [x] Explain agency and both chain branches in the primer, including the
      signed information identity, path-law heat balance, reciprocal example,
      physical assumptions and scope. Rebuild and verify its tracked PDF.

The primer is rebuilt at 73 pages with resolved cross-references, no LaTeX
warnings and no overfull boxes. The changed pages were visually inspected;
the working-tree PDF/dependency check and arXiv freshness gate pass. The source
explanations agree with the existing Lean declarations; this documentation
follow-up introduces no Lean or simulation change.

**Stopping point.** The passive/active interfaces and their joint witnesses are
complete. There is no need to add another general chain interface or to close
every bridge before the manuscript can be reviewed. Further Lean work is useful
when it derives a property from specified dynamics, supplies a missing process
identification or proves a substantive limitation. Adding a field that assumes
the desired conclusion would not do that work.

**A specific physical model does not mean new empirical data.** It means
declaring the internal/environmental states, energy, transition rules,
reservoir, and any control or learning rule. These may be chosen theoretically;
Lean can then prove conditional results or counterexamples. Evidence is needed
to establish that a chosen model describes cortex, not to develop its
mathematics. This distinction qualifies the recommendation to stop extending
the current chain: the next bounded modelling theorem can proceed without
waiting for recordings or biological calibration.

### L1 — Complete finite perception--action update

- [x] Generalize the reciprocal example to alternating finite actuation and
      memory-update substeps with the internal/world roles exchanged.

**Intent.** Replace separate elementary-step accounting with a reusable
composition theorem for the actual two-substep process. Begin with the current
finite, strictly positive autonomous-channel regime at a common thermal scale.
Action and observation may remain aliases of the existing state variables, as
in the witnessed model; extra physical registers require additional accounting
and are outside this first change.

**Completion criteria, specified before implementation:**

1. Carry the first step's final joint law into the second step's initial law,
   with the coordinate swap explicit. Do not existentially choose an unrelated
   second law or assume the final distribution equals the initial one.
2. Identify the resulting joint law with the composed perception--action
   channels. Derive a total entropy/heat balance by cancelling the same
   intermediate entropy, and derive the total mean first law using a consistent
   energy observable and the stated substep work/heat conventions.
3. Derive a whole-update heat-budget consequence. Show it specializes to the
   existing two-bit calculations; retain nontrivial action and memory changes
   and positive actuation heat. Add a regression that detects a mismatched
   intermediate distribution instead of silently composing it.
4. Follow SDD/TDD, retain the axiom audit, and update publication scope and
   tracked PDFs with the verified result. No experimental input is required.

**Stop rule.** Stop when this composition, its budget consequence and its
witness/regression checks pass. Time-dependent protocols, arbitrary extra
registers, weaker support conditions and learning are separate changes. L1
does not establish the register-to-actuator allocation of E34Active or the
coupling-convergence assumption E45Active; it is not a submission prerequisite.

### L2 — Goal-directed policy selection under a finite budget

- [x] Derive a policy choice that improves a specified finite task while
      satisfying the heat budget of its actual perception--action process.

**Done 2026-09-14.** `FiniteControlProblem` evaluates reward, heat and work on
the actual L1 cycle and proves finite feasible maximization. The lamp witness
compares all deterministic bit policies on common channels, initial law and
energy. At budget `log 3 / 4`, copying uniquely maximizes feasible performance:
1/2 versus the feasible baseline's 1/4, with the same total mean heat and zero
mean work. The baseline misses the task target, the constant-true policy
exceeds the budget, and equal final laws can have different heat costs. See
`tasks/agency_control.md` and the completion record below. Learning and the
active chain's resource and spatial bridges remain separate.

**Gap and intent.** L1 accounts for a complete update with supplied channels;
it does not select actions or improve a policy against an objective. L2 adds
purposeful control under declared model assumptions. The objective is an
explicit modelling input, not a consequence of the thermodynamic bound.

**Completion criteria, specified before implementation:**

1. Specify a finite task, objective, permitted policies and comparison baseline.
2. Compute each policy's expected performance and heat/work from its actual L1
   process, using consistent initial/intermediate/final laws, energy and
   reservoir conventions. Do not substitute an unrelated assigned cost.
3. Construct a budget-feasible policy and prove strict improvement in expected
   task performance over the baseline. Supply a nontrivial witness and a
   regression showing that cost feasibility alone does not ensure task success.
4. Follow SDD/TDD and the axiom audit; align publication scope and tracked PDFs
   with the verified result.

**Stop rule.** Stop at the finite control result and its witness/regressions.
Learning dynamics and learning convergence are separate follow-ups. Additional
physical registers or time-dependent control require their own accounting.
L2 does not close E34Active's physical budget allocation or E45Active's spatial
coupling-convergence implication. No empirical data is required for this
mathematical task; cortical identification remains separate. L2 is not a
submission prerequisite.

### Further modelling questions — separate, unscheduled gaps

- [x] **E34Active — common physical resource budget.** Specify a common
      register/controller resource model in which the named energies, heat
      budget and actual operations are identified. The existing numerical heat
      comparison and distinct toy components do not establish a shared physical
      mechanism. A lower bound on erasure heat supplies no upper actuator budget.
      Integrating the agent's processes is useful progress, but closing this
      edge additionally requires identifying the named register and deriving
      its allocation to the controlled process.
      **Done 2026-09-14:** `RegisterLedger` holds one register's update, its
      operations as steps controlled by that register, local detailed balance
      at its own temperature and the identity that its dissipated heat is the
      total those operations deliver. `opHeat_le_dissipation` derives the
      allocation from that identity and the second law;
      `Chain.e34Active_of_ledger` discharges the edge, and
      `Examples/RegisterBudget.lean` witnesses it on the one-bit eraser with an
      exact `(2/5)log 2 + (3/5)log 2 = log 2` ledger. The identity and the
      compressiveness of the register's other operations remain physical
      inputs, each fenced by a regression; they are the separate open item
      below. Specification, resource boundary and verification:
      `tasks/e34_active.md` and the completion record below.
- [ ] **The register ledger's own premises.** The derived allocation rests on
      two model inputs: the accounting identity that the register's dissipated
      heat is exactly the total its operations deliver to its reservoir, and
      the compressiveness of its other operations. Neither follows from a
      microscopic model here. Specify a bipartite register/bath dynamics and
      derive the identity for it, or exhibit the conditions under which it
      fails. `Examples/Bit.lean`'s bath fixes `heat_dissipation` at `log 2` for
      every map of the register, including the identity, so a sharper register
      instance is part of this question. `leaky_exceeds_budget` and
      `compressive_exceeds_budget` show that dropping either input loses the
      bound, so neither is decorative.
- [x] **Learning dynamics.** After the bounded L2 control result, specify how
      the policy changes, which objective drives the update and what resource
      costs it incurs before seeking a learning-improvement or convergence theorem.
      **Done 2026-09-14:** `FiniteFeedbackStep.iterate` and
      `Examples/PolicyLearning.lean` derive actual-law iteration, expected reward
      improvement, convergence to a suboptimal stationary mixture and cumulative
      register heat from energy loss. The thermal energy encodes known L2 rewards;
      individual paths and a different initial preparation can lower reward.
      Specification, resource boundary and verification:
      `tasks/learning_dynamics.md` and the completion record below.
- [x] **Learning from experience.** Specify observations of actual task
      outcomes, an estimator or memory update and a policy update driven by
      that information. Prove that acquired observations affect subsequent
      behaviour and improve a declared performance criterion in a model with
      initially unknown task information. The objective may be supplied; the
      completed policy-register model also supplies the policy values in its
      energy, so it does not establish their acquisition from experience.
      **Done 2026-09-14:** `FiniteObservationalLearner` holds an environmental
      parameter fixed and unknown and updates a policy register from the
      observed outcome of the action its readout executed. The fences are
      signatures: neither `update` nor `readout` takes the parameter, and the
      reward enters no channel. Act--observe--update composes into one
      `FiniteFeedbackStep`, so reward, heat and entropy are read from the same
      law. `Examples/ObservationalLearning.lean` proves strict improvement over
      a frozen register and an uninformative world under a common allowance,
      and `zero_work_needs_parameter_independent_heat` shows the work spent is
      irreducible. Specification, resource boundary and verification:
      `tasks/observational_learning.md` and the completion record below.
- [x] **One continuing physical agent — bounded finite model.** Completed
      2026-09-14: `FiniteProtocol` sequences heterogeneous operations on one
      evolving law; `ContinuingAgent` carries actuation, observation-driven
      register updates and reset on the same parameter/register/environment
      state. `ContinuingProcess` charges expected work to a declared initial
      store and derives total heat and entropy budgets including the system's
      energy drop. The bit witness retains above-chance reward, pays for each
      reset and has a positive recurring cost: the first cycle fits its store,
      while 22 complete cycles cannot. Blinding and omitted-reset controls
      fence the observation and preparation claims. The store constrains
      expectations at every prefix, not individual paths. Initial preparation,
      a microscopic supply, sensor-memory implementation and fabrication are
      supplied or excluded, not derived. Specification and execution record:
      `tasks/continuing_agent.md` and the dated completion section below.
- [ ] **Physical preparation and supply beyond the finite model.** Derive
      preparation of the initial law, model the work store or replenishment
      on individual trajectories, and account for a separately implemented
      sensor memory if one is used. The continuing model's declared prior,
      initial allowance and composite learning-channel reservoir do not
      establish these. Keep this separate from the register-ledger identity,
      spatial actuation and cortical identification.
- [x] **E45Active — a scalar constitutive case.** Completed 2026-09-14:
      `ActuatedCoupling` constructs a spatial density from the named feedback
      step's joint entropy reduction, a supplied nonnegative gain and a supplied
      profile. Regular mesh refinement discharges this instance of E45Active;
      `actuated_limit_le_budget` bounds its limit using that same process's
      budget. A positive-drive noisy actuator has changing spatial energies,
      process/gain/profile regressions and a composed active chain. This is the
      completed scope of the interrupted module, not a microscopic actuator or
      kernel construction. Specification: `tasks/e45_active.md`.
- [x] **E45/E45Active — microscopic actuation and kernel convergence.**
      Completed 2026-09-14: a finite actuator with spatial response modes whose
      occupancies determine both a product-space kernel and a stored
      installation energy. Pathwise, local and expected kernel updates and the
      installation work come from the same executed process. Finite cell-pair
      partitions reconstruct the installed kernel and converge to its
      product-measure integral under spatial refinement, at a refinement index
      independent of the number of executed updates. Both spatial edges are
      discharged on their named laws: the active one on an executed step's final
      law, the passive one on a declared predictive system's joint law.
      Specification: `tasks/e45_kernel.md`. Mode profiles, prices, occupancy
      readout, reservoir and substrate remain declared hardware; fabrication,
      continuing power and cortical identification are not established.
- [ ] Model how local descriptions acquire or preserve overlap agreement and
      how a readout fixes the glued state. For an agency-based mechanism, connect
      observations and updates to a declared local content state and derive
      agreement or a quantified residual. Coordinate this choice with L3/L4's
      consistency work. Conditional proofs and counterexamples can precede
      data; identifying the variables with neural content and testing their
      relevance to experience are separate empirical/interpretive tasks.

R1–R6 continue to track calibration, observation and biological validation.
The final citation/macro review and author/journal metadata items remain in P;
the primer update does not close those tasks.

## 2026-09-13 — L1 complete: a shared-law finite perception--action update

- [x] Add `FiniteFeedbackCycle` in `Phase3_AgencyThermodynamics`: sensing starts
      at the coordinate-swapped actuation final law, and its final law equals
      the existing `Agency.cycle` output. No stationarity premise is supplied.
- [x] Derive the total entropy/heat balance, mean first law with one energy
      observable, and whole-update heat-budget consequence. The intermediate
      entropy and expected energy cancel under the explicit coordinate exchange.
- [x] Specialize to the existing reciprocal two-bit agent and exact costs.
      Add a biased witness with an asymmetric intermediate law, changing sensing
      law and positive actuation heat. Reject a positive but incompatible second
      step and a zero total heat budget.
- [x] Update article, supplement, Table S1 and primer; rebuild and inspect the
      tracked PDFs (38, 32 and 74 pages) and rebuild the 47-page arXiv archive.
- [x] Pass the full zero-warning Lean build and axiom audit: 2,404 declarations
      in 43 modules, only `propext`, `Classical.choice` and `Quot.sound`.
      Explicit headline axiom checks, all pre-commit hooks, 31 PDF/arXiv/figure
      tests, working-tree PDF/dependency timestamps and `git diff --check` pass.

Specification and execution record: `tasks/agency_cycle.md`. Witnesses and
regressions: `Examples/AgencyCycle.lean`. The red regression specifications
failed before implementation. No new simulation, Python source or reference
was added by L1.

The theorem covers two finite autonomous channels with strictly positive
initial masses and transitions, a common thermal scale and consistent energy.
Action and observation alias existing states. Extra registers, protocols,
weaker support, learning and biological identification remain separate tasks.
E34Active's register-to-actuator allocation and E45Active's coupling convergence
are not derived. L1 stops here; the unscheduled modelling questions above and
the P-items remain open. The user requested a combined commit of the agency
extension, active chain, primer and L1 on 2026-09-13.

## 2026-09-13 — Next agentic Lean task recorded

Recorded L2's finite task, explicit objective and policies, same-process
performance/cost accounting, budget-feasible improvement theorem and negative
regression. Kept learning dynamics, E34Active's common resource identification
and E45Active's spatial convergence as separate open tasks. This ledger update
adds no implementation or proved claim.

## 2026-09-13 — Relaxed consistency conditions (external review response)

An external model review of the manuscript on 2026-09-13 raised four points.
Three restate limitations the manuscript already states in its own words:
overlap compatibility as a premise (`main.tex:375`), the rigidity of the exact
fixed point (`main.tex:285`), and the speculative status of the coupling
identification (`main.tex:156`, `main.tex:171`). They confirm the limitations
section rather than revise it, and open no task.

The reviewable content is its closing question: what a relaxed consistency
condition does to the uniqueness results. The question conflates two
relaxations that are independent in this development. Relaxing the fixed point
leaves Derivation 5 untouched, because Banach is downstream of the gluing and
consumes it (`main.tex:291` already says both uniqueness results are separately
conditional). Relaxing overlap agreement is the relaxation that actually
threatens uniqueness. L3 and L4 separate them. Neither is a submission
prerequisite, and neither precedes L2.

### L3 — Approximate fixed point of the self-prediction map

- [x] Replace the conjecture at `main.tex:285` with the bound it guesses at:
      an approximate self is confined to a ball whose radius is set by the
      coupling margin.
      **Done 2026-09-14:** residual and displacement bounds, an exact
      near-threshold sandwich, a sharp cortical witness and nonexpansive
      non-uniqueness are proved. Article, supplement and primer are aligned.
      Specification and verification: `tasks/approximate_self.md` and the
      completion record below.

**Gap and intent.** The manuscript states that approximate self-models may
require a weaker condition than the exact fixed point and leaves no result
behind the statement. Banach's uniqueness is not what the relaxation costs:
the exact fixed point still exists and is still unique. What the relaxation
buys is that the Self becomes graded in `K - 2D` rather than binary. Mathlib
supplies the estimate, so this is a cheap item.

**Completion criteria, specified before implementation:**

1. In `Phase6_ReflexiveTopology`, state and prove: for a boundary whose
   `predict` is `ContractingWith q`, any `s` with `dist s (rb.predict s) ≤ ε`
   satisfies `dist s s_* ≤ ε / (1 - q)` for the Self `s_*`. This is
   `ContractingWith.dist_le_of_fixedPoint`
   (`Mathlib/Topology/MetricSpace/Contracting.lean:256`); do not restate Banach
   around it.
2. Instantiate `q` at `resonanceRate K D τ = exp (-(K - 2D) τ / 2)` and record
   the consequence as an inequality, not a numeral: the tolerance behaves as
   `2ε / ((K - 2D) τ)` near threshold and diverges as `K → 2D⁺`. This is the
   statement that makes self-representation graded in the supercritical margin.
3. Compose the two errors. If the glued state is displaced by `δ`, the residual
   at the displaced state is at most `ε + (1 + q) δ`, so the approximate-self
   ball has radius `(ε + (1 + q) δ) / (1 - q)`. The point of the item is that
   the errors add before division by the contraction gap. Its inverse amplifies
   the bound near threshold; no uniform error control survives as `q → 1`.
4. Negative companion: exhibit a nonexpansive (`q = 1`) self-map on the
   Examples §10 metric with more than one fixed point. This locates the cliff
   at `q → 1`, not at exactness, and pairs with the existing
   `not_contractingWith_resonanceRate` below threshold.
5. Witness with `cortexReflexive`, which contracts by exactly one half, at an
   explicit `ε`. Follow SDD/TDD and the axiom audit; rewrite `main.tex:285` to
   state the proved bound in place of the conjecture, and align the supplement
   and tracked PDFs.

**Stop rule.** Stop at the a-posteriori bound, its threshold instantiation, the
error composition and the non-uniqueness witness. L3 does not construct the
encoding or the readout, which remain a separate obligation (`main.tex:270`),
does not supply restriction resonance, and changes nothing in Derivation 5.

### L4 — Approximate overlap agreement: what survives of uniqueness

- [x] Determine what an `ε`-compatible family determines, with an explicit
      constant, and what it demonstrably fails to determine.
      **Done 2026-09-14:** Route A. Selection by a partition of unity, the
      constant `C(N) = 1` in the uniform mass metric, the `ε = 0` recovery of
      exact gluing, a three-patch witness attaining `ε`, the failure of exact
      gluing at every positive `ε` and two regressions are proved.
      Specification and verification: `tasks/approximate_gluing.md` and the
      completion record below.

**Gap and intent.** `sheaf_glue_unique`
(`PhysicsOfConsciousness/Phase5_GlobalSection.lean:53`) takes `h_compat` as an
equation, and the sheaf condition is equality-or-nothing. Under
`d (ρᵢ sᵢ) (ρⱼ sⱼ) ≤ ε` there is in general neither an exact global section nor
any bound on the diameter of the approximate ones without further structure.
Two routes are available and each has a declared cost. Do not attempt both in
one change; pick one and state which.

*Route A — selection.* The local states are finite measures and admit convex
combination, so a partition of unity subordinate to the cover averages the
family into a canonical global object. Uniqueness is then replaced by a
selection rule, and two partitions are expected to give sections differing by
`O(N ε)` with `N` the cover's multiplicity. The item is to prove that constant,
not to assume it. The cost is interpretive: unity becomes coarse-grained at
scale `δ`, which is defensible only if the identification is shown to depend on
features invariant at that resolution, and `main.tex` does not currently argue
this.

*Route B — obstruction.* The discrepancy is a Čech-style 1-cochain; gluing is
exact iff it is a coboundary, and the least achievable residual is the quotient
norm of its class. This is the metric version of `Phase5_TwistedGluing`. The
trap is already recorded at `supplementary.tex:262`: with phase coefficients the
obstruction is vacuous, because absolute patch phases make every offset a
coboundary (`isCoboundary_of_phaseField`). The `ε`-version is informative only
in content coefficients — precisely the state space that module declines to
choose. Route B therefore requires choosing a content state space first, and
that choice is the physical commitment, not a formality.

**Completion criteria, specified before implementation:**

1. State the relaxed hypothesis with a metric on sections over overlaps. A
   weakening to a predicate carrying no modulus does not answer the question.
2. Prove the positive statement with an explicit constant in `ε` and the
   cover's multiplicity. A statement without a constant is not a relaxation of
   uniqueness, only an abandonment of it.
3. Prove the matching negative: either a family that is `ε`-compatible for
   arbitrarily small `ε` and admits no exact global section, or two approximate
   sections whose distance is not controlled by `ε` alone. Without this the
   hypotheses are not shown to be necessary, which is the failure the existing
   counterexamples exist to prevent.
4. Witness on the three-site cortex, with a regression that rejects a family
   compatible only pairwise.
5. Follow SDD/TDD and the axiom audit; align publication scope and tracked PDFs.

**Stop rule.** Stop at one route with its constant, its negative companion and
its witness. L4 supplies no mechanism by which cortical descriptions acquire
agreement; that remains the unscheduled item above. It does not close the
content-model gap at `main.tex:226`.

### Recorded, not scheduled — from the same review

- **Coboundary repair as a consensus dynamics.** Least-squares minimisation of
  the discrepancy cochain over 0-cochains on the nerve is Laplacian consensus,
  and the residual it cannot remove is the cycle-space component. This is the
  shape a mechanism for acquiring overlap agreement would take, and it is the
  natural successor to the unscheduled overlap-agreement item. It is a
  suggestion and not a result: it presupposes L4 Route B, hence a content state
  space, and a declared dynamics, and the circle-valued case carries subtleties
  the real-valued case does not. Do not schedule before L4.
- **The gap the review did not name.** What is proved is about spatial mass
  profiles, where restriction is functorial and gluing is easy; what is claimed
  is about contents, where matching overlap marginals need not determine a joint.
  `main.tex:226` already cites `abramsky2011` for exactly this, and the content
  model is the standing unscheduled research item. Recorded here so that no
  later reader mistakes the measure-theoretic theorem for the content-theoretic
  one. No task opened.
- **Cover selection remains the deepest conditional** (`main.tex:291`). Both
  uniqueness results are relative to a chosen cover and nothing selects it;
  `tononi2016` makes exclusion explicit and this framework does not. Recorded
  because relaxing consistency makes the selection problem worse rather than
  better: a set of approximate sections over a set of admissible covers. No
  task opened.

This ledger update adds no implementation and no proved claim.

## 2026-09-14 — L2 complete: finite control using the actual update's heat

- [x] State the task and red Lean specifications before implementation. The
      specifications fail on the absent control declarations, then pass with
      the complete implementation.
- [x] Add `FiniteControlProblem` beside the L1 construction. Its bare data are
      the shared initial law, world and memory channels and terminal reward.
      Deterministic policy channels produce the exact law used for reward and
      heat, and the common first law and entropy-budget bound apply. A nonempty
      finite feasible policy set has a reward maximizer.
- [x] Prove exact performance, actuation heat, memory heat and total work for
      every deterministic bit policy in `Examples/AgencyControl.lean`. At the
      supplied heat budget, copy is the unique optimum and doubles lamp success
      over a feasible baseline. The baseline misses the declared target;
      constant true beats copy but is infeasible; copy and invert have equal
      final joint laws and different costs. Both selected substeps permit
      state changes.
- [x] Align article, supplement, status tables and primer, and rebuild their
      tracked PDFs (39, 33 and 75 pages). Visually inspect the changed text,
      equations and tables; rebuild the 48-page arXiv archive from its tarball.
- [x] Pass the full zero-warning Lean build and axiom audit: 2,497 declarations
      in 44 modules, only `propext`, `Classical.choice` and `Quot.sound`.
      Headline axiom checks, all applicable pre-commit hooks, 39 publication
      and macro tests, PDF source-dependency checks and `git diff --check` pass.

Specification and execution record: `tasks/agency_control.md`. The numerical
table contains exact finite expectations proved in Lean, not simulation
estimates. No simulation, Python source, dependency or reference was added.
The reward, initial resource, fixed channels and upper budget are modelling
inputs. This result compares policies for one update and accounts for its
transition work; it excludes policy installation, switching, learning and
additional physical registers. It supplies neither cortical identification nor
a continuing energy source, E34Active allocation or E45Active convergence.
L3, L4, the unscheduled modelling questions and the P-items remain open.

## 2026-09-14 — Learning dynamics: thermal adaptation with actual update costs

- [x] Specify the objective, autonomous register channel, initial preparation,
      resource accounting and stopping point before implementation. Run failing
      Lean specifications before adding the iteration and witness declarations.
- [x] Add `FiniteFeedbackStep.iterate` beside the elementary process. Every
      update receives the previous final law; positivity persists, and finite
      entropy and first-law balances telescope. Zero path work identifies
      cumulative heat with the same process's mean energy loss.
- [x] In `Examples/PolicyLearning.lean`, decode the register into L2's two
      feasible lamp policies and identify its energy with their known reward
      gap. Derive the distribution from the actual channel, strict expected
      improvement, geometric convergence to a stationary mixture, positive
      update heat and a finite cumulative heat bound. The prospective task
      mixture retains L2's heat budget and zero expected work.
- [x] Retain positive-probability reward-decreasing transitions, prove that the
      limit stays below the optimal policy, and show expected reward decrease
      from a different strictly positive initial preparation. Reject frozen or
      reset initial laws by proving consecutive distributions differ.
- [x] Align article, supplement, status tables and primer. Rebuild and visually
      inspect the tracked PDFs (39, 34 and 76 pages); rebuild the 49-page arXiv
      archive and compile it from the unpacked tarball. Final standalone logs
      have no warnings or overfull boxes, matching the pre-change baseline.
- [x] Pass the zero-warning full Lean build and axiom audit: 2,568 declarations
      in 45 modules, only `propext`, `Classical.choice` and `Quot.sound`.
      Explicit headline axiom checks, all applicable pre-commit hooks, 39
      publication/macro tests, working-tree PDF dependency checks and
      `git diff --check` pass. Python hooks skip because no Python changed.

Specification and execution record: `tasks/learning_dynamics.md`. The exact
expectations and limits are proved in Lean; no simulation, reference, Python
source or dependency was added. The register adapts toward a supplied energy
encoding of known task values. It does not learn unknown rewards from data.
Its heat covers register relaxation from a prepared initial law, not preparing
that law, executing/resetting task episodes or installing the policy readout
in an actuator. Those processes remain in the separate open item above.
Neither E34Active's common resource identification nor E45Active's spatial
convergence follows from this learning-time limit. L3, L4 and the other
modelling/submission tasks remain open.

## 2026-09-14 — Agency roadmap and stretch work

**Assessment and priority.** Agency has reached the 80/20 stopping point for
its role in the current manuscript: feedback information, a complete finite
perception--action update with heat/work accounting, budgeted goal-directed
control and policy adaptation toward supplied values are proved and witnessed.
The remaining gaps concern learning from experience, one continuing physical
agent, and the connection to cortical coupling and representation. They remain
substantial research questions. None is a prerequisite for reviewing or
submitting the manuscript with its current scope statements.

The open checkboxes in the modelling section above are the status record for
those gaps. The specifications below explain what would close them; they do
not mark further implementation as complete. All items, including the stretch
work, are recorded at the user's request on 2026-09-14.

### Highest-value optional next step — learning changes the next actual action

**Closed 2026-09-14** by the observational-learning model; see the completion
record at the end of this file. Criteria 1, 2, 4, 5 and 6 are met in full.
Criterion 3 is met for the executed updates and their drive, and explicitly not
for preparation of the prior or a continuing supply: that half is what the
"one continuing physical agent" item above still carries. The specification
below stands as the statement of what was required.


**Intent.** Combine observational learning and execution in one bounded finite
task. An observed outcome changes the policy, and the changed policy controls
the next actual action. Begin with a small state space, explicit initial
uncertainty and a fixed finite horizon. Retain the current support and
autonomous-channel regime where possible rather than first generalizing the
thermodynamic library.

**Completion criteria to specify before implementation:**

1. Declare the environment, internal memory, policy register, action and
   observation variables, objective, permitted update rule, horizon and
   comparison baseline. The learner cannot read the unknown environmental
   parameter or receive precomputed policy values in place of observations.
2. Construct the sequence observation--policy update--next action on one joint
   law, carrying every actual output into the next input. Exhibit dependence
   of the updated policy on the observation and of the next world transition
   on that policy. A changing internal label with unchanged behaviour does not
   satisfy this criterion.
3. Account for the implemented readout and all executed substeps, with common
   energy and reservoir conventions. Include preparation or resets if used,
   specify the source of consumed energy, and state any initially supplied
   resource explicitly. Derive total heat/work and entropy balances for the
   same process used to evaluate performance.
4. Prove strict improvement in a prespecified task-performance criterion over
   a frozen-policy baseline under declared initial uncertainty and a common
   resource allowance. Evaluate the actual trajectories; prospective rewards
   at independently prepared task laws are insufficient for this result.
5. Supply nontrivial witnesses and regressions: observations carry task
   information, policies and subsequent actions can change, and informative
   observations cannot be replaced by an uninformative channel while keeping
   the same improvement claim. Retain the distinction between expected
   improvement and improvement of every sample path.
6. Follow SDD/TDD, the axiom audit and publication/PDF alignment rules. A
   theoretical finite model requires no new empirical data; identifying it
   with cortex is a separate task.

**Stop rule.** Stop at one specified finite task, its whole-process accounting,
an improvement theorem and its negative checks. Do not make arbitrary horizons,
general reinforcement-learning convergence or a cortical identification part
of this change. If the proposed model cannot meet the criterion, record the
obstruction or counterexample before designing a separate alternative.

### Further major gaps — separate modelling changes

**Common resources and sustained operation.** A bounded interacting witness
should expose where useful energy is consumed. A claim about a continuing
agent additionally needs a declared supply or replenishment process and its
work/heat balance. E34Active is closed only when the named register's physical
operations and its allocation to the controlled process are established.
Sharing a state type or satisfying a numerical heat comparison is not that
identification. Keep this bridge task separate if the bounded witness does
not realize that specific register.

**Coupling and representation.** The coupling half is closed: the finite
microscopic actuator changes a product-space kernel through occupancies the
executed step sets, and the cell-pair limit carries explicit regularity and
refinement hypotheses (`tasks/e45_kernel.md`). What it supplies as physical
input is the hardware, not a heat bound. Still open: choose the local content
variables and their observation/update dynamics, then prove overlap agreement,
preservation of agreement or a quantified residual and the required readout
relation. That is the local-agreement gap, and it is not a consequence of
improved task reward. Cortical calibration
and the interpretation of these variables as experienced content remain
distinct empirical/interpretive work.

### Stretch — lower priority until a concrete model needs it

- [ ] **Broader state spaces for agency thermodynamics and control.** Extend
      the finite path-cost and control results to a declared countable or
      continuous model, with the necessary integrability, support and existence
      assumptions and a nontrivial witness. The general `Agency` channel
      interface already accepts measurable spaces; another such interface
      would not close this gap.
- [ ] **Weaker positivity assumptions in the thermodynamic results.** Admit
      zero initial masses or transitions under appropriate forward/reverse
      support conditions. Prove the balance in a meaningful new case and retain
      cases of infinite entropy production or absolute irreversibility where
      required. Do not turn an infinite information quantity into a finite cost
      through `ENNReal.toReal`. Finite information results already cover zero
      atoms; the strict-support restriction here concerns path thermodynamics.
- [ ] **Longer horizons and additional learning-convergence results.** Once an
      interacting learner is specified, prove persistence of task performance
      or convergence/rate results for that process, together with resource
      consumption as the horizon grows. State whether convergence is in law,
      expectation or along paths, and whether the limit is optimal. Another
      convergence theorem for a register with pre-encoded policy values would
      not resolve observational learning or sustained operation.

**Recording check.** This roadmap expands and separates the existing open
items and records the suggested bounded experiment and stretch work. It adds
no Lean declaration, simulation, reference or publication claim.

## 2026-09-14 — L3 complete: approximate self-prediction

- [x] Prove `ReflexiveBoundary.approximate_self_bound` from Mathlib's existing
      a-posteriori estimate: residual at most `ε` gives distance at most
      `ε / (1 - q)` from the named fixed point of the same map. Prove that
      displacement at most `δ` gives residual at most `ε + (1 + q) δ`, and
      compose that residual with the fixed-point estimate.
- [x] Instantiate the bound at `resonanceRate`. For `K > 2D`, `τ > 0` and
      `ε ≥ 0`, `resonance_error_radius_bounds` places the radius between
      `2ε / ((K - 2D) τ)` and that expression plus `ε`. These inequalities
      give the leading threshold behaviour without a series expansion.
      The inverse contraction gap amplifies the bound; divergence of the
      tolerance radius is not a statement that any actual error diverges.
- [x] Exercise the bound on the existing nonconstant, one-site-avatar witness:
      the silent state has residual one and distance two from `cortexState`,
      attaining the bound at `q = 1/2`. On the same metric, identity encoding
      and readout through a whole-space avatar are nonexpansive and have
      distinct fixed points. This is a negative control, not a local
      compression model. The initially failing Lean specifications pass,
      including the zero-residual case.
- [x] Replace the article's approximate-self conjecture with the inequality;
      align the supplement, status tables and primer. Rebuild and visually
      inspect the changed PDF pages: article 40 pages, supplement 34, primer
      77. All standalone logs have zero warnings and overfull boxes, matching
      the pre-change baseline. The 51-page arXiv submission compiles cleanly
      from the unpacked tarball and passes manifest freshness.
- [x] Pass the full zero-warning Lean build and axiom audit: 2,585 declarations
      in 45 modules use only `propext`, `Classical.choice` and `Quot.sound`.
      Explicit axiom checks cover all nine new headline theorems. The 39
      publication/macro regression tests, applicable pre-commit hooks,
      working-tree PDF dependency checks and `git diff --check` pass.

Specification and execution record: `tasks/approximate_self.md`. No Python,
reference, dependency, simulation result or physical assumption was added.
The estimate holds the map and metric fixed, assumes its contraction law and
does not choose the represented variables, construct the readout or derive
restriction resonance. Exact gluing and the chain's identification of the
glued state with a fixed point retain their hypotheses. L4's approximate
overlap problem remains a separate modelling change. The publication audit
is on hold at the user's request; the agency research gaps and author/journal
metadata items remain open.

## 2026-09-14 — L4 complete: selection under approximate overlap agreement

- [x] Run failing Lean specifications for the witness before implementation,
      then implement Route A. The scratch specification file failed on the
      absent declarations and passes unchanged afterwards.
- [x] State the relaxed hypothesis with a metric: `ApproximateGluing` in
      `Phase5_GlobalSection.lean` measures restrictions to an overlap in the
      uniform distance on site masses (`profileDist`), and `Compatible`
      quantifies over every pair of the supplied family.
- [x] Prove the positive statement with its constant. A nonnegative partition
      subordinate to the cover selects a profile within `ε` of each patch on
      that patch, and any two partitions select profiles at distance at most
      `ε`: `C(N) = 1` at every cover multiplicity, because normalized weights
      sum to one rather than to the number of active patches. Arbitrary
      `δ`-fits have diameter `2δ`, off-patch values cannot influence a
      selection, `ε = 0` recovers unique gluing, and an `L`-Lipschitz feature
      varies by at most `Lε`.
- [x] Prove the matching negative on the three two-site patches of §17.1: for
      every positive `ε` the `ε`-compatible family `apxW` admits no exact
      global section, and two partitions select states at distance exactly
      `ε`, so the constant is attained. The total-mass readout moves by `2ε`
      of the `3ε` its Lipschitz constant permits.
- [x] Keep the two regressions explicit. Approximate agreement cannot be
      passed as exact compatibility or as the class field of Derivation 5, and
      agreement on the overlaps `(0,1)` and `(1,2)` alone leaves the
      selections `2ε` apart. Exact pairwise agreement of the fixed §17.1
      family is the `ε = 0` case and still glues uniquely.
- [x] Align article, supplement, Table S1 and primer; rebuild and visually
      inspect the changed tracked PDF pages (article 40, supplement 35, primer
      78). All logs have zero warnings and overfull boxes, matching the
      pre-change baseline, and the 52-page arXiv submission compiles from its
      unpacked tarball.
- [x] Pass the zero-warning full Lean build and axiom audit: 2,662
      declarations in 45 modules using only `propext`, `Classical.choice` and
      `Quot.sound`, with sixteen explicit headline axiom checks. The seven
      applicable gates, the advisory hedging report, the 39 publication and
      macro tests and `git diff --check` pass. Python hooks skip because no
      Python changed.

Specification and execution record: `tasks/approximate_gluing.md`. Witnesses
and regressions: `Examples/Phase5.lean` §21. No Lean axiom, Python source,
dependency, reference or simulation result was added.

The theorems are about finite spatial mass profiles in the uniform metric,
where restriction is functorial; they say nothing about matching marginals of
decoded contents (`main.tex:226`). Selection replaces uniqueness with a choice
at resolution `ε`: L4 supplies no process by which local descriptions acquire
agreement, no rule selecting the cover or the weights, and no argument that a
conscious episode depends only on features invariant at that resolution.
`sheaf_glue_unique`, the `ThermodynamicCover` instances and both chain theorems
retain their exact agreement hypothesis. Route B, the obstruction version, is
not started and still requires choosing a content state space; the recorded
consensus-dynamics suggestion above presupposes it. The unscheduled modelling
questions, the agency research gaps and the P-items remain open.

## 2026-09-14 — E34Active complete: one register's resource ledger

- [x] Specify the resource model, the derived allocation, the witness numbers
      and the regressions before implementation; run the failing Lean
      specifications first.
- [x] Add `RegisterLedger` beside `FiniteFeedbackStep`: one register's update,
      its operations, local detailed balance at that register's temperature and
      the identity `heat_dissipation update = ∑ i, meanHeat i`.
      `opHeat_nonneg_of_compressive` is the existing path-model second law at
      that temperature; `opHeat_le_dissipation` derives the allocation;
      `ledger_bathEntropy` exhibits the total as the register's own bath
      entropy change. `Chain.e34Active_of_ledger` turns a ledger into the edge.
- [x] Witness it in `Examples/RegisterBudget.lean` on §1's one-bit eraser: one
      log-odds family with proved final law, mean heat and joint entropy, and
      two operations delivering `(2/5)log 2` and `(3/5)log 2` — exactly the
      register's `log 2`. `chain_active_budget_jointly_satisfiable` composes
      the whole active branch through the derived edge.
- [x] Fence both inputs. `act_not_compressive`: the controlled operation
      increases joint entropy, so its own second law bounds it in neither
      direction. `compressive_exceeds_budget`: an entropy-preserving operation
      of the same family delivers `(7/3)log 2`, above the whole dissipation.
      `leaky_exceeds_budget` and `leaky_other_not_compressive`: a second ledger
      for the same register, satisfying positivity, local detailed balance and
      the identity, allocates `(7/6)log 2` because its other operation draws
      heat out of the reservoir.
- [x] Align article, supplement, Table S1 and primer; rebuild and inspect the
      tracked PDFs (article 41, supplement 36, primer 79 pages) and the 53-page
      arXiv submission, which compiles from its unpacked tarball. Final logs
      have no warnings or overfull boxes, matching the pre-change baseline.
- [x] Pass the zero-warning full Lean build and axiom audit: 2,773 declarations
      in 46 modules resting only on `propext`, `Classical.choice` and
      `Quot.sound`, with the explicit headline axiom checks agreeing. The eight
      applicable gates, the advisory hedging report, the 143 publication and
      simulation tests and `git diff --check` pass. Python hooks skip because
      no Python changed.

Specification and execution record: `tasks/e34_active.md`. Witnesses and
regressions: `Examples/RegisterBudget.lean`. No Lean axiom, Python source,
dependency, reference or simulation result was added.

The edge's allocation is now derived inside one named register's resource
model rather than compared across separate toy components. What the model
still supplies as physical input is the accounting identity and the
compressiveness of the register's other operations; what it does not supply is
a sequential joint law, a preparation or continuing power source, the
coupling-convergence implication of E45Active, or any cortical identification.
`thermalAgency_e34Active` and its numerical comparison remain in place as the
other discharge of the same edge. The remaining unscheduled modelling
questions, the agency research gaps and the P-items are unchanged.

## 2026-09-14 — E45Active scalar actuation model complete

- [x] Complete the interrupted `Phase3_ActuatedCoupling.lean`, fixing its mesh
      vertex universe. The model defines density from a named feedback step's
      joint entropy reduction, a nonnegative gain and a spatial profile;
      `actuated_coarseGrains` proves its spatial limit under regular refinement.
- [x] Add `Chain.e45Active_of_actuatedCoupling` and
      `actuated_limit_le_budget`: mesh assumptions give convergence, while the
      same process's thermal bound caps the limit through gain and total
      profile. The general chain retains its eight hypotheses.
- [x] Add the positive-drive noisy-actuator witness and changing grid energies
      in `Examples/ActuatedCoupling.lean`. Check stationary-step, gain and
      profile dependence, reject a wrong limit for the same sequence and a
      heat-only cap omitting the conversion, and compose the full active branch
      at a calibrated limit. Run the failing specifications before completing
      implementation and the passing specifications afterwards.
- [x] Align article, supplement, Table S1 and primer; rebuild and inspect their
      PDFs (41, 37 and 79 pages). Final logs have zero warnings or overfull boxes
      and the same underfull counts as a fresh HEAD build. Rebuild the 53-page
      arXiv submission from its unpacked tarball and pass manifest freshness.
- [x] Pass the full zero-warning Lean build, the axiom audit (2,859 declarations
      in 48 modules, only the permitted three axioms), fourteen headline axiom
      checks, 39 publication regression tests, all applicable pre-commit hooks,
      working-tree PDF dependency checks and `git diff --check`.

Specification and execution record: `tasks/e45_active.md`. No new axiom,
Python source, dependency, reference or simulation result was added.

The full E45/E45Active item remains open as microscopic actuation and kernel
convergence. The scalar model supplies its constitutive gain, profile and use
of ensemble entropy reduction; it establishes no local implementation, actuator
work account, product-space kernel or cortical identification. The composed
witness uses the thermal actuator's numerical heat comparison, separately from
the register-ledger witness. Neither construction supplies one continuing
physical agent. Other open agency and publication tasks are unchanged.

## 2026-09-14 — E45/E45Active complete: a microscopic actuator and its kernel

- [x] Add `Phase3_LocalActuator.lean`. `LocalActuator` carries mode occupancies,
      spatial profiles and installation prices; the same occupancies give the
      reciprocal kernel on `M × M` and the stored energy. `kernel_update`,
      `kernel_update_local`, `kernel_symmetric` and `kernel_nonneg` describe a
      transition's change, its spatial locality and the kernel's shape;
      `expected_kernel_update` averages the pathwise changes over the executed
      step, and `installation_first_law` charges the same paths with the
      stored-energy change plus the channel's heat.
- [x] Add `Phase2_KernelMesh.lean`. `KernelMesh` reconstructs each sampled
      weight throughout its cell pair; `energy_eq_integral` identifies the
      cell-mass weighted energy with that reconstruction's product-measure
      integral, and `energy_tendsto` converges it under shrinking sample error
      on a compact substrate of finite mass. `KernelArrangement.coarseGrains`
      is the arrangement-level limit.
- [x] Add `Chain.e45Active_of_localActuator` and `Chain.e45_of_localActuator`,
      discharging the active and passive spatial edges for an arrangement
      holding, respectively, a named step's final law and a declared
      `PredictiveDissipation`'s joint law. Neither proof consults its premise:
      the refinement data, not the bound, supplies convergence. The general
      chain keeps its eight hypotheses.
- [x] Add the thermal-switch witness in `Examples/MicroscopicCoupling.lean`:
      positive installation work `(1 + log 3)/4`, a strictly raised pairwise
      value, a pathwise closure from `0` to `16/9`, sample error `1/(n+1)`,
      first energies `4/3` and `25/12` and limit three on the atomless unit
      interval. Reading the declared predictive law on the same hardware gives
      limit four, and the two declared systems differ by their whole dissipated
      work while discharging the identical passive edge. Wrong limits are
      rejected for both sequences and a zero-work claim for the same paths.
      `chain_active_microscopic_jointly_satisfiable` composes the active branch
      through a product-space kernel.
- [x] Align article, supplement, Table 1, Table S1 and primer; rebuild and
      inspect their PDFs (43, 38 and 81 pages). Final logs have zero warnings
      and zero overfull boxes, with the same underfull counts as a fresh HEAD
      build. Rebuild the 56-page arXiv submission from its unpacked tarball and
      pass manifest freshness.
- [x] Pass the full zero-warning Lean build, the axiom audit (3,028
      declarations in 51 modules, only the permitted three axioms), the headline
      axiom checks, 143 publication regression tests, all applicable pre-commit
      hooks and the working-tree PDF dependency check.

Specification and execution record: `tasks/e45_kernel.md`. Witnesses and
regressions: `Examples/MicroscopicCoupling.lean`. No new Lean axiom, Python
source, dependency, reference or simulation result was added.

The coupling kernel is now constructed from local actions rather than assumed,
and its installation is charged to the same executed paths. What the model
supplies as physical input is the hardware: mode profiles, prices, occupancy
readout, the reservoir convention and the substrate measure. One prepared
update is accounted for; fabrication, preparation of the initial configuration
law and continuing power are not. `Chain.lean` §9's negative result is
unchanged — it is an obstruction to the triangulation architecture, which the
cell-pair construction answers point by point rather than repeals. The
remaining open item is the overlap-agreement and readout question below;
E34Active's allocation and E45Active's scalar case stay closed as recorded.
Cortical identification, field trajectory convergence and the P-items are
unchanged.

## 2026-09-14 — Learning from experience: a register taught by its own outcomes

`FiniteObservationalLearner` (`Phase3_ObservationalLearning.lean`) carries a
prior on parameter and register, a readout `R → A`, a world channel
`W → A → ProbDist O`, an update `O → R → ProbDist R` and a reward `W → A → ℝ`.
The fences are type signatures rather than prose: the update has no `W`
argument, so no channel can read the unknown parameter; the readout has no `W`
argument, so no precomputed policy value can be decoded into the action; and
the reward is used by `performance` and by nothing else. Act--observe--update
composes into a `FiniteFeedbackStep W R`, so `iterate`, the KL-based entropy
balance, local detailed balance, the first law and their telescoped sums apply
to exactly the process the reward is read from. `law_succ_apply` and
`meanHeat_apply` expose the evolving law and its path expectations;
`cumulative_work_eq_heat`, `cumulative_entropy_budget` and `frozen_law` are the
generic accounting and baseline results.

`Examples/ObservationalLearning.lean` witnesses it on a two-action task whose
rewarding action is an unknown bit. The world returns success with probability
`3/4` for the rewarding action and `1/4` for the other; the update is win-stay,
lose-resample. The composite channel is `[[5/8, 3/8], [1/8, 7/8]]` at one
parameter value and its mirror at the other, every entry positive. `law_apply`
gives every mass of the actual joint law at every horizon from the uniform
prior, hence `performance_formula`'s `3/4 - (1/4)(1/2)^n`,
`performance_improves`, `performance_limit` and `performance_below_certainty`.
`update_heat` and `cumulative_heat` give `(log 3/8)(1/2)^n` and
`(log 3/4)[1 - (1/2)^N]` on the same laws; `cumulative_work` makes that whole
sum external work, because the register's two states are degenerate.

The negative half is what separates this from the policy-register model.
`zero_work_needs_parameter_independent_heat` proves that a register energy
giving zero path work forces the drive's heat to be equal at every parameter
value, and `no_zero_work_energy` exhibits `q_1(0,1) = log 3 = -q_0(0,1)`. An
energy landscape that made this learning free would be one that already encoded
the answer. `frozen_performance` and `blind_performance` hold both baselines at
`1/2`, `blind_heat` shows the uninformative one is free, and
`improves_on_baselines` states the strict improvement over both inside a common
allowance, so the improvement is bought by the observations and not by the
update rule or the heat. `observation_informative` and
`outcome_marginal_uninformative` locate the information in the outcome
conditional on the action, not in its marginal.
`reward_decreasing_transition` keeps probability `1/8` on a reward-decreasing
transition, `successive_laws_differ` rejects a frozen register and a reset, and
`action_marginal_unchanged` shows the learner acquires a correlation with the
parameter rather than a preference between actions.

The red specifications failed before the declarations existed and pass with the
proofs. The full `lake build` has zero warnings; the default axiom audit covers
3,154 declarations in 53 modules with only `propext`, `Classical.choice` and
`Quot.sound`, and the explicit headline checks agree. All pre-commit hooks pass
under `uv --project simulations` at the repository root, as do 143 existing
Python tests. No Python, dependency, reference, macro or simulation result
changed.

The article gained one paragraph, the supplement one subsection and one Table S1
row, the primer one subsection and one summary row; four sentences claiming that
learning unknown values remained open were removed as no longer true, and are
recorded in `CHANGELOG.md`. The rebuilt article, supplement and primer have 44,
39 and 82 pages, each one page longer than its predecessor, with no overfull
boxes and the same underfull profile. The 57-page arXiv submission compiles from
its unpacked archive and passes manifest freshness. `git diff --check` passes.

Out of scope and still open: preparing the prior, supplying the work that drives
the updates, executing task episodes beyond the declared updates, fabricating
the readout, optimal-policy convergence, and any cortical identification. The
remaining agency gaps are the register ledger's own premises, one continuing
physical agent, and local content agreement.

## 2026-09-14 — One continuing agent: sequenced episodes on a finite allowance

`FiniteProtocol` (`Phase3_ContinuingAgent.lean`) carries an initial law and a
*sequence* of channels, each stage starting at the law the previous one
produced. Every stage is an ordinary `FiniteFeedbackStep`, so
`sum_entropy_balance`, `sum_first_law` and `cumulative_entropy_budget` telescope
over operations that need not be alike — which is what the `iterate` docstring
said was missing — and `ofStep_step` identifies the constant protocol with
`iterate`, so the repeated case is the same theory rather than a second one.

`ContinuingProcess` adds the resources: one energy in joint coordinates, each
stage's heat, one thermal scale, and `stored`, the usable work available before
the first stage. `Sustains N` says the ledger was never overdrawn up to `N`.
`sustains_totalWork_le`, `totalHeat_le_stored`, `entropy_reduction_le_stored`
and `horizon_le_of_cost` are the four consequences: a sustained run has drawn at
most its store, its reservoirs received at most the store plus the system's
energy drop, the joint entropy it removed is bounded by the same quantity, and
`N` stages each costing `c` require `N * c ≤ stored`. Sustained operation is
therefore a claim about replenishment, and nothing here makes one.

`ContinuingAgent` composes the loop on the joint state `R × Env` with the
parameter `W` fixed: the readout drives `actuate`, which moves the environment;
`sense` reads the environment the action moved and `update` writes the register;
`reset` prepares the environment for the next episode. The three stages run in
that order, three-periodically, on one evolving law. The fences are signatures:
neither `update`, `readout` nor `sense` takes the parameter, and `reward` enters
no channel. `Chain.activeBound_of_continuing` puts a funded stage in the active
node at its store allowance, and `continuing_stage_activeBound` discharges it
for the witness's first cycle, without identifying that allowance with the
register ledger's erasure heat.

`Examples/ContinuingAgent.lean` uses five bit-valued types and a three-bit joint
state (parameter, register and flag), every primitive channel mass
`1/4` or `3/4`, so every stage heat is a rational multiple of `log 3` or
`log (5/3)`. The mass form is transported through the cycle exactly, giving the
agreement map `a ↦ 65/128 + a/128` with the flag returned to `1/4` and
independent at every completed reset: the register's agreement with the unknown
rewarding action is at least `65/128 > 1/2` after every cycle of the mathematical
protocol, and successive cycle laws differ. The finite store funds only a
prefix of that protocol. On those same laws the first cycle costs
`(15/32) log 3 + (1/16) log (5/3)` and every cycle at least
`(3/16) log 3 + (1/16) log (5/3)`, the learning stage's `(1/16) log (5/3)` being
independent of what the agent has learned and the reset's heat strictly
positive. The declared store `4 log 3` funds every prefix of the first cycle and
cannot fund 22 complete cycles. Blinding the observation leaves reward at chance
and the learning stage free; replacing the reset by idle drift leaves the flag
at `17/32` instead of `1/4` and lowers the second cycle's reward from
`8385/16384` to `4157/8192`.

Two conclusions are narrower than first proposed, and the narrower ones are what
is proved: the store bounds *expected* work at every prefix and carries no
battery along a trajectory, and the reset control still learns — it is the
reward comparison, not saturation, that makes the reset load-bearing. Both are
recorded in `tasks/lessons.md` and stated in all three documents.

The red specifications failed before the declarations existed. The full
`lake build` has zero warnings; the default axiom audit covers 3,408
declarations in 55 modules with only `propext`, `Classical.choice` and
`Quot.sound`, and the explicit headline checks agree. All pre-commit hooks pass
under `uv --project simulations` at the repository root, as do the 143 existing
Python tests. No Python, dependency, reference, macro or simulation result
changed.

The article gained a paragraph and its budget equation and a rewritten E34 row,
the supplement a subsection with two displayed equations and a Table S1 row, and
the primer a subsection and a summary row. The rebuilt article, supplement and
primer have 45, 40 and 84 pages against 44, 39 and 82, with no overfull boxes.
The 58-page arXiv submission compiles from its unpacked archive and passes
manifest freshness. `git diff --check` passes.

Out of scope and still open: preparing the initial law, a microscopic or
pathwise model of the store and its replenishment, a separately implemented
sensor memory and its erasure, fabrication of the readout and the actuator,
optimal-policy convergence, unbounded horizons, and any cortical
identification. The first is now its own ledger item; the remaining agency gaps
are that item, the register ledger's own premises, and local content agreement.
Specification and execution record: `tasks/continuing_agent.md`.
