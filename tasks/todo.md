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

None of these overturns a headline claim. Every one of them is a place where a
referee who recomputes will find the manuscript saying more than the artifact
supports, which is precisely the failure mode the whole project is organised
against.

## How this ledger is ordered

**By effort, ascending.** A-items are prose or reference edits against numbers
already in the repository. B-items add a derived quantity to an existing report
script and read it from a saved summary — no production sweep reruns. C-items
need a rerun of an existing sweep at new parameters. D-items need a new design.
R-items are the carried-forward research programme and sit after D because they
are unbounded, not because they rank below it. P-items are submission mechanics
and are last only because two of the three are blocked on someone else; the
third is now gated on A1 and A2.

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
6. **A correction is not a retraction of the result.** In every case below the
   direction of the published finding survives; what changes is the reference it
   is measured against or the cause it is assigned to. Do not weaken a
   conclusion further than the evidence requires, and do not strengthen one
   because a correction turned out to be small.

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

- [ ] `supplementary.tex:469` says "the slow ramps recover the square-root
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

- [ ] The four $\beta_{\rm eff}$ values are presented as one quantity at four
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

- [ ] `supplementary.tex:464` reports delays 0.0619, 0.1947, 0.2341 at
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

- [ ] `supplementary.tex:427` reports a critical decay length of 0.0140 mm and
      says "its boundary lies about sevenfold below the band's 0.1 mm lower
      limit". Grid spacing is $2.0/128 = 0.015625$ mm, so 0.0140 mm is **0.90
      lattice spacings**, and every sampled point in the transition region
      (0.0078–0.0147 mm) is below one cell. The boundary is set by the choice
      `side=128, extent=2.0` and would halve on a 256² sheet, so the sevenfold
      margin has no resolution-independent content.
- [ ] The same summary shows steady order **0.9427 to four decimals at every
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

- [ ] `main.tex:183` gives an operational crossing at $K_{\rm eff}/D$ between
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

- [ ] `main.tex:196` rests the specificity of the descent on a random arm "of
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
- [ ] The learning rate 0.2 was selected by a one-seed sweep on seed 20260906,
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

- [ ] `main.tex:177` reports that at $K = 2.8$ the steady mean order is 0.67735
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
- [ ] `dynamical_selection.py`, `dynamic_ramp.py` and `propagation_of_chaos.py`
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

- [ ] `estimate_growth_rate` fits $\log \bar r$ from `transient = 1.0` up to
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

- [ ] B4 establishes that the reported critical decay length is 0.90 lattice
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

- [ ] B5 establishes that the crossing bracket $[1.857, 2.110]$ contains $K_c/D
      = 2$. A linear refinement of `epsilon_grid` between those two points on the
      three existing seeds would either separate the crossing from 2 or show it
      is not separable at this $N$.

**Completion:** the refined sweep is run and the crossing is reported with a
bracket the grid supports. A result indistinguishable from $K_c$ is the more
interesting one and must not be presented as a failure of the run.

---

## D — New design required

### D1 — A plasticity control matched on cumulative deformation

- [ ] B6 records that the matched-norm random arm ends 10× less deformed than
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

**Scope:** this does not bear on the conservation-law argument
($\sum_i v_i$ is conserved under symmetric coupling, so minimising $\sum_i v_i^2$
equalises drift, which rewards between-cluster coupling), which is analytic and
independent of every control. The manuscript's strongest form of the negative
result rests on that argument and on the within-over-between ratio, not on the
random arm.

### D2 — Scope the generality of the plasticity negative result

- [ ] The abstract's "away from the structure it is asked to learn" and
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
      after the last prose edit. **A1 and A2 are now prerequisites**, and this
      item is no longer a formality: the audit found one wrong numeral and two
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
- The four recorded leaf modules are terminal and are not re-litigated per pass.
- The `.venv` console scripts embed an absolute interpreter path; after moving or
  renaming the checkout run `uv sync --reinstall` in `simulations/` before
  trusting a green pre-commit run.

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
