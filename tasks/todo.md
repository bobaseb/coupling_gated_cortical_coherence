# Working ledger

**Superseded ledgers are read out of git history, not kept in the tree**
(AGENTS.md §5). The M/W/X/Y/Z/G ledger — publication alignment, the winding
state, the amplitude field, the winding rows' scope limits, conditional-to-
falsifiable, and the cover and the region — closed in full, is
`8d8ce0f:tasks/todo.md`. The P submission-readiness items and the pass records
before it are `dde1a36:tasks/todo.md`. The R research programme (R1–R12) is
live in `tasks/research_programme.md`.

## U — Physical unity: a human-consciousness requirement current AI lacks

**Intent.** The paper the author wants (2026-09-25). Thesis: unity of
conscious content requires that agreement between local descriptions be
*physically enforced* — continuously maintained by a coupling whose transients
act on the content dynamics — not merely *computed*. Human cortex plausibly
meets this; current AI hardware (clocked, barrier-synchronized digital
computation) does not, because its logical level is causally closed and
screens off the medium that produces agreement. This recovers the first
draft's claim (`c3def4f:main.tex` abstract: GPUs "disqualified … due to broken
thermodynamic feedback loops") as a stated premise with consequences, rather
than an assertion the formalism was asked to derive and could not.

**Constraints.** The exclusion rests on an added premise and must say so.
The C-block audit ("the net proved advantage of an analog medium is
approximately zero") and `Phase9_EMIdentification` (E56–E89 is
substrate-neutral) stand: nothing routed through the existing conditional
chain can exclude a digital claimant, so the new premise is a separate,
named necessary condition, not a consequence of E56–E89. Fix the criterion
*before* checking where GPUs fall, and state what would make a digital system
pass. The criterion is necessary for unity, not sufficient for consciousness.
AGENTS.md rules apply (references verified online, generated macros, Table S1,
tracked PDFs, no changelog prose).

**Success criteria.** A position/theory paper whose premise is stated in its
first page; two new results (typical-case agreement bound, closure
incompatibility theorem) proved or numerically established; an interventional
test that can be run on both a cortex and an AI system and could come out
against the thesis on either.

- [ ] **U0 — Decide the vehicle.** New paper vs repurposing this manuscript;
  venue; relation to the NoC submission (N19: submit the trimmed paper as the
  technical companion, or fold it in). Draft a two-page outline with the
  definitions and the target theorems before any writing.
  *Outline drafted 2026-09-25: `tasks/physical_unity.md`.* New manuscript in
  `unity/` (author confirmed), the current paper frozen (not archived:
  five gates and the README/index links depend on it) and posted as the
  companion. Open for the author: directory name, venue, companion's
  destination.
  *Decided 2026-09-25:* the companion goes to arXiv now in its full technical
  form (not N19-trimmed), under arXiv's default non-exclusive licence, as a
  priority record; its journal is left open (NoC permits preprints — declare
  the preprint on submission and add the DOI afterwards; check any other
  venue's policy before submitting). NoC is the natural venue for the U
  paper, so sending the companion there too is disfavoured but not excluded.
  The U thesis is not staked by the companion (§5 covers only part of it):
  post U as its own preprint once U7 is settled.
  *2026-09-25:* `unity/main.tex` skeleton committed with premise P on page
  one and three `\claim`s (margin theorem; kernel width sets the decay and
  only a σ<2 tail bounds it — the U3 restatement, chosen over dropping the
  kernel result; interventional tests). Gated from the first commit:
  `check-claims` (hard), `check-prose` and `check-pdf-freshness` now cover
  it, and `unity/main.pdf` is tracked though not yet linked. No numerals or
  citations yet: U3's numbers enter as generated macros with the section
  that reports them, citations after online verification.

Spatial agreement beyond the worst-case chain:

- [x] **U1 — Typical-case agreement bound via effective resistance.** At
  identical frequencies the model is a gradient system; the stationary
  density is `∝ exp(Σ K_ij cos(θ_i−θ_j)/D)`. In the harmonic approximation
  it is Gaussian with precision `Laplacian_K / D`, so
  `Var(θ_a−θ_b) = D·R_eff(a,b)` with `K_ij` as conductances, and expected
  content discrepancy `≲ L·√(D·R_eff)`. Replaces hop count (V-block Route B,
  worst case, attained by a phase gradient) with resistance; distinct from
  V4 (locked configuration, spectral gap). Decide Lean vs numerical;
  non-harmonic rigour needs correlation inequalities (Fröhlich–Spencer 1981
  for low-noise 2D XY — verify).
  *Done 2026-09-25: split.* The harmonic identity stays numerical (U3's exact
  Fourier sum against the nonlinear sheet); it is Gaussian algebra and a Lean
  proof would need multivariate Gaussians with a degenerate precision for no
  new content. What holds without the approximation is proved in
  `Phase10_AgreementResistance.lean`: variational `conductance` (least energy
  at unit drop), `conductance_mul_sq_le_energy`, Rayleigh monotonicity
  `conductance_mono` (a tail added to any kernel never hurts),
  `le_conductance_of_edge` (a direct coupling caps `R_eff` at `1/K_ab` at any
  distance) and `integral_dist_sq_le` (Lipschitz encoder: mean-square content
  discrepancy ≤ `L²` × mean-square phase difference, any distribution).
  Witnesses `Examples/AgreementResistance.lean` §39: a three-site series row
  with conductance exactly ½, raised to ≥ 1 by a direct edge. Recorded leaf.
  `unity/main.tex` §reach states the three facts; Limitations narrowed to the
  harmonic identity and the numerical log growth. Not done: the
  non-harmonic monotonicity of `⟨cos(θa−θb)⟩` in the couplings (Ginibre's
  inequality for plane rotators — verify before citing) would carry
  `conductance_mono` beyond the harmonic regime; Fröhlich–Spencer not needed
  for any current claim.
- [x] **U2 — The kernel's tail is what the field buys.** 2D short-range
  coupling: `R_eff ~ (1/πk) ln d`, agreement degrades logarithmically, reach
  `~ a·exp(πkε²/(L²D))`; Mermin–Wagner forbids true long-range order.
  Power-law tail `K(r) ~ r^−(2+σ)`, `σ < 2` (volume-conducted dipole field
  `~1/r²`): bounded `R_eff`, distance-independent agreement. Frequency
  heterogeneity sharpens this: with short-range coupling phase sync has lower
  critical dimension 4 (Hong et al. *PRL* 2007 — verify). Gives the field
  hypothesis a role about kernel *shape*, not strength. Falsifiable: measure
  the effective kernel's tail exponent.
  *Lean half 2026-09-25* (`Phase10_AgreementResistance`): the short-range side
  is proved without the harmonic approximation. `conductance_le_shell`
  (Nash-Williams: shells in series, coupling reaching at most one shell, give
  conductance ≤ `1/Σ 1/C_k`) and `conductance_mul_log_le` (crossing coupling
  `C_k ≤ c(k+1)`, the planar perimeter law, gives `R_eff ≥ log(n+1)/c`): on a
  sheet, bounded-range coupling cannot give distance-independent agreement,
  and the slope `c` grows with the kernel's width (U3(c)). Witness §39: the
  shell bound is attained on the series row. Not proved: the σ<2 side
  (bounded `R_eff`) needs a flow/Thomson construction over a multiscale path
  family; it stays numerical (U3). *Prose 2026-09-25:* §reach states the
  shell bound and the log lower bound; Limitations narrowed to attainment and
  the σ<2 side. U3's numbers in §reach as generated macros
  (`simulations/unity_macros.py` → `unity/unity_results.tex`, from
  `summary.json` and `resistance.json`, drift test `test_unity_macros.py`).
  Cited 2026-09-25: the dimension-4 phase result is Hong, Park & Choi 2005
  *PRE* 72, 036217 (the 2007 *PRL*, Hong–Chaté–Park–Tang, is about frequency
  entrainment); Mermin–Wagner 1966 and Fröhlich–Spencer 1981 in §reach.
  Ginibre 1970 verified only at abstract level (plane rotators covered) and
  not cited.
  *σ<2 side 2026-09-25* (`Phase10_AgreementResistance`): not a flow but its
  potential-side dual. `one_le_conductance_of_chain`: for site sets
  `{a} = S₀, …, S_m = {b}` with coupling ≥ `κ_k` between consecutive sets, the
  drop `u a − u b` telescopes through the sets' means, each level's drop² is
  ≤ `2E/(κ_k #S_k #S_{k+1})` (Cauchy–Schwarz over the pairs), so
  `R_eff ≤ 2(Σρ_k)²`. `le_conductance_of_geometric` (`ρ_k = A q^min(k,m−1−k)`,
  `q<1`: `C ≥ (1−q)²/(8A²)`, length-free) and `le_conductance_of_powerLaw`
  (sets at scale `2^j` with ≥ `α4^j` sites, coupling ≥ `β(2^j)^−(2+σ)`, `σ<2`:
  `C ≥ (1−q)²α²β/8`, `q = 2^−(2−σ)/2`). As for the perimeter law, the planar
  geometry (disc site counts, pair distances) is a hypothesis, not a lattice
  construction. Witness §39: the series row as a three-level chain with σ=0
  gives `1/512 ≤ ½`. Prose: §reach paragraph after the log bound; σ=3's
  growing resistance now cited (`uFarSigmaThree*`, added to
  `unity_macros.py`); Limitations narrowed to the geometry hypothesis,
  attainment of the log and the σ≥2 growth. Closed.
- [x] **U3 — Numerical check first.** Read discrepancy (phase difference /
  chord) vs distance from the saved sheet summaries if they hold it; else run
  a short-range vs power-law-kernel sheet comparison (separate command, not a
  macro regeneration). Logarithmic vs linear growth decides whether U1–U2 are
  worth building.
  *Done 2026-09-25* (`simulations/unity_agreement.py`, summary in
  `figures/unity_agreement/`). The saved `spatial_kernel` runs could not
  answer it (heterogeneous frequencies, one snapshot), so a new
  identical-frequency sheet: 64² and 128², kernels nearest-neighbour,
  exponential (decay 2 sites), `r^−3` (σ=1), `r^−5` (σ=3), equal row sum
  K=4, D ∈ {0.1, 0.4, 1.2}. Verdict:
  (a) **No linear growth anywhere** at identical frequencies. Short-range
  discrepancy grows as `ln d`; the linear chain bound's worst case is a
  phase gradient, not what noise produces. U1 is worth building.
  (b) **The harmonic formula holds in the ordered phase**: measured /
  `D·R_eff` is 1.0–1.15 at D=0.1 and 1.1–1.26 at D=0.4 (anharmonic
  softening, rising with D). At D=1.2 the nearest-neighbour sheet is past
  its BKT point (≈0.9 at K=4): chord `⟨1−cos⟩` → 1 by 16 sites.
  (c) **U2 needs restating: width, not only tail.** The log coefficient is
  `D/(π s)` with stiffness `s = ½ Σ K(r) x²`; the exponential kernel's `s`
  is 24.9 against 1 for nearest-neighbour, so it grows 25× slower
  (`R_eff` 0.531 → 0.549 → 0.558 at side 128/512/1024) but still grows. Only
  the σ<2 tail is bounded (0.580 → 0.577 → 0.577), i.e. has infinite
  stiffness. At finite cortical extent the practical difference between a
  wide short-range kernel and a σ<2 tail is one factor of `ln(d/w)`. The
  same width sets the order–disorder crossover: at D=1.2 exponential and
  σ=1 both stay ordered (chord ≈ 0.45–0.50, flat), σ=3 nearly disorders
  (0.92). U2's falsifiable measurement therefore needs the kernel's second
  moment as well as its tail exponent, and "the tail is what the field
  buys" holds only asymptotically.
  Not tested: heterogeneous frequencies (Hong et al. 2007 lower critical
  dimension claim), which is where linear growth and U4 would come in.
- [x] **U4 — Relative-phase encoders.** Show encoders reading phase relative
  to the local gradient make travelling waves / windings harmless to content
  agreement (the worst case of the linear chain bound).
  *Lean done 2026-09-25* (`Phase10_RelativePhase`, recorded leaf): sites an
  additive group, phases an additive group (ℝ or `AddCircle`); `relRead` is
  the stencil read relative to the site's own phase; `IsWave` a constant plus
  an additive map (gradients, travelling waves, windings on a torus/ring).
  `relContent_eq_of_wave`: every relative encoder reports one content at
  every site of a wave; `dist_relContent_le`: for wave + departure `η`, a
  Lipschitz relative encoder's discrepancy is ≤ `L(‖relRead η x‖+‖relRead η y‖)`
  — independent of gradient and separation. Witness §40: a winding on
  `ZMod m` where the absolute encoder disagrees at every pair of sites and the
  relative one nowhere; a gradient on ℤ with absolute discrepancy `|δ||x−y|`.
  *Prose 2026-09-25:* §reach, last paragraph. Closed.
- [x] **U5 — Carry the honest costs.** E78 (one oscillator per content patch)
  still applies; the ephaptic amplitude objection remains — a long-range tail
  helps only if its conductance is not negligible against the short-range
  part; harmonic approximation fails above the BKT transition.
  *Prose 2026-09-25:* all three in Limitations.

The causal lens:

- [ ] **U6 — Define physically enforced agreement.** Micro dynamics
  `x ↦ f(x)`, regions with micro states `x_i`, content coarse-grainings `π_i`.
  *Closed*: `π∘f = g∘π`. *Margin*: each `π_i` locally constant on an open
  operating set `M` kept by the dynamics (not everywhere: on a connected
  micro-state space that makes `π_i` constant). *Graded dependence*: `π_j∘f` not locally constant in `x_i` for
  overlapping `i ≠ j`. *Physically enforced*: graded dependence plus
  contraction of overlap discrepancy under sub-threshold as well as logical
  perturbations. Full statement of premise P in `tasks/physical_unity.md`.
  *Prose 2026-09-25:* §enforcement defines closure, margin, graded
  dependence, contraction and physical enforcement as in
  `Phase10_PhysicalUnity`. May reopen under U18.
- [x] **U7 — Target theorem: the margin excludes enforcement.** The first
  formulation ("closure excludes enforcement") is false: a GPU running a
  consensus algorithm or a Kuramoto simulation has a closed logical level
  whose `g` contracts discrepancy. Revised: if every `π_i` is locally
  constant, no sub-threshold perturbation of one region changes any content
  anywhere, so graded dependence and hence P fail. P is thereby an explicit
  rejection of functionalism about unity (a perfect field simulation fails
  it); the paper must say so and answer the simulation objection directly.
  Lean-sized; lands beside `Phase6_Locality`.
  *Theorem proved 2026-09-25:* `Phase10_PhysicalUnity.lean` —
  `not_gradedDependence_of_margin`, `not_physicallyEnforced_of_margin`, and
  `not_physicallyEnforced_of_bits` (margin discharged for any finite word of
  thresholded continuous quantities via `hasMargin_threshold`,
  `HasMargin.pi`). Stated on an operating set `M`, not everywhere (see U6).
  Witnesses `Examples/PhysicalUnity.lean` §38: a non-constant bit, and a
  diffusive pair whose agreement is physically enforced at every state.
  Recorded in `ALLOWED_LEAVES`: the conditional chain is substrate-neutral
  and must not rest on P. *Prose 2026-09-25:* §enforcement states why the
  criterion sits below the content dynamics (content-level contraction is
  computable) and answers the simulation objection by denial, as a premise
  with testable consequences. Closed.
- [ ] **U8 — The unity window.** Lower bound: agreement cannot arrive before
  the causal cone allows (`not_reconstructs_of_outside_past`, C8
  quantitative deadline). Upper bound: disagreement decays at the relaxation
  rate (spectral gap / `R_eff`, U1). Unity requires a nonempty window at the
  content's time scale.
  *Lean done 2026-09-25* (`Phase10_UnityWindow`, recorded leaf; it consumes
  `Phase6_Locality`, whose leaf exemption is therefore removed):
  `mem_ball_of_reconstructs` (lower edge, the cone deadline read forward),
  `disc_iterate_le` / `disc_iterate_le_of_log_le` (upper edge: contraction κ
  reaches ε by `log(d₀/ε)/log(1/κ)` steps), `le_disc_iterate` /
  `lt_disc_iterate_of_lt_log` (no earlier than the slowest rate ρ allows).
  Witness §41: a halving map meets the edge exactly (≤1 at step 3, >1 at 2).
  Not proved: rate = spectral gap or ∝ 1/`R_eff`; that is linear response and
  stays in the text. *Prose 2026-09-25:* §window states both edges;
  Limitations carries the linear-response identification. *Estimate
  2026-09-25* (`simulations/unity_estimates.py` → `unity/unity_estimates.tex`):
  deadline 18–31 ms over 15 cm fibres at 4.9–8.8 m/s plus 0.5 ms; against a
  400 ms integration window and a declared tenfold reduction, the window is
  open if the relaxation time is ≤ ~160 ms. Open: the cortical relaxation
  time itself is unmeasured (the companion's rate-calibration problem).
- [x] **U9 — Field causal-cone signature.** A quasi-static field's cone is
  not the synaptic one: re-agreement between distant regions after a
  perturbation faster than axonal conduction plus synaptic delay would
  indicate non-synaptic coupling. Estimate magnitudes; assess measurability.
  *Prose 2026-09-25:* §tests, with the sourced 18–31 ms deadline and the
  quasi-static field (Gratiy et al. 2017). Open: measurability (can
  re-agreement be timed at ms resolution across that distance).
  *Assessed 2026-09-25 (literature, refs Crossref-verified):* the deadline
  was wrong — a causal bound needs the *fastest* axons (Caminiti 2009: up to
  20 m/s), giving 8 ms over 15 cm, not the 18–31 ms median arrival; §window
  and §tests corrected (`coneMaxMs`). Physics sets the scale: fields peak
  2.36 mV/mm (Fröhlich 2010), detection 0.14 mV/mm (Francis 2003), potential
  ~r^−2.1 (Rebollo 2021) → a local source's field reaches detection within
  ~3.7 mm and misses it by ~5 orders at 15 cm (declared peak distance 1.5 mm;
  `unity_estimates.py`). So the test runs at mm separations (Rebollo's
  cross-cut synchronization); at cm P predicts synaptic re-agreement. Timing
  measurable intracortically: artefact blinds the first ms (Keller 2014),
  volume conduction scales like the artefact (Prime 2020); template
  subtraction (Trebaul 2016), MUA/CSD (Kajikawa 2011), per-subject
  tractography deadline (Caminiti 2013). Closed.
- [x] **U10 — Agreement-as-attractor test on both substrates.** Perturb one
  region (cortex: stimulation; AI: activation patching of one layer/head/
  position) and measure whether agreement with its overlap partners is
  restored and at what rate. Specify the outcome that would count against the
  thesis on each substrate.
  *Prose 2026-09-25:* §tests. Cortex: unchanged decoded content in the
  partner region counts against P. AI: a graded, agreement-directed shift
  driven by an analog perturbation inside every bit's margin counts against
  the thesis. Closed.

Pitfalls to address in the text:

- [x] **U11 — Anti-gerrymandering.** State what passes: analog, in-memory or
  neuromorphic hardware with physical coupling and no barriers. The claim is
  about substrate organisation, not biology.
  *Prose 2026-09-25:* §ai (crossbars, oscillator arrays, neuromorphic chips
  pass or fail by readout; tissue on the same terms). Closed.
- [x] **U12 — Over-inclusion.** Coupled pendulums satisfy the criterion; it is
  necessary for unity, not sufficient for consciousness.
  *Prose:* Limitations. Closed.
- [ ] **U13 — Leakage.** GPUs are not perfectly closed (floating-point
  reduction-order nondeterminism, thermal throttling). Make the criterion
  quantitative: the physical variables must carry content-relevant agreement,
  not content-uncorrelated noise.
  *Lean done 2026-09-25* (`Phase10_PhysicalUnity`):
  `exists_threshold_of_gradedDependence` (graded dependence of a bit word
  occurs only with some bit exactly on its threshold), `HasMarginRadius` with
  `content_eq_of_lipschitz` and `bits_eq_of_lipschitz` (under an L-Lipschitz
  micro dynamics, one-region changes below `δ/(L·Lv)` move no bit — the scale
  leakage must exceed). Witness §38: graded dependence at the threshold, and
  the scale is sharp (a change of exactly 1 flips the bit). Reduction-order
  nondeterminism is a logical-level variation, not graded dependence, and the
  theorems do not speak to it. *Prose 2026-09-25:* §ai, leakage paragraph.
  *Estimate 2026-09-25:* expected supply variation is 0.24 of a textbook
  inverter's static noise margin (Rabaey et al. 2003). L and Lv for real
  hardware are not estimated; the ratio alone is stated.
- [x] **U14 — Position against related work** (verify each online, AGENTS.md
  §4): Rosas, Mediano, Seth et al. on computational/causal closure ("software
  in the natural world") — closest formal neighbour, and they read closure as
  the mark of emergent computation, the opposite of U7's reading; Seth's
  biological-naturalism argument on conscious AI; "mortal computation"
  (Hinton 2022; Kleiner & Ororbia); IIT's hardware argument; McFadden's CEMI
  (closest ally); Mermin–Wagner; Fröhlich–Spencer; Hong et al. 2007.
  *Done 2026-09-25:* §related, every reference verified online (Crossref
  and publisher/arXiv). Kleiner & Ludwig 2024 (*NoC*, "dynamical
  relevance") is the closest neighbour and reaches a related exclusion;
  Rosas et al. 2024, Ororbia & Friston 2023 and Findlay et al. 2024 are
  still arXiv preprints and cited as such.

Human evidence for P:

- [x] **U15 — Dissociate graded coupling from information flow.** Human data
  can falsify P but not confirm it against functionalism: anaesthesia and
  split-brain remove graded coupling and information flow together. Design a
  manipulation that moves one with the other held fixed — candidate: weak
  tACS shifting inter-regional coherence while a measured information-transfer
  quantity (e.g. transfer entropy between the regions) stays matched, testing
  whether the excess-agreement statistic follows coupling or information.
  Assess feasibility; if no dissociation is possible in principle, the paper
  says P is a commitment with falsifiable consequences, not a finding.
  *Prose 2026-09-25:* §tests, the matched-transfer-entropy tACS design with
  the outcome for each direction. Open: feasibility (can coherence be moved
  at matched transfer entropy in practice).
  *Assessed 2026-09-25:* tACS design fails. Dual-site tACS is a common drive
  (synchrony without coupling); coherence follows communication (Schneider
  2021); Reinhart & Nguyen 2019 moved synchrony and directed flow together;
  scalp fields ~0.5–0.8 mV/mm (Huang 2017, Opitz 2016) vs ≥1 mV/mm in rats
  (Vöröslakos 2018); Lafon 2017 no intracranial entrainment; artefacts
  (Noury 2016). Replaced in §tests by a bridge across an interrupted
  connection through an analog vs a quantized closed loop, noise-matched in
  transfer entropy: only the analog loop couples gradedly (the margin theorem
  applied to the apparatus). Possible in principle; animals give decoded
  agreement, reported unity needs a bridged human preparation (Limitations).
  Closed as a design; running it is outside the paper.
- [x] **U16 — Split-brain as a possible dissociation.** Behavioural
  disunity after callosotomy is disunity of access; whether the phenomenal
  field divides is contested (Pinto et al. 2017 *Brain*, "divided perception
  but undivided consciousness"; de Haan et al. 2020 *Neuropsychol Rev*;
  Bayne 2010 switch model — verify all before citing). If phenomenal unity
  survives removal of the main information route, that approaches the U15
  dissociation, carried by residual graded subcortical coupling. Two catches:
  (a) the subcortical routes also carry information, so the argument needs
  unity preserved out of proportion to residual information flow — a
  quantitative bandwidth argument; (b) fields are far too weak across
  hemispheres at centimetre scale, so this supports graded coupling of any
  kind, not fields. State P accordingly and demote U2 from carrier of unity
  to one route among several.
  *Prose 2026-09-25:* §tests, split-brain paragraph (Pinto 2017, de Haan
  2020, Bayne 2010 switch model as a rival, not established). Closed.
- [x] **U17 — Declare what counts as evidence about phenomenal unity.** If
  behavioural disunity can be set aside as mere access, P is shielded from
  every result. Before any test is run, name the observations that bear on
  the phenomenal field (e.g. Pinto-style cross-field responding, reports of a
  unified field) and commit to accepting them against P. The paper's own
  tests measure decoded agreement, which is access-like; say how they relate.
  *Prose 2026-09-25:* §tests, last paragraph: cross-region integrative
  responding and reports of one field, declared in advance, accepted against
  P in both directions. Closed.
- [x] **U18 — Categorical content has a margin too.** The margin theorem
  (U7) applies to any readout locally constant off a threshold, and many
  human contents are: rivalry (one percept or the other), categorical
  perception, any argmax-decoded category. Off its boundaries such a `π_j`
  is locally constant in micro state, so P as stated in U6 can deny unity to
  humans for the same reason it denies it to GPUs. Spikes are thresholded
  events as well; the text must say why spike timing and sub-threshold
  potentials count as graded where clocked bits do not. Candidate
  resolutions: state P on graded content variables (location, orientation,
  timing), or on the micro-level dependence upstream of categorisation, with
  categorical percepts read out of an enforced graded state. Decide before
  the U paper is posted; may reopen the U6 definitions. This is the first
  objection a philosopher raises, and it fits in one post.
  *Decided 2026-09-25: carriers.* P is restated on the graded content
  variables categories are read from (location, orientation, time, relative
  strength of competing percepts); a category meets P through its carrier.
  Lean (`Phase10_PhysicalUnity`): `HasMargin.comp`,
  `GradedDependence.of_comp` (a category depends gradedly only through its
  carrier) and `not_gradedDependence_iterate_of_bits` (every function of a bit
  word, at every horizon `n` whose successor keeps bits off threshold, has no
  graded dependence: the voltages beneath the bits are no carrier, so the
  restatement opens no route for a GPU). Witness §38
  `category_of_enforced_carrier`: the sign of the diffusive pair's enforced
  quantity has no graded dependence off its boundary. Prose: P in
  §intro restated; §enforcement "Categorical contents" paragraph; §ai spike
  paragraph (spike *timing* is the graded carrier; a clocked latch is a
  threshold on transition time, `hasMargin_threshold`, so the clock is a
  margin in time); §tests decodes a graded variable, not a category. U6's
  definitions unchanged: the Lean predicates already take any readout, and a
  carrier is one. Not formalised: which variables count as content (the
  decodability cover decides, as for any content); a carrier could otherwise
  be gerrymandered as the raw micro state.

Relation to the companion (raised 2026-09-25):

- [ ] **U19 — State the E78 → U1 bridge in both papers.** The companion's
  worst-case bound (coherence → content, `L√(2N(1−r²))`) runs out at
  millimetres, leaving centimetre-scale agreement to the bridge assumption
  E78; the U paper's typical-case bound (effective resistance) reaches any
  distance, but only with a kernel tail slower than `r^−4`. One sentence in
  each introduction so the pair reads as one program. Companion side goes in
  its v2 (U20).
  *Blocked 2026-09-25:* the unity side needs a citation of the companion,
  which has no arXiv identifier yet; write both halves once it is posted.
- [ ] **U20 — Companion v2 when the U paper posts.** (a) Cite the U paper.
  (b) Scope `main.tex` §gpu "These results rank no architecture family, imply
  no general inferiority of GPU hardware and settle no question of machine
  experience" explicitly to *this article's* results, so it cannot be quoted
  against the U premise. (c) Present the extracellular field as one
  realization of graded coupling (U16), not a competing claim. Rebuild PDFs
  and the arXiv bundle per AGENTS.md §6–7.

## H — Gates against hedging

**Intent.** The article's hedging is structural, not lexical. On 2026-09-25
`check_hedging.py` reported 0 flagged hits on `main.tex` and a scope density
of 3.3 per 1000 words, while the manuscript carries a scope clause in nearly
every paragraph: "supplies no", "is stipulated", "in a specified model",
"remains a modelling obligation", "declared", "neither … nor". The existing
patterns catch reviewer-English softeners ("arguably", "somewhat") that this
prose never uses. Wording regexes cannot fix that; the gate has to constrain
*where* disclaimers may appear and require *positive claims* to exist.

**Constraints.** TDD: failing fixture tests first, as for the existing
`check_*.py` gates. No allowlist (AGENTS.md §5 reasoning). Hard gate on the U
paper from its first commit; advisory on the current `main.tex` and
`supplementary.tex`, whose form is frozen. `uv`, `ruff`, strict `mypy`,
`vulture`, `xenon` < 10 as for every script here. Wire into
`.pre-commit-config.yaml` and describe in AGENTS.md in the same commit.

**Success criteria.** A draft of the U paper written in the current
manuscript's register fails the gate; one that states claims first and
confines limitations to one section passes. The current `main.tex`, run
advisory, reports its disclaimer count and positions.

- [x] **H1 — Widen the disclaimer lexicon to this project's dialect.** Add the
  structural forms: `(supplies|establishes|derives|identifies|constructs|
  settles|measures|implies) no`, `no (result|theorem|cortical|physical|
  measured) …`, `is (stipulated|an interpretation|an assumption)`, `remains a
  (modelling|…) obligation`, `requires (independent|separate|additional|its
  own)`, `in a (specified|declared) model`, `neither … nor`, `not yet`.
  Calibrate on `main.tex` and report precision on a hand-labelled sample
  before trusting the counts.
- [x] **H2 — Limitations live in one place (hard, U paper).** Scope
  disclaimers are allowed freely in the section labelled `sec:limitations`
  and at most one per section elsewhere. A result that needs a scope clause
  states it once, in its theorem statement, not again in every paragraph
  that uses it.
- [x] **H3 — Claims first (hard, U paper).** The introduction carries a
  numbered claim list (a `\claim{}` macro or `enumerate` under a labelled
  paragraph); each claim is cross-referenced to the section that argues it.
  The gate fails if the list is missing, empty, or a claim has no
  cross-reference. The abstract may contain no disclaimer from the H1 lexicon
  beyond one sentence.
- [x] **H4 — Disclaimer-to-claim ratio (advisory, both papers).** Report
  disclaimers per numbered claim and per section, with the worst sections
  listed, so drift is visible on every commit even where no hard rule fires.
- [x] **H5 — Keep honesty auditable.** A disclaimer removed from the running
  text must survive in `sec:limitations` or in a theorem's statement; the
  gate cannot check meaning, so the AGENTS.md entry states the rule and the
  review checklist asks it. The point is to move qualification, not delete
  it.

### 2026-09-25 — H1–H5 built

- **H1.** `SCOPE_DISCLAIMER` gained the structural forms. Hand-labelled every
  `main.tex` match: new patterns 27/29 correct (misses: "neither … nor" stating
  the paper's own negative result). Bare `cannot` (6/12) and `rather than`
  (5/13) were mostly claims — tightness, contrast — and were narrowed to their
  scope continuations. Final lexicon on `main.tex`: 43/45 (96%) precise;
  density 3.3 → 4.3 per 1000 words.
- **H2–H4.** `simulations/check_claims.py`, hook `check-claims`; hard on
  `unity/main.tex` (passes while absent), advisory on the companion. `\claim`
  is taken from the introduction, i.e. the first `\section`.
- **H5.** AGENTS.md §10 states the move-don't-delete rule and the reviewer's
  question. No separate review checklist exists in the repo; §10 is it.
- **Advisory on the current manuscript.** `main.tex`: 46 disclaimers in 16
  sections, no `sec:limitations`, no claim list; 9 sections over the limit —
  Discussion 8, Self-representation 7, cortical hypothesis 7, Introduction 5,
  Compatibility 5, formal composition 4, observations 4, Coherence 2, abstract
  2. `supplementary.tex`: 145, worst Table S1 section 27, reflexive topology
  19. The companion is frozen in form, so nothing was rewritten; the U paper
  must pass hard from its first commit.

### 2026-09-25 — H gates applied to `main.tex`

The author asked for the gate on the current manuscript, which supersedes the
"advisory, form frozen" constraint above for `main.tex`; the supplement stays
advisory. Before: 46 disclaimers, 9 sections over the limit, no
`sec:limitations`, no claims. After: 39, of which 28 in Limitations and at most
1 elsewhere, six `\claim`s; `check-claims` is hard on `main.tex`. The drop of 7
is merges inside Limitations plus three results restated positively; an audit
of the before/after disclaimer lists mapped every moved item to a Limitations
sentence. Open: the supplement's 145 (Table S1 section 27, reflexive topology
19) if the author wants it held too; the primer was not touched.

## N — Neuroscience of Consciousness submission

**Intent.** Prepare a Research Article for *Neuroscience of Consciousness* that
states the framework's contribution to consciousness research in testable
terms. Keep thermodynamics and GPU implications in the article as short,
qualified passages; put derivations and implementation detail in the
supplement.

**Constraints.** Make the scientific corrections before shortening or
reframing the article. Keep claims at the level supported by the proofs and
data: synchrony is not itself an experiential measure, and the model does not
establish a consciousness criterion. Follow the generated-results,
reference-verification, Table S1, and tracked-PDF rules in AGENTS.md. Use
small, reviewable commits; no new production sweep is a prerequisite for
this submission track.

**Success criteria.** The article identifies its distinct theoretical result,
states an operational route to testing content and self-model predictions,
and gives readers a clear account of what the empirical demonstration does
and does not show. Manuscript and supplement meet the journal's current
format and length rules, agree with each other, and pass repository gates.

- [x] **N1 — Resolve the reconstruction-map limitation.** Check the
  fixed-map reconstruction argument against the diameter bound
  `d(s,t) ≤ 2ε/(1-Λ)` when one `Λ < 1` Lipschitz map reconstructs every state
  within `ε`. Decide whether the theorem applies to a restricted state
  family or requires an input-conditioned map. Update the formal interface,
  manuscript claim, and Table S1 together; add a failing test or proof
  obligation before any code or Lean implementation change.

- [x] **N2 — Tighten the phase-content bound and its interpretation.** Use
  `Σᵢ|zᵢ-m|² = N(1-r²)` to check the pairwise estimate
  `|zᵢ-zⱼ| ≤ √(2N(1-r²))` and propagate the encoder Lipschitz factor.
  Compare this with the currently reported bound and reassess how much
  content difference a high-coherence patch can still carry. Update the
  Lean result, article, supplement, and claim map if the tighter statement
  changes the published conclusion.

- [x] **N3 — Recheck the EEG observation and numerical provenance.** Pass
  perfectly phase-locked rotating signals and noisy spatial fields through
  the same filter, Hilbert, montage, and 100 ms pooling pipeline used for the
  reported statistic; compare instantaneous and pooled coherence. Recheck
  the Bessel-function relation and quadratic-variation interpretation.
  Reconcile the six-versus-eight subject description, 61-bipolar-versus-62-
  scalp channel wording, and provenance of the reported 0.542 ceiling.
  Revise claims and generated publication macros from saved artifacts as
  needed; do not regenerate macros by rerunning a production sweep.

- [x] **N4 — Rewrite the article around its consciousness contribution.**
  State what is new relative to standard synchrony and field accounts, and
  distinguish coherence, content reconstruction, and self-model claims.
  Specify an observable comparison that could disconfirm the proposed link
  to conscious content; state that the present EEG analysis is a measurement
  check rather than an experiential validation. Revise title, abstract,
  introduction, discussion, and limitations accordingly. Verify every new
  reference online before adding it.

- [x] **N5 — Retain concise thermodynamics and GPU passages.** Give each
  topic approximately one article paragraph. For thermodynamics, separate
  the proved cost of changing order from the conditional installed-energy
  estimate and state the thermal-conversion assumptions. For GPU comparison,
  identify the particular reconstruction task, deadline, and rank premise;
  avoid claims of general GPU inferiority or machine experience. Keep
  derivations, hardware assumptions, and sensitivity analysis in the
  supplement, cross-referenced from the article.

- [x] **N6 — Complete the journal-fit and submission audit.** Recheck the
  current *Neuroscience of Consciousness* Research Article instructions,
  including the article word limit, abstract limit, and significance
  statement, then prepare the required components. Trim repeated exposition
  in the supplement while keeping enough methods and proof detail to audit
  the claims. Resolve any mismatch between the article's requirements and
  the supplement's count. Run the relevant repository checks, rebuild tracked
  PDFs with source changes, and refresh the assembled arXiv submission if
  present.

### N7–N16 — Mock *Neuroscience of Consciousness* review (2026-09-24)

A mock referee report recommended major revision. The items below are its
action points. N7 closed in the same pass and N8–N16 on 2026-09-24, N18 later
the same day and N17 on 2026-09-25. Open: N14b (optional, new work) and the
author's
decision whether to split the awakening/ephaptic material into a separate
paper (see the N14 record).

- [x] **N7 — Factual and presentation fixes.** The Data availability subject
  list named six subjects (including `1056`, which was never analysed) against
  the eight in `empirical_collapse.MULTI_SUBJECTS`; it now lists all eight.
  The notation table gave `$D$` a wrong defining location and an unlabelled
  second meaning; it now points at Eq. (1) and labels the phase spread as the
  supplement's convergence-proof usage. `$T$` now points at §6 and §5, where
  it is used. E78 and E89 now point to Table 1 at their first mention
  before it. The AI disclosure in `main.tex`, `index.html` and `README.md`
  adds Claude Opus 5.5 (Claude Code) and GPT-6 Sol (Codex).

- [x] **N8 — Engage the synchrony-critique literature.** The point that
  synchrony does not fix content predates this work (binding-by-synchrony
  critiques, e.g. Shadlen & Movshon, *Neuron* 1999). Cite and position
  against it. State exactly what the formalization adds beyond the informal
  argument; the core results are elementary: gluing uniqueness, Banach,
  triangle-inequality and pigeonhole bounds. Verify every reference online.

- [x] **N9 — Spatial overlap versus content overlap.** The sheaf is over a
  spatial substrate, but the cup example is overlap in *content* between
  distant regions (E78 concedes this in one clause). A disjoint cover
  satisfies compatibility trivially, and columns are rejected as the content
  cover, so no principle currently selects a cover. Either recast the
  construction over content variables with regions as partial decoders, or
  state in the abstract and Discussion that the unity correlate has no
  operational definition yet.

- [x] **N10 — Remove the accuracy confound from the disconfirming test.**
  Two accurate decoders agree automatically: their disagreement is at most
  the sum of their errors. Reported stimuli are usually decoded better, so
  "more agreement on reported trials" follows from single-region fidelity.
  Match per-region decoding accuracy (or signal strength) as well as phase
  coherence, and add a condition that separates inter-region agreement from
  each region's fidelity. Move no-report designs from caveat into the main
  design. Consider a schematic figure of the experiment.

- [x] **N11 — Self-reconstruction condition.** The fixed contraction (E89)
  reconstructs only a bounded-diameter family, a single state at zero error.
  Either formalize the input-conditioned map the text says is needed, or
  demote the minimal-self claim accordingly. Derive or explicitly flag the
  stipulated `Λ = e^{-(K-2D)τ/2}`. Argue the link to Gallagher's
  pre-reflective self rather than asserting it, and compare with existing
  self-model accounts.

- [x] **N12 — Say where the content bound is vacuous.** The √N bound is
  informative for at most `\wavePatchInformativeSites` sites, so the bridge
  E78 carries the whole positive coherence-to-content link. Say so in the
  abstract and Conclusions.

- [x] **N13 — Keep the speed limit; move the thermodynamic chain.** The
  paper concedes that every edge is supplied and that only the final
  contraction-to-uniqueness step infers anything. E12–E45 ("vacuum
  manifold", "register") are opaque to the readership and unconnected to the
  consciousness argument: move that chain, its Landauer/register ledger and
  the active-branch bound to the supplement. Keep one article paragraph
  built on the proved current-cost bound
  `∫σ_J ≥ [arcsin r(τ) − arcsin r(0)]²/(Dτ)`, framed as a speed limit: a
  fast change in coherence has a minimum cost growing as `1/τ`, which bears
  on ignition-like transitions and on recovery latency. State its thermal
  conversion assumptions as now. Reduce the installed-energy condition to
  one sentence beside it (necessary energy price; no cortical `κ`). Cut
  Table 1 to the edges the article argues from (E56–E89) and leave the full
  eight-edge chain to the supplement's table. Coordinate with
  `check-table-coverage`, `check_tableS1.py` and the E78/E89 references
  added in N7.

- [x] **N14 — Tighten the scope; keep and reframe the GPU section.**
  Consider splitting the awakening/ephaptic material (extracellular
  geometry, onset protocol) into a separate paper. Shorten the ramp
  paragraph and figure, given that the fitted exponent's CI excludes 1/2 and
  no common exponent is claimed. Keep the GPU section and change what it
  claims: a digital system is where the three conditions can be measured
  today, with full state access and exact interventions. Open with what a
  claim of unity or self-representation for such a system commits its maker
  to; position against the indicator-properties approach to AI
  consciousness (Butlin et al. 2023 — verify online before citing). Keep the
  causal-mask deadline result as the lead technical content. Move the
  synthetic rank-two task to the supplement.

- [ ] **N14b (optional) — Run the protocol on a real model.** Fit decoders
  for one shared quantity on two separate parts of a real model (layers,
  heads or token positions), test their agreement and whether
  reconstruction survives intervention. This would be the only place the
  proposed measurement is actually carried out. Optional: needs hardware
  not currently available; a small open model on rented or CPU compute is
  the cheapest route. New work, not a condition of the revision.

- [x] **N15 — Move the EEG exercise to the supplement.** It establishes only
  that the pooled bipolar estimand cannot measure spatial coherence; keep a
  one-sentence methods caution in the article.

- [x] **N16 — Readability and journal structure.** Gloss "section",
  "restriction resonance" and "Lipschitz" on first use. Reduce double
  negatives and hedging density. Say where Methods live for a theoretical
  article (journal expects a Methods/Results structure). Add the cover-
  selection limitation to the abstract.

- [x] **N17 (stretch) — Rebuild the sheaf over content variables.** Recast the
  construction with regions as partial decoders: the base is the set of
  content variables, a region's domain is the variables decodable from it
  (the decodability cover of `sec:unity`), restriction forgets variables. Prove
  gluing uniqueness and the approximate-selection result on that cover, and
  say which spatial-measure results do not transfer. Would let the article
  drop "the formal results are stated for spatial covers".

- [x] **N18 (stretch) — Input-conditioned reconstruction map.** Formalize a family
  `F_u` indexed by input, each contracting with its own fixed point `s_u`, and
  state what replaces the fixed-map diameter bound
  (`Encoding.dist_le_of_contracting_reconstructs`) — presumably a Lipschitz
  condition on `u ↦ s_u` plus uniform contraction. Guard against the
  degenerate witness (constant `F_u` returning a stored `s_u`), which
  reconstructs everything and encodes nothing; the code-separation criterion
  must still bind. Would let §6 restore a minimal self that follows a scene.

### N19–N37 — Second mock *Neuroscience of Consciousness* review (2026-09-25)

A second mock referee report recommended major revision. Its core finding is
that the article is two papers and only the synchrony-versus-content one is
for this journal's readers. These items apply to the current manuscript;
the author has since named the physical-unity paper (U block) as the paper
they want, so decide first (N19) whether this manuscript is trimmed and
submitted as the technical companion or folded into U.

Major:

- [ ] **N19 — Split or trim.** Cut the main text to §§2, 4, 6 (compressed),
  7.1, 7.5, 9; move §3 (threshold, speed limit, installed energy), §7.2–7.4
  (ramps, winding, plasticity), §8 (extracellular geometry, `K_eff`,
  awakening protocol) and §5 (digital candidate) to the supplement or a
  separate paper. Compress §4.2 (√N bound, chaining, E78) to one paragraph
  stating once that across cortical distances the coherence-to-content link
  is an assumption. Supersedes the open split decision in the N14 record.
  *Deferred 2026-09-25 (U0):* the arXiv posting is the untrimmed paper; do
  this only if a journal version is prepared.
- [ ] **N20 — Develop the excess-agreement test.** Generative simulation
  showing the fidelity-matched excess-agreement statistic separates
  shared-content, shared-upstream-noise and coherence-driven models at
  realistic trial counts, with a power estimate. Specify the coherence band,
  the error-stratum matching, and the near-chance problem for unperceived
  trials (stratification may leave a small, unrepresentative subset). Name a
  concrete paradigm/dataset (e.g. masked orientation with laminar or ECoG
  recordings in two orientation-coding regions).
- [ ] **N21 — Discriminate from global workspace broadcast.** Ignition and
  broadcast also predict correlated errors on seen trials. State what
  compatibility predicts that broadcast does not, or narrow the claim to
  counting against "content tracks coherence". Sharper version: decode the
  *perceived* value, not the stimulus value, and predict both regions' decodes
  shift toward the subject's misperception (illusion, after-effect,
  continuous report).
- [ ] **N22 — Missing measurement literature** (verify each online, AGENTS.md
  §4): informational connectivity (Coutanche & Thompson-Schill 2013;
  Anzellotti & Coutanche 2018 *TICS*); information sharing / wSMI (King et
  al. 2013 *Curr Biol*); communication subspace (Semedo et al. 2019
  *Neuron*) where data-driven shared directions are excluded; noise
  correlations change with attention (Cohen & Maunsell 2009). Add attention
  as a matched variable or covariate in §9.2.
- [x] **N23 — Label the error-covariance step as a bridge assumption.** No
  result connects exact/ε-compatibility to correlated errors; "two regions
  describing one content should err together" is an added hypothesis. Name
  it (a fifth bridge edge or an explicit premise of the test).
- [ ] **N24 — Say what the sheaf buys over the content cover.** On the
  decodability cover gluing reduces to merging mutually consistent partial
  functions. State what the sheaf formulation adds, or develop the
  probabilistic case (decoded content is a distribution; Abramsky
  contextuality).
- [ ] **N25 — Self-reconstruction: develop or demote.** Under E89 the
  correlate constrains one self-state; `Λ` is stipulated from a linearization
  about a different state; the Gallagher mapping is structural; the self-model
  test has the attention/fidelity confounds of N22. Either construct a
  physical `F_u` with a matched test, or reduce §6/§9.1 to a marked
  conjecture.
- [ ] **N26 — Readability.** Put 3–4 positive claims as numbered statements in
  the Introduction; collect limitations once in the Discussion; drop E-labels
  and Lean vocabulary from running text (keep Table 1); shrink the notation
  table with the material N19 removes.

Minor:

- [x] **N27** — Abstract: the 10-site / 0.312 mm figures depend on the chosen
  0.1 mm decay length and patch order; mark illustrative or remove.
- [ ] **N28** — §9.2 rivalry: there is always a percept and "decoding error
  relative to the stimulus" is undefined for the suppressed eye. Specify the
  adaptation or keep masking only.
- [ ] **N29** — §9.2: define error-stratum matching (continuous or binned,
  number of strata).
- [x] **N30** — §4.2 (`main.tex:255`): "informative for at most 10 sites"
  assumes `L = 1`; state it.
- [ ] **N31** — §3.2: cite thermodynamic/Wasserstein speed limits (Shiraishi,
  Funo & Saito 2018 *PRL*; Dechant; Ito — verify). No value of `C` is given,
  so no floor is computed: say so or cut the ignition/anaesthesia sentence.
- [ ] **N32** — Replace the 8-subject EEG exercise with the constructed-signal
  demonstration alone, or explain why empirical data are needed.
- [ ] **N33** — Move §5 (digital candidate) to the supplement for this
  article (content migrates to U).
- [ ] **N34** — Word count: confirm with the editorial office whether the
  notation table counts (moot after N19).
- [ ] **N35** — Replace the Methods paragraph (`main.tex` ~l.110) with a short
  formal Methods section: Lean toolchain, axiom audit, simulation code and
  seeds.
- [x] **N36** — Reference audit of 2025–26 items (e.g. `corberi2026` arXiv ID)
  given the AI-use statement.
- [ ] **N37** — Remove the installed-energy box from Fig. 1 with N19; cut
  Conclusions to about three sentences.

### 2026-09-25 — Pre-arXiv accuracy pass (N23, N27, N30, N36)

The items that must be right in a permanent posting, ahead of the rest of the
second review. **N30:** the premise was wrong — the site count compares the
phase chord `√(2N(1-r²))` with 2 and is independent of `L`, as the supplement
already said; `main.tex` said the bound itself "is a chord", now "`L` times a
chord … whatever the value of `L`". **N27:** §4.2 names the sheet, the 0.1 mm
decay length and patch order the count and reach are read at, and says they
move with both; the abstract says "one simulated cortical sheet". **N23:** the
error-covariance link is stated as a premise of the comparison in §9 and in
Limitations (Formal scope). **N36:** all ten 2025–26 references checked against
Crossref and the arXiv API: all correct, including `corberi2026`
(arXiv:2609.04732); `bajwa2025` gained its DOI.

### 2026-09-24 — N1 fixed-map diameter limit

`Encoding.dist_le_of_contracting_reconstructs` proves that one fixed
`Λ < 1` map with reconstruction error at most `ε` across a relevant family
restricts every pair in that family to distance at most `2ε/(1-Λ)`.
The article, supplement and Table S1 state this limit beside the code-count
criterion. A full-substrate identity readout illustrates resonance and exact
reconstruction, but has Lipschitz factor one on a nontrivial metric space and
does not discharge E89. A broad state family requires a separately specified,
possibly input-conditioned map; no such map or physical readout is constructed
here.

### 2026-09-24 — N2 phase-content bound tightened

`sum_normSq_sub_order_parameter` proves `∑ₖ|zₖ−m|² = N(1−r²)`, and
`chord_sq_le_of_coherence` gives `chord² ≤ 2N(1−r²)`. `cos_gap_le_of_coherence`,
`chord_le_of_coherence`, the patch, winding and nerve forms and the Phase5
compatibility residuals now carry `√N`, not `N`. The antiphase pair attains
the bound, and one antiphase oscillator among `N` shows the order is sharp.
The saved wave summary is unchanged. Regenerated macros give a patch bound of
15.3 L (still vacuous), at most 10 informative sites, and a 20-diameter
(0.312 mm) nerve reach. The article, supplement, Table S1, primer and
CHANGELOG state the sharper bound, and the published conclusion holds
qualitatively.

### 2026-09-24 — N3 EEG observation and provenance

`eeg_pipeline_check.py` passes constructed signals through the reported
bipolar/filter/Hilbert/100 ms pipeline. A perfectly locked 10 Hz rotation
gives pooled `r ≈ 1e-4`, `a ≈ 4e-4` and zero Bessel residual; centring each
sample recovers `r = 1`. The bipolar montage cuts a κ = 4 field's
instantaneous resultant from 0.89 to 0.06. The filtered phase's
squared-increment rate changes 37× across steps, so the QV rate `2D` needs an
observation model. The Bessel relation `a = Kr/D`, `r = I₁/I₀` checks against
the zero-flux Fokker–Planck solution. Provenance: 0.542 was a stale
hard-coded range. `OBSERVED_CONCENTRATION_RANGE` is now the saved 0.087–0.142,
with a drift test. The design ladder keeps its own declared
`LADDER_CONCENTRATION_RANGE`, and `\designObservedMax` is renamed
`\designLadderConcentration`. The pooled estimand has 61 bipolar pairs, not
62 sites. Every source says eight subjects; no six-subject wording remains.
No recording was re-read and no sweep rerun.

### 2026-09-24 — N4 consciousness framing

The title, abstract and introduction now lead with the distinct result:
phase order does not establish shared content or a self-model, and three
separable conditions say what additionally does. The introduction places the
work against binding-by-synchrony, communication-through-coherence and field
accounts (`singer1995`, `fries2015`, verified online). The Discussion opens
with a disconfirmable comparison: decoded overlap agreement on reported versus
unreported trials at matched coherence, plus a self-model analogue. It ties
the minimal self to `gallagher2000` (verified) and closes with explicit
limitations. Synchrony is not an experiential measure, no consciousness
criterion is claimed, and the EEG analysis is a measurement check.

### 2026-09-24 — N5 thermodynamics and GPU passages condensed

The article's digital-candidate section is now one paragraph. It names the
linear rank premise, one synthetic two-view task and its held-out numbers, and
the causal-mask deadline, and it disclaims architecture ranking, general GPU
inferiority and machine experience. The thermodynamics section, renamed
"Resource premises and composition", opens with one paragraph. That paragraph
separates the proved order-change current bound from the conditional
installed-energy condition and states the thermal-conversion premises
(physical flux, reservoir temperature, local detailed balance). The composition
subsection and Table 1 stay. Removed article text moved verbatim, with its
labels, to the head of the matching supplement sections: current cost,
spectral bottleneck, predictive memory and feedback, and learning/repeated
operation. There is also a new `sec:supp-gpu` subsection. Supplement cross-refs
now resolve natively. Every macro is still cited, and the article is about 8,400
words by `detex`.

### 2026-09-24 — N6 journal fit and submission audit; N block closed

Checked the current *Neuroscience of Consciousness* instructions online:
Research Articles are limited to 9,000 words, abstracts to 250 words, and the
significance statement is ~120 words and unpublished. Data availability, funding,
CRediT roles, ORCID and at least five suggested reviewers are also required.
The article is ~8,000 words by `detex` and the abstract ~227. A Conclusions
section is added for the required-sections list. `submission/neuroscience_of_consciousness.md`
holds the limits table, a draft significance statement and draft CRediT
roles. Open for the author: suggested reviewers, confirming the CRediT roles,
confirming the theory-article section structure, and the editable-format
upload. Supplement trim: the only repeated exposition found by shingle
comparison was the second derivation of the three routes off the population
count, now cut to the sheet-specific numbers. Hypothesis counts ("eight")
agree across article, supplement and primer. The PDFs and `arxiv_submit/` are
rebuilt (101 pages, compiled from the tarball).

### 2026-09-24 — N8 synchrony-critique positioning

The introduction now cites the temporal-binding critique (`shadlen1999`,
verified online: *Neuron* 24(1), 67–77) as the older source of the point that
synchrony does not fix content. It names the core results as elementary
(gluing uniqueness, Banach, triangle inequality, pigeonhole) and states what
formalization adds: the √N rate and the population at which the bound becomes
vacuous, the fixed-map diameter limit, the code count, and a complete premise
inventory with a joint witness.

### 2026-09-24 — N12 where the content bound is vacuous

The abstract and Conclusions now say that the √N coherence-to-content bound
constrains at most `\wavePatchInformativeSites` sites at the simulated sheet's
patch order, so for cortical-size populations the positive link from
coherence to content is the bridge assumption E78, not a derived result.

### 2026-09-24 — N9 spatial overlap versus content overlap

Took the second option: state the gap rather than rebuild the sheaf. §4 now
says the sheaf's overlaps are spatial while the cup example's are overlaps of
content, sketches the content-variable recasting (regions as partial decoders,
overlap = a commonly estimated variable) as the route, and says no result is
stated for it. The abstract, the Discussion's unity subsection and the
limitations paragraph say that no principle selects the cover, so the unity
correlate has no operational definition yet. Recasting the Lean sheaf over
content variables is not attempted; it would be new work.

### 2026-09-24 — N10 accuracy confound removed from the disconfirming test

§`sec:full-test` now states the confound as Eq. `agreement-decomposition`
(`|d_A−d_B| ≤ |e_A|+|e_B|`, and at matched marginal error agreement differs only
through the error covariance). The design matches phase coherence *and* each
region's decoding error (or signal strength), and its statistic is excess
agreement over a fidelity-matched null that pairs decodes across trials within
a stimulus and error stratum. Trials are classed by a no-report marker
(`tsuchiya2015`, verified online: *TiCS* 19(12), 757–770), report-based
classes are secondary. Shared upstream noise is named as the remaining
non-specificity, with an upstream-region comparison. The self-model analogue
matches scene-variable accuracy. New schematic Figure `fig:test` (TikZ); the
abstract states the matched design.

### 2026-09-24 — N11 self-reconstruction demoted, Λ flagged, self link argued

Took the demotion route; no input-conditioned map is formalized. §6 now says
Λ is stipulated, borrowing the uniform density's first-harmonic growth rate
(a rate about a different state from the one `F` acts on), and that under E89
the minimal-self correlate is a condition on one self-state; a self that
follows a changing scene needs a family `F_u` with its own fixed points, not
constructed. The Discussion argues the Gallagher link from two structural
features (perspective built into the scene ↔ fixed point read through part of
itself; immediacy ↔ no higher-order state) and compares with self-model theory
(`metzinger2003`, verified: MIT Press 2003) and interoceptive inference
(`seth2013`, verified: *TiCS* 17(11), 565–573). Formalizing `F_u` remains
possible future Lean work but would be close to trivial without a physical
readout.

### 2026-09-24 — N13 speed limit kept, thermodynamic chain moved

The article's installed-energy subsection moved verbatim, with its labels
(`sec:installation`, `eq:microscopic-kernel`, `eq:installed-coupling-bound`), to
the head of the supplement's installation section. The "Resource premises and
composition" section's thermodynamic paragraph, active-branch bound
(`eq:active-chain-bound`), composition paragraphs and the full eight-edge table
(now `tab:edges`) moved to the head of `sec:supp-composition`. In their place:
§3 gains `sec:speed-limit`, one paragraph on
`∫σ_J ≥ [Δ arcsin r]²/(Dτ)` (Eq. `speed-limit`) framed as a `1/τ` cost floor /
minimum duration for a current budget, bearing on ignition-like transitions
(`dehaene2014`) and recovery latency, with the thermal-conversion premises and
a one-sentence installed-energy price (no cortical κ). §7 is now "The formal
composition": one paragraph and Table 1 cut to E56–E89. Figure 1's box and
caption, the roadmap, notation rows and the primer's overview follow. Macro
suites, `check_tableS1.py` and `check_table_coverage.py` pass.

### 2026-09-24 — N14 GPU section reframed, ramp shortened

The digital-candidate section ("What the conditions ask of a digital
candidate") now opens with what a unity or self-representation claim commits
a system's maker to, positions against the indicator-properties approach
(`butlin2023`, verified online: arXiv:2308.08708, Butlin, Long, Elmoznino,
Bengio, Birch et al.), says a digital system is where the conditions can be
measured today (full state access, exact interventions) and names the
two-part decoder measurement (N14b) as the direct route. The causal-mask
deadline is the lead technical content; the rank premise follows in one
sentence; the synthetic rank-two task and its macros live only in
`sec:supp-gpu`. The ramp subsection is two paragraphs: the fitted exponent,
its bootstrap interval excluding 1/2, the criterion dependence and no common
exponent. Figure `fig:ramp` moved to the supplement's finite-ramp section,
whose existing prose already carried every moved number.

**Not done: splitting the awakening/ephaptic material into a separate paper.**
That is an authorial scope decision (it would remove §8.2–8.4 and the onset
protocol, and change the title's reach); left open for the author.

### 2026-09-24 — N15 EEG exercise moved to the supplement

The article's "Estimator calibration on exploratory EEG" subsection is gone.
Its numbers and argument were already in `sec:supp-eeg` (design counts,
cross-subject range, pipeline check, linear deviation), so only its closing
paragraph on what an informative dataset needs (intracranial recordings,
`oomoto2026`) moved, to the supplement's Interpretation subsection. The article
keeps one methods caution at the end of `sec:identifiability`: pooled bipolar
phase statistics place a locked signal at `\eegCheckLockedPooledR`, so a
spatial test needs a rotation-removing estimand and a modelled montage.
Macro suites pass.

### 2026-09-24 — N16 readability and journal structure

First-use glosses: sheaf, section and global section open §4; "Lipschitz" is
glossed where `L` is introduced; restriction resonance is defined in words at
Eq. `selfmap`. The introduction's roadmap says where Methods and Results live
for a theoretical article (definitions, proofs and simulations; Table S1 and
the supplement; theorems of §3–6 and controls of §8). Negation-heavy
sentences in §2, §6 and the limitations were turned positive; `check-hedging`
flags nothing. The abstract carries the cover-selection limitation (from N9)
and was rewritten to 247 words by `detex -n` after N9–N12 had pushed it to
~299. Main text is 8,578 words by `detex -n` excluding TikZ (8,621 at N6 by
the same count); the submission notes record the part counts and the matched
design in the significance statement.

### 2026-09-24 — N9/N12 follow-up: decodability cover, 10-site overstatement

N12 had the abstract and Conclusions say that beyond
`\wavePatchInformativeSites` sites the coherence-to-content link "rests
entirely on a bridge assumption". That overstated it: the V-block results
already extend it. `chord_le_of_patch_walk_coherence` chains the bound
through overlapping patches for `\waveNerveHops` hops (`\waveNerveReachMm` mm
of the sheet), and `chord_le_of_frequency_locked` removes `N` for a declared
`λ₂` at a locked configuration. The abstract, §4 and Conclusions now state
all three routes and put E78 where it belongs: across centimetre-separated
territories, beyond the chain's reach, with no measured connectivity for the
spectral route. (The §4 sentence making the same overstatement predated N12.)

N9 said no principle selects the cover. §4 now proposes one: the
decodability cover, in which each region gets the variables decodable from it
above a declared criterion on held-out data, and regions overlap on variables
both decode. It cannot be tuned for agreement, and its non-degeneracy
(connected nerve) is testable. Free inputs (decoder class, criterion,
candidate variables) remain, so the correlate is operational relative to
them. The abstract, Discussion and limitations say so, and the N10 design
selects its two regions by this criterion. Rebuilding the sheaf over such a
cover is N17 (stretch). Abstract 249 words by `detex -n` with macros expanded.

### 2026-09-24 — Rules for the decodability cover's inputs; length trim

§4 now gives a rule for each input of the decodability cover, none of which
consults agreement. Variables: experimenter-manipulated and task-relevant,
fixed before recording; shared-variance methods (CCA-like) are excluded as
selecting for agreement. Criterion: cross-validated decoding above a
permutation null at a pre-registered level, reported over a declared range;
exactness is unnecessary because the N10 statistic is excess agreement.
Decoder class: bounded above (unrestricted decoders make every region overlap
every other) and below by the bound's own requirement of `L`-Lipschitz
encoders; linear readout as explicit information (`dicarlo2007`,
`kriegeskorte2019`, both verified online); decoder and discrepancy metric
chosen by held-out decoding accuracy, citing the author's
`bobadillasuarez2020` (verified: *Comput. Brain Behav.* 3, 369–383). The
residue stated as scope: the cover is the experimenter's.

The additions put the main text at 9,110 words. Trimmed, with the supplement
already carrying the content: the winding linearization and amplitude
condition, the plasticity descent paragraph, the ramp's second paragraph
(repeated in the protocol), the Section 7 cover paragraph and the columns and
support-comparison paragraphs (now pointing to the decodability cover), and
the introduction's repeated result summary. Main text 8,729 + abstract 249 =
8,978 by `detex -n`. Notation rows for the removed winding symbols dropped.

### 2026-09-24 — N18 input-conditioned reconstruction map

Specification: `tasks/n17_n18_lean.md`. `Phase6_ConditionedReconstruction.lean`
adds `ConditionedEncoding` (relevant family, declared `input`, encoder, readout
`U → C → S`). `dist_le_of_conditioned_contracting` replaces the fixed-map
diameter by `(2ε + L·d(u_s,u_t))/(1−Λ)` under a per-input contraction on the
family and an `L`-Lipschitz input dependence; `dist_le_of_same_input` is the
fixed-map limit inside one fibre. `selfState` (Banach on a complete space),
`dist_selfState_le` and `dist_selfState_input_le` are the scene-following
self-states. The degenerate witness is named (`stored`, a `Λ = 0` contraction
reconstructing any family whose state is a function of the input), and the
guard is `card_le_card_codes_fibre` / `dist_le_of_encode_const`: the code
criterion binds within an input fibre only. `Examples/ConditionedReconstruction.lean`
§36: four reals in two scenes, one bit, `Λ = 1/2`, `ε = 3/4`; no fixed
contraction reconstructs it, each fibre attains the fixed-map limit and needs
both codes, the stored readout fails on it, and an affine whole-line
contraction's self-states `u + 3/2` attain the fixed-point bound.

Not done: no physical readout, scene variable or derivation of `Λ`. The
article's §5 states the result in prose and keeps the minimal-self correlate a
condition on one self-state under E89; main-text word count is unchanged
(a sentence of the resonance paragraph was cut). Supplement proof paragraph
and a Table S1 row "A self that follows a scene"; primer paragraph in the
reconstruction part.

### 2026-09-25 — N17 gluing over the decodability cover

Specification: `tasks/n17_n18_lean.md`. `Phase5_ContentCover.lean` adds
`DecodingSetup` (relevant family, true values, region readouts, per-variable
decoders) and `domain θ i`, the variables region `i` decodes within `θ` on every
relevant state. With the discrete topology on the variables, Mathlib's
`presheafToTypes` is the sheaf and `decode_glue_unique` is `sheaf_glue_unique`
verbatim; `decode_glue_value` identifies the glued section with the true content
at `θ = 0`. `decode_compatible` derives `LocalContent.Compatible` at `2θ` from
decodability (the N10 accuracy confound as a theorem). `ContentCover.select_close`
/ `select_dist` restate the weighted selection for signed and vector contents on
any index; `select_decode_near_value` puts it within `θ` of the content.
`exists_exact_decoder_of_injOn` and `not_decodes_of_read_eq` bound the decoder
class. `Examples/ContentCover.lean` §37: three variables, two regions with
opposite offsets `b` on the shared variable; exact domains, cover and connected
nerve for `0 ≤ b < 1/2`, exact gluing to the content at `b = 0`, the `2θ` bound
attained and no exact section at `b = 1/10`.

Not transferred, stated in the module docstring, the supplement and the
article: the measure representation and the `√N` phase-to-content bounds, and
anything relating a region's phase order to what it decodes (E78). The
tolerance is worst-case, idealizing the article's statistical criterion.
Article §4 now states the transfer (word count unchanged); the Discussion and
limitations say the phase-to-content bounds, rather than "the formal results",
are stated for spatial covers. Supplement subsection `sec:supp-content-cover`
and Table S1 row "Gluing over content variables"; primer subsection.

**Gate finding.** `check_leaves.py` passed `Phase6_ConditionedReconstruction`
in the N18 commit because `Chain.lean` spells `map` and `stored`, which resolved
to the new `ConditionedEncoding.map` and `stored`. Renamed to `conditionedMap`
and `storedReadout`; both new modules are now recorded in `ALLOWED_LEAVES` as
deliberate terminal results. See `tasks/lessons.md`.

## C — What a continuous medium buys, and what is electromagnetic about it

**Intent.** Two questions the development cannot currently answer about itself:
what an analog substrate is proved to buy, and which results are about an
*electromagnetic* field rather than about any continuous mean-field kernel. The
audit below answers both; the items turn the answers into theorems and prose.

**Constraints.** Every item is SRR and lands in a module that already carries
what it qualifies, so `ALLOWED_LEAVES` gains nothing. Nothing here widens
`Audit.permitted`. Publication edits are present-tense statements of scope, not
narration of what the development used to claim (AGENTS.md §5).

**Success criteria.** `lake build` passes with the audit's footprint unchanged;
anything reaching `main.tex` has a Table S1 row in the same commit
(`check_table_coverage.py`, AGENTS.md §9); `.lean` edits are followed by
`proof_companion/run.sh extract` then `pdf`; the three tracked PDFs are rebuilt
and `arxiv_submit/` refreshed or removed in the same commit (AGENTS.md §6–7).

### The audit

**Four results touch continuity, and the net proved advantage of an analog
medium is approximately zero.**

| Result | Where | What it establishes |
| :--- | :--- | :--- |
| `fieldCorrelation_sited_eq_zero`, `sited_architecture_below_field_optimum` | `Phase7_Rigidity.lean:224,270` | A kernel on finitely many *points* contributes exactly zero to the continuum functional on an atomless substrate |
| `rigid_is_strictly_suboptimal`, `rigid_gap` | `Phase7_Rigidity.lean:167,180` | An architecture whose *wiring support* misses the best-correlated pair is beaten at matched resource |
| `encard_le_packingNumber_range` | `Phase6_Reconstruction.lean:371` | A continuous code space caps the resolvable family above, by its packing number |
| `winding_degree_obstructs`, `loopWinding` | `Phase5_PhaseLifts.lean:29` | A continuum phase field carries an integer the resultant does not |

Each is weaker than it reads, and two of them are neutralized by controls this
repository supplies itself. `fieldCorrelation_cellKernel`
(`Phase7_FiniteRegion.lean:141`) preserves a finite matrix's total weight and
phase correlation *exactly* under a positive-mass cell embedding, so the first
row is about measure-zero support and not about finiteness —
`Phase7_Rigidity.lean`'s own scope note says the comparison is not
resource-matched and is a statement about which functional a measure-zero
substrate registers in. `no_forced_gap_of_best_wired`
(`Phase7_FiniteRegion.lean:185`) is the control on the second, and continuity
does no work in it either: the operative property is reconfigurable support,
which a crossbar also has. The third is a ceiling and never a floor — it bounds
what a continuum code can resolve and never says the medium supplies it. The
fourth is used only as a negative control on the order parameter.

**The electromagnetic commitment is carried entirely by prose.**
`Phase9_EMIdentification.lean:48` states it: nothing in the development
distinguishes an EM kernel from any other continuous mean-field kernel. All five
fields of `IsEMFieldCoupling` are generic — joint continuity, a probability
substrate, `K` as the kernel's double average, `no_site_dominates`, `D` as the
field's own noise — and the witnesses are the unit interval and a three-site
toy. `no_site_dominates` is the only field with physical flavour, and it is
vacuous on a nonatomic substrate, which is exactly the continuum case the EM
hypothesis is about. EM enters in three places, none a theorem:

1. `K_eff = γ N s E f` (`main.tex:543`) — dimensional bookkeeping with `γ`
   undetermined; `E` is any medium's amplitude.
2. The extracellular-geometry argument (`main.tex:550`) — `α ≈ 0.2`,
   `λ ≈ 1.6`, resistive conduction at 0.3–0.6 S m⁻¹, effective-medium theory
   giving contraction → higher `E` → higher `K`. **This is the only place
   Maxwell enters**, and it is the only EM-discriminating handle in the paper.
3. The Fermi calibration in Table S1's E56 row — mV/mm to ms spike-timing shift.

Everything else transfers verbatim to extracellular ion diffusion, potassium
waves, gap junctions modelled as a density, astrocytic calcium, or a mechanical
or optical medium.

### What a continuous medium buys

- [x] **C1 — The winding sector as protected state.** The cheapest of the four
      and the most nearly proved. `char_is_kuramoto_trajectory` makes a winding
      stationary for *any* isotropic symmetric kernel at identical frequencies;
      `loopWinding_eq_zero_of_hasGlobalLift` and `winding_degree_obstructs`
      make the degree an obstruction the resultant does not see. Missing is
      stability: the degree is integer-valued, so a perturbation that keeps
      every lift transition within a half turn cannot move it, and
      `ringTransition`/`winding_succ` already supply the transitions from the
      state. Lands in `Phase5_PhaseLifts` beside the obstruction, with the
      linear criterion from Y2's `twistedKernel`/`charLambda` where a growing
      mode is at issue. The payoff is a statement the article does not make: the
      medium holds a discrete, perturbation-stable integer with no digital
      element, and a redrawn cover or reweighted sites do not move it.

- [x] **C2 — The capacity floor, to match the ceiling.**
      `encard_le_packingNumber_range` bounds the resolvable family above by
      `Metric.packingNumber` of the codes the encoder writes. The converse
      direction is absent: a region of positive measure at resolution `δ` has
      packing number bounded *below*, growing with volume over `δ^d`. This is
      what converts "a continuum code space is large" from a hand-wave into the
      resource-matched comparison `Phase7_Rigidity` §3 explicitly lacks, and it
      makes `b` in `card_le_two_pow` a physical quantity set by SNR rather than
      a declared one. Lands in `Phase6_Reconstruction` beside the packing
      section; `Mathlib.Topology.MetricSpace.CoveringNumbers` is already
      imported. Scope to state: the floor is about the *code space*, not about
      any mechanism reaching it, and an uncalibrated gain `L` still evacuates
      the bound in the direction the module already records.

- [x] **C3 — No hop structure, so no deadline obstruction.** The strongest
      asymmetry in the paper and currently unstated.
      `not_reconstructs_of_outside_past` (`Phase6_Locality.lean:234`) binds a
      synchronous message-passing network: agreement about a change costs `T`
      rounds along `ball nbhd T v`. A full-support field kernel has no `nbhd` —
      the causal past is the whole substrate at every round — so the
      obstruction has nothing to fire on. `sec:gpu` applies this bound to the
      GPU candidate and never says the field model escapes it, which reads the
      fifth unconditional result in one direction only. Lands in
      `Phase6_Locality` as a statement about a `Network` whose `incoming` is
      total. Scope to state, and it is not small: propagation speed is finite,
      so "escapes" means the delay is below the phase time scale, which is a
      calibration and not a theorem.

- [x] **C4 — The reduction costs no erasure.** `K_mf = ∬ K dμ dμ` is performed
      by the medium as a physical sum over mode occupancies
      (`Phase3_LocalActuator`'s `∑ᵢ cᵢ(z) φᵢ(x) φᵢ(y)`), and it erases nothing.
      `Phase1_PhaseSpaceCapacity`'s third point is already careful that heat
      appears at *erasure* and not at losing history — the joint map that keeps
      the record is injective and dissipates nothing. A digital evaluation of
      the same functional over `N` sites performs `Ω(N)` irreversible
      accumulations, each priced by `landauers_principle`. `Phase3_LandauerBridge`
      and `is_erasure_of_not_surjective` are the pieces. This is the classic
      analog energy-per-operation advantage and it would give the
      installed-energy condition a counterpart with teeth. Scope to state: the
      comparison is between two ways of evaluating one functional, not between
      two ways of being conscious, and it prices nothing until the mode
      decomposition is declared — the same `κ` problem, in the same place.

- [x] **C5 — Decline super-Turing computation, in the publication.** Real-valued
      weights buy unbounded capacity only at infinite precision, and any `D > 0`
      destroys it. The paper's own noise floor is the reason, which makes one
      sentence in `sec:gpu` or `sec:scope` cheaper than the objection it
      pre-empts. Present tense: what the noise regime costs an analog account,
      not what anyone once hoped for it.

### What is electromagnetic, and what is not

- [x] **C6 — Say the development is substrate-neutral.** `sec:unconditional`
      claims substrate-independence for five results; the conditional chain
      E56–E89 is equally substrate-neutral modulo calibration, and
      `Phase9_EMIdentification`'s own scope note says so. Stating it costs
      nothing, widens the audience, and is more accurate than the present
      silence. Lands in `sec:scope`, with the `no_site_dominates` vacuity on a
      nonatomic substrate named where Table S1's E56 row already discusses the
      predicate.

- [x] **C7 — Separate EM falsification from field falsification.** The
      supplement's falsification conditions (`supplementary.tex:1643`) falsify
      *some continuous coupling field*, not an electromagnetic one. The
      conductivity and geometry handle of item 2 in the audit is the only
      EM-discriminating test the framework has, because it is the only place
      Maxwell enters. Say which of the six protocol requirements bear on the
      field hypothesis and which bear on EM specifically, so that a null result
      lands on the right claim.

### What a digital implementation owes

**The exclusion is not available, so the bill is.** `main.tex:619` states it: a
universal exclusion needs a necessary condition for consciousness and a proof
that every relevant implementation violates it, and the composition supplies
neither. `Phase9_EMIdentification.lean:48` closes the other route — E56–E89 is
substrate-neutral, so nothing routed through the conditional chain can exclude a
digital claimant without assuming the conclusion. What is available is the
resource bill: a digital claimant to *these* conditions at cortical `N` and the
phase time scale owes a computable quantity, and the three items below compute
it. Each would be worth proving whichever way it came out, which is the property
that makes it survive a reviewer who does not share the prior.

- [x] **C8 — The deadline bound, quantitative.** The highest value per line in
      the C block and the contrast partner C3 leaves unwritten.
      `not_reconstructs_of_outside_past` (`Phase6_Locality.lean:234`) must be
      *handed* a witness `w ∉ ball N.nbhd T v`; bounded fan-in produces one.
      `card_ball_le`: from `∀ v, (N.nbhd v).card ≤ d`, induction on `ball_succ`
      — `insert v ((nbhd v).biUnion (ball nbhd T))`, so the card is at most
      `1 + d *` the previous — gives `(ball N.nbhd T v).card ≤ ∑ i ∈ range (T+1), d^i`.
      When that sum is below `Fintype.card V` a witness exists and the existing
      obstruction fires: reconstruction by deadline `T` on a degree-`d` network
      needs `T ≳ log_d N`. Read against C3's `not_outside_past_of_isFullSupport`,
      which is `T = 1`, this is the sharpest contrast the development can state
      — one round against `log_d N`, both theorems, one `Network` definition,
      `Audit.permitted` untouched. Lands in `Phase6_Locality` beside the ball
      lemmas.

      *Aim it at the interconnect, not the mask.* `main.tex:615` applies the
      deadline bound to a decoder-only transformer's causal mask, which is where
      it is weakest: position `t` reads every position `≤ t`, so `d` is the
      context length and `log_d N` is about one. The bound has force on the
      *physical* substrate, where interconnect degree is genuinely bounded and a
      model sharded across many devices pays `log_d N` hops for agreement. That
      retargeting is also where this framework insists claims belong — on a
      physical realization rather than on an architecture described abstractly.

      Scope to state: `d` and `N` are declared inputs like the communication
      graph and the deadline already are, the bound is about guaranteed response
      and not about what a particular run achieves, and — the same sentence C3
      needs — a substrate with `nbhd v = univ` models a physical field only while
      transit is short against the phase time scale.

- [x] **C9 — Landauer forced by the memory budget, not chosen by the
      implementation.** C4 as it stands is answerable: `clearingSum` erases
      because it is defined to clear, and `recordingSum` proves the reversible
      reply correct at zero cost. The general lemma closes it by pigeonhole —
      `erasedEntropy_ge_of_card_image_le`, from `(Finset.image t univ).card ≤ m`
      to `erasedEntropy t ≥ log (Fintype.card sys / m)`. This is extraction, not
      new mathematics: `erasedEntropy_clearingSum` (`Phase3_LandauerBridge.lean:412`)
      already performs that computation at one image cardinality through
      `card_image_clearingSum`. With it, any evaluation of the `N`-site sum into
      a register space smaller than the input space is non-injective, hence an
      erasure by `is_erasure_of_not_surjective`, hence priced by
      `temperature_mul_erasedEntropy_le_heat`. The claim upgrades from one
      implementation paying to every implementation within a memory budget
      paying, at a stated exchange rate. Lands in `Phase3_LandauerBridge` §4
      beside C4.

      Scope to state, and it is the whole content: this is a **trade, not a
      barrier**. Memory sufficient to retain every intermediate pays zero, which
      is exactly what `recordingSum_injective` says. The theorem prices the
      exchange between memory and dissipation and closes neither end. It also
      still prices nothing in watts until the decomposition of the field into
      site values is declared — the same `κ` problem, in the same place, as C4
      and the installed-coupling argument.

- [x] **C10 — The interconnect corollary.** Contrapositive of `card_ball_le`:
      meeting deadline `T` across `N` sites needs degree `d ≥ N^(1/T)`, and at
      `T = 1` a full crossbar. One `Finset` argument past C8 and the most
      quotable form of it — the deadline is purchasable, and this is the wiring
      it costs. Scope: it bounds the communication graph a guarantee requires and
      says nothing about what hardware is buildable, which is a separate
      question this development does not model.

**Not claimed here either.** That any of C8–C10 excludes a digital candidate
from consciousness. They price the conditions this framework states, for a
candidate that accepts them; a claimant who denies that experience requires
reproducing these dynamics at this `N` and this time scale is untouched by all
three, and no Lean in this repository reaches that claimant. Writing them as an
exclusion would also lose the reader they are aimed at. Four of the five results
that read as anti-digital in this development are already neutralized by controls
this development supplies — `fieldCorrelation_cellKernel` against the
measure-zero support, `no_forced_gap_of_best_wired` against the rigidity gap, the
packing bound being a ceiling and never a floor, and the winding integer, which a
digital architecture carries as well as a field does. The audit above records
that; C8–C10 are the three that survive it.

**Ordering.** C1 and C3 are the highest value per line — C1 because the theorems
are nearly assembled, C3 because it fixes a real asymmetry in how `sec:gpu`
reads. C2 is the foundation the resource-matched comparison needs and should
precede any strengthening of `Phase7_Rigidity` §3. C4 is independent. C5–C7 are
publication-only and can go in one editorial pass.

C8 supersedes C3 as the highest value per line now that C3 is built: C3 is one
half of a contrast whose other half is unwritten, and C8 is the half that
carries a number. C10 is a corollary of C8 and belongs in the same commit. C9 is
independent of both and should follow C4 closely, because it is the answer to
the first objection C4 invites. C8–C10 are Lean, so none of them is an editorial
pass, and none reaches `main.tex` without a Table S1 row in the same commit —
`sec:gpu` is where C8 and C10 would land, and that paragraph currently aims the
deadline bound at the attention graph rather than the interconnect.

**Not claimed, so that it does not return as an open item.** That an analog
substrate computes *faster*, in any complexity-theoretic sense. Continuous-time
dynamical solving is heuristic and does not survive the noise analysis this
framework already commits to, and nothing in the development is about time to
solution. The four items above are about protected state, capacity, latency
structure and energy per reduction — none is a speed claim, and none should be
written as one.

### 2026-09-21 — C1–C4 built, the Lean half

**C1, `Phase5_PhaseLifts.lean`.** `phaseTurns` unwraps a real phase difference
into whole turns plus a principal part in `[-π, π)`; `ringPhaseTransition` reads
those integers between consecutive ring sites. Three results make the degree an
invariant rather than an artefact. `loopWinding_ringPhaseTransition_relift`: the
loop sum is unchanged by re-lifting any site by any whole number of turns, so it
is a function of the circle-valued field and not of the unwrapping.
`ringPhaseTransition_winding`: below `2|q| < n` the integers read off the phases
are `ringTransition`, so the two routes to the degree agree.
`winding_degree_stable`: move every site by anything strictly inside
`windingMargin n q = π/2 − π|q|/n` and the degree is still `q`, exactly, and the
state still admits no global real-valued phase lift.

*Does not establish.* That the margin is sharp — nothing exhibits a perturbation
just outside it that moves the degree. That a cortical field carries the
integer, or that it is measurable in tissue. The regime is `2|q| < n` and the
margin closes as the winding fills the ring, so a degree turning nearly once per
site is protected against nothing. `windingPerturbed` inhabits the hypothesis
with a state that is not the winding, and `loopWinding_uniform_ne_winding`
exhibits two states of the same ring with different degrees, so the hypothesis
is neither empty nor droppable.

**C2, `Phase6_Reconstruction.lean`.** `measure_le_mul_packingNumber`: a maximal
`δ`-separated family is a `δ`-cover, so `μ A ≤ v · packingNumber δ A` whenever
every `δ`-ball measures at most `v ≠ 0`. `measure_le_pow_mul_packingNumber`
specialises it to a Haar measure on a finite-dimensional real space, where the
ball measure is `δ^d` times the unit ball's and the floor reads as volume over
`δ^d`. `Encoding.measure_le_mul_packingNumber_range` carries the first to the
codes an encoder writes, which is the quantity
`encard_le_packingNumber_range` already bounds the declared family above by.

*Does not establish.* Any mechanism reaching the floor: it is a property of the
code space and the resolution, not of an encoder, a readout or a family of
states. The ceiling's gain `L` is still declared and uncalibrated, so an
unbounded amplifier still evacuates the bound in the direction the module
records. The two bounds meet only once `δ` is a measured noise floor and `L` a
measured gain, and neither is measured here.

**C3, `Phase6_Locality.lean`.** `Network.IsFullSupport`, with
`isFullSupport_iff_incoming_isSome` checking the name against `incoming`.
`ball_eq_univ_of_full`: after one round the causal past of any site is the whole
network. `not_outside_past_of_isFullSupport`: the hypothesis that fires both
`not_reconstructs_of_outside_past` and
`not_resonates_regionReading_of_outside_past` is unsatisfiable at any deadline
but zero, so the deadline obstruction has no instance on a full-support kernel.

*Does not establish.* That a field escapes latency. `nbhd v = univ` models a
physical field only while transit across the substrate is short against the
phase time scale, which is a calibration — conduction speed, diameter,
frequency — and this module measures none of them. The theorem is exactly: given
a network with no neighbourhood structure, this module's obstruction is silent.

**C4, `Phase3_LandauerBridge.lean` §4.** `recordingSum` and `clearingSum`
compute the same register value over `N` sites; the first keeps the site array
and the second clears it. `recordingSum_injective` and
`erasedEntropy_recordingSum`: the reduction destroys exactly zero.
`erasedEntropy_clearingSum`: clearing destroys `N log |Val|`, and
`temperature_mul_le_heat_clearingSum` prices it at temperature times that.
`clearingSum_is_erasure` routes through `is_erasure_of_not_surjective`, which is
where finiteness of the phase space does the work.

*Does not establish.* Anything about two ways of being conscious, or about two
substrates: the comparison is between two evaluations of one functional, both
maps on one finite phase space. The zero on the recording route is the absence
of a Landauer charge, not free computation — a reversible implementation still
pays for the noise floor. And `N log |Val|` prices nothing until the
decomposition of the field into site values is declared, which is the same `κ`
problem as the installed-coupling argument's, in the same place.

**What remains.** C5–C7 are publication-only and untouched: decline super-Turing
computation in `sec:gpu` or `sec:scope`, state substrate-neutrality in
`sec:scope`, and separate EM falsification from field falsification in the
supplement's protocol conditions. None of the four items above is named in
`main.tex`, so `check_table_coverage.py` is satisfied as it stands; naming any
of them there requires a Table S1 row in the same commit.

## D — What bears on a machine candidate as it is built today

**Intent.** `sec:gpu` states its obstructions in prose and instantiates none of
them on the architecture it names. It says the causal mask fixes a region's
causal past "rather than chosen by interpretation" — and no Lean object is that
network, while `Examples/Locality.lean` §25 gives a three-site line the same
status. Three of those obstructions can be theorems about the *deployed*
architecture rather than about digital computation in principle. The target is
not exclusion. `sec:gpu`'s own sentence stands and stays: a universal exclusion
would need a necessary condition for consciousness and a proof that every
relevant implementation violates it, and the composition supplies neither. What
these items buy is that the obligations the section does state acquire a
determinate test and a determinate failure mode.

**Constraints.** Every item is SRR. The network instance lands under
`Examples/`, beside the witnesses it is one of; the channel bound lands in
`Phase6_Reconstruction`, which already carries the counting argument. Nothing
widens `Audit.permitted` and nothing adds to `ALLOWED_LEAVES`. Publication edits
are present-tense statements of scope (AGENTS.md §5).

**Success criteria.** `lake build` passes with the audit's footprint unchanged;
the instance is *checked* to have the causal past the architecture gives rather
than a declared one, per `PhysicsOfConsciousness/AGENTS.md` §2; anything
reaching `main.tex` has a Table S1 row in the same commit; `.lean` edits are
followed by `proof_companion/run.sh extract` then `pdf`; the three tracked PDFs
are rebuilt and `arxiv_submit/` refreshed or removed in the same commit.

### The asymmetry, now that C3 has proved the other half

`not_outside_past_of_isFullSupport` closes the objection that the deadline bound
obstructs this framework's own candidate: on a full-support kernel the
hypothesis firing `not_reconstructs_of_outside_past` is unsatisfiable at any
deadline but zero. That half is proved. The half applied to the machine
candidate is still prose, and it is the half a reader checks.

- [x] **D1 — The causal mask as a `Network`.** The highest value per line in
      this section, and the one `sec:gpu` already claims. Instantiate a
      decoder-only forward pass: `V := Fin P × Fin L` over position and layer,
      `nbhd (t, ℓ)` empty at `ℓ = 0` and `{(s, ℓ-1) | s ≤ t}` otherwise. Prove
      `ball nbhd n (t, ℓ) ⊆ {(s, _) | s ≤ t}` **for every `n`**, which is the
      statement worth having: the causal past does not merely grow slowly, it
      never reaches a later position at any depth. Paired with C3 that is the
      asymmetry stated on both sides — one round reaches everything on a
      full-support kernel, no number of rounds reaches forward under a causal
      mask — and `not_reconstructs_of_outside_past` then fires with an explicit
      `w` the architecture supplies rather than the model declares.
      Scope to state, and it is load-bearing: this is **one forward pass**.
      Across token steps the model does read its own prior output, so the
      theorem says nothing about the autoregressive loop, which is D2's
      subject. A statement that elided the difference would be the overclaim
      this item exists to avoid.

- [x] **D2 — The autoregressive bottleneck.** Everything a model carries about
      its own internal condition from one step to the next passes through a
      sampled token. That is `card_le_card_codes` with `Fintype.card C` the
      deployed vocabulary, and it needs no new machinery — what it needs is the
      statement, and the honest bound. Over `k` steps the alphabet is
      `|vocab|^k`, which is large, so the bound bites on a *single-step*
      self-report claim and not on an extended one. That is still the right
      shape and it is a fact about the architecture as deployed rather than
      about digital computation, which is the distinction this whole section is
      organized around. Lands in `Phase6_Reconstruction` beside the counting
      argument, or as a witness if the vocabulary is made concrete.

- [x] **D3 — Choosing the cover empties the agreement claim.** `sec:gpu` says
      it in prose — "the cover is a choice, and choosing it to secure agreement
      empties the claim" — and a prose claim about what a choice can always
      achieve is exactly the shape that should be a theorem. For any candidate
      and any declared agreement, exhibit a cover on which the agreement holds
      trivially. `IsUniformCover`, `pairCover` and `mean_patch_order` are the
      machinery. Aimed at interpretability claims that nominate attention heads
      or residual-stream subspaces as the parts that agree, and it applies to
      the cortical proposal identically, which is the reason to state it.

- [x] **D4 — The resource-matched comparison `Phase7_Rigidity` §3 lacks.** C2
      supplied the prerequisite floor; this is the thing it was a prerequisite
      for. **The sign of the result is not predictable and this item is not to
      be written as though it were.** Once `b` is a real number the comparison
      may well come out ambiguous, or favourable to the machine candidate. That
      is a reason to do it — a comparison whose outcome is assumed is not a
      comparison — and a reason not to promise in advance what it shows. Note
      that §3's two existing comparisons are neutralized by controls this
      repository supplies against itself (`fieldCorrelation_cellKernel`,
      `no_forced_gap_of_best_wired`), and those controls stay.

- [x] **D5 — Say the asymmetry in the publication.** Once D1 and D2 exist,
      `sec:gpu`'s two middle paragraphs state theorems rather than
      architectural observations, and the section can say which obstruction
      bites where without implying a verdict. Table S1 rows for every
      identifier the article names, in the same commit
      (`check_table_coverage.py`, AGENTS.md §9). The paragraph headed "What is
      not excluded" is unchanged by all of this and should be checked to still
      read correctly beside the stronger middle.

**Ordering.** D1–D3 are built; the dated section below says what they reach.
D4 waits until someone is prepared to publish whatever sign it returns — the
comparison is worth making and its outcome is not to be promised in advance, so
starting it is a publication decision rather than a proof step. D5 is last by
construction and is now unblocked: the two theorems its paragraphs would state
exist.

**Not claimed, so that it does not return as an open item.**

*Exclusion.* No item here approaches one, and none should be written as though
it did. Exclusion needs a necessary condition for consciousness plus a proof
that every relevant implementation violates it. This framework states
conditional relations and has no necessary condition, which is structural
rather than a gap that more work closes.

*An energy no-go from C4.* Reversible computing is a standing counterexample
and §4's scope note already concedes it: nothing says a digital machine must
take the clearing route. C4 prices erasure, not computation.

*A continuity no-go.* Two of the four support comparisons are neutralized by
controls in this repository, deliberately. Strengthening past them means
deleting the controls, which is the one move not available.

*A speed claim.* Unchanged from C's closing paragraph, and it applies here
identically: nothing in the development is about time to solution, and D1's
saturating causal past is a statement about reach, not about latency.


### 2026-09-21 — D1–D3 built, the machine-candidate half

**D1, `Phase6_Locality.lean` and `Examples/Locality.lean` §31.** The obstruction
`sec:gpu` states in prose is now an object. `ball_rank_le` is the general fact:
give the sites a rank that no neighbourhood increases, and the causal past stays
below that rank at *every* depth — not growing slowly, never crossing.
`notMem_ball_of_rank_lt` is the contrapositive, and it is what fires
`not_reconstructs_of_outside_past` at every deadline at once rather than at a
chosen one.

§31 is the deployed architecture: `V = Fin P × Fin L` over token position and
layer, each site hearing from positions at most its own at the layer below. The
neighbourhood is spelled `u.2.val + 1 = v.2.val` rather than with a subtraction,
because `Fin` subtraction wraps; the embedding layer then reads nothing as a
consequence (`mask_nbhd_layer_zero`) instead of by a case split.
`mask_ball_subset_le` is the headline — the causal past of position `t` is inside
`{u | u.1 ≤ t}` for every number of rounds — and `mask_no_guarantee` fires the
deadline bound with the site the mask supplies. Paired with C3's
`not_outside_past_of_isFullSupport`, the asymmetry is stated on both sides: one
round of a full-support kernel reaches everything, no number of rounds reaches
forward under a causal mask.

*Does not establish.* Anything about the autoregressive loop: this is **one
forward pass**, and across steps a model does read its own prior output, which is
D2's subject. Anything about latency — `ball` counts hops and nothing in the
development is about time to solution. And no verdict about a device: whether an
execution is this graph, and at what deadline, are the empirical questions
`Phase6_Locality`'s header already declines. The controls fence the two cheap
ways to be right for the wrong reason: the graph delivers backwards at round one
(`mask_backward_mem_ball`), and on `mask 2 2` a report on an earlier position is
exact at round one (`mask_reads_earlier_position`) while the same instance
rejects forwards at every deadline (`mask_forward_no_guarantee`). What fails
fails by direction, not by a missing path.

**D2, `Phase6_Reconstruction.lean`.** `tokenChannel` names the channel a
self-report claim is about — the code is the token sequence emitted over `k`
steps, because that is what the next step reads — and `card_le_card_tokens` is
`card_le_card_codes` counted in it: a family of relevant states pairwise more
than `2ε` apart and reconstructed to within `ε` is no larger than
`|vocab| ^ k`. `card_le_card_tokens_one` is where it bites, a single step
distinguishing at most `|vocab|` states of the thing reporting;
`not_reconstructs_of_card_tokens_lt` is the usable contrapositive.

*Does not establish.* Nothing about digital computation or about what a model can
compute: it counts one declared channel's codes. Over `k` steps the alphabet is
`|vocab| ^ k`, which is large, so the bound is stated as constraining a
single-step claim and not an extended one. It prices nothing — a cardinality is
not a bit count. And a claim resting on activations rather than on text has
declared a different encoding, to which the same bound applies with that one's
alphabet, possibly the machine's whole state; which channel a claim is about is
the claim's to declare.

**D3, `Phase4_KuramotoDynamics.lean` and `Examples/Phase4.lean` §32.** The prose
claim was that choosing the cover to secure agreement empties the claim, and
`mean_patch_order_singleton` already said the thing it needed: the cover by
single sites reports one on every configuration. Read backwards that is
`exists_isUniformCover_mean_patch_order_eq_one` and
`exists_isUniformCover_le_mean_patch_order` — any declared agreement level at or
below one is available on a legal `IsUniformCover`, whatever the state, so the
existential has no refuting instance.
`order_parameter_zero_mean_patch_order_singleton_char` is the widest gap on one
state: a nontrivial winding has global resultant exactly zero and
singleton-cover agreement exactly one.

*Does not establish.* That patch order is a bad observable. It is the strictly
finer one and on a *fixed* cover it measures the state: §32 exhibits two sites in
antiphase, two legal covers, and the reported agreement zero on one
(`mean_patch_order_bothCover`) and one on the other. What is empty is the
existential, not the observable, and the same reading applies to the cortical
proposal — which is the reason to state it rather than to aim it.

**What remains.** D4 and D5. D4 is the resource-matched comparison
`Phase7_Rigidity` §3 lacks; its sign is not predictable, §3's two existing
comparisons stay neutralized by the controls this repository supplies against
itself, and it is not to be started as though the outcome were known. D5 is the
publication half and is now unblocked. No publication file is touched by this
pass: none of the new identifiers is named in `main.tex`, so
`check_table_coverage.py` is satisfied as it stands, and naming any of them there
requires a Table S1 row in the same commit. `lake build` is clean with no
warnings; the axiom audit covers 5604 declarations in 91 modules, up from 5569,
all resting only on `propext`, `Classical.choice` and `Quot.sound`. The proof
companion is re-extracted and rebuilt.

### 2026-09-21 — C8 and C10 built, the deadline priced

**`Phase6_Locality.lean`.** `card_ball_le` bounds the causal past by
`∑_{i ≤ n} dⁱ` on a graph of fan-in `d`, by induction on `ball_succ`: each round
adds the site itself and multiplies the frontier by at most `d`.
`card_ball_le_mul_pow` reads the same count as `(n+1)·dⁿ`, which is where the
logarithm comes from. `exists_notMem_ball_of_bounded_degree` is the step the
item was about — `not_reconstructs_of_outside_past` has to be *handed* a site
outside the causal past, and until now only an architectural order produced one;
below `Fintype.card V` the count produces one instead.
`not_reconstructs_of_bounded_degree` fires the obstruction with it, so a
guarantee by deadline `T` across `N` sites of degree `d` needs `T` of order
`log_d N`.

C10 is the same count backwards. `card_le_geomSum_of_reaches`: a network whose
causal past at `T` is everything has `Fintype.card V ≤ ∑_{i ≤ T} dⁱ`, so the
deadline is purchasable and this is the wiring it costs;
`le_degree_of_reaches_one` is the `T = 1` case, `N ≤ 1 + d`, the crossbar.

Read against C3's `not_outside_past_of_isFullSupport` the asymmetry is
quantitative on both sides, and the full-support section says so: full support
*is* that crossbar, and `ball_eq_univ_of_full` is the degree bound at `d = N`,
where the count covers the site set at the first round and no witness is left to
pick out.

**`Examples/Locality.lean` §25.** `line_degree` by `decide`, then the same
round-one rejection reached a second way: `line_exists_notMem_one` and
`no_guarantee_at_one_of_degree` produce the site from the fan-in and the site
count alone, where `far_notMem_one` names it. `line_needs_degree_two` runs the
count the other way — three sites at one round need a site of degree two, and
the line has none.

*Does not establish.* Anything about latency: `ball` counts hops, and nothing in
the development is about time to solution. Anything about buildable hardware —
what C10 bounds is the communication graph a guarantee requires, which is a
separate question this development models nowhere. And `d` and `N` are declared
inputs exactly as the communication graph and the deadline already are, so the
bound prices a guarantee under a declared graph rather than measuring a device.
The theorems are about a guarantee across two declared values; a report right
about one fixed world stays right about it at any round, which §25's
`coincidental_at_one` exhibits.

**What remains in this block.** C5–C7 and C9, and the publication half: none of
the identifiers above is named in `main.tex`, so `check_table_coverage.py` is
satisfied as it stands, and naming any of them there requires a Table S1 row in
the same commit. `lake build` is clean with no warnings; the axiom audit covers
5614 declarations in 91 modules, up from 5604, all resting only on `propext`,
`Classical.choice` and `Quot.sound`.

### 2026-09-21 — C9 built, the budget charges instead of the implementation

**`Phase3_LandauerBridge.lean` §4.** The answerable half of C4 was that
`clearingSum` erases because it is defined to clear.
`erasedEntropy_ge_of_card_image_le` quantifies over implementations instead of
exhibiting two: an update whose reachable set fits in `m` states destroys at
least `log (|sys| / m)`, by pigeonhole on the states it fails to reach.
`is_erasure_of_card_image_lt` routes a budget below the phase space through
`is_erasure_of_not_surjective`, where finiteness does the work, and
`temperature_mul_log_le_heat_of_card_image_le` prices it.

`log_card_div_card_reg` and `erasedEntropy_clearingSum_of_budget` check the
general lemma against the instance it generalizes: charged only for the states
it fails to reach, the clearing evaluation still owes the `N log |Val|` that
`erasedEntropy_clearingSum` computes from its definition. The bound is tight
there, so it replaces the exhibited comparison rather than standing weaker
beside it.

*Does not establish.* A barrier. This is a **trade**: memory sufficient to
retain every intermediate pays exactly zero, which is `recordingSum_injective`,
and enlarging the budget to the whole phase space sends the bound to zero. The
theorem prices the exchange between memory and dissipation and closes neither
end of it. It prices nothing in watts either, until the decomposition of the
field into site values is declared — the same `κ` problem, in the same place, as
C4 and the installed-coupling argument. And nothing here says a digital machine
must take the clearing route; reversible computing remains the standing
counterexample §4's scope note already concedes.

**What remains in this block.** C5–C7, and D4–D5 in the D block. No publication
file is touched: none of the new identifiers is named in `main.tex`. `lake
build` is clean with no warnings; the axiom audit covers 5619 declarations in 91
modules, up from 5614.

### 2026-09-21 — D4 built, and the sign it returns

**The sign, first, because the item was written not to promise one.** The
comparison returns a **criterion and not a verdict**, and continuity is not on
either side of it. A continuum code space read at a finite resolution is a
finite alphabet whose capacity is a bit count, and whether it beats a `b`-bit
digital alphabet is decided by the region's measure against `2^b` resolution
cells — a volume, a noise floor and a dimension, every one of them measured.
Nothing in the comparison favours an analog medium as such.

**`Phase6_Reconstruction.lean`, the `Floor` section.** C2 supplied the floor to
match `encard_le_packingNumber_range`'s ceiling, which is what lets both sides
be counted in one currency: mutually resolvable codes.
`two_pow_lt_packingNumber_of_lt_measure` is the comparison — the continuum
strictly out-resolves `2^b` exactly when `2^b · v < μ A` —
and `two_pow_lt_packingNumber_of_lt_measure_haar` reads it on a
finite-dimensional real space as volume against `2^b · δ^d`, where the exchange
rate is `b` against `log₂(volume) − d log₂ δ`.
`Encoding.encard_le_two_pow_of_packingNumber_le` runs it the other way, reaching
`card_le_two_pow`'s conclusion with no alphabet to count, so the statement is a
comparison rather than a boast in one direction.

**`Examples/Phase6.lean` §33.** Both signs on one code space, the unit interval
under Lebesgue measure. `fine_resolution_beats_two_bits`: at `δ = 1/16` four
cells come to `1/2` and the interval's measure exceeds it, so the continuum
holds more than `2^2` codes. `coarse_resolution_holds_one_code`: at `δ = 2` the
interval's diameter is below the separation two codes would need, so it holds
one, and any alphabet matches. The volume and the substrate are the same in
both; the resolution is what moved.

*Does not establish.* Any mechanism: the floor is a property of the code space,
so nothing says an encoder writes those codes, that a readout separates them, or
that the states they would encode exist. Any calibration: `δ` and `L` are
declared, an uncalibrated gain still evacuates the ceiling in the direction the
module records, and the two bounds meet only where both are measured. And
nothing about §3 of `Phase7_Rigidity`'s two support comparisons, which stay
neutralized by the controls this repository supplies against itself —
`fieldCorrelation_cellKernel` and `no_forced_gap_of_best_wired` are unchanged.

**What remains.** C5–C7 and D5, all publication-only, in one editorial pass.
`lake build` is clean with no warnings; the axiom audit covers 5629 declarations
in 91 modules, up from 5619.

### 2026-09-21 — C5–C7 and D5, the editorial pass, and the block closed

**`sec:gpu`, "Codes, not reports" (D5).** The counting constraint names its
channel: `tokenChannel` for the token sequence a model emits, because that is
what its next step reads, `card_le_card_tokens` for the vocabulary size raised
to the number of steps, and `card_le_card_tokens_one` where it bites. The
paragraph says the bound is slack over an extended exchange and constrains a
single-step claim, and that a claim resting on activations has declared a
different channel.

**`sec:gpu`, "The region, not the readout" (D5, C8, C10).** The causal-mask
sentence stated an architectural observation; `mask_ball_subset_le` and
`mask_no_guarantee` make it a theorem firing at every deadline at once, with the
one-forward-pass scope stated. The deadline bound is then **retargeted**, which
was C8's point: it is weakest on the attention graph, where fan-in is the
context length, and has force on the physical interconnect, where
`card_ball_le_mul_pow` gives rounds growing like the logarithm of the device
count and `le_degree_of_reaches_one` prices the one-round deadline in wiring.
`not_outside_past_of_isFullSupport` states the other side, with the finite-speed
calibration named so that it does not read as an escape from latency.

**`sec:gpu`, "What is not excluded" (D4, C5).** The capacity comparison, stated
as a criterion: the continuum out-resolves `2^b` codes exactly when its volume
exceeds `2^b` resolution cells, and below that the inequality runs the other
way. C5 rides on the same sentence — real-valued states carry unbounded capacity
only at unbounded precision, and the noise floor the dynamics is stated against
removes it, so no computation beyond a Turing machine's is credited.

**`sec:scope` (C6).** Substrate-neutrality stated for the conditional chain and
not only for the unconditional results, with `no_site_dominates` named and its
vacuity on a nonatomic substrate said where it matters. What carries the
electromagnetic identification is the calibration and the extracellular-geometry
argument, which is the one place a field equation enters.

**`supplementary.tex`, falsification conditions (C7).** The six protocol
requirements are split: the second, the calibrated geometry-to-coupling
relation, is the only EM-discriminating one; the rest are satisfied or failed
identically by ion diffusion, gap junctions as a density, astrocytic calcium or
a mechanical medium. A null result now lands on the right claim.

**Table S1.** Three rows added — the deadline and its wiring cost, the channel a
self-report is counted in, and capacity at a declared resolution in both
directions — each ending on what its identifiers do not reach;
`no_site_dominates` went into the existing E56 row.
`check_table_coverage.py` reports 35 declarations named by the article, all
mapped.

**Notation.** The interconnect fan-in is `\nu`, with a Table 1 row, because `d`
already means a metric and a separation in this article.

**Artifacts.** All three tracked PDFs rebuilt, two passes each, with the
overfull-box count unchanged at zero against `HEAD`; `arxiv_submit/` rebuilt
from scratch and compiled from the unpacked tarball at 96 pages.

**The C and D blocks are closed.** The R research programme in
`tasks/research_programme.md` stays live and is untouched by this pass.

## V — The content bound's grain, and three routes off it

**Intent.** `sec:content-connection` states the positive coherence-to-content
result and its own limit in one breath: Eq. `eq:main-content-coherence` bounds a
chord, a chord never exceeds `2`, so at the sheet's patch-local order
`\waveBandLocalOrder` the bound carries information only at
`\wavePatchInformativeSites` sites or fewer. Three. The article now says so in
the abstract, in `sec:unconditional` and in the Discussion, which is the honest
reading and leaves the framework's first arrow spanning three oscillators. This
block is the three ways off that number. Each removes a different step of the
proof; none is a repair of the prose, and each would be worth proving whichever
way it came out.

**Constraints.** Every item is SRR and lands in a module that already carries
what it qualifies, so `ALLOWED_LEAVES` gains nothing. Nothing here widens
`Audit.permitted`. A new identifier reaching `main.tex` takes a `tab:full` row
in the same commit (AGENTS.md §9). `.lean` edits are followed by
`proof_companion/run.sh extract` then `pdf`. The three tracked PDFs and
`arxiv_submit/` are refreshed in the same commit (AGENTS.md §6–7).

**Success criteria.** `lake build` passes with the audit's footprint unchanged;
the publication numbers that change are regenerated macros and not typed
numerals (AGENTS.md §3); publication edits are present-tense statements of
scope.

### The audit

**The `N` has exactly one source.** From the order-parameter identity,
`∑_{ij} (1 - cos(θᵢ-θⱼ)) = N²(1-r²)`. Every term is nonnegative, so each term is
at most the whole sum. That single step — a sum of `N²` nonnegative terms
bounded by their total — permits all the disorder in a population to sit in the
one pair the conclusion is about, and it is where the factor `N` enters
`chord_le_of_patch_coherence`. The three routes below decline that step in three
different ways: by asking for fewer pairs (A), by asking over shorter distances
(B), or by not reading phase differences off `r` at all (C).

| Route | Declines | Removes `N`? | Mathlib has |
| :--- | :--- | :--- | :--- |
| A | each-term-≤-total, for a counting bound | yes, entirely | sum/card monotonicity |
| B | direct comparison of distant patches | no — trades it for path length | `SimpleGraph.Walk` |
| C | reading `Δθ` off the order parameter | yes, replaces it with `λ₂` | `lapMatrix`, `posSemidef_lapMatrix`, `Real.mul_le_sin` |

### Route A — the same sum, in the norm the statement wants

- [x] **V1 — Markov on the pair sum.** Replace each-term-≤-total by
      `t * card {(i,j) : 1 - cos(θᵢ-θⱼ) > t} ≤ ∑ ≤ N²(1-r²)`, a two-line `calc`
      from `Finset.sum_le_sum_of_subset_of_nonneg`. The conclusion is
      **`N`-free**: the fraction of pairs whose chord exceeds `c` is at most
      `2(1-r²)/c²`, at any population size. At `r = 0.99` that is 4% of pairs
      above `1·L`; at the sheet's own `\waveBandLocalOrder` it is 37%, weak but
      scale-free, and it improves quadratically in the locking. Lands in
      `Phase4_KuramotoDynamics` beside `chord_le_of_patch_coherence`, which it
      does not replace — the uniform bound stays, at its stated grain.
      Scope to state: this counts pairs and says nothing about *which* pairs, so
      it cannot name a site, and the outliers it permits may be exactly the ones
      a cover's overlaps sit on.

- [x] **V2 — Approximate gluing in measure.** *Scoped and declined; see the
      2026-09-21 entry below.* The item with real design risk,
      and it should be scoped before it is started. `approximate_diameter_le`
      (`Phase5_GlobalSection.lean:611`) takes overlap discrepancy bounded by `ε`
      in **uniform** distance and returns a weighted selection within `ε` of
      each patch. V1's conclusion is not of that shape, so it cannot be fed in:
      a fraction-of-pairs hypothesis has no sup-norm content. The partition-of-
      unity average of profiles agreeing off a small set is close to each in
      `L¹`, and *not* in sup norm, so the honest version weakens the conclusion
      as well as the hypothesis — a section determined off a set of controlled
      size rather than everywhere. Whether that object still deserves to be
      called a glued state is the question to answer first, and the answer may
      be no. Estimate on the proof is 250–400 lines; estimate on the design
      question is one sitting with the existing selection argument.
      Scope to state: unity is being weakened from "every overlap agrees" to
      "almost every overlap agrees", which is arguably the right claim — one
      rogue site should not unmake an experienced situation — but it is a
      different claim and the publication has to say which one it makes.

### Route B — chain the local bound through the nerve

- [x] **V3 — Disagreement accumulates in hops, not in population.** The cheapest
      item here and the one that moves the headline number. The observation is
      that the theorem bounds all `N²` pairs while the sheaf only ever asks
      about *overlapping* ones: distant agreement needs no direct bound, because
      a site in patch `p₀` and a site in patch `p_k` are compared through the
      sites they share with the patches between them, by triangle inequality in
      the content space. Error then grows **linearly in the number of hops**.
      With the sheet's own nearest-neighbour value `\waveNeighbourChordBound`,
      the crossover is at 14.4 hops rather than 3 sites:

      | hops | bound | |
      | ---: | ---: | :--- |
      | 1 | 0.139 L | informative |
      | 10 | 1.388 L | informative |
      | 14 | 1.943 L | informative |
      | 15 | 2.082 L | vacuous |

      This also dissolves the dilemma `sec:content-connection` currently states
      as closed — that shrinking a patch tightens the bound and thins its
      overlaps at the same rate, so the two ends are not reached by one cover.
      Chained, they are: small patches are where the bound bites, and the path
      is how it reaches distance. The machinery exists.
      `Phase5_TwistedGluing.lean` already builds a Čech-style 1-cochain on
      overlaps and reads its coboundary class as the obstruction; a discrepancy
      cochain summed along a walk is the same object over a different coefficient
      structure, and `SimpleGraph.Walk` indexes the chain. Lands in
      `Phase5_ContentDynamics` beside `compatible_of_patch_coherence`, with the
      nerve's connectivity as a hypothesis on `LocalSectionSynchronization`
      alongside `HasNonemptyOverlaps`.
      Scope to state: fourteen hops of column-sized patches is millimetres, not
      a hemisphere, and the accumulation is linear, so this moves the scale by
      an order of magnitude and does not reach the distant territories whose
      agreement unity is about. The per-hop constant is the sheet's, not
      cortex's.

### Route C — connectivity, entering through the dynamics

- [x] **V4 — The spectral gap replaces the population count.** The principled
      removal of `N`, and it is not astronomical provided the gap is *declared*
      rather than derived. At a locked configuration the phase differences are
      not free: they satisfy `K ∑ⱼ Aᵢⱼ sin(θⱼ-θᵢ) = ωᵢ - Ω`. Read that against
      the graph Laplacian instead of against the order parameter and the maximum
      pairwise difference is controlled by frequency heterogeneity over `K`
      times the algebraic connectivity — no averaging, no `N`, and the bound
      *improves* as the coupling graph becomes better connected, which is the
      statement one wants on physical grounds and the one `r` cannot express.
      Mathlib supplies more than expected: `SimpleGraph.lapMatrix`,
      `posSemidef_lapMatrix`, `lapMatrix_mulVec_apply` and
      `lapMatrix_mulVec_eq_zero_iff_forall_reachable` are there, and
      `Real.mul_le_sin` (Jordan, `2/π · x ≤ sin x` on `[0, π/2]`) together with
      `Real.mul_abs_le_abs_sin` handles the nonlinearity **without linearising**,
      at a cost of one factor of `π/2`. What Mathlib does not supply is `λ₂`
      itself — no Fiedler value, no Courant–Fischer on the Laplacian's kernel
      complement — so the item declares a `SpectralGap` structure carrying
      `λ > 0` and the Rayleigh hypothesis `⟪θ, Lθ⟫ ≥ λ‖θ‖²` for mean-zero `θ`,
      exactly as `PricedArrangement` declares `κ`. Estimate 200–300 lines.
      Lands in a new section of `Phase8_CoherentStability`, which already carries
      the coherent branch's spectral-gap inequality.
      Scope to state: `λ` is declared hardware data and this derives it for no
      graph, which is the same standing `κ` has and should be said in the same
      words; the result is about a locked configuration and supplies no
      existence proof for one; and the balance equation is the identical-frequency
      spatial model, so applying it to the scalar threshold still needs the
      reduction `sec:scaling` already flags.

### What reaches the publication

- [x] **V5 — Say which route the article takes.** Any of the three changes the
      number now in the abstract, `sec:unconditional` and the Discussion, and
      those three sites must move together. V3 alone replaces "only at three
      sites or fewer" with a hop count and a per-hop constant, both regenerated
      macros. V1 adds a second sentence in a different quantifier and must not
      be allowed to read as a strengthening of the first. V4 adds `λ` to Table 1
      and an E78 sentence, since what it qualifies is the edge from coherence to
      the cover.

- [x] **V6 — What functional connectivity does not buy.** Structural
      connectivity is a declared graph and is what V4 consumes. Functional
      connectivity is an estimate, and feeding an estimate into a hypothesis
      strengthens no conclusion: it inherits the decoder failure modes
      `sec:observations` already records, shared-prior shrinkage manufacturing
      agreement and regional bias manufacturing disagreement. Using measured
      functional connectivity to *choose the cover* is worse than neutral, being
      the "choosing the cover to secure agreement empties the claim" problem in
      new clothes. One scope sentence, wherever V4 lands.

### 2026-09-21 — V1, V3 and V4 built; V2 scoped and declined

**V1, `Phase4_KuramotoDynamics.lean` §11.** `sum_gap_eq` puts the pair sum in
closed form over the product type; `card_gap_le` is Markov on it, and
`card_chord_le` and `chord_fraction_le` carry it into the chord metric. The
conclusion is scale-free: the fraction of pairs separated by `c` or more is at
most `2(1-r²)/c²` at any population size, and where the uniform bound improves
like `√(1-r²)` this one improves like its square. The bad set is supplied as an arbitrary `Finset` of pairs rather than
filtered, which is strictly more general — the filter is the largest such set —
and keeps a decidability instance for a real inequality out of the statement.

`card_site_gap_le` and `site_fraction_le` read the same sum by rows, which the
item did not ask for and which the V2 decision turned on: a site with many
distant partners spends its own row, so the sites that disagree with a fraction
`δ` of the population by `c` or more are themselves at most `2(1-r²)/(δc²)` of
it. Most sites agree with most sites, at a rate fixed by the order parameter.

*Does not establish.* Anything about a named pair or a named site. Both
statements bound counts, and the exceptional set they permit is unlocated — it
may be exactly the sites a cover's overlaps sit on. The uniform bound stays, at
its own grain, because it is what a statement about a particular overlap needs.

**V3, `Phase4_KuramotoDynamics.lean` §12 and `Phase5_ContentDynamics.lean`.**
`patchNerve` is `SimpleGraph.fromRel` on "these two patches share a site";
`chord_le_of_patch_walk` chains a per-patch diameter `β` along a walk in it, and
`chord_le_of_patch_walk_coherence` reads `β` off each patch's own resultant.
`compatible_of_patch_nerve` is the content-level form, with the nerve's diameter
as an explicit hypothesis. Four metric lemmas were needed first and are in §5:
`chord_sq`, `chord_eq_norm`, `chord_triangle`, `chord_le_abs_sub`.

*The constant is `(hops+1)β`, not `hops·β`.* Both endpoint sites pay a step
inside their own patch, the shared sites of the walk being interior to the
chain, so a `k`-hop walk gives `(k+1)β` and the crossover moves by one: at the
sheet's nearest-neighbour value the last informative walk is 13 hops
(`14 × 0.1388 = 1.943`) and 14 hops is vacuous (`15 × 0.1388 = 2.082`). The
item's table is the bound as a function of *patch diameters travelled*, which is
`hops+1`, and V5 must regenerate it as such rather than as a hop count.

*Does not establish.* Any nerve's connectivity: that is a property of the cover
and is supplied. Nothing makes the accumulation sublinear, so the reach is a
dozen patch diameters and not a hemisphere, and the per-hop constant is the
sheet's rather than cortex's.

**V4, `Phase4_RotatingFrame.lean` §8, with the content half in
`Phase5_ContentDynamics.lean`.** `couplingForm` is the coupling-weighted
Dirichlet form and `SpectralGap` declares the Rayleigh inequality on mean-zero
fields. `is_frequency_locked` is the balance equation, and
`is_frequency_locked_iff` proves it equivalent to the rigid rotation of the
configuration solving the Kuramoto equations, so the hypothesis is a solution of
the system rather than a condition resembling one. `sum_mul_coupling_sin`
symmetrizes; `couplingForm_le_pairing` applies Jordan's inequality termwise,
keeping the sine and paying `2/π` rather than linearizing;
`spread_le_of_frequency_locked` closes with Cauchy–Schwarz. The conclusion is
`4λ²‖θ − θ̄‖² ≤ π²‖ω − Ω‖²`, and `chord_le_of_frequency_locked` reads it at a
named pair. `compatible_of_frequency_locked` is the content residual with no
population count, no patch and no cover geometry in it.

*Three design calls.* It lands in `Phase4_RotatingFrame` and not in
`Phase8_CoherentStability` as the item proposed: that module is the scalar
Fokker–Planck circle-density development, it cannot see `KuramotoSystem`, and
the balance equation is precisely the residual detuning the rotating-frame
reduction leaves behind when the frequencies are not identical — which is the
case that file's own scope note declines. `SpectralGap` is declared on the
weighted coupling rather than on `SimpleGraph.lapMatrix`, because the
development's coupling is a real matrix and not an unweighted graph;
`couplingForm_eq_lapMatrix` identifies the two on an adjacency matrix, which is
what anchors `λ` to algebraic connectivity, and `SpectralGap.scale` makes the
coupling strength visible as `K λ`. The nerve's connectivity in V3 is an
explicit hypothesis rather than a predicate on `LocalSectionSynchronization`:
the content module's cover is a plain family of sets and the module uses nothing
from the sheaf, which is a property worth keeping.

*Does not establish.* `λ` for any graph — it is declared hardware data in the
standing of `PricedArrangement`'s `κ`, and `Examples/Phase4.lean` §34 computes
one only for the complete graph. Existence of a locked configuration: it is
assumed, the critical coupling appears nowhere, and §34 exhibits one rather than
producing it. The quarter-turn confinement is assumed and is not implied by
locking. And the detuning enters in the population's `ℓ²` norm, which is
extensive — no `N` appears in the statement, and a population whose frequency
spread grows with its size pays for that growth through the data. What is
removed is the unconditional factor, not the physics of heterogeneity.

**Witnesses.** `Examples/Phase4.lean` §34 computes the complete graph's gap
(`K N`, with the Rayleigh inequality an equality at every mean-zero field) and
runs the whole estimate on two oscillators with *different* natural frequencies
locked at `±π/12`: every hypothesis discharged, the configuration provably not
phase-locked, and the resulting chord bound `π/4`, which `chord_le_two` makes a
constraint. §35 is V3's: four sites, three patches in a line, and a bound on the
pair `0`,`3` that no patch contains, at `3√(2−√3) ≈ 1.553` — informative where
the direct patch bound is not merely weak but unavailable.

**V2 — scoped and declined.** The design question was whether a section
determined off a set of controlled size still deserves to be called a glued
state. The answer that settles the item is upstream of that: *the hypothesis
cannot be supplied.* V1 bounds a fraction of pairs and `site_fraction_le` bounds
a fraction of sites, and neither locates the exceptional set. A cover's overlaps
are a set of sites fixed before the state is known, so reading either bound as
agreement on an overlap requires the exceptional set to miss that overlap —
a joint fact about the state and the cover that no coherence hypothesis
supplies. The only route to it is to choose the cover in the light of the state,
which is the move `sec:unity` already identifies as emptying the claim, and
which V6 names again for functional connectivity.

The object itself is not uninteresting, and the reason to record the decision
rather than the failure is that it is a decision about *which* object. Gluing in
the sheaf sense is determination: the global section restricts to each local
one. An almost-everywhere agreement determines a state only up to the
exceptional set, so what is produced is an `L¹` class and not a state, and every
consumer downstream must be a functional continuous in that norm — a population
average, not a site-wise evaluation. That trade has a real cortical reading
(population codes are redundant, and a small lesion produces no discontinuity in
what is experienced) and a real cortical cost (coincidence detection is a
sup-norm operation, it is the canonical binding operation, and it is exactly
what an `L¹` guarantee does not cover). Small measure is also not small
influence in a network with hubs. Any future version of this item states which
of the two it means before it proves anything, and does not reach it through
V1.

**What remains.** V5 and V6 are publication-only and untouched: no identifier
introduced here is named in `main.tex`, so `check_table_coverage.py` is
satisfied as the tree stands, and naming any of them there takes a `tab:full`
row in the same commit. The three tracked PDFs and `arxiv_submit/` are therefore
unaffected by this pass; the publication still states the three-site reading,
which remains true of the uniform bound it is a reading of.

**Verification.** `lake build` clean with zero warnings; the audit reports 5716
declarations in 91 modules, up from 5629, all resting only on `propext`,
`Classical.choice` and `Quot.sound`. `check_leaves`, `check_sorry` and
`check_table_coverage` pass.

### 2026-09-21 — V5 and V6 built; the V block closed

**The three routes reach the article, each in its own quantifier.**
`sec:content-connection` gains three paragraphs after the vacuity sentence,
which stays: it is true of the uniform bound and is what the three decline.
Route A states the fraction `2(1-r²)/c²` and the site form beside it
(`chord_fraction_le`, `site_fraction_le`), read on the same patch where the
uniform bound gives `\wavePatchChordBound L` and constrains nothing, at
`\wavePatchPairFraction`; it is labelled a different quantifier and not a
stronger statement, and the unlocated exceptional set is said in the same
breath. Route B gives the nerve, the metric argument and `(k+1)β`
(`chord_le_of_patch_walk_coherence`, `compatible_of_patch_nerve`) with the
reach as the item asked — `\waveNerveHops` hops, `\waveNerveDiameters` patch
diameters, `\waveNerveReachMm` mm of that sheet — and says the connectivity is
supplied. Route C gives the balance equation, the Dirichlet form and
`2λ₂‖θ−θ̄‖ ≤ π‖ω−Ω‖` (`spread_le_of_frequency_locked`,
`chord_le_of_frequency_locked`, `compatible_of_frequency_locked`) with its four
declared inputs listed and none discharged.

**The three sites moved together.** The abstract's "the estimate is vacuous
across the distant territories" clause becomes the uniform bound's grain plus
the three replacements, each against a declared input. The
`sec:unconditional` paragraph keeps `\wavePatchInformativeSites` as the uniform
reading's own limit and closes on what none of the three changes: a count
locates no site, the other two consume a declared cover or declared hardware
data, so phase order by itself still reaches no territory too far away to share
a patch. The Discussion says the same in its opening list and turns the
"population-size dependence" sentence in `sec:full-test` into what each route
asks a measurement for.

**`λ₂`, not `λ`.** The article already spends `λ` twice — the kernel eigenvalue
at a winding and extracellular tortuosity — so the spectral gap is written
`λ₂`, which is the standard name for algebraic connectivity and costs the
notation table one row rather than a third meaning. The E78 row of Table 1
gains the two alternative readings of the coherence-to-cover edge: through the
sites a connected cover's patches share, or through `λ₂` instead of through any
patch count, declared hardware data in the standing of `κ`. `β` and `k` take a
notation row scoped to `sec:content-connection`, as the table's convention for
a reused letter provides.

**V6.** One paragraph closing `sec:content-connection`: structural connectivity
is the declared graph that supplies `λ₂`; measured functional connectivity is
an estimate, inherits the decoder failure modes `sec:observations` records, and
using it to choose the cover is the move `sec:unity` identifies as emptying a
gluing claim.

**Supplement and claim map.** `sec:supp-compatibility` gains the development —
`eq:chord-fraction`, `eq:chord-nerve` and `eq:spectral-spread`, the witnesses at
`Examples/Phase4.lean` §34–35, and the sentence that neither route weakens
`SharedEncoder`. Table S1 gains two rows rather than one, because A and B are
unconditional theorems and C is not: "How many pairs a bound can miss, and
agreement across a connected cover" at `Theorem`, and "Agreement read off the
coupling graph rather than off the resultant" at `Theorem (conditional)`.
`check_table_coverage` reports 42 declarations named by the article, all mapped.

**Macros.** `_wave_content_macros` gains `\wavePatchPairFraction`,
`\waveNerveDiameters`, `\waveNerveHops` and `\waveNerveReachMm`, all derived in
that function from the summary already read there;
`\waveNeighbourChordBound` is reused as the per-diameter constant rather than
written a second time. The drift test carries the four new values.

*A number checked rather than changed.* `\waveNeighbourChordBound` is
`2√2|sin ψ|` and not `2√2|sin(ψ/2)|`, which is the exact two-site value. That is
correct: `chord_le_of_char_patch` takes its patch resultant from
`cos_le_mean_patch_order_winding`, which lower-bounds it by `cos ψ` rather than
by `cos(ψ/2)`. The published bound is sound and not tight, and it is the
constant route B chains.

*Does not establish.* Nothing new is proved: this pass is publication-only and
touches no `.lean` file. The reach of route B is that sheet's and not cortex's;
`λ₂` is computed for no cortical graph; and the counting route still names no
site, which is why the uniform bound's sentence stays where it is.

**Artifacts.** `simulations/simulation_results.tex` regenerated from the saved
summaries with no sweep rerun. All three tracked PDFs rebuilt, two passes each,
with the overfull-box count unchanged at zero; `arxiv_submit/` rebuilt from
scratch and compiled from the unpacked tarball at 96 pages.

**Verification.** `check_prose`, `check_figures`, `check_table_coverage`,
`check_tableS1`, `check_pdf_freshness` and `check_arxiv_freshness` pass;
`check_hedging` reports 0 flagged in both files. `test_simulation_tex` and
`test_generated_macros` pass, so no generated macro is uncited. `ruff`, `mypy`,
`vulture` and `xenon` clean on the generator. No Lean file changed, so the
audit's footprint and the proof companion are untouched.

**The V block is closed.** The R research programme in
`tasks/research_programme.md` stays live and is untouched by this pass.

## G — PRX Life consolidated review response (major revision)

**Context.** Two synthetic referees (anthropic/claude-fable-5.1 +
openai/gpt-astra-latest, consolidated 2026-09-22) recommend major revision:
restructuring, not a patch. The review lands 11 major and 14 minor concerns.
The previous Block G addressed a gentler single-model Gemini review and is
superseded in full. The consolidated review is at
`prx-life-review-consolidated.md`; its assessment at
`.gemini/antigravity-cli/brain/f8590112-f885-4848-970d-3a16b4afb781/review-assessment.md`.

**Principles for the revision.**

1. Rederive where possible; delete only as a last resort.
2. Salvage thermodynamics (main §7) and GPU/LLM (main §6) with non-trivial
   Lean derivations and/or simulations; demote to supplement only if no
   substantive strengthening is found.
3. The bootstrap on existing data *confirms* α = 0.5 is excluded at p < 0.02 —
   the fix is not a different statistical method but a different framing (what
   the prediction discriminates) plus larger-N / tighter-threshold runs.
4. Every publication edit is a present-tense statement of scope, not a
   narration of what the development used to claim (AGENTS.md §5).
5. Items are ordered by dependency and priority (P0 → P3). Each item states
   its proof hook. Nothing is marked complete without running it.

**Constraints.** `lake build` must pass with the audit's footprint unchanged.
Anything reaching `main.tex` has a Table S1 row in the same commit
(`check_table_coverage.py`, AGENTS.md §9). `.lean` edits are followed by
`proof_companion/run.sh extract` then `pdf`. The three tracked PDFs are
rebuilt and `arxiv_submit/` refreshed or removed in the same commit
(AGENTS.md §6–7). New references are verified via web search before commit
(AGENTS.md §4).

**Success criteria.** Every major concern is either resolved (derivation,
simulation, or restructuring) or explicitly scoped as a stated limitation with
a concrete future-work target. A staff engineer reading the diff would say:
"this is a restructuring, not a patch."

---

### P0 — Fixes that block everything else

- [x] **G1 — Bootstrap the delay exponent over replicas.**
      *Review concern: Major §4.* The 95% CI [0.394, 0.494] is OLS on 6
      ensemble-mean points. The per-replica data exists: 32 replicas × 8 speeds
      in `simulations/figures/dynamic_ramp_replicas_v*.npz`, stored as
      `order_replicas` of shape `(n_samples, 32)`.
      **Action:**
      (a) Add `bootstrap_delay_exponent(speeds, escape_matrix, n_boot=10000)`
          to `dynamic_ramp_analysis.py`. For each bootstrap iteration, resample
          32 replica indices with replacement per speed, compute resampled mean
          delay, fit the power law, collect exponent. Report percentile CI.
      (b) Wire into `dynamic_ramp_report.py` so `DYNAMIC_RAMP_REPORT.md` and
          the TeX macros carry both OLS and bootstrap CIs.
      (c) The bootstrap will *confirm* α ≈ 0.444 with CI still excluding 0.5
          (preliminary: [0.397, 0.495], p(α ≥ 0.5) < 2%). This is the honest
          result. The response to the reviewer is: the finite-N escape-threshold
          artefact is the known source of downward bias (manuscript already shows
          0.490 at r ≥ 0.05 vs 0.425 at r ≥ 0.2). The bootstrap CI is now the
          replica-level one, which is what the reviewer asked for.
      **Verify:** `pytest simulations/test_dynamic_ramp.py` passes; bootstrap
      CI appears in `DYNAMIC_RAMP_REPORT.md`; generated TeX macros updated.

- [x] **G2 — Larger-N and tighter-threshold delay runs.**
      *Review concern: Major §4 cont'd.* The reviewer asks for "larger N
      (floor ~1/√N)" with the stochastic ensemble rerun at the tightened
      criterion. The repository already has N=500 and N=8000 runs.
      **Action:**
      (a) If N=8000 runs already have per-replica data, extract and bootstrap.
          If not, run N=8000 with 32 replicas at 8 speeds (reuse existing
          `dynamic_ramp.py` infrastructure).
      (b) Run the r ≥ 0.05 criterion on the N=2000 ensemble (the supplement
          says 0.490 but this was never bootstrapped).
      (c) Report the three-way comparison: N=2000/r≥0.2, N=2000/r≥0.05,
          N=8000/r≥0.05. If the exponent converges toward 0.5 as N→∞ and
          threshold→0, say so. If not, say so.
      **Verify:** New `.npz` files present; `DYNAMIC_RAMP_REPORT.md` updated
      with all three conditions; no hardcoded numerals in `main.tex`.

- [x] **G3 — Fix the installed-energy inconsistency: derive stored field
      energy.**
      *Review concern: Major §2.* The cortical U_inst = 1.0×10⁻⁶ J is
      metabolic signalling power × residence time. The theorem bounds *stored*
      energy in field modes. These are different quantities.
      **Action:**
      (a) Derive a Fermi estimate of stored electromagnetic field energy in a
          cortical volume. Use measured LFP amplitudes (~1 mV/mm extracellular
          gradient) and tissue permittivity/conductivity (σ ≈ 0.3 S/m,
          ε_r ≈ 10⁵ at low frequency; Logothetis et al. 2007, Gabriel et al.
          1996). Electrostatic energy density w = ½ε|E|² gives
          ~10⁻¹⁹–10⁻¹⁶ J in a 0.2mm-radius sphere, i.e. 10¹–10⁴ k_BT.
          This is 10 orders of magnitude below the metabolic number.
      (b) If the stored-field number is too small to satisfy the bound
          (U_inst > 2D/κ), this is informative: it means the field's *static*
          energy is not what funds coupling — the continuous metabolic
          *replenishment* is. Rewrite the bound's cortical discussion: the
          theorem says "you need this much stored energy to maintain K > 2D";
          cortex achieves it via continuous metabolic power, not via a static
          capacitor. The distinction between stored and dissipated is the
          distinction between a battery and a generator.
      (c) Add the stored-field calculation to `fermi_estimate_check.py` and
          generate TeX macros for both numbers. Update `supplementary.tex`
          §2.2 to present both: stored field energy (tiny, insufficient alone)
          and metabolic power budget (large, sufficient via continuous
          replenishment). The main text states the conclusion in one sentence.
      (d) Verify reference: "Barbour 2017" for σ = 0.3–0.6 S/m. Cross-check
          against Logothetis et al. 2007 and Gabriel et al. 1996. If Barbour
          2017 is not the right source, replace.
      **Verify:** `pytest simulations/test_fermi_estimate.py` passes; both
      energy numbers appear in generated TeX; `supplementary.tex` §2.2
      distinguishes stored from metabolic; `main.tex` carries no hardcoded
      joule value.

---

### P1 — Structural revision and missing citations

- [x] **G4 — Reframe the "unconditional results" with Kuramoto citations.**
      *Review concern: Major §3.* The five results are presented as "what holds
      without the cortical hypothesis." They are elementary but the framing
      invites the overstatement reading. The relevant Kuramoto literature is
      largely uncited.
      **Action:**
      (a) Retitle §2 to something like "The landscape any phase-coherence
          account inherits" — positioning these as inherited constraints, not
          novel results.
      (b) Add citations: Acebrón et al. 2005 (Rev. Mod. Phys. review),
          Ott & Antonsen 2008 (dimensionality reduction), Dörfler & Bullo
          2014 (network topologies), Breakspear 2017 (brain dynamics review).
          Add these to `.bib` and cite them in the opening paragraph of §2.
          State that the mathematical features below reflect standard
          properties of phase oscillators, and this framework's contribution
          is tracking their implications for content decoding.
      (c) For K_c = 2D (main:150), add Strogatz & Mirollo 1991 and
          Acebrón 2005 alongside Sakaguchi 1988.
      (d) Correct the propagation-of-chaos scope: cite Dai Pra & den Hollander
          1996 and Bertini, Giacomin & Pakdaman 2010. Replace "is a research
          programme rather than a lemma" with a properly scoped sentence in the
          supplement.
      (e) Verify all new references via web search before commit.
      **Verify:** `check_prose` and `check_hedging` pass; new citations are in
      `.bib`; all verified via web search.

- [x] **G5 — Add neural inertia literature and operationalise the emergence
      protocol.**
      *Review concern: Major §1.* The emergence prediction (v^{1/2} delay) is
      the generic delayed-bifurcation result (Baer, Erneux & Rinzel 1989;
      Berglund & Gentz 2002) and doesn't test the field hypothesis. The neural
      inertia literature is uncited. The protocol is a wish list, not a design.
      **Action:**
      (a) Cite Friedman et al. 2010 (PLoS ONE — neural inertia in Drosophila
          and mice), Hudson et al. 2014 (PNAS — metastable states in
          emergence), Proekt & Hudson 2018 (BJA — stochastic basis for neural
          inertia). Position the framework's prediction relative to this
          literature: the v^{1/2} exponent is generic; the framework's
          *discriminating* content requires a separately specified spatial
          onset model. The homogeneous threshold result supplies no ordering
          of regions.
      (b) Rewrite §9.3 as a concrete protocol sketch: manipulate emergence
          rate v via propofol infusion rate (within-subject, multiple rates);
          measure time-to-response as the observable (not ΔK); specify that
          the discriminating test is the *spatial* signature (high-density
          ECoG or Neuropixels), not the exponent alone.
      (c) Compare matched, prespecified field-score and structural-connectivity
          onset models on held-out sessions. Both use the same baseline order,
          diffusion, drug drive, threshold and observation model. Earlier
          field-score onset is conditional on those inputs; hub-first is one
          declared comparator, not a universal synaptic-model prediction.
      (d) Verify all new references via web search before commit.
      **Verify:** §9.3 reads as a protocol, not a wish list; neural inertia
      refs in `.bib`; discriminating alternative stated.

- [x] **G6 — Compress E78 / compatibility saturation.**
      *Review concern: Major §5.* ~2000 words establishing the uniform bound
      saturates at ~0.2mm, then keeping it as a "non-standard ingredient."
      **Action:** Compress §4.2 to one paragraph stating the result and its
      scope limitation. Move the detailed derivation to the supplement (it may
      already be there — check for duplication). State once: at the sheet's own
      patch order the bound is informative for ≤ 3 sites; beyond that, the
      coherence-to-content link requires the cortical hypothesis (H8).
      **Verify:** `main.tex` §4.2 is ≤ 1 paragraph; supplement carries the
      full argument; no duplication.

- [x] **G7 — Present EEG exercise honestly.**
      *Review concern: Major §7.* At a = 0.104, I₁/I₀(a) = a/2 to within
      10⁻³. The data cannot distinguish the Bessel relation from a straight
      line.
      **Action:**
      (a) Retitle §8.6 to "Estimator calibration on exploratory EEG."
      (b) State explicitly: bipolar-montage scalp EEG sits in the linear
          Bessel regime (a_max = 0.542, deviation from a/2 < 1%). The exercise
          confirms the estimator is well-behaved in this regime but does not
          test the nonlinear prediction.
      (c) State what *would* test it: intracranial recordings (ECoG/sEEG/LFP)
          where local synchrony reaches a > 1, or narrowband alpha-spindle
          burst analysis. Cite the sample-size requirement (≥ 31,000 pooled
          phase samples or ≥ 1000 independent sites).
      (d) Do NOT claim the data are "compatible with the Bessel relation" —
          say "compatible with the Bessel relation and with any monotone
          alternative in this regime."
      **Verify:** `check_prose` and `check_hedging` pass; §8.6 reads as
      calibration, not as evidence.

- [x] **G8 — Reframe consciousness identification as interpretive
      motivation.**
      *Review concern: Major §8.* The glued state and reconstruction are
      proposed as correlates but no independent measurement for "experience"
      is offered.
      **Action:**
      (a) In §1 and §10.1, reframe: the framework's *empirical* content is
      the coupling-gated onset prediction and the spatial signature. The
      identification of the glued state with experiential unity is
      interpretive motivation — it says *why* the mathematics might matter,
      not *what* the test measures.
      (b) Keep the identification as explicit, labelled motivation. Do not
      delete it — it is the paper's reason for existing — but do not call
      it a testable proposal without a proposed measurement on the
      experiential side.
      **Verify:** §1 and §10.1 carry the reframing; `check_prose` passes.

---

### P2 — Salvage thermodynamics and GPU/LLM with new derivations

- [x] **G9 — Resolve the continuous-dissipation target with corrected premises.**
      The proposed positive order-only bound is false for the declared
      identical-frequency gradient model. `supercritical_zero_dissipation`
      constructs positive self-consistent stationary order at every D > 0,
      K > 2D with zero probability-current dissipation;
      `no_positive_order_only_bound` refutes every bound strictly positive at
      all positive orders. The constant stationary trajectory also refutes the
      time-averaged version. The valid quantitative replacement,
      `current_integral_sq_le`, proves `(integral J)^2 <= D * sigma_J` for a
      continuous positive normalized density and continuous current. A uniform
      density under constant drive is stationary and attains equality with
      `sigma_J = omega^2 / D`; the D = 1, omega = 2 witness pays four.
      Exact analytic equality replaces a numerical tightness check.
      Main text, supplement, Table S1 and primer state the distinction.
      **Open physical follow-up:** identify a cortical nonequilibrium drive,
      its current and thermal conversion. The ramp-speed target G9(c) is resolved in scope: `cosine_rate_sq_le_dissipation`
      proves the operator's cosine-moment speed bound, and
      `arbitrary_coupling_speed_zero_cost` refutes an unrestricted K-dot bound.
      `uniform_time_dependent_solution` checks the actual nonautonomous PDE for
      the uniform counterexample. An ordered actuator-cost relation remains a
      physical follow-up; no TUR or cortical power calibration is claimed.

- [x] **G10 — Prove the spectral approximation bound with an actual rank budget.**
      `Phase6_AttentionRank.lean` proves the finite-dimensional spectral tail
      lower bound against every competing rank-constrained linear map, including
      maps mixing the eigenmodes. Squared Hilbert--Schmidt error pays the tail
      of the **squared** eigenvalues. `spectralTruncation_rank` and
      `spectralTruncation_error` establish attainability. The reconstruction
      corollary derives the rank budget from a linear encoder/readout's
      intermediate dimension. A two-mode witness (eigenvalues three and one)
      attains error one and proves every rank-one competitor pays at least one.
      `softmax_rank_counterexample` proves rank-one two-position logits yield
      rank-two attention, refuting the original query/key-dimension premise.
      Main text, supplement, Table S1 and primer give the valid scope.
      **Open follow-up:** a physical kernel spectrum / continuum Mercer bridge
      and an independently justified rank constraint on an attention operator.
      G10(b) is also complete: `mutualInfo_le_output_entropy` bounds the existing
      KL information, including zero atoms; `token_information_bits_le` gives
      k log₂|V| bits for arbitrary finite joint laws of whole sequences, and
      `no_tokens_no_information` proves zero at k = 0. The binary copy attains
      one bit; the independent-output control has the same marginals and zero
      information. Cache state and timing are not silently included.

---

### P3 — Biological realism, prose, and minor concerns

- [x] **G11 — Heterogeneous-frequency control on the delay scaling.**
      *Review concern: Major §9.* All threshold results assume identical
      frequencies, mean-field sinusoidal coupling, no delays, and positive
      couplings.
      **Action:**
      (a) Run the delay-scaling simulation with quenched frequency
          heterogeneity: Lorentzian g(ω) with half-width γ = 0.5, 1.0,
          1.5 rad/s (the supplement already reports K_c shift at γ = 1.5).
          Check whether the exponent changes or only the prefactor shifts.
      (b) Cite Kuramoto 1984 and Strogatz 2000 for K_c = 2γ under Lorentzian
          heterogeneity. Note that heterogeneity softens the transition.
      (c) Acknowledge conduction delays and E/I balance as open questions.
          The supplement's Dale-balanced rescue (K_eff/D ∈ [1.88, 2.06]) is
          a numerical finding, not a theorem.
      (d) Scope the claim: results hold for the mean-field idealisation; the
          qualitative prediction (delay scaling ∝ v^α with α near 0.5) is
          expected to be robust to moderate heterogeneity on normal-form
          grounds.
      **Verify:** New heterogeneous-frequency `.npz` files present; exponent
      comparison in `DYNAMIC_RAMP_REPORT.md`; no hardcoded numerals.

- [x] **G12 — Move Lean identifiers out of main text.**
      *Review concern: Major §10.* Inline `PhysicsOfConsciousness.Kuramoto.
      stationaryThreshold_eq` breaks reading flow.
      **Action:**
      (a) Replace inline Lean identifiers in `main.tex` with mathematical
          English. State each result as: hypotheses, conclusion, scope, one
          paragraph. The Lean name goes into the Table S1 row.
      (b) Keep `\texttt{}` spans only where Table S1 / `check_table_coverage`
          requires them — i.e. one occurrence per result, typically in a
          "the Lean identifier is X" parenthetical or footnote.
      (c) Rewrite the abstract to remove sentences like "That grain is the
          uniform bound's, not phase order's."
      **Verify:** No inline Lean path longer than one dot-segment in main
      prose paragraphs; `check_table_coverage` still passes; abstract reads
      to a non-Lean reader.

- [x] **G13 — Fix notation collisions.**
      *Review concern: Minor §1.* E is both encoder and field amplitude; λ is
      eigenvalue and tortuosity; U is stored energy and patch; T is rounds and
      temperature; D is diffusion and phase spread.
      **Action:** Audit the notation table (main:591+). Reassign where the
      collision crosses a single section: e.g. rename the encoder to Φ or
      use script-E (ℰ) for the field amplitude. Keep collisions that are
      standard in their respective sub-literatures and separated by ≥ 2
      sections, but note them in the notation table.
      **Verify:** Notation table updated; no single section uses the same
      symbol for two things.

- [x] **G14 — Minor citations and data availability.**
      *Review concerns: Minor §§2–14.*
      **Action (batch):**
      (a) Add Strogatz & Mirollo 1991 alongside Sakaguchi 1988 for K_c = 2D.
      (b) Plasticity controls (main:477): add seeds or label as illustrative.
          Three seeds is acknowledged as few.
      (c) Compatibility estimator AUC = 0.986 (main:492): add "on synthetic
          data" qualifier.
      (d) Verify "Barbour 2017" for cortical conductivity; cross-check against
          Logothetis et al. 2007 and Gabriel et al. 1996.
      (e) State ds005620 subject/run list and preprocessing code path.
      (f) State Lean toolchain version and Mathlib commit hash in data
          availability.
      (g) Harmonise "Supplemental Material" vs "supplementary.tex".
      (h) Add comparison paragraph with IIT, GWT, and predictive processing
          in §10.3 or the supplement's §20. Frame as: "IIT derives Φ from
          intrinsic information; GWT from broadcast; this framework from
          phase coherence under physical coupling. The coupling gate is the
          differentiator."
      (i) Fix Eq. (14) framing: state as "deterministic tracking
          approximation that fails at onset" rather than "benchmark."
      (j) §9.1 columns: either offer a candidate alternative content cover
          or explicitly scope as "the content cover remains an open empirical
          question."
      (k) Fig. 3: show per-replica points or a bootstrap band, not only the
          ensemble mean ± 1 SE. (Follows from G1 bootstrap.)
      (l) Fix typographic `\allowbreak` rendering; consider footnotes or a
          table for long Lean identifiers.
      (m) Verify all 2026 references at submission time.
      **Verify:** Each sub-item checked individually; `check_prose`,
      `check_hedging`, `check_table_coverage` pass.

---

### Review section

2026-09-23 audit of completed G items, excluding running G2/G11 sweeps:
G1's replica interval is now stated in both publication files and the article
no longer treats the finite estimate as proof of the ideal exponent. G3's
metabolic expenditure and electrostatic field energy are separated from the
formal installed actuator energy; a supply-to-occupancy model remains open.
G4's cited Kuramoto references are now present in the bibliography, and the
mean-field scope has relevant citations. G6--G10 and G12--G13 have their stated
source and manuscript scope; G12's inline Lean identifiers were removed from
article prose. G5 and G14 were reopened here for a specified spatial comparator,
replica-level figure, identifier typography and reference verification. The
Lean toolchain and Mathlib revision are now stated
in data availability. Verification: `lake build` completed with the audit's
5797-declaration footprint restricted to the three permitted axioms; 34 focused
simulation tests passed; `check_prose`, `check_hedging`, `check_tableS1`,
`check_table_coverage`, `check_figures`, `check_pdf_freshness` and
`check_arxiv_freshness` passed; both publication PDFs compiled without final
LaTeX warnings. The new bibliography entries were checked against journal or
PubMed records before insertion.

G5/G14 completion — 2026-09-23 — The article and supplement now define
field-score and structural-degree models with matched inputs, one scale each,
and a held-out onset comparison. The figure shows the first sustained escape
of each uncensored replica at its recorded order, alongside mean curves and
standard-error bands. In the supplement, manually broken identifiers use
breakable literal code formatting instead of embedded `\allowbreak`; the
remaining mathematical use was rewritten. All nine 2026 references were
checked against publisher or preprint records. The neural-inertia reference
check also corrected the Proekt--Hudson DOI from `.036` (an unrelated case
report) to `.035`. Focused ramp tests (22) and Ruff, strict mypy, Bandit,
Vulture, Xenon, and Tach passed. Both publication PDFs were rebuilt; final
LaTeX passes had no undefined references or overfull boxes. The prose,
hedging, Table S1, claim-coverage, figure, PDF-freshness, and arXiv-freshness
gates passed. The production sweeps were not rerun.

G1 — 2026-09-23 — Replica bootstrap added to the dynamic-ramp report and
generated TeX macros. `test_dynamic_ramp`, `test_dynamic_ramp_analysis`,
`test_dynamic_ramp_report`, and `test_simulation_tex` pass.

G2/G11 — 2026-09-23 — All eight N=8000 ramp checkpoints and all twelve
heterogeneous-frequency checkpoints completed. The saved summaries and
`DYNAMIC_RAMP_REPORT.md` give the three threshold/size fits and the
heterogeneity comparison. The N=8000 tighter-threshold fit moves farther from
one-half; the largest frequency width leaves only two uncensored legs, so no
three-width exponent conclusion is supported. G15 carries the remaining
matched-window audit and publication interpretation. The production runners
reported `complete`; focused analysis/report tests and static checks passed.

### 2026-09-23 — G9 / G10 Lean derivations and premise checks

Specification: `tasks/g9_g10_lean.md`. Failing headline-name and typed witness
regressions were run before integration. The formal results use only the three
permitted logical axioms. The spectral proof uses Parseval, projection onto the
competitor's range, and a finite weight-exchange inequality, with no spectral
gap assumption disguised as a field. The current bound uses square completion
on the positive normalized density. No new physical structure or postulate is
introduced. Existing unrelated workspace changes are preserved.

Validation results are recorded in the specification after the final build.

### 2026-09-23 — G10(b) and G9(c), Lean-first continuation

Proved finite-output information capacity in `Phase3_FiniteInformation` and
sequence capacity in `Phase6_Reconstruction`. The proof uses the existing
measure-theoretic KL definition; reference atoms need not all be positive.
`Examples/InformationCapacity` checks a saturating binary copy and an independent
control. The Fokker--Planck weighted-current inequality gives a cosine-moment
speed bound by integration by parts; the sinusoidal-drive witness has nonzero
rate and positive cost. A uniform solution with positive exponential coupling
has arbitrary coupling derivative and zero phase-current cost, so an
unrestricted coupling-ramp speed bound is refuted. Remaining G tasks concern
simulations, references, protocols or physical calibration, not a specified
unproved Lean theorem. Final combined verification is recorded in the G9/G10
specification.

### G15–G24 — Scientific focus, stronger tests and a shorter manuscript

**Intent (2026-09-23).** Following the G review response, rewrite the article
around one scientific argument: phase coherence alone is insufficient evidence
for a unified representation; specify the additional decoding and reconstruction
conditions, demonstrate failures of common observables, and state independently
measurable tests. Preserve the cortical field hypothesis and the motivation from
unity and self-representation, with their evidential status explicit. The user
requests a clearer voice and reduced text. This is a planned editorial revision;
the tasks below are not completed by adding this plan.

**Constraints and success criteria.** Use the current manuscript and corrected G
results as the scientific baseline. Keep assumptions needed to interpret each
claim next to that claim. Give each result and its limitation one primary home.
Preserve proofs and reproducibility in the supplement/repository while reducing
repetition across both documents. Working editorial target: reduce article prose
by at least 30%, aiming for roughly 8,000–9,000 words and a 200–250-word abstract;
these are project targets, not asserted journal limits. Establish a consistent
prose-count method before comparing drafts, excluding bibliography and the
notation/claim tables. Record exceptions if a necessary explanation exceeds the
budget. No new production sweep or formal extension is implied by this rewrite.

**Stash inspection.** Read `attempted-rewrite`, currently `stash@{0}`, at immutable
commit `5cdd8bef02bdcd4e5fe50ac37366867e6e1b93f4`; it was not applied or dropped.
It changes `main.tex`, two PDFs and `scratch/main_diff.patch`. Simple whitespace
counts from abstract through discussion are 14,020 tokens in its parent and
12,473 in the rewrite (about 11% reduction); the current article has 13,617 by
the same rough measure. These are TeX token counts, not publication word counts.
The rewrite largely preserves the section structure. Useful features include
shorter sentences, concrete subjects and the cup example. It also retains the
obsolete claim that the delay prediction needs no absolute calibration and
introduces overstatements: toy witnesses "prove they can exist in reality";
the work identity "ensur[es]" an allowance that must instead be assumed;
"the past strictly causes the future" replaces a specific Markov condition.
Its claims of a "definitive" test, generic positive learning cost and physical
proof from favourable observations also need correction. Use it as a source of
individual wording ideas checked against current results, not as a replacement
manuscript. Conversational fillers and metaphors such as "magically", "cranks
up" and "buy the distance back" are not the requested clear scientific voice.

- [x] **G15 — Resolve what the G2/G11 ramp results establish.**
      Complete and audit the existing G2/G11 analyses before choosing the final
      empirical headline. Saved summaries inspected on 2026-09-23 report
      approximately 0.444 at N=2000/r≥0.20, 0.637 at N=2000/r≥0.05, and
      0.720 at N=8000/r≥0.05, using different uncensored speed sets. All
      production checkpoints are complete. The heterogeneous summary has fits
      near 0.24 and 0.18 from only three usable speeds each, with insufficient
      fit legs for the third width. These are provisional
      artifact readings, not independently validated scientific conclusions.
      Compare matched speed windows as well as all eligible legs; check threshold
      placement relative to fluctuations, initialization, critical coupling,
      censoring, zero delays, sampling resolution and bootstrap exclusions.
      Inspect residuals and whether a single power law is an adequate description;
      replica uncertainty alone does not establish adequacy across ramp rates.
      Distinguish stationary onset, ideal dynamical delay and finite operational
      escape. Do not assume tightening the criterion restores one-half or that
      heterogeneity only shifts a prefactor. Treat the bootstrap fraction above
      one-half as a bootstrap summary, not automatically a hypothesis-test p-value.
      Carry G11's publication work here: verify and cite the Lorentzian threshold
      literature, state conduction delays and E/I balance as open controls, and
      scope any robustness statement to the mean-field idealisation actually tested.
      **Verify:** Completed artifacts and analysis support one explicit conclusion
      with its regime; generated macros, report and both publication files agree.
      Add failing tests first for any analysis correction. Further simulations
      require a specific unresolved diagnostic question and separate scope.

- [x] **G16 — Select the central argument and allocate section budgets.**
      Draft a short outline with a purpose and word budget for each section.
      Organize around coherence, compatibility and reconstruction; connect the
      winding, identifiability and decoder controls to the measurements each
      requirement needs. Separate inherited mathematics, the framework's
      contribution, numerical findings and proposed physical interpretation.
      Integrate elementary counterexamples where they motivate a condition;
      remove the repeated five-result inventories in abstract, introduction,
      standalone survey and discussion. Present formal verification as assurance
      of specified implications, with joint witnesses establishing mathematical
      satisfiability. Explain the biological question those implications clarify.
      **Verify:** Each retained main-text section advances the central argument;
      the outline meets the total budget and carries an explicit destination for
      material moved out. Outline work can proceed while G15 is unfinished.

- [x] **G17 — Integrate G9/G10 in proportion to their role.**
      Keep a concise current/dissipation result where it limits physical resource
      claims, including ordered zero-current equilibrium and the distinction
      between density-change cost and actuator cost. Give installed energy a
      short statement with the unidentified cortical calibration clearly named.
      Move extended feedback, learning, supply ledgers and machine-candidate
      discussion to existing relevant supplement sections where they do not
      advance G16's argument. Retain the actual linear-rank premise, softmax
      counterexample and finite-output information scope in their destinations.
      **Verify:** A migration map accounts for substantive claims and citations;
      main text explains why each retained resource result matters. Moving a
      result preserves its hypotheses and creates no duplicate exposition.

- [x] **G18 — Rewrite in a direct scientific voice using the stash selectively.**
      Write from G16's outline using the current corrected claims. Use concrete
      subjects, active verbs, short paragraphs and familiar words; introduce
      mathematical terms when the argument needs them. State the result, its
      necessary assumptions and its consequence together. Replace long defensive
      qualifications with precise scope statements and remove repeated warnings.
      Avoid rhetorical contrasts, colloquial intensifiers, unsupported universal
      claims and numbered inventories in the abstract. Keep the cup example if it
      helps readers distinguish timing, shared content and perspective.
      Rewrite the abstract and introduction after the body establishes the final
      emphasis. Reduce the supplement's duplicated explanations as well; preserve
      its technical derivations and methods.
      **Verify:** Before/after prose counts meet the agreed working budget; every
      claim borrowed from the stash is checked against the current theorem or
      evidence. A reader needs neither Lean identifiers nor drafting history to
      follow the article. Final empirical wording depends on G15.

- [x] **G19 — Make the proposed biological test assessable.**
      Preserve G5's matched field/connectivity comparison and explain what a
      held-out advantage would establish. Specify independent covariate estimation,
      train/test separation, onset and behavioural endpoints, nuisance controls,
      missing/censored observations and a declared predictive scoring rule.
      Address correlated field/connectivity scores and regimes where the models
      cannot discriminate; avoid treating structural degree as every synaptic
      alternative. State which calibration/pilot inputs are needed for precision
      or power planning instead of inventing a sample size. Distinguish a protocol
      sketch from a demonstrated cortical mechanism and retain the separate
      measurement problem for experience.
      **Verify:** Each proposed observation has a stated inferential target and
      failure condition; outstanding physical and experimental inputs are named.

- [x] **G20 — Audit scientific meaning after compression.**
      Compare the rewrite against the corrected manuscript and source results.
      Check especially stored energy versus expenditure, necessity versus
      sufficiency, mathematical existence versus physical realization, budget
      assumptions versus conclusions, phase order versus content, and measured
      onset versus a stationary branch. Preserve G7's EEG calibration status,
      synthetic decoder scope and G8's interpretive identification. Manually map
      article claims to Table S1 even when removal of inline identifiers means
      the automated coverage gate cannot see them.
      **Verify:** Each headline has evidence, hypotheses and a scope limitation;
      no shorter sentence strengthens a theorem or turns a proposal into a result.

- [x] **G21 — Validate and deliver the rewritten publication.**
      Run the relevant prose, hedging, Table S1, coverage, figure and generated
      macro checks. Verify new references online if introduced. Rebuild every
      affected tracked PDF with cross-references resolved; inspect the rendered
      abstract, figures and tables. Review the primer for content drift and keep
      the assembled arXiv submission current under repository rules. Run analysis
      tests for changed analysis and the Lean audit if formal sources change.
      **Verify:** Report final word counts, material moved, scientific conclusions
      and remaining empirical questions; source/PDF deliverables and applicable
      gates agree. Keep the attempted-rewrite stash intact as a reference.

- [x] **G22 — Bound the current cost of changing phase-order magnitude.**
      *Motivation:* the current theorem bounds the rate of a fixed cosine moment,
      while a cortical or simulated onset is commonly summarized by the
      rotation-invariant magnitude $r=|\int e^{i\theta}\rho|$. The existing
      positive-order stationary counterexample rules out a universal cost of
      maintaining order; it does not rule out a cost for changing order within
      a finite time.
      **Proof target:** for a positive normalized periodic density evolving by
      $\partial_t\rho=-\partial_\theta J$, constant $D>0$, and current
      $\sigma_J(t)=\int J^2/(D\rho)$, derive or refute
      $\dot r^2\leq D\sigma_J(1-r^2)$ under explicit regularity assumptions.
      Where $r(t)$ is absolutely continuous and stays below one, integrate it
      to obtain
      $\int_0^\tau\sigma_J(t)\,dt\geq
      [\arcsin r(\tau)-\arcsin r(0)]^2/(D\tau)$.
      Treat times with $r=0$ or $r\to1$ by a separate argument or state the
      theorem's domain precisely. The bound concerns probability-current cost;
      it is not heat or metabolic power without a physical conversion.
      **Numerical test:** add failing tests first. Simulate regular periodic
      density evolution under prespecified coupling schedules and save $r(t)$,
      $J(t,\theta)$, accumulated $\sigma_J$, duration, initial condition and
      numerical resolution. Compare ramps and alternative schedules with the
      same endpoints and duration; include the exact uniform zero-cost path and
      ordered relaxation controls. Check the bound and report its slack over
      the regimes where an operational onset occurs. Repeat across diffusion,
      ramp rate and moderate heterogeneity; identify where the homogeneous
      proof ceases to apply.
      **Verify:** Lean proves the stated functional inequality and integrated
      consequence with explicit periodicity, positivity and differentiability
      assumptions; simulations recover the bound within numerical error and
      expose informative tightness or a clear counterexample; the report and
      any publication macro read only saved artifacts. A main-text claim is
      useful only if it constrains the measured finite-onset protocol beyond
      the stationary zero-cost counterexample. No cortical work or power claim
      follows without calibrated current and thermal conversion.

- [x] **G23 — Close the learning–phase–actuator feedback loop.**
      *Motivation:* the existing learned-coupling construction attaches an
      actuator to a learner's executed law, but supplies phase observations
      rather than evolving the phase dynamics under the coupling that learner
      installs. Build one explicit process in which a register update changes
      actuator occupancy and installed coupling, phases evolve under that
      coupling and declared noise, a sensor samples those phases, and the
      resulting observation updates the same register.
      **Model:** specify finite or discretized phase state, update order,
      observation channel, learning rule, coupling readout, mode prices, thermal
      scale and reservoir. Carry the joint law through every stage. State local
      detailed balance and path-support conditions where a heat theorem uses
      them; otherwise report work and phase-current cost as distinct ledgers.
      Include preparation, sensing, reset, installation work and depletion or
      replenishment of the work store. A finite source with positive net cost
      must eventually stop; continuing operation needs a named replenishment
      mechanism.
      **Controls:** compare an informative phase sensor to a matched blind or
      shuffled sensor with the same marginal phase order, initial law, actuator,
      learning rule and resource allowance. Also include an unchanging actuator,
      an uninformative prior and a control that has the same learned marginal
      but no phase feedback. Measure held-out task accuracy, shared-content
      agreement, reconstruction error, coherence, installed energy, cumulative
      work, heat and any current cost separately. Use training data only to fit
      readouts and thresholds; score on held-out episodes and state families.
      **Verify:** failing tests precede implementation; the formal development
      proves the joint transition and resource ledger for the named process;
      simulation recovers analytical small-state cases and distinguishes the
      matched controls. A positive result establishes a closed-loop witness for
      its supplied model, not cortical realization. Mapping its register,
      actuator, noise and replenishment to cortex remains an explicit physical
      follow-up. This item can support a concise resource paragraph only if
      phase dynamics, learning and the work ledger materially constrain one
      another in the resulting process.

- [x] **G24 — Test reconstruction limits on one shared digital and phase task.**
      *Motivation:* the finite-rank theorem and token/causal-past bounds state
      measurement obligations, but the current GPU section has no comparison
      showing how those limits affect a task relevant to compatibility and
      self-reconstruction. Construct a benchmark with a known global state,
      independently specified local observations, shared quantities on
      overlaps and a declared encoding region. Require each candidate to
      reconstruct the state and its own relation to it after interventions.
      **Candidates and budgets:** include (i) the article's explicit linear
      bottleneck class, where the spectral-tail theorem applies, (ii) a
      nonlinear decoder-only transformer, for which query/key dimension alone
      is not treated as an operator-rank budget, and (iii) a phase-based network
      with a declared coupling graph. The transformer control must be small
      enough to train and evaluate on CPU for the fixed synthetic task; specify
      its size, sequence length and runtime budget. Measure the actual internal
      code, its effective rank under a prespecified tolerance, token output,
      causal past, communication rounds, parameter count, memory and latency.
      Hardware energy measurement is an optional follow-up, not a prerequisite.
      Do not infer a physical coupling or consciousness from architecture labels.
      **Design:** vary bottleneck dimension, local observation noise, overlap
      agreement, communication deadline and intervention distance. Train on
      some state families and score on held-out families, unseen combinations
      and interventions that alter the encoded self-state while preserving the
      external scene. Include full-capacity and shuffled-code controls, a
      compatible/incompatible decoder control and a same-order/different-content
      control. Use the measured target-operator spectrum to predict the linear
      model's error floor, then test that prediction on held-out inputs; report
      nonlinear architectures as controls for the theorem's linear premise.
      **Verify:** preregister scoring rules and splits; derive the input-weighted
      rank bound if task inputs are not isotropic; tests first for all analysis
      and simulation changes; publish seeds, checkpoints and machine-readable
      results. The experiment must separate theorem-predicted linear error,
      general reconstruction failure and hardware cost. A successful result
      supports claims about these candidates and budgets only. Record whether
      the CPU benchmark fits its declared runtime budget. Any hardware energy
      study is a separate follow-up requiring access to the named hardware. A
      main-text GPU section is warranted only if the comparison yields a result
      that changes how the framework's reconstruction conditions are assessed.

**Remaining empirical questions.** Cortical mode prices,
supply-to-occupancy calibration, independent content decoders and an
experiential endpoint remain gaps. The spatial field/connectivity comparator
needs independent covariate maps and held-out emergence recordings. The finite
ramp results establish no common asymptotic delay exponent.

**G16/G19 progress (2026-09-23).** `tasks/g16_outline.md` fixes the article's
central argument, a section-by-section 8,005-word working budget and the
migration destinations for resource and machine material. G17 prose migration
placed machine interpretation and the finite-resolution capacity scope in the
supplement, and shortened the article's code/causal-reach, installed-energy,
learning and hardware comparisons while retaining their load-bearing premises.
The awakening protocol now predeclares training and held-out sessions, a
regional log predictive score that retains
censored onsets, behavioural recovery as a separate endpoint, nuisance and
negative controls, discrimination limits for correlated covariates, and the
pilot measurements needed for precision planning. A held-out advantage is
restricted to the specified comparator; the causal and experiential questions
remain separate. Publication prose, hedging, Table S1, coverage and figure
gates passed. Both publication PDFs were rebuilt twice; their rendered protocol
paragraphs were checked with PDF text extraction. The PDF and arXiv freshness
gates passed. No new references or simulation numerals were introduced.
The G18 abstract pass replaced the five-result inventory with a 155-word
statement of the conditions, their mathematical and physical scopes, and the
held-out spatial comparison. The shorter length keeps the full abstract on
page one in the rendered PDF. The body and introduction receive their planned
rewrite in the main-text pass below.

**G18 main-text pass (2026-09-23).** The article's TeX-stripped prose count,
excluding figures and longtables, is now 8,141 words versus 12,576 at commit
`7d8c5ba21e3b25b8f9459cc67aff9b8da6f55752`, a 35.3% reduction by the
same method. The introduction, inherited-limit survey, winding discussion and
discussion now state each result once with its assumptions nearby; derivation
details remain in Supplemental Material. The abstract still fits on page one.
The main-text scientific audit checked installed energy against
metabolic expenditure, necessity against sufficiency, mathematical witnesses
against cortical realization, stationary branch against observed onset, EEG
calibration against evidence, and synthetic decoder scope. The article's
headline results have corresponding limitation rows in Table S1. The completed
cross-document audit is recorded below.

**arXiv artifact (2026-09-23).** `./prepare_arxiv.sh` rebuilt the merged
submission after the main-text compression. It compiled from the unpacked
`arxiv_submit/ax.tar.gz` in three passes and produced a 96-page PDF.
`check_arxiv_freshness.py` reports the new manifest current. The assembled
PDF's first page and appendix marker were checked by text extraction.

**G22–G24 first increment (2026-09-23).** Lean-first foundations are in
`Phase8_OrderCurrent.lean` (weighted current second-moment bound and the
arbitrary-direction order factor), `Phase3_PhaseFeedback.lean` (joint
phase/sensor/register transition and a declared finite work-store ledger), and
`Phase6_InputWeightedRank.lean` (diagonal input-second-moment spectral tail).
New examples exercise a two-phase feedback/blind-sensor distinction and the
anisotropic reversal of the retained rank-one mode. These are partial results:
G22 now has a smooth positive-order magnitude derivative and integrated arcsine
theorem in `Phase8_OrderSpeed.lean`; G23 now ties declared stage prices to the
joint law in `Phase3_FeedbackLedger.lean`, with physical calibration and full
controls open; G24 now has a sampled-basis input-law error theorem in
`Phase6_SampledRank.lean`, with general covariance and the shared CPU benchmark
open.
`simulations/followup_foundations.py` supplies analytical counterparts with nine
regression tests, including a manufactured continuity path, exact joint-channel
probabilities, and weighted rank floors. No sweep or training run is claimed.
Detailed scope and remaining obligations are in `tasks/g22_g24_foundations.md`.
All three checklist items remain open. Manuscript edits are deferred by explicit
user instruction.

**G22 numerical pilot (2026-09-24).** A conservative periodic-density solver
and artifact-only report now save and compare five initial protocols in
`simulations/figures/g22_pilot/`. Equal-endpoint early, linear and late ramps
produce distinct final order and positive current costs above the endpoint
bound; uniform and ordered-relaxation controls behave as expected. A grid test
checks convergence toward exact diffusion relaxation. The first pilot has no
operational onset or heterogeneity and does not close G22; quantitative
resolution study and broader parameter sweeps remain open. See
`tasks/g22_g24_foundations.md` for numerical values and scope.

**G22 Lean continuation (2026-09-24).** `Phase8_OrderSpeed.lean` proves the
rotation-invariant magnitude rate and finite-time arcsine current-cost bound
for a positive normalized periodic classical density. The proof identifies
its real first-harmonic magnitude with the norm of the existing complex order
parameter, derives both moment rates by spatial integration by parts, and
requires a pointwise continuity equation plus justified time differentiation
under the spatial integral. The integrated theorem assumes smooth order and
cost and a strict 0 < r < 1 domain; zero-order instants, the limiting
unit-order case and an absolutely continuous extension remain open. The
numerical breadth and operational-onset assessment in G22 also remain open.
No manuscript changes were made in this increment.

**G23/G24 Lean continuation (2026-09-24).** `Phase3_FeedbackLedger.lean` proves
the closed joint-law recurrence, expected installation-energy balance on the
actual phase/register paths, its finite-horizon telescoping form, a funded
ledger with sensing, reset, preparation and replenishment, and eventual
exhaustion under a positive expected net-cost floor without replenishment.
The deterministic Bool witness has a nonzero signed installation change.
These are declared work prices, not heat; local detailed balance, a bath,
physical price calibration, a stop rule and matched feedback controls remain
open. `Phase6_SampledRank.lean` specializes the weighted rank theorem to a
normalized nonisotropic eigenbasis input law and proves truncation attains its
expected-error floor. The two-mode witness has an exact 9/17 floor. General
correlated inputs and the shared digital/phase CPU benchmark remain open.

**G22–G24 analytical continuation (2026-09-24).** A new Lean identity in
`Phase3_PhaseFeedback.lean` proves that summing the updated register out of
one joint transition recovers exactly the installed phase channel. Python now
propagates the full finite joint law and checks an informative sensor against
a blind sensor with the same phase marginal on a symmetric two-state model;
the register's next-phase prediction differs. This is an analytical control,
not a held-out task benchmark or a calibrated work/heat model. For G24, a
Python singular-value calculation gives the optimal linear rank-error floor
for a supplied positive-semidefinite input second-moment matrix, including
correlations; random rank-one competitors check it. This general covariance
formula is not yet a Lean theorem or a shared digital/phase benchmark. G22
solver tests now cover three diffusion values, two durations and three ramp
schedules, checking density positivity, mass conservation, monotone current
cost and the endpoint bound within a fixed numerical tolerance. Saved sweep
artifacts, heterogeneity and operational onset are still open. No manuscript
files were edited in this continuation.

**G22–G24 saved-grid and ledger continuation (2026-09-24).** The G22 solver
now saves a declared 30-trajectory grid at 48 cells, three diffusion values
(0.25, 0.5, 1.0), two durations (0.4, 1.0), three equal-endpoint ramps, and
uniform and ordered-relaxation controls. The separate report reads only the
saved artifacts in `simulations/figures/g22_grid/`; it checks normalization,
positive density, increasing time, accumulated cost, and recomputes the
endpoint bound before summarizing. All saved protocols have nonnegative
bound slack, positive density and mass error below 4e-16; uniform controls
have zero cost. This fixed grid still shows no declared operational onset,
contains no heterogeneity, and is not a continuum error estimate.
For G23, finite joint-law costs now use the executed transition and reject
inconsistent supplied laws. A declared preparation/sensing/reset/installation
account telescopes against installed-mode energy in the two-state check;
the new Lean phase-marginal recurrence shows that the current joint law
averages the installed phase channel. The account is not heat or a physical
reservoir model. For G24, a numerical truncated
linear decoder attains the general covariance rank floor for positive-definite
and singular two-dimensional input laws. The general covariance result is
still unformalized in Lean, and the shared digital/phase CPU benchmark remains
open. No manuscript files were edited.

**G22–G24 operational and shared-task continuation (2026-09-24).** An
exploratory order threshold `r = 0.3`, chosen after inspecting the saved G22
grid, is crossed only by the `D = 0.25`, duration-one early ramp among the
30 saved protocols. The artifact-only report interpolates its first
upcrossing. A separate seven-grid resolution set (32–256 cells) moves the
crossing estimate from 0.976945 to 0.923921; the last 192-to-256 change is
about 0.00193. At 256 cells, integrated current cost is about 2.576 times
the endpoint floor. This is a late crossing under an exploratory threshold,
not preregistered onset evidence or a continuum error bound.
For G23, an explicit next-phase prediction score retains the joint law and
installed action. In the symmetric two-state model, informative and matched
blind sensors preserve the same phase marginal while scoring 0.90 and 0.65
after feedback begins. It is a model control, not held-out cortical behavior.
For G24, `g24_shared_task.py` now fixes a four-bit global state, two local
views overlapping on two bits, a self-state flip intervention, even-parity
training combinations and odd-parity held-out combinations. The saved linear
baseline includes the task arrays, fitted rank-0-through-4 decoder matrices,
seed, effective ranks, dense storage, CPU fitting time and squared-error
scores. In the noiseless task, held-out errors (6, 3, 2, 1, approximately 0)
match the measured covariance-tail floors. With independent local noise 0.1,
the rank-4 held-out error is about 0.041 versus a training floor of 0.0401.
Fitting took below the declared two-second CPU budget. These are linear-only
results; transformer and phase candidates, broader state families, fixed
communication budgets, and hardware measurements remain open. No manuscript
files were edited.

**G22–G24 audit and matched control (2026-09-24).** The existing G22
heterogeneous grid now has 18 saved two-frequency trajectories spanning two
diffusion values, three frequency spreads and three equal-endpoint schedules.
For each cohort the density stays positive and normalized; the marginal
density obeys continuity with the aggregate current. Its current-cost bound
therefore still applies to that marginal, while the larger cohort-resolved
cost is a separate account. The lone crossing at the exploratory `r = 0.3`
threshold remains a late-onset numerical example, not a prespecified onset
test or a continuum error estimate. The homogeneous drift model itself no
longer describes either frequency cohort when spread is nonzero.

G23 now includes a replay control that takes the informed process's register
marginal at each step from an external schedule and removes its correlation
with phase. It preserves the same phase and installed-action marginals on the
symmetric two-state example, but final next-phase prediction accuracy is
0.5822 versus 0.8092 with feedback; the blind control also scores 0.5822.
The replayed schedule is a diagnostic requiring external control, not an
autonomous learner or a thermodynamic implementation of that schedule.
Its saved joint laws, installation work, declared sensing/reset prices, bath
heat and finite-store trajectory are in `simulations/figures/g23_closed_loop/`.
The conservative pathwise funding rule executes two steps without a charger
and eight with the declared charger. Shared-content agreement, reconstruction
and held-out state-family scores still require an expanded model.

G24 now has saved CPU comparisons among the full linear map, a two-token
width-four attention decoder, and a two-node phase graph at zero, one and
three communication rounds, at seeds 24--26 and one noisy setting. The new
artifact-only `g24_artifact_audit.py` recomputes training and held-out errors
and code rank from the saved datasets and checkpoints, and rejects checkpoint
drift. The noiseless held-out squared errors across seeds are about
0.053--0.329 for attention and 4.679--17.188 for the three-round phase
candidate; the full linear map has floating-point-zero error. These are
candidate- and training-budget-specific outcomes. The task splits and scores
were declared in code before these runs but were not externally preregistered;
further task families and a controlled communication-deadline sweep remain
open. None of the three G items is marked complete by this audit, and no
publication claim or physical energy estimate has been added.

**G24 overlap stress (2026-09-24).** A held-out perturbation now changes only
the second local view's two overlapping quantities while holding the global
target and first view fixed. Distances 0.5 and 1.0 are saved in each candidate
dataset, and the artifact audit recomputes their scores from checkpoints.
At distance 1.0 in the noiseless seed-24 run, squared error is 0.5 for the
full linear map, about 2.185 for attention, and about 88.20 for the three-round
phase candidate. The phase score varies sharply with seed (about 44.49 and
2332.39 at seeds 25 and 26), exposing poor robustness of this fitted readout
rather than an architecture-wide limit. This intervention creates incompatible
local observations, so the target is a declared robustness reference; the
exact-gluing premise does not hold for the perturbed pair.

**G22–G24 closure (2026-09-24).** The three checklist items above are closed
for their stated formal and finite-model acceptance criteria; none establishes
cortical realization or an experience measure. Publication claims and tracked
PDFs are current, and `simulations/g_followup_results.tex` is generated by
`g_followup_macros.py` from saved JSON summaries without rerunning any solver
or training. Its drift test passes. The arXiv submission was repacked and
compiled from its tarball after the source changes.

G22's `Phase8_OrderSpeed.lean` proves the rotation-invariant speed inequality
and integrated arcsine bound for a smooth positive normalized periodic path
with `0 < r < 1`. The proof makes its continuity, periodicity and
differentiation-under-the-integral hypotheses explicit; it claims no
absolutely continuous extension through zero order. The finite-volume report
now recomputes both discrete continuity and trapezoidal current cost from
saved density and flux, and rejects tampered trajectories. At the exploratory
`r = 0.3` crossing, the 256-cell run reaches the threshold at about 0.9239,
with current cost about 0.1201 against a floor of 0.04623. The crossing time
changes by about 0.00193 from 192 to 256 cells. The 30-path homogeneous
schedule/diffusion/duration grid includes uniform and relaxation controls;
the 18-path two-frequency grid separates aggregate from cohort-resolved cost.
Its report recomputes both ledgers from saved cohort flux. Frequency spread
invalidates the homogeneous drift description of each cohort, while the
aggregate continuity bound still applies to their marginal. The threshold
was selected after exploratory inspection; these are numerical onset
illustrations, not a prospective cortical test or a continuum error theorem.

G23's formal joint transition and finite-store ledger are paired with the
binary process in `g23_closed_loop.py`: register orientation installs a signed
phase coupling, the bath-supported phase transition obeys local detailed
balance and positive support, the sensor observes the new phase, and the
observation updates the same register. The saved path law charges preparation,
sensing, reset and installation work; bath heat covers the phase flip only.
Without replenishment, its positive continuing expected work drives the
unrestricted store below zero, while the conservative stop rule halts safely;
the named external charger sustains the declared horizon. The independent
training episodes and two held-out field families in `g23_benchmark.py` use
one frozen register readout. In the lower-field held-out family, informative
next-phase accuracy is 0.7832 versus 0.5522 blind and 0.5576 replayed; the
matched controls have zero marginal phase order. The artifact-only benchmark
audit verifies the sampled accuracy, binary symbol agreement and phase
reconstruction error. This symbol agreement is the model's toy shared-content
measure; independent semantic decoders, sensing/reset reverse protocols,
physical replenishment and cortical calibration remain empirical work.

G24's shared task varies linear bottleneck rank, independent local noise,
overlap disagreement, self-state shift, communication rounds and graph-hop
intervention distance. Saved checkpoints contain the actual internal codes;
artifact-only audits recompute their ranks and scores and the weighted linear
spectral-tail floor. The parity split has rank-two predicted and held-out
errors both equal to 2 in the noiseless task. The scene-family split gives
near-zero full-linear training error and about 2.667 held-out error, showing
failure under a changed input family rather than a failure of the training-law
rank theorem. The small attention and phase controls also fail on that held-out
family under their declared CPU budget; no architecture-wide ranking follows.
The three-node phase chain's encoding is unaffected by a two-hop intervention
until two synchronous rounds. A protocol-only commit `033522c` fixed seeds,
splits, scoring, success rule and source hashes before the confirmation batch.
Seeds 27--29 and the noisy seed-27 run passed all artifact audits and the
120-second per-candidate CPU budget; the prespecified noiseless full-linear
criterion (training error below 0.1 and held-out error above 1) held at all
three seeds. Hardware energy was not measured and is not inferred from model
labels. A named-hardware energy study and independent biological content
decoders are separate follow-ups.

The Lean leaf gate records `Phase8_OrderSpeed`, `Phase3_FeedbackLedger`,
`Phase6_CovarianceRank` and `Phase6_SampledRank` as terminal results rather
than inventing downstream chain claims. The three predecessor modules
`Phase8_OrderCurrent`, `Phase3_PhaseFeedback` and
`Phase6_InputWeightedRank` now have genuine consumers and their leaf
exemptions were removed. `check_leaves` passes with the updated baseline.
The exact G24 source bytes named in the timestamped protocol are retained
under `simulations/figures/g24_confirm_source/`; active copies were formatted
after the confirmation run, and artifact audits still pass.

### G25–G30 — Fast followers from the G22–G24 manuscript review

The thermodynamic section has a defensible main-text role through the cost of
changing order and the explicit conditions on feedback and resource supply.
Its physical interpretation remains conditional. The digital section supplies
reconstruction and causal-access measurements; the current CPU examples do
not establish a GPU or LLM limitation. These small follow-ups tighten those
claims and feed the still-open G20/G21 audit and delivery work.

- [x] **G25 — Remove the remaining macroscopic-energy overclaim.**
      The opening of “Thermodynamics and composition” still calls the resource
      condition nonrestrictive for every macroscopic candidate, while the
      corrected installation section leaves mode energy and conversion factor
      uncalibrated. Replace that universal conclusion with the actual scope:
      restrictiveness for a physical candidate depends on its specified modes,
      prices, coupling reduction and diffusion. Audit the composition table,
      supplement and primer for the same inference. Keep stored mode energy,
      metabolic expenditure, work allowance and register heat distinct.
      **Verify:** no passage infers satisfaction or vacuity of the installed
      energy condition from macroscopic size or a large metabolic budget alone.

- [x] **G26 — Center the thermodynamic section on its useful bound.**
      Lead with G22's finite-time order-change current-cost floor and the
      stationary ordered zero-current control. Explain the measurable inputs
      (endpoint order, elapsed time, diffusion and a reconstructed current)
      and retain the smooth positive-density and 0 < r < 1 domain. State that
      the result constrains a change in order, not an arbitrary coupling ramp
      or maintenance of stationary order. Keep the exploratory status of the
      numerical onset threshold visible. Use the saved cost/floor macros if
      a numerical illustration helps; do not rerun sweeps for prose changes.
      Compress the feedback and repeated-operation material to the conclusions
      needed in the article, with derivations in the supplement. Preserve the
      distinction between a standalone result and an edge consumed by the
      eight-hypothesis composition.
      **Verify:** a reader can identify what the bound rules out, its domain,
      and the additional physical conversion needed before calling it thermal
      dissipation or cortical power. No implication from heat to compatibility
      or self-reconstruction is suggested.

- [x] **G27 — Audit the feedback witness against the thermodynamic prose.**
      Map each main-text heat/work assertion to the formal theorem and the
      implemented stage that supports it. In particular, check whether “For
      that model” before the cumulative entropy/heat/work inequality suggests
      that the numerical G23 sensor and reset stages satisfy the full thermal
      protocol: their assigned prices and phase-flip bath heat do not by
      themselves supply reverse channels and local detailed balance for the
      whole cycle. Make any additional assumptions explicit at that sentence.
      Audit the “near-equilibrium” characterization separately: positive path
      support, local detailed balance and energies of order kT do not alone
      specify proximity to equilibrium. Retain the label only with a defined
      criterion and evidence for the witness. Preserve expected-budget versus
      trajectory-store distinctions and the passive Markov premise.
      **Verify:** the text distinguishes proved conditional inequalities,
      numerical stage accounting and an implemented physical heat protocol.
      Every retained regime claim has an explicit supporting condition; a
      complete sensing/reset reservoir model remains a separate research task
      if it is not already available.

- [x] **G28 — State what the G24 confirmation actually replicates.**
      Artifact review found identical train/test arrays at noiseless seeds
      27–29. The deterministic linear fit repeats the same calculation;
      nonlinear initialization changes are a different source of variation.
      Describe the noiseless linear result as numerical reproducibility and
      distinguish it from robustness across independent datasets or state
      families. Preserve the timestamped protocol and its actual success rule,
      while stating which runs were exploratory and which were fixed before
      execution. Do not retroactively reinterpret repeated zero-noise rows as
      independent observations.
      **Verify:** an artifact-only check reports array equality and the actual
      sources of variation; the article, supplement and working summary agree
      on the limited evidential meaning of the confirmation batch. Any new
      noisy/family replication is separately specified before execution.

- [x] **G29 — Add the successful target-map control to the G24 account.**
      The saved task supplies a target operator that reconstructs every
      noiseless held-out state exactly, including all three confirmation
      datasets checked in review. Add this explicitly supplied-map control to
      the artifact report alongside the fitted full-linear decoder. Label it
      as an oracle using the declared task map, not a decoder learned from the
      restricted training family. Explain how the scene-equality training
      constraint leaves a direction unidentified and why the fitted decoder's
      failure does not establish an intrinsic capacity limit. Keep the parity
      training-law rank floor distinct from a held-out error guarantee.
      **Verify:** failing tests precede analysis changes; the report recomputes
      control error from saved arrays, and any publication number comes from
      a saved summary through a drift-tested macro. No production training is
      needed for this control and no architecture-wide ranking is inferred.

- [x] **G30 — Tighten the digital section and deliver the corrected prose.**
      Correct “earlier positions” to “positions at or before t” in the
      decoder-only causal-mask paragraph, matching the formal causal past.
      Keep the section proportionate to its demonstrated contribution:
      reconstruction across a declared family, interventions on internal codes,
      independently decoded shared quantities and access within a deadline.
      Preserve the actual linear-rank premise, the softmax counterexample and
      the absence of a measured GPU energy or actual LLM benchmark. Present
      G24 as a finite task illustration with the G28/G29 qualifications.
      **Verify:** manually compare compressed claims to their theorem premises
      and saved controls under G20. For G25–G30 publication edits, run applicable
      gates, rebuild each affected tracked PDF with two LaTeX passes, review
      primer consistency and refresh an existing arXiv build under G21. Record
      validation without treating code tests as a scientific meaning audit.

**G25–G30 completion (2026-09-24).** The article now leads its thermodynamic
discussion with the G22 finite-time probability-current floor, states its
smooth positive-order domain and gives the saved exploratory cost and floor
through generated macros. The stationary zero-current control and the lack of
a physical heat conversion remain explicit. The universal macroscopic-energy
claim was removed: mode prices and coupling calibration decide whether the
installed-energy condition restricts a candidate. The G23 cycle inequality is
identified as conditional on a shared physical ledger and stagewise local
detailed balance; the numerical witness specifies phase-flip bath heat and
declared sensing/reset work prices, not a complete heat protocol. The
two-bit witness is no longer described as near equilibrium without a measured
criterion.

The G24 artifact audit now computes the declared target map's training and
held-out errors directly from saved arrays. It gives zero noiseless held-out
error on the scene-family task, while the fitted full-linear decoder gives
about 2.667. A separate artifact report shows that noiseless confirmation
seeds 27–29 have identical train/test arrays; the noisy seed-27 inputs differ.
The manuscript distinguishes repetition of the deterministic linear fit from
variation in nonlinear initialization and states the training-family rank
limit. The causal-mask wording now includes position $t$ itself. The primer
was brought into agreement with these results and with the finite G23
feedback model.

Focused analysis tests (28) pass, along with Ruff, strict mypy, Bandit,
Vulture, Xenon, Tach, prose, Table S1, coverage and figure checks. Main,
supplement and primer PDFs were rebuilt with two LaTeX passes each; the arXiv
tarball compiled from its unpacked files, and freshness checks pass. No Lean
source or reference changed. These are presentation and artifact-audit
corrections; a physical sensing/reset reservoir model and cortical mode-price
calibration remain separate research questions.

### G15, G18, G20 and G21 closure — 2026-09-24

**G15 conclusion.** All saved G2/G11 checkpoints are complete. The
artifact-only analysis now records log-fit residuals, slopes after omitting
each speed, maximum precritical and initial order, coupling-grid step and
censoring for the three size/threshold settings. On all eligible legs the
fitted delay exponents are 0.444, 0.637 and 0.720; on matched speeds they are
0.444, 0.634 and 0.710. Their log-residual RMS values are 0.059, 0.091 and
0.240, and the N=8000 low-threshold fit contains a log residual whose
magnitude is 0.474. The N=2000/high-threshold fit is a usable finite-window
description, while the larger-population low-threshold fit has appreciable
scatter and the three fits support no common asymptotic exponent. Across the
saved legs, precritical order can exceed the absolute escape criterion;
first-postcritical detection can then be immediate. The largest saved
coupling step is 0.010, so delays near that scale are resolution-limited.
The N=2000/high-threshold and N=8000/low-threshold settings contain censored
replica legs. The low-threshold N=2000 bootstrap has zero-delay draws, which
are excluded from log fits; its bootstrap fraction above one-half is a
resampling summary, not a hypothesis-test probability. The stationary
square-root exponent is a separate theorem, not a finite-ramp finding. The
three-speed heterogeneous fits and the two-speed width-1.5 control cannot
settle exponent robustness; conduction delays and E/I balance remain open.
The existing `acebron2005` citation and its Lorentzian-threshold discussion
were checked against the publisher record and the review's equation. The
article, supplement and primer now state the same finite-range conclusion.

**G18 completion.** The abstract, introduction, body and discussion follow
the G16 coherence/compatibility/reconstruction outline. The supplement keeps
the derivations and controls, including the G22–G24 additions, while the
article carries their scope and empirical implications. The main-text
compression audit in `tasks/g16_outline.md` gives the migration map. Under a
single source-token proxy that removes figures and longtables and counts the
abstract through the last discussion section, the article changes from
13,459 words at `7d8c5ba` to 9,130 now, a 32.2% reduction. This proxy counts
math and TeX arguments and is wider than the earlier `detex` prose count.
PDF text extraction, which includes tables and references, changes from
18,201 to 13,860 words for the article. The supplement changes from 50,465
to 51,665 extracted words because the later G22–G24 methods and theorem map
add technical content; its repeated introductory argument is not kept as a
second article. The abstract has 160 tokens by the source proxy and remains
entirely on the first rendered page. The attempted-rewrite stash remains
untouched.

**G20 claim audit.** Each article headline was read against its model,
supporting Table S1 row and failure condition:

| Article claim | Table S1 or empirical support | Limit retained in the article |
| --- | --- | --- |
| Stored modes bound mean coupling and the stationary branch has a threshold | Installed-energy and Critical Coupling Threshold rows | Prices, spatial reduction and cortical identification are inputs; energy above the necessary bound is insufficient. |
| Phase order constrains shared content only through encoders | Coherence bounds vector-content disagreement, pair-count, patch-nerve and locked-graph rows | Overlap encoders, cover geometry or locking data are supplied; synchrony alone does not identify content. |
| Compatible sections glue and reconstruction fixes a state | Global gluing, Reflexive Topology and Reconstruction rows | Cover, shared quantities, map accuracy and readout gain are supplied; physical realization and experience do not follow. |
| Changing order has current cost; feedback has a conditional heat budget | Order and probability-current dissipation and Agency/feedback rows | Stationary order has zero-current examples; current needs thermal conversion, and sensing/reset heat needs a full protocol. |
| A digital candidate can be tested for rank, code resolution and deadline | Spectral error, Input-weighted reconstruction floor, Information ceiling and Locality rows | The linear rank premise and specified channels/graphs are essential; the CPU task gives no GPU energy or LLM-wide result. |
| Finite ramp and EEG results guide an awakening test | Saved ramp/EEG analyses; not Lean claims | Operational escape depends on threshold, noise and sampling; EEG is estimator calibration, and the held-out field/connectivity comparison is proposed. |
| Unity and minimal self are interpretations | Conditional composition and joint-witness rows | Mathematical satisfiability gives neither cortical realization nor an experiential endpoint. |

**G21 delivery.** The ramp-analysis tests and generated-macro drift checks
pass. Ruff, strict mypy, Bandit, Vulture, Xenon and Tach, the prose and
hedging checks, Table S1 status and claim coverage, figure duplication,
PDF freshness and arXiv freshness all pass. No Lean source or new reference
was introduced. Both publication PDFs and the primer PDF were compiled twice;
the abstract is fully on page one, figure captions and Table S1 were checked
by PDF text extraction, and the merged arXiv document compiled from its
unpacked tarball. Its retained content is a conditional mathematical
framework with finite numerical controls and a proposed spatial onset
comparison. Cortical coupling, content decoding, complete feedback heat
accounting and experience remain empirical questions.
