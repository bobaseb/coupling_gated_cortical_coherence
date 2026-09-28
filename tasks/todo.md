# Working ledger

**Superseded ledgers are read out of git history, not kept in the tree**
(AGENTS.md §5). Everything closed through the U46 review response — the U
block's built items and pass records, and the H, N, C, D, V and G blocks with
their dated sections — is `c3cf854:tasks/todo.md`. The M/W/X/Y/Z/G ledger is
`8d8ce0f:tasks/todo.md`; the P submission-readiness items and the pass records
before it are `dde1a36:tasks/todo.md`. The R research programme (R1–R12) is
live in `tasks/research_programme.md`. This file carries open items only;
closed ones are marked in place, then archived the same way.

## U — Physical unity: a human-consciousness requirement current AI lacks

**Intent.** The paper in `unity/`: unity of conscious content requires
physically enforced agreement. As stated since U44–U46, within every window of
the contents' time scale, some graded carrier of each region depends above the
noise floor on every region it overlaps, through a contracting coupling. The
margin theorem excludes content read from bits. Constraints and history:
`c3cf854:tasks/todo.md` §U and `CHANGELOG.md`.

- [x] **U47 — Correlated carriers: replace the declared independence.** The
  window bound (1 − p)^K (`measure_not_reachesWithin_le`) assumes the carriers
  joining two regions fail independently, and the carrier counts 10/100/1000
  are declared. Nearby membranes share input, and a passing state is a
  near-threshold event, so positive correlation raises the chance that no
  carrier passes; fully correlated carriers fall back to the single-carrier
  value (0.085 per 400 ms in the sparsest regime). Designed 2026-09-27, not
  started; do (a)–(c) before (d).
  (a) *Simulation* (`unity_occupancy.py`, tests first). V_i = S + P_i: S a
  shared OU of variance c, P_i private of variance 1 − c, same τ, so the
  marginals are unchanged. Given S's path the carriers are independent, so
  P(no link) = E_S[(1 − h_S)^K] and the pairwise correlation of passing is
  ρ = Var(h_S) / (h̄(1 − h̄)). Propagate the private coordinate p = V − S on
  the grid for M sampled shared paths at once (an n × M mass matrix; fixed
  seed, standard error reported); the threshold, reset (μ − S) and
  `passing_states` shift by S(t); burn-in of several τ; record h_S at 40 and
  400 ms in one run. Sweep c ∈ {0, 0.1, 0.25, 0.5, 0.75, 0.9}, the six
  (τ, rate) regimes, scales {0.25, 0.5, 1}, K up to 10^4. Report c*, the
  largest c at which the link probability at K = 100 per 400 ms stays ≥ 0.9.
  Output to a new `figures/unity_occupancy/correlated.json`, leaving U45's
  summary byte-identical. Tests: c = 0 reproduces `hit_probability` and
  (1 − h)^K; P(no link) non-decreasing in c; ρ(0) ≈ 0; deterministic under
  the seed; small config < 30 s. About 20–30 min on the Pi; split helpers
  so the xenon rank stays below C.
  (b) *Lean* `measure_not_reachesWithin_le_variance`: for N = Σ_k 1{E k}, each
  E k measurable and implying `ReachesWithin`, with E[N] > 0, P(no reach) ≤
  Var N / E[N]². Via {¬reach} ⊆ {N = 0} ⊆ {E[N] ≤ |N − E[N]|},
  `ProbabilityTheory.meas_ge_le_variance_div_sq` (Mathlib
  `Probability/Moments/Variance.lean`) and `MemLp.of_bound`. No independence.
  Doc-string: exchangeable reading (1 − h)(1 + (K − 1)ρ) / (Kh), which tends
  to ρ(1 − h)/h, a floor set by correlation, not by K. Then the proof-
  companion chain (extract, pdf, check).
  (c) *Anchor.* Verify online a range for the shared share of membrane-potential
  variance between **neighbouring** cells in awake cortex: the carriers
  joining a to b are b's cells receiving from a, which are neighbours. Under
  the model the Vm correlation equals c. Candidates: Poulet & Petersen 2008
  (dual whole-cell, behaving mice); Crochet et al. 2011 ("highly correlated
  membrane potential dynamics"); Ecker et al. 2010 and de la Rocha et al.
  2007 (spike-count correlation versus input correlation). **Risk:**
  neighbouring Vm correlations may be high in some awake states, so the
  result may weaken the per-window claim. Outcome policy as in U36: report
  it, and stop before (d) if the link falls well below the paper's current
  statements.
  (d) *Paper.* §enforcement link sentences at the cited c (ρ, c*, and the
  floor in words); Limitations "The cortical estimates" states the model's
  scope instead of independence; `app:occupancy` method; a `tab:formal` row;
  `\uCor…` macros through `unity_macros.py` with drift and mutation tests;
  abstract and claim 1 only if the result changes them; PDF, arXiv build,
  CHANGELOG if a claim is withdrawn.
  *(a) done 2026-09-27; stopped before (d) under the outcome policy.*
  `unity_correlated.py` → `correlated.json` (256 shared paths, seed
  20260927, ~55 min on the Pi); the shared increment is applied inside the
  exact step (a linear split added spurious variance, ~10 % bias in h). The
  marginal is unchanged (h̄ within MC error); resolution check: ρ 0.365 →
  0.367, links agree to 1e-3. Worst regime, smallest noise share (1/16):
  400 ms link with K = 100 is 0.9999 / 0.9986 / 0.988 / 0.907 / 0.72 at
  c = 0 / 0.25 / 0.5 / 0.75 / 0.9 (K = 1000: 0.99 at c = 0.75); c* ≥ 0.75 in
  every regime and scale, ≥ 0.9 in 8 of 12. ρ up to 0.29 at c = 0.75.
  **Two printed statements fail at realistic c:** "a window without one
  [K = 100] occurs less than once in 10^3" (miss 0.0014 at c = 0.25, 0.012
  at 0.5, 0.093 at 0.75) and "within 40 ms the probability is at least 0.59"
  (0.51 / 0.38 / 0.23). The headline (a passing carrier within 400 ms with
  high probability) survives to c ≈ 0.75 at K = 100. (c) anchor verified
  qualitatively: Poulet & Petersen 2008, *Nature* 454:881–885, "highly
  correlated during quiet wakefulness", reduced during whisking; the
  numbers 0.72 ± 0.11 / 0.33 ± 0.17 are from a search summary, **not yet
  read in the paper**. The same abstract: single spikes are driven by "a
  large, brief and specific excitatory input that was not present in the
  V(m) of neighbouring cells", i.e. the near-threshold drive is private,
  which the one-component model does not capture. (b) Lean not started.
  *(d) done 2026-09-27 at the author's request (option 1):* §enforcement keeps
  the independent-carrier numbers as baseline and states the correlated
  result (`\uCor…` macros, floored lower bounds and ceiled upper bounds, with
  drift and mutation tests); Poulet & Petersen cited for the qualitative
  statement only; Limitations and `app:occupancy` updated; CHANGELOG entry.
  (b) moved to U47b below.
- [x] **U47b — Lean: the window bound without independence.** As (b) above:
  `measure_not_reachesWithin_le_variance`, P(no reach) ≤ Var N / E[N]², then a
  `tab:formal` row and the proof-companion chain. The paper currently says
  the formal per-window bound is the independent one (Limitations).
  *Done 2026-09-27:* measure_not_reachesWithin_le_variance in
  Phase10_PhysicalUnity.lean: for measurable events E k each implying
  ReachesWithin and N their count with positive mean, P(no reach) ≤ Var N /
  E[N]^2, under IsFiniteMeasure and with no independence; Chebyshev on N = 0.
  Docstring gives the exchangeable floor ρ(1 − h)/h. lake build and the axiom
  audit pass; proof companion rebuilt. tab:formal row added and Limitations
  now states both forms.
- [ ] **U47c — Read Poulet & Petersen 2008 in full.** Confirm the Vm
  correlations (search summary: 0.72 ± 0.11 quiet, 0.33 ± 0.17 whisking;
  not read in the paper) and the distance between recorded cells. If
  confirmed, cite measured values against the swept shares in §enforcement
  (e.g. the link at c ≈ 0.33 and 0.72) instead of a qualitative statement,
  and consider sweeping c = 0.33 and 0.72 exactly. Also consider a second,
  private near-threshold drive (their spikes are driven by input absent from
  neighbours' Vm), which would make the one-component model pessimistic.

*Review pass 2026-09-27 (score 4/10 standalone, ~4.5 read with the
companion; 5 = reject).* Verdict: well written, honest about its limits,
cheap theorems and an expensive premise, and reviewers will score the
premise. U48–U56 are ordered by leverage; U57–U58 are the gaps a second read
found. Work order: U49 (cheap, removes an easy objection), then U50/U52
(decide the paper); U47's simulation can run alongside. Estimated ceiling with
everything done: 5.5–6 at *Neuroscience of Consciousness*; about 5 if U47
comes back badly; above 6 needs data (a bridge pilot).

- [x] **U48 — Make the bridge the centerpiece.** The analog versus quantized
  bridge at matched transfer entropy is the only test that separates P from
  computational functionalism, and the paper's most original content. Make it
  claim 1, expand §tests' treatment, and add a feasibility sketch in rodent or
  NHP with decoded agreement as the readout: closed-loop hardware, recording
  and stimulation sites, the transfer-entropy estimator and trial counts.
  *Done 2026-09-27, trial counts deferred:* the bridge is claim 1 and the
  abstract states its prediction before the proofs; §tests "A first
  preparation" anchors the loops in Jackson, Mavoori & Fetz 2006 and
  Guggenmos et al. 2013 (event-triggered, i.e. the quantized arm), with
  transfer entropy (Schreiber 2000); all three verified via Crossref. Trial
  counts need the power of the companion's excess-agreement statistic,
  which is N20; the paper says so instead of inventing a number.
- [x] **U49 — The fluctuation yardstick looks rigged.** 2Φ(½) − 1 ≈ 0.38 is
  also the largest response a Gaussian-noise threshold gives to a shift of one
  noise amplitude, so binary readouts fail by the choice of constant and at
  best tie it. (a) Justify the constant independently of that coincidence, or
  show the chip/membrane separation is robust across a range of yardsticks:
  the margin of 506 noise amplitudes suggests it is, so report the passing
  fractions as a function of the yardstick. (b) Settle ≥ versus > in "reach"
  in text and Lean; at ≥ a bit sitting exactly on its threshold passes.
  *Done 2026-09-27.* (a) `unity_occupancy.py --yardstick` →
  `yardstick.json`, `\uYard…` macros; §enforcement "The yardstick" and
  `app:occupancy`. Membrane best response ≥ 0.64 in every regime and noise
  share; at yardsticks 0.01–0.6 the logic node passes nowhere and the 400 ms
  visit probability is ≥ 0.037 at 0.6 (0.085 at θ*). (b) The review's premise
  was wrong: asked in both directions, a binary readout's response is at most
  Φ(1) − ½ ≈ 0.34 < θ*, so no tie arises and ≥ stays, in text and Lean
  (`θ ≤ shiftResponse`). Lean untouched: every theorem takes θ as a parameter.
  Noted, not a defect: `GradedAboveNoise` is vacuous when Θ ≤ σ (a carrier
  within its noise of threshold); the bit theorems assume a change above the
  noise within the margin, so they are unaffected.
- [x] **U50 — Argue "one subject ⇒ one system at the noise floor", or reframe
  the abstract.** The step from "unity counts subjects" to "systems are
  counted by graded dependence above the noise floor" is asserted, and
  Block's nation and the scattered records are intuition pumps. A
  functionalist rejects exactly this step. Either give it an argument (why
  this grain and not causal integration at another), or change the abstract's
  "we argue that unity requires" to "we propose P and derive its
  consequences". Keep P stated plainly (memory: the author wants the premise
  stated, not hedged); this is about what the paper claims to have *shown*.
  *Done 2026-09-27 with U52:* argued, abstract unchanged. New §enforcement
  paragraph "Unity is not one more content": on Bayne's mereological account
  (verified online) unity is parthood in one total experience, parthood is
  not a further part, and computed agreement only writes another record
  (a regress; a workspace's common reader included). The threshold-crossing
  scale is excluded because it is that record exchange. The closing states
  the dialectic: a functionalist rejecting P must reject one of two claims.
  The intro's reason and Limitations "The premise" follow (an access account
  of unity rejects the first step).
- [x] **U51 — Present the margin theorem as a lemma.** It is one step
  (continuous map into a locally constant readout). Put the contribution's
  weight on what is not trivial: the noise-floor criterion, the noisy margin
  bound and its attainment, and the occupancy measurement. Lean-checking a
  one-step lemma draws attention to how little is checked.
  *Done 2026-09-27:* "the margin lemma" throughout; "the noisy margin
  theorem" is named where introduced as the form that carries the argument;
  abstract and claim 1 now lead with the noisy bound and its attainment.
  Lean names unchanged (no identifier in the main text).
- [x] **U52 — "Each bit is a separate system" needs more than one paragraph.**
  Physicists will read it as a redefinition, since crosstalk and a shared
  supply are real interactions. The whole paper rests on this move: expand
  the argument that the noise-floor scale belongs to the parts, and why
  sub-margin crosstalk does not count.
  *Done 2026-09-27:* conceded, not denied: crosstalk and a shared supply make
  the voltages one system; unity is of contents, read through margins, which
  factor to within the error rate. "Its contents are as many systems as it has
  bits, carried on voltages that form one."
- [x] **U53 — Demote or compress §reach.** The r^−4 threshold is classical
  (Chung–Fuchs, Kunz–Pfister), and the field estimate shows the
  non-synaptic tail dies within millimetres, so at centimetre scale the
  section says only that synapses are graded. Candidate: drop r^−4 from the
  abstract and claim 2, compress the section, keep the proofs in the
  appendix. Must be consistent with U19's restatement.
  *Done 2026-09-27 with U19's unity half:* r^−4 out of the abstract and
  claim 2; §reach is two paragraphs plus "Agreement in time" (proofs and
  simulations in `app:reach`). Claim 2 is at the phase level; "From phases
  to contents" names the companion's bridge assumption across centimetres,
  and Limitations says the same. The field sentence says the long-range part
  is synaptic.
- [x] **U54 — The weak-nudge prediction is low-risk.** Weak fields shifting
  graded decoded content in connected areas is expected under almost any
  theory, so the test can refute P but barely confirms it. Say so in §tests,
  or sharpen it: what does P predict that generic modulation does not (for
  example, proportionality below threshold and direction toward agreement,
  not merely a change)?
  *Done 2026-09-27:* §tests says a change alone confirms little and states
  the form P predicts: sign toward agreement, proportional down to the
  weakest strength that moves the stimulated region, no threshold; wrong sign
  or a threshold counts against P.
- [x] **U55 — Sharpen the delta against Kleiner 2024 and IIT/Findlay 2024.**
  "Digital hardware suppresses its physics" is already published (Kleiner),
  and IIT already denies simulations experience. State the novel part in
  §related: the contraction condition, the noise-floor criterion and the
  bridge test.
  *Done 2026-09-27:* §related names the three additions to Kleiner & Ludwig
  (noise-scaled system count, contraction, the bridge) and says P's verdict is
  read from one measurement on both substrates, where IIT's is read from
  causal structure.
- [x] **U56 — Condition P on the companion's correlate; present a two-stage
  program.** The companion calls the glued state a *proposed correlate* and
  says "nothing here establishes a consciousness criterion", while the unity
  paper takes it as the definition of unity and states a necessary condition
  on it: a firm premise on a hedged proposal. In `unity/main.tex`, state that
  P is conditional on that identification, and present the companion's
  excess-agreement test (perceived versus unperceived) as stage one: if it
  fails, P has nothing to constrain; if it passes, the bridge asks whether the
  agreement must be enforced. Alternatively commit to the identification in
  companion v2 (U20).
  *Done 2026-09-27 (unity side):* §cover states P is conditional on the
  companion's proposed correlate and lays out the two stages. U20(d) remains
  the companion-side decision.
- [x] **U57 — Answer gradual replacement (fading and dancing qualia).** Chalmers'
  argument (neurons replaced one at a time by functionally identical digital
  units; verify online: Chalmers 1995 in Metzinger (ed.) *Conscious
  Experience*, and *The Conscious Mind* 1996, ch. 7) is the standard objection
  to any substrate-dependent view, and the paper does not mention it. A
  philosophy referee will raise it. P's answer is specific: the replaced units
  read their inputs through margins, so each replacement removes graded
  dependence across its links, and unity fails at the boundary of the replaced
  region while reports, computed from contents, stay unchanged. Say what P
  predicts along the sequence and why the reports do not track it (the
  simulation objection of §enforcement, applied part by part). The bridge is a
  local, testable instance of partial replacement: say so in §tests, which
  also serves U48.
  *Done 2026-09-27:* §enforcement "Gradual replacement", citing Chalmers
  1995 (verified: Metzinger (ed.), *Conscious Experience*, Imprint Academic,
  pp. 309–328). Two parts: exact replacement is unavailable (margin lemma),
  so behaviour is an empirical question the bridge asks for one connection;
  where replacement is exact, P accepts that reports stay while unity
  changes, because unity is not a content. *Open tension for U48:* the
  evidence standard of §tests counts behaviour as evidence about unity, so
  the paragraph restricts it to systems whose contents ride their own
  coupling; a referee may call that ad hoc.
- [x] **U58 — Cite and position against Butlin et al. 2023.** "Consciousness in
  Artificial Intelligence: Insights from the Science of Consciousness"
  (arXiv:2308.08708; verify authors, year and venue online) is the default
  reference point for any claim that current AI lacks a property of
  consciousness, and it assumes computational functionalism as a working
  hypothesis. One paragraph in §related: P is the premise that report sets
  aside, stated so that it can be tested (the bridge), and it adds a
  substrate condition to an indicator list rather than a new indicator.
  *Done 2026-09-27:* verified on arXiv (19 authors, 2308.08708; adopts
  "computational functionalism … as a working hypothesis"); new §related
  paragraph "Indicator properties".

*Review pass 2026-09-27, second read (score ~4.5/10 after U49, U50, U52;
5 = reject).* Items the first pass did not raise, plus the author's
reframing (U65). Work order: U65 first (it sets the frame the others are
written in), then U61, U59, U60, U62, U63, U64 last.

- [x] **U65 — Reframe: a finer grain, not a refutation of functionalism.**
  Author's direction, 2026-09-27: a metaphysical position is not refuted by
  experiment, and the paper does not try to. P is itself a functional
  condition stated at the grain of graded physical dynamics (the intro
  already says so); the contribution is that at this grain cortex and
  mainstream digital chips come apart, while at the grain of an algorithm
  they do not. The bridge asks which grain unity tracks. This does not hedge
  P: the premise stays as stated; only its opponent changes. Sites, all in
  `unity/main.tex`:
  (a) Abstract "rejects computational functionalism" → P fixes the
      functional role at the grain of graded dynamics, where cortex and
      digital chips differ.
  (b) Intro, paragraph after Premise P, "therefore rejects computational
      functionalism about unity" → P and algorithm-grain functionalism are
      two grains of one kind of claim; say which cases they classify
      differently (the simulation).
  (c) The bridge claim "which separates P from computational
      functionalism" → "which tests whether unity tracks the graded grain
      or the algorithmic one".
  (d) End of "Counting systems at the noise floor", "A computational
      functionalist who rejects P must reject one of the two" → state the
      two claims as what fixes the grain; keep the dialectic, drop the
      adversary.
  (e) §tests "Separating coupling from information" and the bridge readout
      ("decides between P and computational functionalism", "supports P
      over the information-flow form") → the bridge holds information flow
      fixed and varies the grain of coupling; unity following the analog
      loop is evidence that unity tracks the finer grain. Check U48's new
      text and U57's "Gradual replacement" for the same framing.
  (f) Limitations "The premise", "The bridge's reach", "Human evidence":
      a fine-grained functionalism agreeing with P is the intended reading,
      not a leftover. Rewrite as scope, not retreat.
  (g) §related "The grain of a function" becomes the frame, not one entry:
      move its point (Block's coarse grain, Godfrey-Smith) into the
      introduction.
  Mind check-claims (§10): the rewritten sentences must not add disclaimers
  outside `sec:limitations`. Interacts with U55 and the U58 paragraph
  (positioning against Kleiner, IIT and Butlin et al. becomes "which grain",
  not "who is right") and eases U59/U60, which no longer carry a refutation.
  PDF and arXiv rebuilds per §6/§7.
  *Done 2026-09-27:* all seven sites rewritten to the grain framing. Abstract
  and introduction state P as a functional condition at the grain of graded
  dynamics, with the Block and Godfrey-Smith point moved into the introduction
  and the §related entry removed; claim 1, §tests and the bridge readout ask
  which grain unity tracks; the dialectic closing 'Counting systems' drops the
  adversary; Butlin and Kleiner paragraphs and Limitations (premise, bridge's
  reach, human evidence) rewritten as scope. CHANGELOG records the withdrawn
  'rejects computational functionalism'.
- [x] **U59 — The regress argument proves too much.** "Unity is not one more
  content" (§enforcement) says a rule that compares and corrects records only
  writes another record. A gate is physical coupling, and a synapse also
  compares and corrects; a downstream membrane integrating spike times is
  arguably one more record too. What separates chip from cortex is the
  margin/noise-floor argument of the next paragraph, not the regress. Either
  state what makes a margin-held record different from a graded carrier
  *inside* the regress argument, or demote the paragraph to motivation for
  "Counting systems at the noise floor" so it carries no independent weight.
  U57's "Gradual replacement" leans on "unity is not a content", so check it
  too. Keep P stated plainly.
  *Done 2026-09-27:* kept the paragraph and gave the regress its stopping
  point inside it: a record is defined as a content held by a margin, so a
  rule's output is sealed off from graded state; a synapse or a membrane near
  threshold moves with every change of its inputs above their noise and is a
  further coordinate of the state, not a record. The margin separates rule
  from synapse, and the next paragraph fixes its scale. Gradual replacement
  still reads correctly on this definition.
- [x] **U60 — The criterion reads as weakened until cortex passes.** Every
  carrier → some carrier, every instant → within a window: each weakening sits
  exactly where cortex would fail. Say in the introduction what the weak form
  amounts to (two regions are one system iff some margin-free path links a
  carrier of each within the window) and why that, and not the strong form,
  is the right reading of one total state. A reader who works this out alone
  reads it as gerrymandering. Move qualification, never delete it (§10).
  U47(a)'s correlated-carrier result bears on the window form: settle U47(d)
  first or together.
  *Done 2026-09-27:* the introduction now says what the window form amounts to
  (two regions are one system when some carrier of each registers the other
  above its noise within the window, so no change above noise is sealed off)
  and why: a region is many carriers, a content is held over its time scale,
  and the strong form would split a single noisy neuron from its own inputs
  between spikes. U47(d) had already settled the correlated-carrier numbers.
- [x] **U61 — Bridge timing confound.** Matching transfer entropy by lowering
  the analog loop's bandwidth slows its relaxation, and §reach's "agreement
  in time" condition then fails P for a graded but too-slow loop. A null
  result would be ambiguous between "unity does not follow graded coupling"
  and "the analog loop was too slow". Show that the matched cutoff keeps the
  loop's relaxation time within the content window (`app:window`'s τ bound),
  or state it as a design constraint on the cutoff with its bound computed
  from the macros. Reopens U48: the centerpiece must not carry this hole.
  *Done 2026-09-27:* stated as a design constraint with its bound from the
  macros. A first-order loop settles with time constant 1/(2π f_c) and the
  bridged coupling relaxes no faster than its loop, so the analog cutoff stays
  at or above \ueBridgeMinCutoffHz (0.99 Hz), whose time constant is the
  shortest relaxation time of app:window (160 ms); if matching would take it
  lower, the quantizer's step is coarsened instead. unity_estimates.py
  generates the macro, with a test.
- [x] **U62 — Analog in-memory accelerators.** §ai says analog, in-memory
  and neuromorphic substrates "can satisfy P", so the same transformer on a
  crossbar and on a GPU would differ in unity: the reductio "The margin's
  width" tries to defuse. Say which way P decides current analog in-memory
  hardware. Typical designs digitise column currents through ADCs between
  layers, which would put them under the margin theorem; if so, say so, and
  what a passing design would need (no restoring stage between coupled
  graded contents). Verify the ADC claim against a source before stating it.
  *Done 2026-09-27:* new §ai paragraph 'Analog in-memory accelerators': in a
  64-core phase-change chip each row's current is digitized by its own ADC
  into integers, and activations and inter-core traffic run on them (Le Gallo
  et al. 2023, Nature Electronics 6:680-693, verified online and in the arXiv
  full text), so contents crossing a converter fall under the margin lemma and
  such a chip fails P between layers; a passing design needs coupled graded
  contents with no restoring stage between them.
- [x] **U63 — Literature on analog versus digital representation.** The
  definition of a symbol as "a content read through a noise margin"
  (§ai, "Symbols and physical contents") sits next to Piccinini's account of
  digital computation, Maley's analyses of analog representation, and
  Maudlin's Olympia argument on counterfactual sensitivity (candidates only;
  verify authors, titles, years and venues online per AGENTS.md §4 before
  citing). One or two sentences each in §related: where P's margin
  definition agrees or differs.
  *Done 2026-09-27:* new §related paragraph 'Analog and digital': Piccinini
  2008 (Pacific Phil. Q. 89:32-73), Maley 2011 (Phil. Studies 155:117-131) and
  Maudlin 1989 (J. Phil. 86:407-432), each verified online. P's symbol is
  Piccinini's reliable digit stated in the parts' noise; P's line follows
  Maley's discrete/continuous pair, not analog/digital; P's counterfactual
  condition is on present activity, which Maudlin's idle machinery fails.
- [x] **U64 — Split "Counting systems at the noise floor".** About 50 lines
  in one paragraph (§enforcement); the lines after "The count looks strange"
  read as patched in. Three paragraphs: the scale the parts supply; the chip
  under the noisy margin theorem; the dialectic. Do after U65/U59/U60, which
  may rewrite it.
  *Done 2026-09-27:* split into 'Counting systems at the noise floor' (the
  scale the parts supply), 'The chip, counted' (the chip under the noisy
  margin theorem) and 'What the premise rests on' (the two claims that fix the
  grain). Text otherwise unchanged.
- [x] **U66 — Cite Miller, Brincat & Roy on analog wave dynamics.**
  *Done 2026-09-27:* Miller et al. 2026 (J Neurosci 46(33):e0711262026,
  doi:10.1523/JNEUROSCI.0711-26.2026, PMID 42618509), verified online and read
  from the PsyArXiv preprint z48x7 v3. Two sentences in §related 'Field
  theories': their waves, sustained by synaptic and ephaptic coupling, are one
  realiser of graded coupling; their analog/digital line is parallelism, P's is
  the noise margin, which a parallel digital machine keeps. Their ephaptic
  effects are local and waves travel at synaptic speed, which agrees with the
  field-cone estimate.

*Review pass 2026-09-27, third read (score ~6/10 after U34, U35, U61–U66;
5 = reject).*

- [x] **U67 — Reports at the bridge.** The gradual-replacement answer lets
  reports stay while unity changes, and §tests reads unity from reports: a
  null bridge result could be excused (the U57 open tension). *Done
  2026-09-27:* §tests states that the standard binds P. The replacement answer
  covers systems built to reproduce reports by computation; a bridged cortex
  reads each region from its own coupled carriers and the quantized loop
  matches information, not behaviour, so behaviour is evidence there. One
  sentence in §enforcement points to it.
- [x] **U68 — The line is drawn inside each substrate.** The margin lemma is
  near trivial and threshold crossings are excluded as messages; a referee
  reads "digital defined out, then formalised". *Done 2026-09-27:* the lemma
  is called elementary by design (disputing it means disputing a definition),
  and a new §enforcement paragraph 'Where the line falls': the count discards
  spikes as messages exactly as it discards bit flips, cortex passes only on
  the sub-threshold range near threshold, and the verdict reverses within
  each substrate (a switching bit passes, latched neural counts fail).
- [x] **U69 — Stimulation artefact in the continuous loop.** Event-triggered
  loops (Jackson 2006) blank around pulses; the analog loop drives
  continuously and the paper discussed artefact only for the field cone.
  *Done 2026-09-27:* §tests paragraph 'Stimulation artefact': record
  multi-unit activity, drive with a current following its envelope in the
  band below; subtract the loop's own output through a calibrated transfer;
  one output stage smooths the quantizer's steps so the residual reaches both
  arms by one path; open-loop blocks measure it per arm.
- [x] **U70 — The bridge's readout without the companion.** The bridge read
  unity only as the companion's excess decoded agreement, a correlate still
  to be tested, so the empirical payoff sat two conditionals away. *Done
  2026-09-27:* the first preparation's primary readout is behavioural (a task
  combining the two areas' values, e.g. matching across their fields), with
  decoded agreement as the neural readout; §cover says a negative companion
  result removes the neural measure and leaves the behavioural one. The
  "conditional on that identification" scope sentence stays.
- [x] **U71 — §reach tied to P, the timing condition made a prediction.**
  §reach read as a separate paper and left open whether cortex relaxes in
  time. *Done 2026-09-27:* §reach opens with the two things P asks of the
  coupling (reach, timing) and points to the restoration test; 'Agreement in
  time' ends with the prediction (relaxation at most \ueTauFastMs ms across
  cortex, \ueTauLocalMs ms within a posterior zone; slower counts against P);
  the restoration test and the Limitations bullet point at it.
- [x] **U72 — Limitations read as a list of concessions.** Twelve bullets;
  'The premise' and 'The bridge's reach' conceded that P is assumed and that
  a functionalist absorbs either outcome. *Done 2026-09-27:* ten bullets, no
  scope statement removed (AGENTS §10): 'From phases to contents' folded into
  'Reach', 'Attractors' into 'Which variables are contents'. 'The premise'
  names the cortical tests as what bears on P; 'The bridge's reach' notes an
  account that sees the quantizer already sits at P's grain.
- [x] **U73 — Lean: the record regress as a theorem.** §enforcement 'Unity
  is not one more content' argues in prose that a rule reading and writing
  records only adds a record, and that the margin stops the regress. The
  mereological step (unity is not a further content, Bayne 2010) stays a
  cited premise; the regress step is formalizable in `Phase10_PhysicalUnity`
  with `CoupledAtNoiseFloor`, `SameSystem`, `response_le_of_marginRate`.
  (a) *A record joins nothing:* a region whose content has a margin rate
      `ε < θ`, with every region admitting a change above its noise within
      the margin's width, is coupled to no region; `SameSystem r j ↔ r = j`.
      Must hold when the other regions are graded (not only bits).
  (b) *No chain passes through a record:* for `i j ≠ r`, `SameSystem i j`
      in the extended system iff an `EqvGen` chain of couplings avoiding `r`
      joins them; by induction, for any finite set of records (rules on
      rules). The fiddly part is the `EqvGen` restriction.
  (c) *A graded reader joins:* three regions under `noisyLin` (U34), `i` and
      `j` uncoupled, each coupled to a graded reader `g`; then
      `SameSystem i j`. The stopping point: a reader on the chain, not a
      record beside it.
  Order: failing statements first, then proofs; then `tab:formal` rows and
  the paragraph rewritten to argue from them (claims: records drop out of
  every chain, graded readers stay in), with rebuilt PDF; then the proof
  companion rebuild (see the lean-change rebuild chain). Add a Limitations
  scope item for the write-back case unless U74 lands.
  **Success.** The regress claim has table rows; the only prose-only step
  left in the paragraph is the cited mereological premise.
  *Done 2026-09-27:* new section 'Records and readers' in
  `Phase10_PhysicalUnity`. (a) `not_coupledAtNoiseFloor_of_record` and
  `sameSystem_iff_eq_of_record`; nothing is assumed of the other regions'
  contents. (b) `sameSystem_iff_of_records` holds for an arbitrary set of
  records, so no induction on finite sets was needed; it rests on
  `eqvGen_of_isolated` / `eqvGen_iff_of_isolated` (points related to nothing
  but themselves drop out of every `EqvGen` chain, and the restricted closure
  is reflexive, so the iff needs no hypothesis on the endpoints). (c)
  `Examples/PhysicalUnity.lean`: `reader_sameSystem` under `noisyLin` with
  uniform noise on [0, 1] (response 1/2 at a change of 1/2, via `unif_rise`),
  beside `tally_sameSystem_iff`, a record whose carrier reads two graded
  regions and joins neither. `tab:formal` has four new rows; the paragraph
  argues from them and the §enforcement intro claim states the result.
  Not established: the reader witness is linear with one noise law; which
  cortical elements are readers rests on the noise-floor measurements of
  §enforcement, not on these theorems.
- [x] **U74 — Lean (stretch): write-back through a record adds no link.**
  U73 shows the record itself joins nothing, but a rule that writes
  corrections back could in principle couple `i` to `j` directly. Hypothesis
  needed: `j`'s next content depends on region `i` only through the record's
  symbol (the dynamics factors through it). Then a change of `i` within the
  margin's width moves `j`'s content by at most the record's error rate, so
  the rule creates no coupling `i`–`j` at the noise floor. Harder than U73:
  the factoring hypothesis must be stated on the noisy dynamics, and the
  bound composed through two noisy steps. If it lands, drop the Limitations
  item U73 adds; if not, the item stays.
  *Done 2026-09-27:* `shiftResponse_le_of_factors` and
  `not_coupledAtNoiseFloor_of_factors`. The factoring hypothesis is stated
  per noise realisation: a change of `i` moves `j`'s content only when it
  moves the record's symbol read after the random step `g ω`; one noise `ω`
  drives both steps, so the write-back may carry noise of its own. The bound
  is the record's error rate (via the new `shiftResponse_le_of_ne_le`).
  Witness `writeBack_not_coupled`, with `writeBack_moves_at_crossing` showing
  the route carries threshold crossings. No Limitations item was added. Not
  established: a leak around the record is a separate path, bounded only
  when it too runs through a margin (Lean doc-string scope).

*Review 2026-09-27 (grade 5/10, borderline reject; major revision). U75–U80
are its points, most severe first. U75–U77 plus two figures (U78) would move
it to about 7.*

- [x] **U75 — The per-window rescue may rescue chips too.** Cortex passes at
  only 0.014–2.3% of occupied states, so P is
  stated per window: some carrier passes within the content's time scale.
  But §enforcement 'Where the line falls' concedes that "a bit caught in the
  middle of switching passes", and a node toggling at GHz rates spends a
  comparable small fraction of its time in transition, entered many times per
  400 ms window. The bit occupancy model (app:occupancy) restores the bit to
  its rail every step and so never samples a transition. The implicit reply,
  that a chip's content is read at the latch and transients are traces
  (§ai 'Clockless logic', 'Why spikes are not bits'), is not made where it
  is needed. As written, a reader can say the criterion was relaxed until
  cortex passed, and chips were measured at a different point.
  (a) Run the chip through the same per-window protocol, transients
  included: switching activity factor, transition time, and the latch's
  setup/hold window (metastability included).
  (b) State in the window paragraph what content each substrate reads, and
  why a transient passing at the voltage level is not a passing *carrier*:
  the latch samples outside the transition, while downstream membranes
  integrate spike times as they arrive. If the asymmetry needs a definition,
  it belongs in §enforcement's definitions, not in §ai.
  **Success.** The window paragraph says why a switching bit does not satisfy
  the per-window condition, with a number from (a).
  *Done 2026-09-27:* (a) `unity_switching.py` → `switching.json`, closed
  form, rerun by its test. At 1 GHz, activity 0.02–0.5, 20 ps transitions, a
  node's crossing time passes (exactly at the fluctuation, by the spike-time
  identity) at 0.02–0.5% of states, inside the membrane's 0.014–2.3%, and
  every 40 ms window holds a transition except with prob < 10^-100: the
  reviewer is right at the voltage level. The latch reads the rail (timing
  closure), so passes nowhere. A synchronizer (Ginosar 2011, 28 nm example:
  T_W 20 ps, τ 10 ps, f_D 100 MHz) samples inside its aperture ≤ 0.2% of the
  time, 8×10^5 times per 400 ms, and its resolution does pass. (b) New sixth
  definition, *next content* = what the carrier's readers take, when they take
  it, in §enforcement; new paragraph 'A switching chip, counted the same way'
  after the window paragraphs; 'Where the line falls' names the synchronizer;
  abstract and Claim 2 say "the value a clocked latch reads". The synchronizer
  is answered by protocol (it decides the cycle, not the value) and scoped in
  the 'Hardware near its thresholds' limitation.
- [x] **U76 — Matched transfer entropy does not match task information.** The
  loops can match total transfer entropy on multi-unit envelopes and still
  differ in how much of the *task variable* gets through, or in waveform
  distortion from the quantizer and the different cutoff. A behavioural gap
  would then have a mundane, information-level explanation. Add either (a) a
  control matching decodability of the task variable across the bridge (and
  checking it is matched) alongside transfer entropy, or (b) an argument for
  why transfer entropy is the right invariant for the grain question. Related:
  'The bridge's reach' limitation already concedes that a fine-grained
  functionalist absorbs either outcome, which narrows the test to "graded vs
  information-level" rather than "graded vs algorithmic". Make the abstract
  and Claim 1 say exactly the narrower thing, or strengthen the design until
  the wider claim holds.
  *Done 2026-09-27:* both. (a) §tests 'Separating coupling from
  information' adds a task-decodability check: the task variable is decoded
  from each loop's delivered current, and the loops count as matched only when
  decodability and transfer entropy both agree; the step and the cutoff are the
  two settings for the two conditions, chosen on pilot blocks and rechecked on
  compared blocks. 'A first preparation' sets both. (b) Abstract, intro,
  Claim 1, §tests opening, related work (Butlin, Kleiner) and 'Human evidence'
  now say the bridge separates the graded grain from the information
  exchanged, not from the algorithmic grain.
- [x] **U77 — The weight rests on prose, not on the theorems.** The margin
  lemma is "elementary by design", so the Lean results verify what follows
  from the definitions. The contested steps are argued in prose: unity is
  not one more content (Bayne, cited), records cannot compose a whole, and
  the relevant scale runs from a part's noise to its threshold, with
  threshold crossings counted as messages. Reviewers will say the
  formalization is rigorous about the easy part. Remedy: open §enforcement
  with the argument's structure (two premises, then what is proved from
  them), give the noise-to-threshold scale its own argument rather than a
  paragraph of stipulation, and say plainly in the intro which steps are
  theorems and which are premises.
  *Done 2026-09-27:* §enforcement opens with 'The argument in outline': two
  named premises, wholeness (Bayne's mereological account) and counting (one
  system = every change between noise and threshold registers), then the three
  proved results, then what is measured. 'Counting systems at the noise floor'
  is now a three-step argument from the physics criterion of non-factoring:
  below noise a difference is not a held state, a threshold crossing is a
  message (so a record, by the previous paragraph), and in the remaining range
  an unregistered change is a coordinate along which the joint state factors.
  The intro names the two premises as the argued steps and the rest as
  theorems; 'What the premise rests on' shrinks to the conclusion.
- [x] **U78 — No figures.** Add at least (a) a bridge schematic: two regions,
  interrupted connection, analog vs quantized loop sharing filter, output
  stage and artefact subtraction; (b) one occupancy/yardstick plot: passing
  fraction and per-window link probability for the membrane vs the bit
  (with U75(a)'s transients) across yardsticks. Figures come from saved
  summaries (AGENTS §3); check `check-figures` and `check-pdf-freshness`.
  *Done 2026-09-27:* (a) `fig:bridge`, TikZ in `unity/main.tex`: two regions,
  the interrupted connection, one direction of the loop (multi-unit record,
  rectify/smooth, shared filter, analog cutoff vs quantizer step, shared output
  stage, stimulator) and the artefact subtraction; placed in §tests and cited
  from 'The setup is a bridge'. (b) `fig:yardstick`, `unity_yardstick.png`
  beside the paper (unity/prepare_arxiv.sh rejects subdirectories), drawn by
  `simulations/unity_figures.py` from `yardstick.json` and `switching.json`:
  passing share and 400 ms visit probability per yardstick for the membrane
  band, the switching node's crossing time, the synchronizer bound and the
  latched value. check-figures reads only the companion; check-pdf-freshness
  and prepare_arxiv.sh pass.
- [x] **U79 — §reach is loosely tied to P and mostly classical.** Its results
  restate Mermin–Wagner, Chung–Fuchs recurrence and Kunz–Pfister ordering
  through effective resistance, and Claim 3 reads as carried over from the
  companion. U71 added the tie to P's two demands, and it is still a long
  section for the one prediction it feeds (the relaxation-time bound).
  Either shrink it to a page with the rest in app:reach, or make the link to
  the bridge/restoration tests carry the section. Decide whether Claim 3
  stays a numbered claim.
  *Done 2026-09-27:* shrunk. §reach ('When and how far a coupling enforces
  agreement') opens with P's two demands, then 'Agreement in time' (the
  relaxation-time prediction the restoration test checks), then one 'Reach'
  paragraph: resistance identity, the two classical bounds, the Lipschitz
  encoder, and that centimetre restoration measures synaptic coupling. About a
  page. Monotonicity, the direct-edge cap, the second-moment point, the
  relative encoder and the companion's bridge assumption moved to app:reach
  (retitled; four tab:formal rows now point there). Claim 3 stays numbered,
  led by the relaxation-time prediction; the abstract says the same.
- [x] **U80 — Presentation.** (a) Paragraphs are long and abstract, and terms
  defined in words (carrier, record, reader, content, trace) pile up: add one
  running example carried through §cover–§ai. (b) "$10^{-53878}$"
  (l.~474) invites ridicule; report a bound such as $<10^{-100}$ (change
  the macro's generator, not the prose). (c) The definition of unity and the
  bridge assumption lean on a self-citation (the companion); state enough of
  both in-paper that the argument stands without it.
  *(b) done 2026-09-27:* `unity_estimates.REPORTED_ORDERS = 100` and
  `reported_orders`; `\ueErrorOrders` and `\uOccBitOrders` now print 100 and
  the prose says "below $10^{-100}$".
  *(a), (c) done 2026-09-27:* (a) §cover 'A running example': a bird's
  location represented by a visual and a parietal area defines content,
  carrier, trace and unity; callbacks in §enforcement (a register holding the
  location is a record, a third-area cell integrating both and projecting back
  is a reader), §ai (the chip holds each estimate as a word, agreement by a
  program step) and §tests 'A first preparation'. (c) §cover 'The definition,
  stated precisely': compatibility on overlaps, unique gluing, the
  ε-approximate selection, and the decoded-agreement measure with
  $|d_A-d_B|\le|e_A|+|e_B|$ and its null. The bridge assumption is stated in
  app:reach and renamed the *phase-to-content assumption*, so that "bridge"
  names only the experiment.

*Self-assessment 2026-09-27 after U75–U80 (grade ~6/10, weak accept). U81–U85
are what keeps it below 7, most severe first. U81 and U82 are the ones a
hostile reviewer would open with.*

- [x] **U81 — "Next content" must predate the chip case.** U75 confirmed the
  review's worry at the voltage level: a switching node's crossing time passes
  at 0.02–0.5% of its states, inside the membrane's 0.014–2.3%, in every
  window. The separation now rests on the sixth definition (a carrier's next
  content is what its readers take, when they take it), added in the same
  commit that needed it. A reader can call it the second tuning of the
  criterion, after the per-window form. Remedy: derive it from §cover's
  carrier definition, whose first condition already asks that the regions a
  region drives *respond* to the variable, so that "read at the clock edge"
  follows from the carrier condition rather than being stipulated beside it.
  Then check that the membrane's per-window result and the latch's failure
  both follow from the carrier definition unchanged.
  **Success.** §enforcement has five definitions again, or the sixth is stated
  as a lemma of §cover's; no sentence introduces the reader-relative reading
  only where the chip needs it.
  *Done 2026-09-27:* §cover's carrier paragraph now says the first condition
  (the driven regions respond to it) fixes *when* a variable is a carrier: a
  reader responds at the times it takes the variable, so a cell's spike time is
  taken on arrival and a latch's input only inside its aperture at the edge,
  the voltage between edges being a trace like the supply current. Next content
  = what the readers take next, stated there as a consequence, before any chip
  is counted. §enforcement is back to five definitions, the closed-content one
  pointing to §cover for π(f(x)); the switching-chip paragraph cites the carrier
  condition. The membrane's next content (first spike in the window) and the
  latch's (value at the edge) are unchanged, so both results follow as before.
- [x] **U82 — The synchronizer by principle, not by protocol.** A
  synchronizer's first stage latches transitions by design, 8×10^5 times per
  400 ms, and its resolution passes. The paper answers that it decides the
  cycle, not the value, which holds only for transfer protocols that hold the
  value across the boundary, a contingent design fact now parked in the
  'Hardware near its thresholds' limitation. Options: (a) state it up front as
  a prediction P makes about hardware: a machine whose contents are read from
  how its synchronizers (or metastability-based random sources) resolve
  passes P's graded-dependence half at those carriers, and then ask whether it
  meets the contraction half (it pulls no two regions toward agreement);
  (b) show that the contraction half fails for every synchronizer, which would
  make the verdict principled. Prefer (b) if it is provable, and a Lean row if
  it is.
  **Success.** The synchronizer paragraph gives a reason from P's own two
  demands, and the limitation shrinks or goes.
  *Done 2026-09-27:* neither (a) nor (b): the graded-dependence half already
  decides it. By U81 the synchronizer's next content is what its second stage
  takes, one bit, and the paper's binary ceiling (no single binary readout's
  two-sided response to one noise amplitude exceeds Φ(1)−1/2 ≈ 0.34 < 0.383)
  holds at the aperture's centre too; the stage's own noise only lowers it. So
  it fails at every sample, whatever the transfer protocol, and so does a
  metastability random source. U75's "its resolution does pass" was wrong by
  the paper's own ceiling. `unity_switching.py` adds `BINARY_CEILING`,
  `synchronizer_passes` and a per-yardstick share (the bound only up to the
  ceiling); the figure drops the synchronizer there. 'Where the line falls' now
  reverses the verdict with a crossbar driving the next array directly. The
  limitation shrinks to hardware reading one graded quantity through several
  bits held near threshold together (not covered). No Lean row: the ceiling is
  a Gaussian computation (`test_unity_occupancy`), not a Lean theorem.
- [x] **U83 — The third step of the counting argument.** 'Counting systems at
  the noise floor' concludes that one unregistered change in the
  noise-to-threshold range makes two systems, "since their joint state
  factors along it". Critics will say that one unregistered direction does not
  factor a joint state; physics asks for a product decomposition, not a single
  unmoved direction. Either argue the step (the held-but-unregistered
  coordinate is a subsystem whose state the other part's dynamics is
  independent of, at that scale), weaken the conclusion to what one direction
  gives, or say which it is and why the weaker reading still separates records
  from graded readers.
  *Done 2026-09-27:* the third option. The third step now states physics'
  criterion as a product decomposition (each part's dynamics independent of the
  other's state at the resolution), shows a record meets it outright (inside
  its margin its next content ignores the other's whole graded state, up to the
  error rate) and a graded reader meets its opposite (no coordinate of the read
  region is ignored), and says the count draws the line at the strict end: one
  unregistered change makes two. Records and graded readers are classed alike
  by both readings, and they are the cases the argument turns on. 'The premise'
  limitation says where the readings part: a carrier registering some changes
  in the range and not others.
- [x] **U84 — Length and density of §enforcement.** After U75–U80 the section
  carries six definitions, an outline, and about twenty paragraphs. Candidates
  to move to an appendix: the noise paragraph's MLR detail, 'A neuron in
  numbers' (its content is in the occupancy result), the correlated-carrier
  numbers after the first one. Target: §enforcement readable in one sitting,
  with the argument's spine (outline → definitions → margin lemma → wholeness
  → counting → the chip, counted → the membrane and the switching chip,
  counted) visible from the paragraph titles.
  *Done 2026-09-27:* titles now run outline → Definitions → margin lemma →
  Noise → noisy margin theorem → why below the content level → why unity
  tracks enforcement → Wholeness → Counting → the chip, counted → where the
  line falls → the membrane, counted → the switching chip, counted → the
  yardstick, with Categories, Gradual replacement and 'What the premise rests
  on' after the figure. Noise now precedes counting, so the fluctuation is
  defined before it is used. Moved out: 'A neuron in numbers' and the
  monotone-likelihood detail to a new app:noise (two tab:formal rows repointed),
  the correlated-carrier miss probabilities and short-window result to
  app:occupancy; 'A logic gate in numbers' folded into 'The chip, counted'.
  Page count unchanged (59); every macro still cited.
- [ ] **U85 — No data, so choose the venue for a design paper.** The central
  test is proposed, not run, and the empirical parts are models with declared
  parameters. That caps the grade near 6 at venues that expect results. Fold
  into U31: target a venue where a conceptual argument with a preregistered
  design is a normal format, and consider a Registered Report of the bridge's
  first preparation (Stage 1 needs exactly the design §tests now states).

*Self-assessment 2026-09-27 after U81–U84 (grade ~6/10, weak accept; about
6.5 at a venue for conceptual work). U85 (no data) is still the main cap.
U86–U90 are the rest, most severe first; U85 plus U87 plus U89 would move it
to about 7.*

- [x] **U86 — The weight still rests on two premises.** Wholeness (Bayne's
  mereological account) and counting (the noise-to-threshold scale) are
  argued, not derived. The paper now says so, but a reviewer who rejects either
  rejects the paper, and the Lean results cannot help. Options: (a) show what
  survives under the main rival account of unity (joint access), e.g. which
  predictions of §tests hold without wholeness; (b) give the counting premise
  independent support from how physics already individuates subsystems at a
  resolution (coarse-graining, effective theories), beyond the product
  decomposition U83 added. **Success.** Each premise has either a second
  argument or a stated fallback showing which claims survive without it.
  *Done 2026-09-27:* both. Counting gets a second argument in §enforcement's
  counting paragraph: physics individuates degrees of freedom by the effective
  description valid at the parts' resolution; a chip's is its logic (closed
  content level, Rosas et al.'s computational closure), whose bits interact
  only through the rule, while block-averaging a coupled sheet leaves a coupled
  sheet. Wholeness gets a fallback and a test: 'What the premise rests on' says
  joint access predicts equal unity under the two loops (same information to
  the same regions), so the bridge decides wholeness vs joint access too; the
  introduction says so. 'The premise' limitation states what survives each
  rejection: without wholeness the theorems, count and measurements stand and
  only the unity→one-system step goes; without counting chips still fail P by
  the margin theorems, and only the argument from wholeness to P goes.
- [x] **U87 — Audit every generated number against its sentence.** U82 found
  that U75's "the synchronizer's resolution passes" contradicted the paper's
  own binary ceiling. A reviewer who finds one such slip distrusts the rest.
  For every macro in `unity_estimates.tex` and `unity_results.tex`, check that
  the sentence citing it states what the generator computes (quantity, units,
  direction of the bound, regime) and that no two sentences contradict each
  other. Consider a test that pins the claim each macro supports (e.g. the
  synchronizer's share is zero above `BINARY_CEILING`). **Success.** A
  checklist with every macro ticked, and fixes committed.
  *Done 2026-09-27:* all 130 macros audited against generator and sentence.
  The checklist is executable: `test_unity_claims.CHECKLIST` classes every
  macro (declared / point / lower / upper / range / orders), fails on any
  unclassed macro, and checks each lower/upper/range print against the exact
  value. Fixed: (1) `ueGradedWindowPercent` computed where the *flip
  probability* reaches θ*, not the response: now half an amplitude (0.099%),
  and the sentence says a two-sided change never reaches it. (2) bounds that
  rounded the wrong way: `ueEpspPassMv` 0.63→0.64, `ueBridgeMinCutoffHz`
  0.99→1, `ueFieldReachMm` 3.7→3.8, `uYardHitMinHigh` 0.037→0.036, pass ranges
  now outward (0.013–2.4%); estimates carry `ROUNDED_UP/DOWN`, macros `_sig`.
  (3) correlated links/misses were point estimates stated as bounds with
  c=0.75 resting on <1 SE: now two Monte Carlo SEs beyond every regime
  (0.88, 0.98; misses 0.0018/0.017/0.12), stated in app:occupancy. (4) "a
  membrane visits passing states within every window" (claim 2, wholeness,
  premise, margin's width) overstated a 0.085–0.997 hit probability: now "some
  carrier of a region … with high probability", the premise paragraph citing
  the 1000-carrier bound. (5) timing: "signal travel uses at most 31 ms" was
  typical arrival; the prediction is now 160–166 ms by fibre class. (6) "the
  separation holds at every yardstick" now says latch vs membrane; below
  Φ(1)−1/2 a synchronizer's first stage can pass at ≤0.2%. (7) "no binary
  readout reaches the fluctuation" now says under thermal (Gaussian) noise.
  (8) the pass range states its noise share. "Every tenth cycle" is now
  `\uSwDataMHz`. Pinned also: latching at 1/5 ms changes nothing, saved
  synchronizer/latch shares, node range inside membrane range, hit monotone in
  yardstick, and every results macro cited.
- [x] **U88 — The per-window rescue is still the soft spot.** The membrane
  passes at only 0.014–2.3% of its states. The switching node's crossing time
  passes at a similar rate and is rejected only because no reader takes it, so
  the separation rests entirely on the carrier condition (U81). Hostile
  reviewers will aim there. Strengthen the independent case that downstream
  cells read spike times as they arrive (evidence for spike-timing-dependent
  integration, not just rate readout) and state what P predicts if cortical
  readers turned out to integrate over windows that discard sub-jitter timing.
  *Done 2026-09-27:* the saved occupancy summary already held the case: spike
  times binned to the whole next-content window, i.e. a reader that registers
  only whether the membrane fired. It passes at 0.014–2.3% of states (new
  `uOccCountPassMin/MaxPercent`), and at exactly the timing reader's share in
  every 10 ms regime (pinned in `test_unity_macros`). So the membrane's verdict
  no longer rests on readers taking spike times; a count reader responds at
  least as much (data processing). The same reader of a chip node takes a
  quantity fixed by restored logical inputs. §cover's carrier paragraph now
  cites the millisecond integration windows (Pouille & Scanziani 2001, Gabernet
  et al. 2005, König et al. 1996, Panzeri et al. 2001; verified on Crossref and
  PubMed). P's refutation condition is stated: readers that pool only over
  windows longer than a content's time scale would make P deny cortex unity.
- [x] **U89 — Cases the analysis leaves open.** (a) The binary ceiling
  Φ(1)−1/2 assumes Gaussian noise; a sharply peaked unimodal law can put more
  mass within one amplitude. State the class of noise laws for which one bit
  stays below the fluctuation, or bound it generally. (b) Hardware reading one
  graded quantity through several bits held near threshold together (a
  time-to-digital converter's delay line) is not covered (the 'Hardware near
  its thresholds' limitation). Either settle it (with common input noise the
  word is a function of one noisy scalar, so data processing caps it at the
  fluctuation; with independent per-stage noise it may not be) or state it as
  a prediction about hardware. **Success.** Both are settled or stated as
  predictions, and the limitation shrinks.
  *Done 2026-09-27:* (a) the two-sided response of one bit is the smaller of the
  noise law's masses on the two width-a intervals meeting at the threshold; for
  a symmetric single-peaked law it peaks with the threshold at the state, at the
  mass between centre and one amplitude. So one bit stays below the fluctuation
  exactly when the law puts less than twice the fluctuation within one SD of its
  centre: Gaussian, logistic, Laplace do, Student-3 does not (0.409). Stated in
  §enforcement and app:occupancy; the synchronizer's noise is thermal, so
  Gaussian. The membrane paragraph's "no binary readout passes at any margin"
  now says *when the step's noise includes one amplitude of the change* (a
  membrane read only as spike-or-not over a short window does pass, since less
  than its stationary noise enters the window). (b) settled, not a prediction:
  a word of stages reading one quantity is a function of it plus independent
  noise, so by data processing it responds no more than the quantity; thresholds
  at ±a/2 attain it. Such a stage is a graded reader, counted as an analog one.
  `unity_switching.py` adds `NOISE_LAWS`, `bit_ceiling`, `word_response`, and
  `switching.json` records both. The limitation is now 'The hardware counts'.
- [x] **U90 — Length.** 59 pages; the argument's structure is hard to see on a
  first read even after U84. Target a main text that a reviewer can read in one
  sitting: candidates are §tests' preparation detail, §ai paragraphs that
  restate the margin lemma (Leakage, the margin's width), and §related. Move,
  don't delete (AGENTS §10 for any disclaimer that moves).
  *Done 2026-09-27:* moved, nothing deleted, into four new appendices:
  app:digital (Leakage, the margin's width), app:bridge (the loops' matching
  arithmetic, stimulation artefact), app:field (the field's strength and the
  timing measures), app:related (biology, analog/digital, field theories); the
  synchronizer's numbers and the multi-bit argument joined app:occupancy. Each
  main-text site keeps a short statement of the result and a pointer.
  Limitations now starts on p. 35 (37 before U86–U89, 39 before this move);
  the whole PDF is 64 pages because U86–U89 added content. No disclaimer
  moved (check-claims counts unchanged). Also repaired: U89's insertion had
  split app:occupancy's synchronizer paragraph, leaving its MTBF sentence after
  the multi-bit paragraph.
- [x] **U91 — Plain prose, section by section.** *Done 2026-09-27 (`9e476dd`):*
  abstract and all eight main-text sections rewritten for a non-specialist;
  sentences 27.6 → 22.6 words on average; count's strictness stated in
  §enforcement; bridge gains positive-control blocks. Appendices unchanged.
- [x] **U92 — Local unity and switching.** *Done 2026-09-28 (`975d60c`):* P asks
  for agreement only among unified regions; a hub routing thresholded messages
  leaves unified islands, a graded hub joins them (per window, possibly in
  turn); thalamic tonic vs burst mode as the candidate test (Sherman 2001).

*Self-assessment 2026-09-28 after U91–U92 (grade 6/10, borderline accept at a
specialist venue; about 5.5 at a selective one). Readability, the positive
control and local unity moved it up from 5. U93 is the ceiling; U93 plus U95
plus U97 would move it to about 7. U85 (no data) still caps it.*

- [x] **U93 — Counting still carries the argument, and it is argued rather than
  proved.** U86 added the effective-description argument, but a philosopher
  will still call the strict reading (every change between noise and threshold,
  not some) a stipulation, and the Lean results cover only the easy steps. Give
  counting an independent anchor: a case where physics already individuates
  systems at the noise floor (e.g. decoherence and pointer states,
  thermodynamic subsystems, or open-system effective theories) and classes it as
  the count does. **Success.** A cited physics precedent that draws the line at
  the parts' own noise, stated in §enforcement's counting paragraph, with the
  strict/product difference argued rather than only admitted.
  *Done 2026-09-28:* §enforcement gains "A precedent: clusters in a gas": Hill's
  (1955) physical-cluster criterion, reviewed by Sator (2003, Phys Rep; both
  verified), bonds two molecules when attraction outweighs relative thermal
  kinetic energy and takes clusters as chain-connected components; sub-thermal
  interaction changes the pressure and joins no cluster. The strict reading is
  now argued: where response grows with the change, a carrier misses a change
  in the range only by a margin narrower than the range or by a threshold at
  the state, both record-type registration, so strictness adds no condition.
  Limitations' Counting item states where that argument holds and that Lean
  proves count→P, not the count.
- [x] **U94 — Cortex passes only through definitions a reviewer can call drawn
  for the purpose.** A chip passes at the voltage and fails only by what the
  latch reads (U81, U88); cortex passes only in the per-window, some-carrier
  form. Show the verdict does not depend on the window: sweep the window
  length independently of the \ueContentMs{}~ms percept time and report where
  the membrane stops passing, and fix the window from psychophysics cited
  independently of this paper. **Success.** A generated range of windows over
  which the separation holds, with its lower end stated.
  *Done 2026-09-28:* `unity_window.py` sweeps the per-window link from one time
  step to 1000 ms in one pass per regime and share (`window.json`). Some of
  1000 independent carriers links two regions more often than not in every
  regime and share from 3 ms upward (100 carriers: from 31 ms), and at the
  temporal-order threshold of 20 ms (Hirsh & Sherrick 1961, verified) with
  probability ≥ 0.98. Half grid and half step move both ends earlier (1.6 and
  16.9 ms), so the printed ends are conservative. Stated in §enforcement and
  app:occupancy; Limitations notes the sweep assumes independent carriers.
- [x] **U95 — No power or feasibility estimate for the bridge.** Two settings
  (step, cutoff) must match transfer entropy and task decodability at once;
  that may have no solution, and no effect size or trial count is given.
  Add a script that simulates both loops on a model pair of regions, finds the
  matching (step, cutoff) region, and estimates trials for the behavioural and
  neural comparisons at a declared effect size. Numbers enter as generated
  macros, classed in `test_unity_claims.CHECKLIST`. **Success.** app:bridge
  states whether a match exists, its tolerance, and a trial count.
  *Done 2026-09-28:* `unity_bridge.py` simulates both loops on a linear model
  pair (task OU → A + own noise → recording → shared filter → cutoff or
  quantizer → shared output → leaky B), linear-Gaussian TE from A's recording
  to B's, task decodability from B's recording (the information that reaches
  B; decoding the noiseless delivered current barely moves with the cutoff,
  since a first-order filter loses nothing without downstream noise). Finding:
  exact equality on both is not generic; at TE match the analog loop keeps
  *less* task information whenever the task SD ≥ half a step (step 10: cutoff
  17–95 Hz, gap 0.025–0.06 R²), and can keep more (up to 0.075) when the task
  spans a fifth of a step. So the matching rule is now "same TE, analog loop
  no more task information" (abstract, claim 1, §enforcement, §tests,
  Figure 2, index.html). Trials: 1248 per loop behavioural (0.75 vs 0.70),
  393 neural (d = 0.2); at 1248, TE matched within 2% and gap within 0.0053.
- [x] **U96 — The thalamus prediction is thin.** U92 predicts more cross-patch
  unity in tonic than in burst mode from one review, and P's own logic says
  burst spikes keep graded timing. Either derive the difference (response at
  the noise floor of a relay cell in each mode, by the occupancy protocol) or
  scope it as a direction to test, not a prediction. **Success.** A computed
  or cited difference in graded dependence between the two modes, or the
  sentence reworded.
  *Done 2026-09-28 (`f49d7d8`):* reworded, with the reason. Tonic relay is
  near-linear (an integrate-and-fire model predicts LGN responses to natural
  movies; Lesica & Stanley 2004, verified); bursts are all-or-none, triggered
  by excitation after prolonged inhibition, and need renewed hyperpolarization
  (Sherman 2001), yet burst onset is graded like a spike time. So the direction
  is left to the occupancy protocol on relay cells recorded in each mode, and P
  predicts more cross-patch unity in whichever mode passes more often within a
  window. Computing it needs a relay-cell model with a T current, which the LIF
  occupancy model lacks.
- [x] **U97 — Length.** 66 pages, main text about 12,500 words. Target about
  9,000: move the switching chip and yardstick detail to app:occupancy, keeping
  the result and a pointer in §enforcement, as U90 did. Move, don't delete
  (AGENTS §10). **Success.** Main text ≤ 9,000 words, every macro still cited.
  *Done 2026-09-28:* main text (abstract to Limitations) 13,373 → 8,980 words
  (counted after U93–U96 added ~400); PDF 70 → 63 pages. Moved, not deleted:
  new app:count (logic-node detail, effective descriptions) and
  app:replacement (gradual replacement in full); app:occupancy gains the
  membrane, window, reader, shared-input and switching detail and Figure 1;
  app:digital gains clockless logic; app:field the causal-cone setup;
  app:window the precise cone statement; app:bridge the pilot-block procedure
  and why the analog arm is analog end to end. Main-text sites keep result +
  pointer; §ai, §tests, §cover, §reach, Related work and Limitations
  tightened sentence by sentence. Every macro and reference still cited;
  check-claims disclaimers 3 → 4 (none removed).
- U85 (no data) remains the cap; see above.

- [ ] **U31 — Venue.** No new data and a self-described short theorem put an
  ML venue at 4–5 regardless of content. Peer review target: *Neuroscience of
  Consciousness* or *Phil. Trans. B*. arXiv posting: cs.AI primary (author has
  endorsers there), q-bio.NC and optionally cs.ET cross-listed; abstract now
  leads with the theorem and bound (`e6e2886`) so the CS position-paper rule
  is less likely to apply. Arxiv abstract box: write `r^-4` plainly. Comments
  field: pages, theorem with proof, analytic bounds, simulations, formal
  appendix.
- [ ] **U32 — Cite the companion's PsyArXiv DOI.** The companion was
  submitted to PsyArXiv (awaiting moderation as of 2026-09-26);
  `unity/references.tex` cites it as "Manuscript" with the GitHub link. Swap
  in the DOI once posted, preferably before the unity paper's arXiv v1, then
  rerun `unity/prepare_arxiv.sh` and commit with the rebuilt PDF. The DOI
  also unblocks the unity half of U19, which was waiting on an identifier.
- [x] **U34 — Lean: the noise-amplitude reduction for additive unimodal
  noise.** Raised 2026-09-26 after U33. `gaussian_shift_le` covers only
  Gaussian noise. For additive noise with a unimodal density `p`,
  `p(y) − p(y − d)` changes sign once, so the event maximising the response is
  a half-line and the response is `sup_t F(t) − F(t − d)`, which grows with
  `d` for any law. Prove the response grows with the change under additive
  unimodal noise, generalise `gaussLin` to any such noise law, and state the
  reduction per side: with asymmetric noise a change of `+σ` and one of `−σ`
  can differ, so the criterion is decided by those two changes. Covers
  Gaussian, Laplace, logistic, uniform, Cauchy, Student-t; heavy tails need
  no log-concavity. Hard part: the half-line is optimal over every set, not
  only measurable ones (outer measure, as in `shiftResponse`).
  Counterexample to record in the docstring: noise ±1 with probability ½
  each has response 1 at a shift of 1 and ½ at a shift of 2, so some
  hypothesis is needed. **Success.** `gaussian_shift_le` is an instance.
  *Done 2026-09-27:* one argument serves U34 and U35. `SingleCrossing P Q`
  (an upper set carries the whole excess of `Q`) gives, by Scheffé's bound
  over every set (`rise_le_of_restrict`, outer measure via `toMeasurable`),
  stochastic dominance and `lawRise_le_of_crossing`: in a family whose laws
  cross once in order, the rise grows away from `θ₀` on each side. A shifted
  unimodal density crosses once (`singleCrossing_shift_of_unimodal`), and for
  additive noise the rise is even in the shift (`lawRise_map_add_le_neg`), so
  the per-side statement was not needed here: `lawRise_map_add_mono_of_unimodal`
  holds for `|b| ≤ |a|` whatever the signs. `noisyLin` generalizes `gaussLin`
  (per-region noise laws), with `noisyLin_coupledAtNoiseFloor_iff`.
  `gaussian_shift_le` is now an instance (via `gaussianPDF_unimodal`; gains
  `v ≠ 0`); the convolution proof and its two helpers are gone. The ±1
  counterexample is in the section docstring. §enforcement states the
  generalization; tab:formal gains rows.
- [x] **U35 — Lean: the reduction for families with monotone likelihood
  ratio.** The general form of U34, for state-dependent noise: if the next
  content's laws form a family with monotone likelihood ratio in a parameter
  that the region's change moves monotonically, the response grows with the
  change on each side, and `gradedAboveNoise_iff_of_mono` applies. Covers
  one-parameter exponential families: Poisson spike counts, binomial release,
  gamma intervals, whose variance changes with the state. Two further scope
  items: nonlinear dynamics need the parameter to move monotonically with the
  change, a hypothesis on the dynamics and not on the noise; vector-valued
  contents fall outside monotone likelihood ratio, and for a symmetric
  unimodal law in several dimensions Anderson's theorem gives growth along
  each ray, so the criterion becomes the smallest response over changes of
  size σ. Several times the size of the Gaussian proof; do U34 first.
  *Done 2026-09-27:* `singleCrossing_of_mlr` and `singleCrossing_expFamily`
  (densities `h y exp(θy − A θ)` against any reference law, so counting
  measure covers Poisson and binomial). `gradedAboveNoise_iff_of_sides`: with
  a real micro state and the response growing on each side, the criterion is
  decided by `+σ` and `−σ`; `gradedAboveNoise_iff_of_crossing` supplies this
  when the next content's law is `P (φ s)` with `φ` monotone or antitone (the
  dynamics hypothesis). Vector contents and Anderson's theorem are recorded
  as scope in the section docstring, not proved.
- [ ] **U19 — State the E78 → U1 bridge in both papers.** The companion's
  worst-case bound (coherence → content, `L√(2N(1−r²))`) runs out at
  millimetres, leaving centimetre-scale agreement to the bridge assumption
  E78; the U paper's typical-case bound (effective resistance) reaches any
  distance, but only with a kernel tail slower than `r^−4`. One sentence in
  each introduction so the pair reads as one program. Companion side goes in
  its v2 (U20).
  *Unity half done 2026-09-27 (U53):* the companion was already cited as a
  manuscript, which sufficed; only the companion half (v2, U20) remains.
  *Blocked 2026-09-25:* the unity side needs a citation of the companion,
  which has no arXiv identifier yet; write both halves once it is posted.
  *Review 2026-09-27:* read together, the two papers make this gap more
  visible, not less. The unity reach section turns phase agreement into
  content agreement through the same kind of Lipschitz encoder, so across
  centimetres both papers rest on E78. Restate the unity claim as: coupling
  bounds *phase* disagreement at every distance, and turning that into
  agreement in *content* across centimetres is E78, named as such. See U53.
- [ ] **U20 — Companion v2 when the U paper posts.** (a) Cite the U paper.
  (b) Scope `main.tex` §gpu "These results rank no architecture family, imply
  no general inferiority of GPU hardware and settle no question of machine
  experience" explicitly to *this article's* results, so it cannot be quoted
  against the U premise. (c) Present the extracellular field as one
  realization of graded coupling (U16), not a competing claim. The awakening
  hypothesis puts fields into effective coupling while the unity paper
  shows a local source's field misses detection by orders of magnitude at
  centimetre scale; say explicitly that the field story is local and
  centimetre-scale coupling is synaptic, so the program speaks with one
  voice. (d) Decide the tone mismatch with U56: either commit to the glued
  state as the correlate of unity, or keep it hedged and let the unity paper
  condition P on it. Rebuild PDFs
  and the arXiv bundle per AGENTS.md §6–7.

## N — Neuroscience of Consciousness submission

- [ ] **N14b (optional) — Run the protocol on a real model.** Fit decoders
  for one shared quantity on two separate parts of a real model (layers,
  heads or token positions), test their agreement and whether
  reconstruction survives intervention. This would be the only place the
  proposed measurement is actually carried out. Optional: needs hardware
  not currently available; a small open model on rented or CPU compute is
  the cheapest route. New work, not a condition of the revision.
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
- [ ] **N28** — §9.2 rivalry: there is always a percept and "decoding error
  relative to the stimulus" is undefined for the suppressed eye. Specify the
  adaptation or keep masking only.
- [ ] **N29** — §9.2: define error-stratum matching (continuous or binned,
  number of strata).
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
- [ ] **N37** — Remove the installed-energy box from Fig. 1 with N19; cut
  Conclusions to about three sentences.
