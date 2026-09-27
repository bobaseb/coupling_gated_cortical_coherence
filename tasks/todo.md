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
- [ ] **U34 — Lean: the noise-amplitude reduction for additive unimodal
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
- [ ] **U35 — Lean: the reduction for families with monotone likelihood
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
