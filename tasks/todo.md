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

- [ ] **U47 — Correlated carriers: replace the declared independence.** The
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

*Review pass 2026-09-27 (score 4/10 standalone, ~4.5 read with the
companion; 5 = reject).* Verdict: well written, honest about its limits,
cheap theorems and an expensive premise, and reviewers will score the
premise. U48–U56 are ordered by leverage.

- [ ] **U48 — Make the bridge the centerpiece.** The analog versus quantized
  bridge at matched transfer entropy is the only test that separates P from
  computational functionalism, and the paper's most original content. Make it
  claim 1, expand §tests' treatment, and add a feasibility sketch in rodent or
  NHP with decoded agreement as the readout: closed-loop hardware, recording
  and stimulation sites, the transfer-entropy estimator and trial counts.
- [ ] **U49 — The fluctuation yardstick looks rigged.** 2Φ(½) − 1 ≈ 0.38 is
  also the largest response a Gaussian-noise threshold gives to a shift of one
  noise amplitude, so binary readouts fail by the choice of constant and at
  best tie it. (a) Justify the constant independently of that coincidence, or
  show the chip/membrane separation is robust across a range of yardsticks:
  the margin of 506 noise amplitudes suggests it is, so report the passing
  fractions as a function of the yardstick. (b) Settle ≥ versus > in "reach"
  in text and Lean; at ≥ a bit sitting exactly on its threshold passes.
- [ ] **U50 — Argue "one subject ⇒ one system at the noise floor", or reframe
  the abstract.** The step from "unity counts subjects" to "systems are
  counted by graded dependence above the noise floor" is asserted, and
  Block's nation and the scattered records are intuition pumps. A
  functionalist rejects exactly this step. Either give it an argument (why
  this grain and not causal integration at another), or change the abstract's
  "we argue that unity requires" to "we propose P and derive its
  consequences". Keep P stated plainly (memory: the author wants the premise
  stated, not hedged); this is about what the paper claims to have *shown*.
- [ ] **U51 — Present the margin theorem as a lemma.** It is one step
  (continuous map into a locally constant readout). Put the contribution's
  weight on what is not trivial: the noise-floor criterion, the noisy margin
  bound and its attainment, and the occupancy measurement. Lean-checking a
  one-step lemma draws attention to how little is checked.
- [ ] **U52 — "Each bit is a separate system" needs more than one paragraph.**
  Physicists will read it as a redefinition, since crosstalk and a shared
  supply are real interactions. The whole paper rests on this move: expand
  the argument that the noise-floor scale belongs to the parts, and why
  sub-margin crosstalk does not count.
- [ ] **U53 — Demote or compress §reach.** The r^−4 threshold is classical
  (Chung–Fuchs, Kunz–Pfister), and the field estimate shows the
  non-synaptic tail dies within millimetres, so at centimetre scale the
  section says only that synapses are graded. Candidate: drop r^−4 from the
  abstract and claim 2, compress the section, keep the proofs in the
  appendix. Must be consistent with U19's restatement.
- [ ] **U54 — The weak-nudge prediction is low-risk.** Weak fields shifting
  graded decoded content in connected areas is expected under almost any
  theory, so the test can refute P but barely confirms it. Say so in §tests,
  or sharpen it: what does P predict that generic modulation does not (for
  example, proportionality below threshold and direction toward agreement,
  not merely a change)?
- [ ] **U55 — Sharpen the delta against Kleiner 2024 and IIT/Findlay 2024.**
  "Digital hardware suppresses its physics" is already published (Kleiner),
  and IIT already denies simulations experience. State the novel part in
  §related: the contraction condition, the noise-floor criterion and the
  bridge test.
- [ ] **U56 — Condition P on the companion's correlate; present a two-stage
  program.** The companion calls the glued state a *proposed correlate* and
  says "nothing here establishes a consciousness criterion", while the unity
  paper takes it as the definition of unity and states a necessary condition
  on it: a firm premise on a hedged proposal. In `unity/main.tex`, state that
  P is conditional on that identification, and present the companion's
  excess-agreement test (perceived versus unperceived) as stage one: if it
  fails, P has nothing to constrain; if it passes, the bridge asks whether the
  agreement must be enforced. Alternatively commit to the identification in
  companion v2 (U20).

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
