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
  value (0.085 per 400 ms in the sparsest regime). Plan in progress
  (2026-09-27): a shared-plus-private input model in `unity_occupancy.py`
  (link probability as a function of the shared-input fraction), a
  correlation-robust second-moment bound in Lean, and a verified cited range
  for the shared fraction in awake cortex. Outcome policy as in U36: report
  whatever comes out.

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
- [ ] **U20 — Companion v2 when the U paper posts.** (a) Cite the U paper.
  (b) Scope `main.tex` §gpu "These results rank no architecture family, imply
  no general inferiority of GPU hardware and settle no question of machine
  experience" explicitly to *this article's* results, so it cannot be quoted
  against the U premise. (c) Present the extracellular field as one
  realization of graded coupling (U16), not a competing claim. Rebuild PDFs
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
