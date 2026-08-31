# Physics of Consciousness — work plan

**Replanned 2026-08-30.** The prior file — 3,545 lines, every completed pass
recorded in full — is archived at
`_archive/todo_2026-08-30_pre-strategic-replan.md`. Nothing in it is deleted,
and where an item below refers to a past pass by name ("The motion stops
somewhere", "The coherent branch is a single point") that section is in the
archive. Read it when you need the reasoning behind a closed decision; do not
re-litigate a closure without recording why.

This file replaces the old one because the project's *bottleneck changed*. The
old ledger was organised around closing formalization gaps, and it did that
well: as of `861f252` there are no `sorry`, no declared axioms, and every class
carrying physical content is inhabited. What remains open in the Lean is no
longer what limits the paper. What limits the paper is that one link in the
deductive chain is an **invalid inference**, one is an **assertion dressed as a
derivation**, one is a **theorem that cannot see its own subject**, and the
manuscript has **no figures**. Those are the items below.

---

## Standing rules — carried forward, still binding

1. **A physical postulate that mentions a class field must be a field of that
   class, never a standalone axiom quantified over all instances.** A postulate
   is an obligation each model discharges, not a global claim about every model.
   This rule exists because three of five original axioms each proved `False`.
2. **Every class carrying physical content gets a witness in `Examples.lean`,**
   and where possible a theorem showing the witness is as strong as the class
   permits (the shape of `contracting_implies_const`, `ThermodynamicCover.phase_locked`).
   An uninhabitable class makes its theorems vacuous just as surely as an
   inconsistent axiom did.
3. **Do not strengthen a class to close a gap.** Add a predicate and prove
   theorems about it (the `IsRestrictionResonance` pattern), so the gap is
   visible rather than absorbed.
4. **Treat the "what it takes" column as a hypothesis to be checked, not a plan
   to be executed.** Recorded estimates have now been wrong — pointing at the
   *wrong obstacle*, not merely being pessimistic — on O8, O10, O11 and O20.
   Grep the pinned Mathlib before believing any blocker.
5. **Verify every reference online before committing it.** No fabricated or
   unverified citations. (`AGENTS.md` §4.)
6. **Compile gate on every manuscript change:** overfull hboxes checked against
   `HEAD` rather than assumed, zero undefined references or citations, page
   counts recorded.
7. **Build gate on every Lean change:** zero `sorry`, zero warnings, `lake build`
   clean, and `#print axioms` on every new result reporting only `propext`,
   `Classical.choice`, `Quot.sound`.

---

## Where the development stands — 2026-08-30

**Lean.** 12,822 lines across 19 modules. Zero `sorry`. Zero declared axioms.
`Examples.lean` is 4,164 lines and carries 18 witness sections plus §17.1.

**Landed 2026-08-30 (`861f252`).** O20(d)+(e): `lojasiewicz_estimate`,
`excess_decay`, `velocity_abs_le_exp`, `phase_tendsto`, `excess_tendsto_zero`,
`kuramoto_tendsto_global_minimum` in `Phase4_RotatingFrame` §7, witnessed on
three sites in `Examples.lean` §17 by a trajectory with no closed form. The
recorded LaSalle blocker was a misidentification.

**Landed 2026-08-31 — W1.** `Phase5_EquilibriumBridge.lean`:
`kuramoto_limit_minimizes` and `ThermodynamicCover.ofConvergentTrajectory`,
witnessed by `Examples.lean` §17.1. Derivation 5's
`thermodynamic_equilibrium` is now derived from the dynamics on a class of
initial data rather than assumed on every instance, and O20 is closed. The
cover's *other* physical hypothesis, `section_agrees_of_phase_eq`, is untouched.
Full pass record below.

**Landed 2026-08-31 — W4.** `Phase3_PredictiveThermodynamics.lean`: mutual
information defined from Mathlib's `klDiv`, the data processing inequality for
`X_t → S_t → S_{t+1}` proved, Still's bound carried as a class field, and every
consequence downstream of it derived. Witnessed by `Examples.lean` §18 with two
instances, a counterexample fencing the no-back-action hypothesis, and a proof
that the `axiom` form of the bound is refutable. Derivation 3's invalid inference
is withdrawn in both documents. Full pass record below.

**Landed 2026-08-31 — W3.** Derivation 4 is split into a coarse-graining
theorem and a named empirical commitment, retitled so it is no longer a
"Derivation", given its critics and four falsification conditions, and the
frustration/positivity contradiction is confronted rather than caveated. Prose,
plus one Lean docstring. Full pass record below.

**Landed 2026-08-31 — W5.** `Phase6_ReflexiveTopology.lean` restructured:
`ReflexiveBoundary` carries the avatar's write and its read-out, `predict` is
their composite rather than a field, and `self_of_constResonance` no longer
typechecks. The contraction rate is `resonanceRate K D τ = exp(-(K - 2D)τ/2)` and
the Self follows from `K > K_c`, which connects Derivation 6 to Derivation 7 for
the first time. `Examples.lean` §10 rebuilt around a map that factors through the
one-site avatar. Full pass record below.

**Manuscript.** `main.tex` 84 pages, `supplementary.tex` 14, six figures, merged
arXiv build 45 pages.

---

## The frame — read this before picking up an item

The decision taken 2026-08-30 is to write **the ambitious framework paper**,
accepting that its readership is the EM-field / resonance community. Two things
follow, and every item below serves one of them.

**First: the chain has to actually run.** The current chain has three defects of
different kinds, and only one of them is a missing theorem:

| Link | State | Item |
|---|---|---|
| Finite phase space | Vocabulary; no theorem consumes it | W6 |
| SSB → boundary | Proved at π₀; π₁ and up available, not taken | ~~W2~~ done |
| → dissipation | Sound | — |
| → prediction | Still's bound; nonpredictive information is what dissipation pays for | ~~W4~~ done |
| → continuous field | Split: coarse-graining is a theorem, the EM identification is a named empirical commitment | ~~W3~~ done |
| → coherent state | Theorem on a basin, class field discharged from it | ~~W1~~ done |
| → reflexive fixed point | The map is the avatar's read-out of its own encoding; blinding moves the Self, and the rate is `exp(-(K-K_c)τ/2)` | ~~W5~~ done |
| → experience | Stipulation. **Kept, named, owned.** Not a defect | — |

The manuscript now has six figures and a methods section (~~W7~~ done); the
claim-by-claim identifier table is Table S1 in the supplement.

**Second: no new physics is derived here, and the paper should say so.** Every
physical result invoked is established — Picard–Lindelöf, Barbălat 1959,
Sakaguchi 1988, Kibble 1976, Still et al. 2012, Landauer, Gibbs, Banach. What is
new is that they are stated in one formal language, their mutual consistency
mechanically checked, and the points relying on stipulation located exactly.
That is a defensible claim and it is more than most theories of consciousness
can make. It is **W8**, and it should be written early rather than bolted on,
because it changes how every other section is phrased.

**Venue.** Primary target **PRX Life** (physics of living systems; send a
presubmission inquiry rather than a cold submission — the editors will say
quickly whether the consciousness framing is disqualifying). Fallbacks in order:
*J. R. Soc. Interface* → *Neuroscience of Consciousness* → *Entropy*. Note that
W4 is what moves the ceiling: without it this is an *Entropy* paper.

---

## Work items — take ONE at a time, in this order

Each item is self-contained. Record the pass in this file under a dated heading
in the style of the archive (what was built / non-vacuity / what it does *not*
establish / manuscript updates), then move to the next.

**W1, W8, W2, W4, W3, W7 and W5 are done (2026-08-31).** Every defect the frame
table listed in the chain is closed or named, the manuscript has figures, and the
Self theorem now sees the avatar. What remains is **W6** — give Axiom 1 a theorem
that consumes it, or stop calling it an axiom.

### W1 — Discharge `thermodynamic_equilibrium` from the convergence theorem

**Done 2026-08-31.** Pass recorded below under *2026-08-31 — W1*.

- [x] **Objective.** Build the bridge from `kuramoto_tendsto_global_minimum` to
      `ThermodynamicCover`, so that Derivation 5's standing hypothesis is
      *derived* on a class of initial data rather than assumed on every instance.
- **Why.** Every Derivation 5 result is conditional on
  `ThermodynamicCover.thermodynamic_equilibrium`. The convergence theorem now
  produces exactly the configuration that field demands — but nothing connects
  them. `Phase4_RotatingFrame` does not import `Phase5_GlobalSection`, and
  `Examples.lean` §17 stops at `trio_reaches_minimum` without constructing a
  cover. This is the single cheapest conversion of an instance obligation into a
  theorem left in the development.
- **There is a live defect to fix in the same pass.** The docstring at
  `Examples.lean:3191` claims §17 "is what discharges
  `ThermodynamicCover.thermodynamic_equilibrium` on an instance rather than
  assuming it." That is **false as written** — no cover is built there. Either
  make it true by building one, or correct the sentence. Do not leave it.
- **What it takes.** A theorem taking a trajectory satisfying the initial-data
  conditions of `kuramoto_tendsto_global_minimum` and producing a
  `ThermodynamicCover` whose phase field is the limit `thetaInf`, with
  `thermodynamic_equilibrium` discharged by the minimality already proved. The
  import direction needs thought: Phase5 currently sits below RotatingFrame in
  the dependency order, so the bridge likely belongs in `Examples.lean` or a new
  small module rather than in Phase5 itself. Check before restructuring.
- **Done when.** A `ThermodynamicCover` instance exists whose
  `thermodynamic_equilibrium` field is discharged by a *convergence* argument
  rather than by `phase_locked_minimizes_potential` applied to a
  constant-by-construction phase field, and Table 1's Derivation 5 row records
  the change.

### W2 — Prove the domain-wall theorem (Derivation 1)

**Done 2026-08-31.** Pass recorded below under *2026-08-31 — W2*.

- [x] **Objective.** Turn "topology dictates the natural creation of defects"
      from prose into a theorem.
- **Why.** Derivation 1 is named "Symmetry Breaking and the Inevitability of
  Boundaries" and currently proves pointwise vacuum minimization a.e. plus a Z₂
  double-well witness. The inevitability — the actual content of the section — is
  asserted. This is the cheapest genuinely-new theorem available.
- **What it takes.** The π₀ case of the Kibble mechanism:

  > Let `X` be connected, `φ : X → V` continuous, `M ⊆ V` the vacuum manifold.
  > If `φ x₁` and `φ x₂` lie in **different connected components** of `M`, then
  > `∃ x, φ x ∉ M`.

  Proof: the image of a connected set is connected; a connected subset of `M`
  lies inside a single component of `M`; contradiction. Mathlib has
  `IsConnected.image` (`Topology/Connected/Basic.lean:315`) and
  `IsPreconnected.subset_connectedComponent`. Confirmed present in the pinned
  Mathlib.
- **Scope discipline.** Do the π₀ / domain-wall case and **stop**.
  `Mathlib/Topology/Homotopy/HomotopyGroup.lean` exists and π₁ ≠ 0 → vortices is
  the next case, but the paper only uses domain walls. Record the extension as
  available-and-not-taken.
- **Non-vacuity.** The existing `Examples.lean` §11 Z₂ witness has vacuum
  manifold `{-1, 1}` — two components — so it should discharge the hypothesis
  immediately. Confirm the field genuinely leaves `M`, rather than the statement
  holding vacuously.
- **Done when.** Table 1 gains a row, and Derivation 1's central sentence cites a
  theorem.

### W3 — Demote Derivation 4 from a derivation to an empirical identification

**Done 2026-08-31.** Pass recorded below under *2026-08-31 — W3*.

- [x] **Objective.** Prose only, no Lean. Split the current single step in two.
- **Why.** "The continuous macroscopic EM field is the primary dissipative
  structure interacting with the universe" is smuggled into the chain as a proof
  step. It is not one, and it is the paper's weakest joint precisely because it
  is presented as load-bearing deduction. Stated openly as the framework's
  central *empirical commitment*, it becomes the falsifiable part — which is what
  the GWT contrast already claims for it.
- **What it takes.**
  - **(a) Coarse-graining, formal.** Discrete coupled units → continuous field
    with a symmetric kernel. `Phase2_MeshConvergence` already carries half of
    this; cite it rather than reproving anything.
  - **(b) Physical identification, empirical.** *The field realizing that kernel
    in cortex is the endogenous EM field.* Its own subsection, its own evidence,
    **its own critics cited** — the current draft cites only supportive work.
    State the failure conditions.
  - Downgrade "primary dissipative structure" to a modulatory-but-integrative
    role, which is what the cited experimental work (Fröhlich & McCormick,
    Anastassiou, Pinotsis & Miller, Ruffini) actually supports.
- **Fix the frustration/positivity contradiction in the same pass.** Derivation 4
  grounds memory capacity in *geometric frustration* — "a jagged phase space of
  near-equal energy states." But every downstream Kuramoto theorem carries
  `h_pos : ∀ i j, sys.A i j > 0` (`Phase4_KuramotoDynamics.lean:247`), which is
  an unfrustrated ferromagnet with a unique global consensus minimum. The system
  that stores memory and the system the theorems describe are **not the same
  system**. This is not recorded anywhere in the archive and it is a real defect.
  Confront it in the text; do not add a caveat and move on.
- **Done when.** Derivation 4 no longer appears in the chain table as a
  derivation, and the frustration claim is either dropped or explicitly scoped
  outside the regime the theorems cover.

### W4 — Replace Derivation 3 with the thermodynamics of prediction

**Done 2026-08-31.** Pass recorded below under *2026-08-31 — W4*.

- [x] **Objective.** Replace an invalid inference with a published theorem, and
      formalize it.
- **Why.** The current step is: σ ≥ D_KL(P‖Q)/Δt, therefore gradient descent on σ
  drives D_KL → 0. **This does not follow.** Descending on the left of an
  inequality does not force the right side down; σ relaxes to a positive NESS
  value and the bound is not tight. The archive records this as O15, "a sentence
  to weaken in `supplementary.tex`." That filing is wrong — it is not a sentence,
  it is the inference that buys the paper predictive processing, the Free Energy
  Principle, symbol grounding, and its entire claim on cognitive science.
- **The replacement.** **Still, Sivak, Bell & Crooks (2012), "Thermodynamics of
  Prediction," *PRL* 109:120604.** For a system driven by an environmental
  signal:

  ```
  W_diss  ≥  k_B T · [ I(X_t ; S_t)  −  I(X_t ; S_{t+1}) ]
               \____ memory ____/      \_ predictive info _/
  ```

  Dissipation is bounded below by the **nonpredictive** information the system
  retains. Memory that does not predict is exactly thermodynamic waste, so a
  system minimizing dissipation is thereby driven to make its retained
  information predictive. That is Derivation 3, as a theorem, since 2012.

  Pair it with **Kawai, Parrondo & Van den Broeck (2007)**,
  ⟨W_diss⟩ = k_BT · D_KL(forward ‖ time-reversed) — the *equality* the loose
  bound was gesturing at.
- **Mathlib support is much better than the archive assumed.** Verified present
  in the pinned Mathlib:
  - `Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean` —
    `klDiv_comp_right_le` for a `Kernel` with `IsMarkovKernel`. This is the data
    processing inequality in exactly the form a driven system is written in.
    Also `klDiv_map_le`.
  - `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean` —
    `klDiv_compProd_eq_add : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`.
    This is the decomposition that separates memory from predictive information.
  - `Mathlib/InformationTheory/KullbackLeibler/Basic.lean` and `KLFun.lean`.

  **Mutual information is NOT in Mathlib** — no `mutualInfo`, no `condEntropy`,
  no `measureEntropy`. Define `I(X;Y) := klDiv joint (product of marginals)`,
  which is the right definition and makes every lemma above apply directly.
- **What it takes.** Define mutual information (small). Set up the driven Markov
  chain with `Kernel` / `compProd` (medium). Prove the memory/prediction
  decomposition from the chain rule and DPI (medium). Realistically the largest
  remaining item — comparable to the whole `Phase8_SelfConsistency` effort — but
  it is *bounded*, and the hard analysis is already in Mathlib.
- **Do not oversell it.** Still gives you *prediction is thermodynamically
  favored*. It does **not** give you the Free Energy Principle, hierarchical
  generative models, or Bayesian inference. Claim the theorem, cite FEP as
  consonant, do not claim to have derived Friston. Write the scope paragraph
  before writing the Lean.
- **This subsumes O15.** The `supplementary.tex` sentence gets *replaced*, not
  weakened.
- **Done when.** Table 1's "Structural Resonance KL Bound" row is replaced by a
  memory/prediction row, and Derivation 3 cites a theorem rather than an
  inference.

### W5 — Redesign Derivation 6 so the Self theorem can see reflexivity

**Done 2026-08-31.** Pass recorded below under *2026-08-31 — W5*.

- [x] **Objective.** Make `self_of_constResonance` **false**.
- **Why.** That theorem — replacing any avatar by a constant leaves a legal
  `ReflexiveBoundary` with the same region, the same predictive model and the
  same Self — is currently reported as a strength (it shows
  `IsRestrictionResonance` does work rather than restating). It is the section's
  central problem: the fixed-point theorem cannot detect whether the avatar reads
  the field. As it stands, Derivation 6 is Banach's theorem with a
  consciousness-flavored label.
- **What it takes.**
  1. **Build the self-prediction map out of the restriction**, so that
     `IsRestrictionResonance` becomes a *consequence* of being the fixed point
     rather than a predicate bolted on beside it. Then the theorem says something
     about reflexivity instead of something about complete metric spaces.
  2. **Derive the contraction rate from `K` and `D`** rather than hard-coding
     `1/2`. "The dynamics contracts at rate f(K,D)" is a physical claim; "we
     defined a map that contracts by a half" is not.
- **Keep.** The `massEquivOn` germ–measure dictionary (O21) and the uniform
  metric on densities (O9) are good and should survive the redesign. So should
  the recorded negative result that Lévy–Prokhorov does not support the argument
  on a discrete substrate.
- **Done when.** `self_of_constResonance` no longer typechecks, and the file
  records why its falsity is the point.
- **How it came out.** Both halves landed. (1) was done by making `predict` a
  *definition* — `readout ∘ auto_resonance` — rather than a field, which is
  stronger than the item asked: `IsRestrictionResonance` is not derived from being
  a fixed point (see the recorded negative result on faithful extensions in the
  pass note — faithfulness and contraction are incompatible on a separating
  avatar), but the fixed point now *does* say something about reflexivity, namely
  `self_mem_range_readout` and `self_eq_readout_restrict`, and blinding the avatar
  moves the Self. (2) was done as `resonanceRate K D τ = exp(-(K - 2D)τ/2)`, with
  the contraction derived from `K > K_c` and its unavailability below threshold
  recorded as a theorem. The `massEquivOn` dictionary, the uniform metric and the
  Lévy–Prokhorov negative result all survive unchanged, as the item required.

### W6 — Make Axiom 1 do work

- [ ] **Objective.** Give the first premise a theorem that consumes it, or stop
      calling it an axiom.
- **Why.** The section's own footnote concedes it "contributes vocabulary rather
  than content." No theorem in the development consumes a symmetry group or a
  metric.
- **What it takes.** What the chain actually uses downstream is not the Poincaré
  group but **finite phase space ⟹ bounded information capacity**:
  `H(μ) ≤ log |X|`, with equality iff uniform. Small theorem. The Poincaré group
  then becomes an illustration in prose, which is all it ever was.
- **Leave Noether closed.** O12 stays decided-not-doing: `SymmetryInvariantAction`
  has no dynamics, so no conserved quantity can attach to it, and a Table 1 row
  backed by one degree of freedom would spend the paper's one rhetorical asset.
  Reason unchanged; do not re-rank without recording why.
- **Done when.** Either a theorem consumes Axiom 1, or the section is retitled
  from "Axiom 1" to a setting/vocabulary section.

### W7 — Manuscript presentation

**Done 2026-08-31.** Pass recorded below under *2026-08-31 — W7*.

- [x] **Objective.** Make the paper readable by the people it is aimed at.
- **What it takes.**
  - **Figures. There are currently zero in 55 pages.** Required: (i) a schematic
    of the chain marking which links are theorems, which are instance
    obligations, and which are prose — the table in "The frame" above is the
    content; (ii) the bifurcation diagram `r(K)`, whose existence, uniqueness,
    continuity at threshold and strict monotonicity are all now proved and none
    of it is shown to the reader; (iii) the four existing simulation figures from
    `simulations/`, **in the main text, with methods.**
  - **Table 1 to the supplement.** It runs pages, is written in Lean identifiers
    with `\allowbreak` throughout, and several cells contain full paragraphs.
    Replace with a five-row summary: claim / status / what is assumed.
  - **Move the proof narrative out of the main text.** The fold-then-cross
    argument for `vonMisesSRatio_strictAntiOn` is a page of Derivation 7. It
    belongs in the supplement.
  - `\date{\today}` will print a build date. Fix.
- **Done when.** A cognitive scientist or physicist can read the main text
  without a Lean background.

### W8 — Write the honesty paragraph, and write it early

**Done 2026-08-31.** Pass recorded below under *2026-08-31 — W8*.

- [x] **Objective.** State plainly that no new physics is derived.
- **Why.** Every physical result invoked is established: Picard–Lindelöf,
  Barbălat 1959, Sakaguchi 1988 (K_c = 2D), Kibble 1976, Landauer, Gibbs, Banach,
  Still et al. 2012. A physicist referee will establish this in three paragraphs
  if the paper does not. Conceding it in the abstract costs nothing and buys
  credibility that the rest of the paper's honesty has already earned.
- **Draft.**
  > No new physics is derived here. Every physical result invoked is
  > established. What is new is that they have been stated in one formal
  > language, their mutual consistency mechanically checked, and the points where
  > the chain relies on stipulation rather than derivation located exactly.
- **Then say what the framework does buy.** The one prediction that is the
  framework's own and no rival's: the **sleep-inertia timescale mismatch** —
  phase realignment of cortical rhythms (~ms) against astrocytic volume / CSF
  clearance (~10²–10³ s), so that recovery tracks the slow variable through the
  bifurcation and yields a *delayed sigmoid* rather than the exponential a purely
  electrical account predicts. Different functional form, fittable, discriminating.
  It is currently one paragraph. Make it the discussion's centrepiece.
- **Write this before W3 and W7**, because it changes how those sections are
  phrased.

---

---

## 2026-08-31 — W1: the equilibrium hypothesis, discharged by a dynamics

**What was built.**

A new module, `PhysicsOfConsciousness/Phase5_EquilibriumBridge.lean` (170 lines),
importing both `Phase5_GlobalSection` and `Phase4_RotatingFrame`. The import
direction question the item raised resolved cleanly: `Phase4_RotatingFrame` and
`Phase4_MacroscopicScaling` are siblings — neither imports the other — so a
module above both introduces no cycle and nothing needed restructuring. Three
declarations:

* `kuramoto_limit_minimizes` — `kuramoto_tendsto_global_minimum` restated
  against a *given* limit instead of the one it constructs internally. The
  convergence theorem returns its limit existentially, which is unusable to a
  caller who already has a phase field in hand; `ThermodynamicCover` puts one in
  exactly that position, since the class fixes `phase` before anything is proved
  about it. The proof is `tendsto_nhds_unique` and nothing else.
* `ThermodynamicCover.ofConvergentTrajectory` — the constructor. Takes a
  `LocalSectionSynchronization` whose `phase` is the limit of a Kuramoto
  trajectory satisfying §7's hypotheses, and returns a `ThermodynamicCover`
  whose `thermodynamic_equilibrium` field is discharged by that convergence.
  The cover's `A`, `A_symm`, `A_pos` are read off the *dynamics'* system rather
  than chosen separately, so the system whose equilibrium the class asserts and
  the system whose trajectory is run are the same system.
* `ThermodynamicCover.ofConvergentTrajectory_phase` — the `rfl` lemma that lets
  a caller chain the constructor's hypothesis into `phase_locked` without
  unfolding.

`Examples.lean` §17.1 (about 190 lines) is the witness. `trioTraj` names the
trajectory §17 had left existentially quantified; `trioLimit` names its limit.
Three patches on the existing `Cortex` substrate, `trioPatch i` being everything
except site `i`, so every pairwise overlap is a single nonempty site
(`trioPatch_overlap_01`). The local data is built §14's way, not §4's: each
patch carries its own mass profile via `sectionOfMassOn` on its own open, no
measure on all of `Cortex` appears in the instance, and
`section_agrees_of_phase_eq` is discharged by computing that the profiles agree
off their blind sites (`trioW_agree`). `trioCover` is then
`ofConvergentTrajectory` applied to that cover.

**Non-vacuity.**

* `trioCover_start_not_locked` — the trajectory starts at `(0, 0, ½)`, which is
  provably not phase-locked. The configuration Derivation 5 demands is arrived
  at, not posited.
* `trioCover_phase_locked` — lockedness holds of the instance, but unlike §4 and
  §13 it is a *consequence* of the dynamics rather than of how the phase field
  was written.
* `trioW_ne_glued`, `trioW_ne_01` — the three profiles are pairwise distinct and
  none is the glued state.
* `trioCover_glued_eq`, `trioCover_invariantMeasure` — the section the three
  patches glue to has profile `(2, 1, 3)`, which is none of the three. So one
  cover now carries both the emergence reading of Derivation 5 (§14's property)
  and the derived-equilibrium reading (this pass's).

**What this does *not* establish.**

* Minimality still routes through `phase_locked_minimizes_potential'`. What the
  dynamics supplies is that the limit is *phase-locked*; lockedness implies
  minimality by the pointwise `cos ≤ 1` argument that was already in Phase 4.
  The content is that lockedness is derived on a class of initial data rather
  than assumed on every instance — not a new characterisation of the minimum.
* The hypotheses are restrictive and cannot be dropped. Splay and twisted
  configurations are equilibria of the same flow, so the arc condition and the
  energy threshold are the scope of the statement, not slack in it.
* **The cover's other physical hypothesis is untouched.**
  `LocalSectionSynchronization.section_agrees_of_phase_eq` — synchronised patches
  agree where they overlap — remains an instance obligation, and no dynamics in
  this development bears on it. Derivation 5 rested on two physical assumptions;
  it now rests on one, plus a basin condition on initial data.
* `ThermodynamicCover` is still a class with a field, deliberately. The standing
  rule forbids turning it into a standalone axiom, and the statement is false of
  arbitrary configurations, so the field stays and the constructor is the way to
  discharge it.

**The live defect the item named is fixed.** The docstring at the old
`Examples.lean:3191` claimed §17 "is what discharges
`ThermodynamicCover.thermodynamic_equilibrium` on an instance rather than
assuming it." It was false — §17 stopped at `trio_reaches_minimum` and built no
cover. It now points at §17.1, where a cover exists, so the sentence is true as
written rather than corrected away.

**Docstrings corrected.** Three stale passages in `Phase5_GlobalSection.lean`
said the physical work of reaching the minimum "is done by the informal argument
in the manuscript (and, numerically, by `simulations/kuramoto.py`), not by Lean."
That is no longer true and all three now point at the bridge. **O20 is closed**
in the direction it asked about.

**Manuscript updates.**

* Table 1, "Phase synchronization to Unity" row: records that the equilibrium
  hypothesis is no longer assumed on every instance, names
  `ofConvergentTrajectory` and `Examples`~§17.1, and states that the
  overlap-agreement hypothesis is untouched.
* `main.tex` Derivation 5: the paragraph opening "Two hypotheses still carry
  physical content and both are instance obligations" was false after this pass
  and is rewritten; a new paragraph after the §17 discussion states what the
  bridge does and what remains assumed.
* `supplementary.tex` §5: the caveat "phase-locking is not derived from dynamics
  here" is scoped to the file and pointed at the bridge.

**Gates.**

* `lake build` clean, 17,610 jobs, zero `sorry`, zero warnings.
* `#print axioms` on all 17 new declarations: `propext`, `Classical.choice`,
  `Quot.sound` only.
* `main.tex` 55 → **57 pages**; overfull hbox magnitudes **identical to `HEAD`**
  (23, checked by diffing the sorted list, not assumed); zero undefined
  references or citations.
* `supplementary.tex` **10 pages**, overfull 13 → **12** (two long identifiers in
  pre-existing text gained `\allowbreak`s after the insertion shifted their
  paragraphs); zero undefined references or citations.

**Note for W7.** §17.1's three-patch geometry — three opens, three pairwise
overlaps of one site each, profiles pinned to `(2,1,3)` — is the clearest
picture of Derivation 5 in the development and is a candidate for the chain
schematic figure.

**Next item: W8** (write the honesty paragraph), since the ledger requires it
before W3 and W7, then W2.

---

## 2026-08-31 — W8: the honesty paragraph, and the one prediction that is ours

Prose only; no Lean touched.

**What was written.**

* **A new `\subsection*{What is new here, and what is not}` closing the
  Introduction** — placed early, as the item required, because it changes how
  every later section can be phrased. Three paragraphs: the concession that no
  new physics is derived, with each invoked result named and cited; what *is*
  new, which is that the results are stated in one language, mechanically
  checked against each other, and the stipulations located; and a forward
  pointer to the one prediction that is the framework's own.
* **The abstract** now carries the concession in its own sentence rather than
  the weaker "without introducing new fundamental physics", and its
  two-assumptions clause is corrected for W1: the synchronization step is
  "proved from a dynamics for initial data inside an explicit basin and assumed
  outside it", which is the true status. It also names the sleep-inertia
  prediction, so a reader who stops at the abstract knows where the paper is
  falsifiable.
* **A new section, `The Sleep-Inertia Timescale Mismatch`** (`\label{sec:prediction}`),
  before the Corollary. The two sleep paragraphs were moved out of Derivation 7
  and given four new `\paragraph` blocks: *why this implies a delayed sigmoid*,
  *what the alternative predicts*, *what would falsify it*, and *what this
  prediction assumes*. The mechanism paragraph is the substance — the fast
  variable rides the equilibrium branch, so the slow variable (astrocytic
  volume, `10²–10³` s) carries the entire time course, and composing a monotone
  `K(t)` with the branch geometry gives latency → continuous rise → saturation.
  The three facts about the branch that force that shape are named as theorems
  (`fixed_point_eq_zero_of_le_critical`, `supercritical_fixed_point_existsUnique`,
  `coherent_branch_continuous_at_threshold`, `coherent_branch_strictMono`), all
  four verified to exist. A jump at threshold would predict a step; a
  non-monotone branch would predict overshoot; neither is what is proved.

**Eight references added, every one verified online** (`AGENTS.md` §4). The
honesty paragraph names established results, and naming them without pointers
would have been its own defect. Landauer in particular was invoked in the title,
the abstract, Derivation 2 and the Corollary with **no citation anywhere** —
that is now fixed at both prose sites.

| key | verified as |
|---|---|
| `landauer1961` | IBM J. Res. Dev. 5(3), 183–191 |
| `kibble1976` | J. Phys. A 9(8), 1387–1398 |
| `sakaguchi1988` | Prog. Theor. Phys. 79(1), 39–46 |
| `barbalat1959` | Rev. Roumaine Math. Pures Appl. 4, 267–270 |
| `still2012` | Phys. Rev. Lett. 109(12), 120604 |
| `banach1922` | Fund. Math. 3(1), 133–181 |
| `coddington1955` | McGraw-Hill, New York (Picard–Lindelöf) |
| `cover2006` | Wiley-Interscience, 2nd ed. (Gibbs' inequality) |

**A stale claim in the Conclusion, corrected.** It read: "the motion is proved
to stop along every trajectory, but *where* it stops is not proved: that a
physical field reaches the phase-locked configuration remains an assumption,
discharged numerically rather than formally." That was already false at
`861f252` and doubly so after W1 — an *under*claim, but a wrong one. It now
states the conditional result, names `ofConvergentTrajectory`, says plainly that
the unconditional statement is **false** because splay and twisted states are
equilibria, and identifies what is still assumed: that a physical cortex starts
inside the basin.

**What this does *not* do.**

* It does not make the framework falsifiable in more than one place. The
  sleep-inertia prediction is the only one that discriminates against a rival;
  everything else the framework says about synchrony is shared.
* It does not license the prediction's numbers. The section says so: `K_c = 2D`
  is conditional on the von Mises density with no link to a trajectory, so the
  argument leans on the *existence and continuity* of the branch at threshold —
  which is proved — and not on the threshold's value. The identification of `K`
  with a monotone function of extracellular geometry is a modelling assumption,
  and the claim is about functional form, not a time constant.
* It does not rewrite the Derivation sections in the new voice. W3 and W7 are
  where that happens; this pass supplies the frame they were waiting on.

**Gates.**

* `main.tex` 57 → **63 pages**. Overfull hboxes 23 → **21**, and the 21 are a
  strict subset of `HEAD`'s (diffed, not assumed): the two new boxes the first
  draft introduced were removed by shortening the section title and rewording
  one abstract clause. Zero LaTeX warnings, zero undefined references or
  citations.
* `supplementary.tex` untouched, 10 pages.
* Lean untouched; no rebuild needed.

**Note for W7.** The prediction section is the natural home for a figure — the
`r(K)` bifurcation diagram beside the composed recovery curve `r(K(t))`, which
would show the flat foot and the exponential alternative on one pair of axes.
W7 lists the bifurcation diagram already; this is the second panel it wants.

**Next item: W2** (the domain-wall theorem), then W4.

---

## 2026-08-31 — W2: the wall is forced, not asserted

**What was built.**

Two theorems in `Phase1_Primitives.lean` §3, the π₀ case of the Kibble mechanism:

* `exists_notMem_of_no_common_preconnected` — the primary form. On a
  `PreconnectedSpace` substrate, if **no** preconnected subset of `M` contains
  both `phi x₁` and `phi x₂`, then `∃ x, phi x ∉ M`. Stated with the separation
  hypothesis rather than with `connectedComponentIn` because that is the form a
  witness can discharge directly — exhibit the reason no connected piece of the
  vacuum manifold spans both values.
* `exists_notMem_of_connectedComponentIn` — the standard phrasing, derived from
  it in two lines, since `connectedComponentIn M (phi x₁)` is the largest
  preconnected subset of `M` through that point.

The estimate in the item was correct for once: `IsPreconnected.image`,
`isPreconnected_univ` and `IsPreconnected.subset_connectedComponentIn` were all
present and the proofs are four lines each. No hypothesis mentions energy, a
potential, or a symmetry.

**Non-vacuity — and it needed more than the item anticipated.**

`Examples.lean` §11.1. The item predicted §11's Z₂ witness would "discharge the
hypothesis immediately". It does not, quite: §11 proved only that `1` and `-1`
are in `DynamicalVacuum wellV` and that `0` is not, which leaves open that the
vacuum set is *larger* and possibly connected. So the pass first computes it —
`wellVacuum_eq : DynamicalVacuum wellV = {-1, 1}`, from `(v²-1)² ≤ 0` — and only
then proves the disconnection, `wellVacuum_separated`, in the form the theorem
consumes: a preconnected subset of `ℝ` is order-convex, so one spanning `-1` and
`1` contains `0`, which is the top of the barrier.

`wellV_domain_wall` is the payoff and quantifies over **every** continuous field
on **any** connected substrate reaching both minima — no formula appears in the
statement. That is the sense in which the wall is inevitable rather than
exhibited.

Non-emptiness of that class is then checked separately, because a theorem
quantified over all fields is worthless if none satisfies its hypotheses:
`kink` (the clipped identity on `ℝ`) does, `kink_leaves_vacuum` fires the
theorem, `kink_zero_notMem` locates the wall at the origin, and
`kink_connects_distinct_vacua` confirms the two endpoint values are distinct
minima rather than the hypotheses holding degenerately.

**What this does *not* establish.**

* Only π₀. `π₁ ≠ 0` forcing vortex lines and `π₂ ≠ 0` forcing monopoles are the
  rest of Kibble's classification, and `Mathlib/Topology/Homotopy/HomotopyGroup.lean`
  would support at least the next one. **Available and not taken**, per the
  item's scope discipline — recorded in the docstring, in `main.tex` and in
  `supplementary.tex`, so it is a decision rather than an omission.
* It is a *different* obstruction from `has_topological_defect`, which is the
  null-homotopy notion — maps into `M` that cannot be contracted *within* `M`.
  Neither implies the other, and the docstring says so.
* It does not connect the wall to energy. The theorem is pure topology; that an
  energy-minimising field ends up in two different components is not derived
  from anything, and the manuscript does not claim it is.
* **`supplementary.tex`'s Theorem 1 is still stronger than what is formalized.**
  It is stated in terms of `π₁` and a coset space `G/H`. That was already true
  before this pass and remains true after it; the supplement now says so
  explicitly rather than leaving the reader to notice.

**Manuscript updates.**

* **Table 1 gains a row** — "Inevitability of Boundaries (π₀)" — naming the
  theorem, the witness, and the higher-homotopy cases as not taken.
* **Derivation 1's central sentence now cites a theorem.** Two new paragraphs
  say what was asserted before, what is proved now, why the proof is elementary,
  and what the witness had to establish that §11 had not.
* **`supplementary.tex` §1's standing scope note is corrected.** It read "Lean
  establishes that a defect *obstructs extension*, not that a defect must
  exist." The second half is no longer true and the paragraph now separates the
  two directions, with the π₁-vs-π₀ gap named.

**Gates.**

* `lake build` clean, 17,610 jobs, zero `sorry`, zero warnings. (A first draft
  used `push_neg`, which is deprecated in this toolchain; replaced with a
  `not_not` term rather than silenced.)
* `#print axioms` on all 9 new declarations: `propext`, `Classical.choice`,
  `Quot.sound` only.
* `main.tex` 63 → **64 pages**; overfull hboxes **21**, a strict subset of
  `HEAD`'s 23 (diffed). Zero warnings, zero undefined references.
* `supplementary.tex` **10 pages**; overfull 13 → **11**, again a strict subset
  (diffed). Zero warnings.
* Lean now 11,561 lines across 18 modules.

**Two notes for later items.**

* *For W6.* The π₀ theorem is the first result in the development that consumes
  a *topological* hypothesis on the substrate (`PreconnectedSpace X`). Axiom 1's
  section supplies a symmetry group and a metric and is consumed by nothing;
  this is a nearby example of what "a theorem that consumes the setting" looks
  like, though it is not itself a consumer of Axiom 1.
* *For W7.* The chain schematic can now mark the SSB → boundary link as a
  theorem rather than prose. Two of the three defects the frame table listed are
  closed; **W4 is the remaining one**, and it is the one that moves the venue
  ceiling.

**Next item: W4** — replace Derivation 3's invalid inference with Still et al.

---

## 2026-08-31 — W4: the inference, replaced rather than weakened

**What was built.**

A new module, `PhysicsOfConsciousness/Phase3_PredictiveThermodynamics.lean`
(481 lines), and `Examples.lean` §18 (about 320 lines).

*Definitions.* Mathlib has `klDiv` but no mutual information, no conditional
entropy and no measure entropy — confirmed absent from the pinned revision by
grep, as the item predicted. `mutualInfo μ := klDiv μ (μ.fst.prod μ.snd)` is the
standard definition and the one that makes every lemma in
`Mathlib/InformationTheory/KullbackLeibler/` apply unchanged. Valued in `ℝ≥0∞`,
so Gibbs' inequality is discharged by Mathlib's construction rather than
re-proved.

*The Markov chain is built into the shape of the evolution, not asserted beside
it.* `evolvedJoint μ κ := (Kernel.id ∥ₖ κ) ∘ₘ μ`. The parallel kernel acts as the
identity on the system coordinate and through `κ` on the signal coordinate, so
there is no channel from `X_t` to `S_{t+1}`. That *is* the hypothesis
`X_t → S_t → S_{t+1}`, and it is unstatable-as-false rather than assumed.

*The theorem.* `predictiveInfo_le_mutualInfo` — `I(X_t;S_{t+1}) ≤ I(X_t;S_t)`.
The proof is three rewrites: `evolvedJoint_fst` and `evolvedJoint_snd` compute
the evolved marginals (`μ.fst` and `κ ∘ₘ μ.snd`), `Measure.prod_comp_right`
identifies the product of *those* with the parallel kernel applied to the product
of the originals, and `klDiv_comp_right_le` finishes. The two marginal lemmas are
the only real plumbing and each is six lines.

*Two regimes, proved rather than described.* `predictiveInfo_id` — a frozen
signal is perfectly predicted, so nonpredictive information is zero.
`evolvedJoint_const` / `predictiveInfo_const` / `nonpredictiveInfo_const` — a
signal that forgets its own past can be predicted not at all, so the *entire*
memory is nonpredictive. The second needed the evolved joint computed outright:
pushing `μ` through `id ∥ₖ const ν` gives `μ.fst ⊗ ν`.

*The postulate.* `class PredictiveDissipation` carries the joint law, the signal
dynamics, `k_B T`, the dissipated work, a finite-memory field, and Still's bound
as `still_bound`. Standing rule 1, and the `axiom` form is refutable for exactly
the reason `kl_bound_axiom` was — `Examples.lean` §18.4 proves it
(`still_bound_is_not_an_axiom`) rather than describing it.

*What is derived from it.* `dissipatedWork_nonneg` — the second law, the exact
analogue of `discrete_entropy_rate_nonneg` but with the data processing
inequality in place of Gibbs'. `nonpredictive_le_dissipation` — the inference in
the valid direction. `predictive_eq_of_no_dissipation` — a quasi-static drive
leaves every retained bit predictive. `predictive_ne_top` — predictive
information is finite as a *consequence* of the finite-memory field, so that is
the only finiteness hypothesis the class needs.

*KPV.* `IsKPVDissipation` is a predicate on an instance, not a further class
field — the `IsRestrictionResonance` pattern, per standing rule 3.
`nonpredictive_le_arrow` derives that the arrow of time bounds the wasted memory.
It has no independent mathematical content and the docstring says so.

**Non-vacuity — §18, and it is the larger half of the pass.**

The witness is a correlated two-bit law: `corrJoint` puts mass `1/2` on each
agreeing configuration. Establishing that its mutual information is *neither zero
nor infinite* is where the work is.

* `memory_ne_zero` routes through `klDiv_eq_zero_iff`, so it reduces to
  `corrJoint ≠ indepJoint`, checked on one singleton (`1/2` against `1/4`) rather
  than by evaluating an integral.
* `memory_ne_top` needs absolute continuity, obtained from the fact that the
  reference law charges *every* singleton with `1/4`, so a set it annihilates is
  empty; integrability is `Integrable.of_finite`.
* `frozenSystem` — a static environment. `dissipatedWork := 0` is *permitted*,
  not assumed: `still_bound` is checked and discharged by `predictiveInfo_id`.
  `frozenSystem_all_memory_predictive` fires the zero-dissipation theorem and
  pairs it with `memory_pos`, so the conclusion is about a system that does
  remember something.
* `scrambledSystem` — an environment redrawn at each step.
  `scrambledSystem_dissipates` proves the instance is *forced* to dissipate, and
  the floor is its whole mutual information. `scrambledSystem_dpi_strict` shows
  the data processing inequality is strict here where it was an equality in
  §18.1, so it is not secretly one or the other.
* `scrambledSystem_kpv` discharges the KPV predicate on this instance, with the
  forward ensemble the correlated law and the reversed one the product of its
  marginals. The docstring says plainly that this is the saturating case and that
  a physical instance would have slack.

**The theorem is fenced.** §18.3 builds `writeKernel`, a Markov kernel on the
*pair* that copies the system's state into the signal, and proves
`writeKernel_increases_mutualInfo`: it carries an independent two-bit law to a
perfectly correlated one, raising mutual information from `0`. So
`predictiveInfo_le_mutualInfo` is not a fact about Markov kernels in general, and
the `id ∥ₖ κ` form carries the physics rather than decorating it. This is the
service `§16`'s one-way kernel performs for the symmetric-kernel theorems.

**What this does *not* establish.**

* **It is not the Free Energy Principle.** Still's bound says prediction is
  thermodynamically favoured. It says nothing about hierarchical generative
  models, variational free energy or Bayesian inference. The manuscript now cites
  FEP as *consonant* and says explicitly that this is weaker than derivation.
* **Symbol grounding does not follow, and the manuscript no longer claims it.**
  Maximal predictive information is compatible with the system storing a lossy or
  unrecognisable function of the signal; a state that predicts is not thereby a
  state that means. What survives is narrower and is stated as such.
* **Still's bound itself is a postulate here.** Deriving it needs a stochastic
  thermodynamics — path measures, a time-reversal involution, Crooks' fluctuation
  theorem — none of which is in Mathlib. Everything downstream is derived; the
  bound is not.
* **Nothing connects `S` to the rest of the development.** The signal is
  abstract. There is no link to the Kuramoto dynamics of Phase 4 or the
  continuous field of Phase 8, and none is claimed.
* **The old bound is retained, not deleted.** `StructuralResonance` is a
  consistent postulate and `structural_resonance_bound` a correct rearrangement
  of it; what was wrong was the use made of it. Both files now say so at the
  point of use.

**The live defect the item named is fixed.** `Phase3_KLBound`'s docstring said
this bound "is what the informal argument of Derivation 3 appeals to when it
claims structural resonance forces KL(P ‖ Q) → 0", and filed the limit as merely
"not formalized". That understated it: the limit does not follow. The docstring
now says the inference is invalid, why (`σ` relaxes to a positive NESS value, so
the bound delivers `D_KL ≤ Δt·σ_NESS` and never zero), and where the replacement
is. The module header carries the same note.

**Manuscript updates.**

* **Derivation 3 is rewritten and retitled** — "Prediction as the Thermodynamic
  Cost of Memory". It states the old argument, withdraws its final step and says
  exactly why; states Still's bound; gives the three consequences as theorems;
  explains where the no-back-action hypothesis lives and exhibits what breaks
  without it; describes both witness regimes; adds the KPV equality; and closes
  with a *what this does not establish* paragraph that retracts the FEP and
  symbol-grounding claims by name.
* **Table 1 gains a "Nonpredictive information bounds dissipation" row**, and the
  old "Structural Resonance KL Bound" row is **rescoped rather than deleted** —
  it now records that the postulate is retained, yields `σ ≥ 0`, and that no
  limit may be read off it. Deleting it would have hidden a class that is still
  in the Lean and still inhabited; the item said "replaced", and what is replaced
  is the chain-level claim, which now sits in the new row.
* **`supplementary.tex` §3.** The old Theorem 3 is printed, withdrawn, and
  replaced by a new Theorem 3 stating the data processing inequality and Still's
  bound together. O15's sentence — "what remains unformalized is the limit
  itself… which would need a coercivity or Łojasiewicz-type estimate we do not
  have" — is **replaced, not weakened**: the new text says the gap was in the
  inference and not in the analysis, and that the earlier filing misdescribed it.
* **One reference added, verified online** (`AGENTS.md` §4): `kawai2007` —
  Kawai, Parrondo & Van den Broeck, *Dissipation: The phase-space perspective*,
  Phys. Rev. Lett. **98**(8), 080602 (2007). `still2012` was already present and
  correct from W8, and is now actually used rather than only named.

**Gates.**

* `lake build` clean, 17,612 jobs, zero `sorry`, zero warnings.
* `#print axioms` on all 19 new module declarations and all 27 new `Examples`
  declarations: `propext`, `Classical.choice`, `Quot.sound` only.
* `main.tex` 64 → **70 pages**; overfull hboxes **21**, *identical* to `HEAD`'s
  set (diffed as a multiset, not assumed — no new boxes and none removed). One
  new box did appear on the first draft, from `predictive_eq_of_dissipatedWork_eq_zero`
  at the end of a paragraph; the Lean theorem was **renamed** to
  `predictive_eq_of_no_dissipation` and the sentence rewrapped, rather than the
  box being tolerated. Zero LaTeX warnings, zero undefined references.
* `supplementary.tex` 10 → **11 pages**; overfull 11 → **8**, a strict subset of
  `HEAD`'s (two long identifiers in pre-existing text gained breaks after the
  insertion shifted their paragraph). Zero warnings, zero undefined references.
* Lean now 12,378 lines across 19 modules.

**Notes for later items.**

* *For W7.* §18's two regimes are the clearest picture in the development of what
  Derivation 3 now claims, and the natural figure is the memory/prediction split:
  one bar per instance, divided into predictive and nonpredictive parts, with the
  dissipation floor drawn against the second. It needs no simulation.
* *For W3.* Derivation 3 now names its own retraction in the text. Derivation 4
  has two things to retract in the same voice — the "primary dissipative
  structure" claim and the frustration/positivity contradiction — and the
  paragraph shape used here (*state the old claim, withdraw it, say why, state
  what survives*) is the template.

**Next item: W3** — demote Derivation 4 from a derivation to an empirical
identification, and confront the frustration/positivity contradiction.

---

## 2026-08-31 — W3: two claims that were being run together, separated

Prose, plus one Lean docstring — a deliberate deviation from the item's "prose
only, no Lean", recorded below.

**What was written.**

Derivation 4 is gone as a *derivation*. In its place, `\section{Macroscopic
Scaling: A Theorem and a Commitment}` (`\label{sec:scaling}`), whose opening
paragraph says it is the chain's fourth step and is deliberately not numbered as
one, and why. The section has four parts.

* **The formal half.** `mesh_refinement_convergence` is cited, not reproved, and
  what it gives is stated exactly: the discrete coupling energy is the midpoint
  rule over unordered edges (`sum_sum_mul_of_symm` — this is what makes it a
  quadrature of the continuous energy rather than a different quantity that
  happens to converge), and it converges to `∫_S f` along regular refining
  triangulations, witnessed on `[0,1)`. Then what it does *not* give, which is
  more than the old paragraph admitted: it is a statement about an **energy
  functional, not a dynamics**; the appeal to the Renormalization Group was
  decorative and is withdrawn, since no RG flow is constructed anywhere in the
  development; the limit object is a scalar stress-energy density, not an
  electromagnetic field; and `ContinuousNeuralField` is **posited as a structure,
  not produced by any theorem** — the propagation-of-chaos gap (O14) is what
  stands between the finite Kuramoto system and its continuum limit.
* **The empirical half**, set off as a displayed commitment: *in the mammalian
  cortex, the field realizing the coarse-grained coupling kernel is the
  endogenous electromagnetic field.* Stated as a claim about biology, with the
  supporting literature, then the withdrawal, then the critics, then the
  failure conditions.
* **The frustration paragraph**, which is the pass's other half.
* **The supporting physiology** (astrocytic syncytia, mitochondria), kept
  unchanged.

**"Primary" is withdrawn, by name.** The old sentence — *the continuous
macroscopic EM field is the primary dissipative structure interacting with the
universe* — is quoted in the text and retracted, because none of the work cited
for it supports the word. What the experiments show is modulation: Anastassiou
and Koch report endogenous fields of 1–5 mV/mm shifting spike timing by 1–3 ms.
The replacement claim is that the field is **modulatory in its effect on
individual neurons and integrative in its spatial reach**, and the text says
plainly that the framework needs the second property and that conflating the two
was the error.

**Critics, which the draft had none of.** Three references added, each verified
online (`AGENTS.md` §4):

| key | verified as |
|---|---|
| `pockett2002` | *Difficulties with the electromagnetic field theory of consciousness*, J. Consciousness Studies 9(4), 51–56 |
| `anastassiou2015` | *Ephaptic coupling to endogenous electric field activity: why bother?*, Curr. Opin. Neurobiol. 31, 95–103 |
| `voroslakos2018` | *Direct effects of transcranial electric stimulation on brain circuits in rats and humans*, Nat. Commun. 9, 483 |

Pockett is the sharpest of them precisely because she has defended an
electromagnetic theory herself (`pockett2012` was already cited, supportively);
the text says so. Vöröslakos et al. bound *applied* rather than endogenous
fields, and the text says that too rather than overclaiming it.

**Four falsification conditions**, enumerated in the text: epiphenomenality under
field cancellation (the decisive experiment, and in principle available); a
magnitude gap, stated as the question of whether measured ephaptic coupling
suffices to place the system above `K_c`; a timescale mismatch that would kill
the sleep-inertia prediction of W8; and dissociation of field coherence from
reported unity, which would leave the global section with no physical carrier.

**The frustration/positivity contradiction, confronted.** The item called this a
real defect not recorded anywhere. It is, and checking it made it sharper than
recorded:

* `KuramotoSystem.A : V → V → ℝ` is symmetric and otherwise unconstrained, so
  **the setting admits frustration**. It is the theorems, not the formalism, that
  exclude it.
* Every result identifying *where* the dynamics ends assumes positivity:
  `phase_locked_minimizes_potential` and `potential_min_iff_phase_locked`
  (`A i j > 0`), the class field `ThermodynamicCover.A_pos` — hence every
  conclusion of Derivation 5 — and `kuramoto_tendsto_global_minimum`, which needs
  the **strictly stronger** uniform bound `0 < a ≤ A i j`, because `a` enters the
  Łojasiewicz constant. The ledger recorded pointwise positivity; the convergence
  theorem wants more than that.
* What survives with **no sign hypothesis at all**: `is_kuramoto_trajectory_exists`
  and `_unique`, rotating-frame covariance, `dynamic_potential_antitone`,
  `dynamic_potential_tendsto`, the dissipation integral, and Barbălat giving
  `velocity_sq_tendsto_zero`. So *that* the motion stops is frustration-agnostic;
  *where* it stops is not, and every claim the framework makes about the
  destination lives on the positive side of that line.
* On the continuum side the accounting differs: `phase_locked_minimizes_entropy_of_symm`
  assumes only symmetry and so tolerates signed kernels — but it takes the
  existence of a dynamically phase-locked field as a hypothesis, which is exactly
  what frustration threatens. Recorded, because it is a place the two sides of the
  development disagree about what is assumed.

The claim is **scoped out of the chain, not repeated**: the text says the memory
capacity of a frustrated cortical network is supported by no theorem here, that
the chain uses the unfrustrated regime, and that whether a frustrated network can
hold many near-degenerate patterns *and* still synchronize enough of itself to
admit a global section is an open question about mixed-sign oscillator networks —
named as the most substantive gap we know of. Derivation 5's opening sentence,
which read "generated by millions of *frustrated* micro-components" two lines
above theorems requiring positive coupling, is corrected and now points at
`sec:scaling`.

**The Lean deviation.** The item said prose only. One docstring was added, to
`phase_locked_minimizes_potential` in `Phase4_KuramotoDynamics.lean`, recording
the positivity/frustration split at the site where the hypothesis is introduced.
No proof, statement or declaration changed, and no new declarations exist, so no
new axiom checks apply. The reason for deviating: the defect is Lean-visible —
it is a hypothesis on a theorem — and this repository's standing practice is that
scope notes live in docstrings, where the next reader of that theorem will meet
them. Leaving it only in the manuscript would have hidden it from the place it
is actually enforced.

**Table 1.** Three rows, so that the split is visible in the table and not only in
the prose:

* *Coarse-graining of a symmetric coupling* — the theorem, marked "Theorem,
  narrower than the prose it supports".
* *The field is the endogenous EM field* — marked **Empirical commitment**, "not
  formalized and not derived". The old table listed no row for this at all, which
  read as an oversight; absence is now replaced by a decision.
* *Frustration as memory capacity* — marked **Recorded gap**, naming the three
  positivity sites and the results that carry no sign hypothesis.

**Abstract.** Adds Still's bound to the enumeration of established results
invoked (W4 had added the result but not updated the list), and one sentence
naming the EM identification as an empirical commitment rather than a deduction,
with the modulatory downgrade and the four falsification conditions.

**`supplementary.tex` §4.** Two insertions. A *scope of that sentence* paragraph
after the opening, separating the coarse-graining theorem from the EM
identification and stating that nothing in the section depends on the latter
mathematically — every result is about a coupled oscillator system, whatever the
phases are taken to name. And a *positivity, and the regime these theorems cover*
paragraph after the Phase 4 implementation note, carrying the same accounting as
the main text in the supplement's register.

**What this does *not* do.**

* It does not make the EM identification more likely to be true. It makes it
  visible, attackable, and separable from the mathematics — which is the whole of
  the change.
* It does not resolve the frustration question. It records that the framework's
  memory story and its synchronization story describe different coupling
  regimes, and stops.
* It does not close O14. The continuum limit is still a posited structure, and
  the section now says so in the main text rather than only in the supplement.
* It does not touch Derivations 5–7, whose theorems are unchanged; only
  Derivation 5's opening sentence is corrected, and only because it asserted
  frustration.

**Gates.**

* `lake build` clean, 17,612 jobs, zero `sorry`, zero warnings. No declaration
  changed; the docstring is the only Lean edit. (A first draft placed the
  docstring before `omit [DecidableEq V] in`, which does not parse; the doc
  comment belongs between the `omit … in` and the `theorem`.)
* `main.tex` 70 → **77 pages**; overfull hboxes 21 → **20**, a strict subset of
  `HEAD`'s (diffed as a multiset). Four new boxes appeared in the first draft and
  all four were removed rather than tolerated — by shortening the section title,
  by `\allowbreak`s in two long identifiers, and by writing `Examples`~§6 for
  `Examples.lean`~§6 in line with the rest of the file. The box that disappeared
  is the old section title *Derivation 4: Macroscopic Scaling and Elec-*. Zero
  LaTeX warnings, zero undefined references or citations.
* `supplementary.tex` **11 pages**, overfull **8**, a strict subset of `HEAD`'s
  11. Zero warnings, zero undefined references.
* Lean 12,405 lines across 19 modules.

**Notes for W7.**

* The chain schematic now has a third category of link to draw, not two: theorem,
  instance obligation, and **empirical commitment** — `sec:scaling` is the only
  link of the third kind, and marking it differently from the stipulation at the
  end of the chain is the point of the figure.
* The four falsification conditions are a natural boxed panel rather than an
  enumerate, and the second of them ("does measured ephaptic coupling place the
  system above `K_c`?") is the one that connects to the bifurcation diagram W7
  already wants.

**Next item: W7** — figures, Table 1 to the supplement, the proof narrative out
of the main text, and `\date{\today}`.



---

## 2026-08-31 — W7: six figures, and the reference table out of the argument

**What was built.**

*Figure 1, the chain schematic (TikZ, in `main.tex`).* Ten boxes, one per link,
each carrying the claim and its status in words, colour-coded five ways:
theorem, theorem resting on a class field, empirical commitment, stipulation,
vocabulary. This is the frame table of this file turned into the reader's first
picture of the argument. The colour is redundant — every box states its status
in italics and the caption spells out each key — so the figure survives
greyscale printing and colour-blind readers.

*Figure 4, the bifurcation diagram (`simulations/bifurcation.py`, new).* The
curve `r(K)` at `D = 1`, computed from the *same* integrals `Phase8_SelfConsistency`
defines: `Z`, `M`, `S` by trapezoid on 4001 points over `[-π, π]`, `E = S/Z`,
`R = M/Z`. The coherent branch is found by bisecting `E(a) = D/K` and reading
`r = aD/K` — which is `coherent_iff_sRatio_eq`, and bisection is *licensed* by
`vonMisesSRatio_strictAntiOn` rather than merely convenient. Every feature drawn
is a proved statement and the caption names the theorem for each:
`fixed_point_eq_zero_of_le_critical` (only `r = 0` at or below threshold),
`supercritical_fixed_point_existsUnique` (exactly one `r > 0` above),
`coherent_branch_continuous_at_threshold` (the branch leaves the axis
continuously), `coherent_branch_strictMono` (it grows). The script prints its own
checks: the branch is strictly increasing at all 500 sampled couplings, and the
residual `|r − R(Kr/D)|` at `K = 4D` is 2.2e-16. Passes `ruff`, `mypy --strict`,
`bandit`, `vulture`, `xenon`, `tach`.

*Figures 2, 3, 5, 6 — the four existing simulations, in the main text with
methods.* Mesh refinement into §Macroscopic Scaling; structural resonance and
the finite-`N` Kuramoto transition into Derivation 7; hardware comparison into
the Corollary. A new §*Numerical illustrations: methods* before the Conclusion
gives every parameter, seed and integrator for all five computed figures.

**What the figures are careful not to claim.** Each caption says what its figure
does *not* show, because a picture is the easiest place in a paper to overclaim.
The bifurcation diagram shows no stability — nothing in the development says the
coherent branch is the dynamically selected one. The finite-`N` simulation is
the *deterministic Lorentzian-disorder* model, not the noisy identical-frequency
model the Lean formalizes; both have threshold `2D`, by Kuramoto's argument and
by Sakaguchi's respectively, and the agreement is a known feature of the
mean-field model rather than a result of ours. This was worth catching: the two
`K_c`s had been run together in the prose, and the soundness section's sentence
"`K_c` is nowhere in our Lean development" now says *which* `K_c` it means.
The mesh figure's `O(N^{-2})` is the midpoint rule's rate, not a prediction of
the framework, and its last point is within a factor of ten of the reference
computation. The resonance figure's `σ` settles at a *positive* plateau — which
is the visual form of exactly the reason W4 withdrew the old `σ → min ⟹ D_KL → 0`
inference — and its right panel falls 5% in 2000 steps, so it shows a direction
of drift, not convergence. The hardware figure shows a *randomly* wired
architecture being beaten, while the theorem is about fixed wiring support, where
an architecture already wired to the best pair is not beaten.

**Table 1 to the supplement.** The 20-row longtable is now Table S1 in
`supplementary.tex` under a new §*Claims and their Lean identifiers*, renumbered
`S\arabic{table}` so it prints as S1 in both the standalone and the merged arXiv
build. The main text gets a five-row table: claim / status / what is assumed.
Five prose references to "Table 1" were retargeted to S1; the one that stayed
was rewritten, since it was the sentence about the frequency-spread `K_c`.

**The proof narrative out of the main text.** The fold-and-cross argument for
`vonMisesSRatio_strictAntiOn` — the two reflections onto `[0, π/2]`, the
`2 cosh X cosh Y = cosh(X+Y) + cosh(X−Y)` identity, the crossing point from the
IVT that avoids Fubini — was a page of Derivation 7 and is now
Supplement §5.1. What stays in the main text is the conclusion, the reason the
obvious differentiation route fails, and one sentence on the shape of the
argument.

**`\date{\today}` fixed** to `31 August 2026`, and `prepare_arxiv.sh` updated in
the same pass: it now copies the five PNGs into `arxiv_submit/`, includes them in
the tarball, and its `\date` deletion matches the new line. `main.tex` sets
`\graphicspath{{simulations/}{./}}` so bare filenames resolve both from the repo
root and from the flattened tarball, and `\providecommand{\nolinenumbers}{}`
keeps the figures compiling after the script strips `lineno`. Float parameters
were loosened (`topfraction` 0.9, `textfraction` 0.07) because six floats in the
compact arXiv build otherwise pile up at the end — Figure 1 was landing on page
27 and is referenced on page 3; it now sits on page 3.

**Also in this pass, at the author's request:** the AI-assistance paragraph moved
from *Acknowledgments* to a *Contributions* section, stating which tool did which
work and adding Claude Opus 5 in Claude Code for the later formalization passes,
the figures and this restructuring, with responsibility for every claim resting
with the author.

**What this does not establish.** Nothing mathematical. No theorem was proved, no
Lean file was touched, and the Lean development is byte-identical to `b274e0b`.
The figures illustrate proved statements; they are not evidence for them, and
each caption says so. Whether the paper is now readable by a cognitive scientist
is a claim only a reader can settle — what is checkable is that the main text no
longer contains the identifier table or the fold proof, and that every figure has
its methods.

**State.**

* `main.tex` 77 → **82 pages** (six figures and a methods section added, a page
  of proof narrative removed); overfull hboxes **20**, an exact match for
  `HEAD`'s multiset — the four introduced by the methods paragraphs were removed
  rather than tolerated, by moving the script names out of the run-in headings.
  Zero LaTeX errors, zero undefined references or citations.
* `supplementary.tex` 11 → **14 pages**, overfull **8**. Zero errors.
* Merged arXiv build **43 pages**, zero errors, figures adjacent to their text.
* Lean 12,405 lines across 19 modules, unchanged.

**Notes for W5.**

* Figure 1's ninth box is the honest statement of the W5 defect and is written to
  be *deleted* when W5 lands: "The map does not yet detect whether the avatar
  reads the field." When `self_of_constResonance` stops typechecking, that clause
  comes out of the figure and out of Table 1's fifth row.
* The bifurcation script's structure — define the Lean objects by quadrature,
  then assert the proved qualitative facts as printed checks — is worth reusing
  if W5 or W6 wants a figure.


---

## 2026-08-31 — W5: the fixed-point theorem can see the avatar, and the rate is K and D

**What was built.**

`Phase6_ReflexiveTopology.lean` 319 → **553 lines**, restructured rather than
extended. The change is to the *structure*, and everything else follows from it.

`ReflexiveBoundary` no longer carries a `PredictiveModel` field. It carries the
avatar's **write** (`auto_resonance`, the encoding of the global state into the
avatar region) and its **read-out** (`readout`, the global state that encoding
predicts), and

```
ReflexiveBoundary.predict rb s = rb.readout (rb.auto_resonance s)
```

is a definition, not a field. `predictive_model` survives as a derived def
because the manuscript names it. That single move is what W5 asked for: the
self-model runs through the avatar region or it does not exist, so every
statement about `predict` is now a statement about the avatar.

**The old theorem is gone and its replacement says the opposite.**
`self_of_constResonance` — blinding the avatar leaves the same predictive model
and the same Self — does not typecheck any more, and the failure was checked
rather than assumed: elaborating the old proof term verbatim gives

```
Application type mismatch: h_contracting has type ContractingWith c rb.predict
but is expected to have type ContractingWith ?m (rb.constResonance a₀).predict
```

`constResonance` still builds a legal boundary — the class still has nothing to
object with, which is why the predicate is still needed — but its dynamics is a
different one. Three theorems replace the old one:

* `constResonance_predict_const` — the blinded self-model is a **constant map**.
  It has stopped being a function of the field.
* `constResonance_existsUnique_self` — it does have a unique fixed point, namely
  `readout a₀`, and naming it is the point: no metric, no completeness and no
  contraction are used, because Banach is not being applied to anything.
* `not_self_of_constResonance` — **blinding moves the Self.** A fixed point of
  the field's own model is not a fixed point of the blinded one as soon as
  `readout a₀ ≠ s`. Witnessed, not assumed: `cortexBlind_self_ne`.

**What being a fixed point now buys.** Two theorems that are false statements
about the old structure, because there `predict` had nothing to do with `readout`:

* `self_mem_range_readout` — the Self lies in the range of the read-out, so it is
  reconstructed from a single section over the avatar region. The
  "low-dimensional avatar" the module header has always claimed, as a theorem.
* `self_eq_readout_restrict` — under `IsRestrictionResonance`, the Self satisfies
  `s = readout (restrictToAvatar s)`: the field is what its own localized
  self-encoding reconstructs.

`predict_eq_readout_restrict` and `isRestrictionResonance_iff_of_injective` make
the predicate a statement *about the dynamics* rather than one bolted on beside
it — the second is an iff and needs `Function.Injective readout`, which is stated
as a hypothesis and used nowhere else.

**The rate.** `resonanceRate K D τ = exp(-(K - critical_coupling D) τ / 2)`, the
linear relaxation factor of the mean-field order parameter with `K_c = 2D`.
`Phase6` now imports `Phase8_ContinuousField` for `critical_coupling`; that file
has no in-project imports, so no cycle. Three theorems:

* `resonanceRate_lt_one` (`τ > 0`, `K > K_c`) and `one_le_resonanceRate`
  (`τ ≥ 0`, `K ≤ K_c`) split the parameter plane at Sakaguchi's threshold.
* `not_contractingWith_resonanceRate` — at or below threshold `ContractingWith`
  at that rate is false **for every self-map of every metric space**, because its
  first conjunct is `rate < 1`. The argument is unavailable below `K_c`, not
  merely unproved.
* `self_of_supercritical` — the unique fixed point, from `K > K_c` rather than
  from a numeral. `reflexive_topology_implies_self`, `self_unique` and
  `self_eq_of_avatar_eq` are generalized from `ContractingWith (1/2)` to a
  `{c : NNReal}`.

**Non-vacuity.** `Examples.lean` §10 was rebuilt, not patched. The old witness
`relax s = ½ s + ½ baseline` **had to be removed**: it reads `density s x` at
every site, so it does not factor through a one-site avatar — which is exactly
the defect W5 names, and is why the redesign is not cosmetic. What replaces it:

| | |
|---|---|
| `avatarRead` | the single mass a section over the one-site avatar region carries |
| `avatarReadout` | that mass, averaged with the baseline, put back as a global state |
| `cortexReflexive` | the boundary; `predict` is the composite by definition |
| `Phi_cortexPredict` | the prediction in closed form — everything it knows about `s` is `density s Site.mid` |
| `cortexPredict_dist` | the exact factor: **one half of what the avatar sees**, both inequalities |
| `cortexPredict_not_const`, `cortexPredict_fixed`, `cortexPredict_fixed_unique` | non-constant; the fixed point named; uniqueness re-derived by hand |
| `cortexTau`, `cortexSupercritical`, `cortexResonanceRate` | `K = 3`, `D = 1`, `τ = 2 log 2`, where `resonanceRate 3 1 τ = 1/2` exactly |
| `cortexHasSelf` | now `∃!`, and obtained from `self_of_supercritical` — from `K > K_c`, not from a numeral |
| `cortexSubcritical_not_contracting` | the *same* map at `K = 1`: no Banach argument at all |
| `cortexState_eq_readout_restrict`, `cortexState_mem_range_readout` | the two new positive theorems, on the witness |
| `cortexBlind_self_ne`, `cortexBlind_existsUnique_self` | the reversal, on the witness |

`cortexPredict_dist` is worth flagging as an honest loss. The old `relax_dist`
gave `dist (relax s) (relax t) = dist s t / 2` — half the distance between the
*states*. The new map cannot: it is blind off the avatar region, so two states
differing only away from `mid` have identical predictions. That is the fold, and
the theorem states it rather than hiding it.

**What this does *not* establish.**

* **Resonance is still not derived.** `IsRestrictionResonance` remains an
  instance obligation. A route was tried and rejected: assume the read-out is a
  right inverse of the restriction (`restrictToAvatar ∘ readout = id`, "what the
  avatar writes is what it reads back"), and resonance at the fixed point falls
  out in one line. It is unusable — that hypothesis forces `predict` to preserve
  the restriction exactly, so for two states differing on the avatar region
  `dist (predict s) (predict t) ≥ dist s t` and the map is not a contraction
  unless the avatar region separates nothing. **Faithful extension and
  contraction are incompatible on a separating avatar.** Recorded so it is not
  re-attempted.
* **Resonance at the Self is not the discriminator.** With a faithful read-out
  the blinded boundary's own fixed point also satisfies resonance *at that point*
  — a blind avatar is right about exactly the one state it forces. What blinding
  destroys is that the Self depends on the field, which is why the negative
  theorem is `not_self_of_constResonance` and not a resonance failure.
* **`avatarReadout` is still a modelling choice.** No field dynamics in the
  development produces it. W5 removed the stipulation of the *rate*, not of the
  map.
* **`K = 3` is a choice of units for the witness**, not a measurement. Nothing
  here derives a coupling constant from cortex. The Lipschitz bound at the
  mean-field rate is an instance obligation; what changed is that it is now
  stated in the substrate's parameters and its *consequence* is conditional on
  the same threshold Derivation 7 proves the phase transition at. Derivation 6
  and Derivation 7 were previously unconnected.
* **The linearization is near-threshold.** `ṙ = ((K - K_c)/2) r + O(r³)` is the
  standard mean-field result; the exponential rate is exact only near `K_c`. The
  module header says so.

**Manuscript updates.**

* **Figure 1, box 9** — the clause written to be deleted when W5 landed
  ("The map does not yet detect whether the avatar reads the field") is out,
  replaced by what is now true: the map is the avatar's read-out of its own
  encoding, blinding moves the fixed point, and the rate is `e^{-(K-K_c)τ/2}`.
* **Table 1, row 5** — "contraction on a complete metric space" replaced by the
  read-out factorization, the rate as an instance obligation, and the threshold
  deciding the contraction.
* **Derivation 6** — the single 1,100-word paragraph is now six paragraphs with
  run-in headings: *What carries the weight*, *The map is the avatar, or there is
  no map*, *Auto-resonance as a constraint*, *The contraction rate is K and D,
  not a numeral*, *What is still not established*. The old negative result is
  stated as the defect it was, then reversed.
* **Supplement §Reflexive Topology** — stages (iii)–(v) rewritten; Table S1's
  Derivation 6 row rewritten.

**Gates.**

* `lake build` clean, 17,612 jobs, zero `sorry`, zero warnings. `#print axioms`
  on all 25 new or changed results reports only `propext`, `Classical.choice`,
  `Quot.sound`.
* **A discrepancy found in passing, not fixed here.** This ledger and the
  manuscript both say the development "declares no axioms". `Axioms.lean` in fact
  declares three live ones — `landauer_principle`, `phase_space_is_compact`,
  `principle_of_least_action` — under a comment that says they "are commented out
  because they are not actively invoked". They are not commented out. Nothing in
  the chain depends on them (every `#print axioms` above confirms it), so the
  *substance* of the claim holds, but the wording does not. Either comment them
  out as the note says, or reword the claim to "no axiom is reachable from any
  result". Left for the next pass rather than folded into W5; recorded so it is
  not rediscovered.
* `main.tex` 82 → **84 pages**; overfull hboxes 20 → **18**, a strict subset of
  `HEAD`'s (diffed as a multiset; the two that vanished were in the old
  Derivation 6 paragraph). Zero errors, zero undefined references or citations.
* `supplementary.tex` **14 pages**, overfull **8**, magnitudes *identical* to
  `HEAD`'s. Zero errors.
* Merged arXiv build 43 → **45 pages**, zero errors, zero overfull, zero
  undefined.
* Lean 12,405 → **12,822 lines** across 19 modules; `Examples.lean` 3,981 →
  4,164.

**A tooling note that cost half an hour.** `grep -c` in this environment is a
shell function wrapping `ugrep --ignore-files`, which silently skips
`.gitignore`d paths — so `grep -c Overfull main.log` reported *nothing* for a
build in a scratch directory and appeared to prove `HEAD` had zero overfull
boxes. Use `awk '/Overfull/{n++} END{print n+0}'` or `sed -n 's/…/p'` when
counting in build artefacts. The compile-gate numbers above were re-measured that
way.

**Next item: W6** — give Axiom 1 a theorem that consumes it (`H(μ) ≤ log |X|`,
equality iff uniform), or retitle the section from "Axiom 1" to a setting section.


## Low value — listed so they are not rediscovered as new

Do not pick these up ahead of W1–W8. Both are completeness work with no claim
attached; neither changes a sentence of either document.

- **O10 (remainder).** Construct the continuum drift map
  `K ↦ (x ↦ ∫ K(x,y) sin(θ_y − θ_x) dy)` as a bounded operator
  `L²(μ⊗μ) → L²(μ)`. The estimate is Cauchy–Schwarz (kernel bounded by 1, so on a
  finite measure space the operator norm is at most `μ(M)^{1/2}`); the work is
  `Lp` bookkeeping. `Mathlib/MeasureTheory/Function/Holder.lean` (`holderL`) and
  `condExpL2` are the precedents for the cost. It generalizes a theorem that is
  already proved, witnessed, and fenced by a counterexample.
- **O16.** The midpoint rate on the concrete `[0,1)` witness. Not a Mathlib gap —
  `discreteEnergy` is already recorded as the midpoint rule and the error bound
  is `taylor_mean_remainder_lagrange` per cell. What blocks the general statement
  is the development's own generality: the abstract `Mesh` lives over a metric
  space with no second derivative. Record the scope point whether or not it is
  proved.

## Closed as decided-not-doing — do not re-rank without recording a reason

Carried from the consolidated ledger. Full reasoning in the archive.

- **O12 — Noether.** `SymmetryInvariantAction` has no dynamics, so no conserved
  quantity can attach to it. The obstacle is structural, not difficulty; point
  mechanics was prototyped end to end in one session. See W6.
- **O13 — deriving the von Mises stationary density from the SDE.** Needs the
  Fokker–Planck operator, existence and uniqueness of stationary solutions, and
  spectral stability. Confirmed absent from Mathlib by grep. Keep the density as
  a **declared modelling input** and cite the mean-field literature for it; that
  is a standard ansatz, not a hidden gap.
- **O14 — the mean-field limit.** Propagation of chaos for the finite Kuramoto
  system. A research programme, not a task. This is the single gap between
  `exhibits_phase_transition` and a statement about a trajectory, and the
  docstrings and manuscript already state it in exactly those terms.
- **O15 — `lim D_KL = 0`.** **Superseded and closed by W4 (2026-08-31)**, which
  replaced the inference rather than weakening the sentence. The recorded filing —
  "a sentence to weaken in `supplementary.tex`" — was wrong about the *kind* of
  defect, not merely its size: the gap was in the inference, not the analysis.
- **O17 — the step from the hardware results to "von Neumann architectures cannot
  be conscious."** Informal, and `main.tex` says so. Note for W3/W7: the
  measure-theoretic half (`fieldCorrelation_sited_eq_zero`) says a finitely-sited
  kernel is invisible to a functional that ignores null sets. That is a fact
  about the functional, not about the architecture, and real silicon is not a
  measure-zero set. Do not let the Corollary or Conclusion lean on it.
- **O18 — global section ↔ unity of experience.** The framework's core
  stipulation, fenced by the Russellian-monism framing. **Kept deliberately.**
  Not a defect; recorded so it is not mistaken for one.

---

## Beyond this paper — recorded, not scheduled

Two papers exist in this repository that are not the framework paper, and
neither is blocked by anything above. Recorded here so the decision to defer them
is deliberate rather than forgotten.

1. **A formalization paper.** The Kuramoto development on its own — well-posedness,
   Barbălat (absent from Mathlib), dissipation, the K_c = 2D bifurcation, the
   Bessel ratio monotonicity by the fold-then-cross route, which may be a new
   proof of a known result. Consciousness in one motivating sentence or none.
   Target **ITP** / **CPP**, or **JAR** for the full library. Nearly free: the
   Lean is done. Separately, upstreaming Barbălat's lemma and the Bessel ratio
   monotonicity into Mathlib is a weekend and a permanent citable contribution.
2. **The audit paper.** Three axioms each proving `False` from one shared root
   cause; a conjecture false via `diam ∅ = 0`; two potentials never chained, one
   provably unbounded below; a threshold predicate sensitive to substrate mass; a
   witness emptied by the 0/1 metric; the Lévy–Prokhorov negative result. Six
   errors that survived prose review. The finding is independent of whether the
   framework is right, which is what makes it robust. Target **BBS** (high
   variance, and the commentary format suits it), or *Neuroscience of
   Consciousness*, or a philosophy-of-science venue.
