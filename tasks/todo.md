# Physics of Consciousness — work plan

**Replanned 2026-08-31 (second replan of the day).** The prior file — 1,815
lines, W1–W8 all closed and recorded in full — is archived at
`_archive/todo_2026-08-31_pre-composability-replan.md`. The file before it is
`_archive/todo_2026-08-30_pre-strategic-replan.md`. Nothing is deleted. Where an
item below refers to a past pass by name (W1–W8, O10, O16) that record is in the
first archive; the pre-W1 history is in the second. Read them when you need the
reasoning behind a closed decision; do not re-litigate a closure without
recording why.

This file replaces the old one because **the bottleneck changed again**. The old
ledger was organised around the eight defects the chain had on 2026-08-30, and it
closed all eight: every link is now a theorem, a named class field, a named
empirical commitment, or an owned stipulation, and the manuscript has six figures
and a methods section. That work is done and it was the right work.

What limits the paper now is not a defect in any *link*. It is two things that
are visible only when you look at the document as a whole:

1. **The chain does not compose.** Every node is honest; no edge is checked. The
   build certifies that ten developments each compile, not that they run into
   one another. No theorem anywhere states n1 → … → n9.
2. **The manuscript reads as a changelog.** 64 drafting-history markers across
   `main.tex` and `supplementary.tex` narrate the project's own corrections in a
   document whose reader has never seen a previous draft.

Those were C1–C5 and P1–P4 below.

**All nine are closed as of 2026-08-31**, in one session, with pass records at
the end of this file. `Chain.lean` exists and `chain` composes the chain from a
finite phase space to the Self with eight named hypotheses, jointly witnessed;
Figure 1 marks its arrows and no longer draws the two that are not inferences;
and both publication files pass `check_prose.py`, which is now a pre-commit hook.

**Nothing in that section is open.** The next pass is planned in *Work items —
the next pass* below: S1–S3 sharpen the one prediction that is the framework's
own, F1–F2 take on the deepest objection a referee will raise, and T1–T5 are what
the C/P session itself generated. The presubmission inquiry was deliberately
sequenced after P3 and is now unblocked.

---

## Standing rules — carried forward, still binding

1. **A physical postulate that mentions a class field must be a field of that
   class, never a standalone axiom quantified over all instances.** A postulate
   is an obligation each model discharges, not a global claim about every model.
   This rule exists because three of five original axioms each proved `False`.
2. **Every class carrying physical content gets a witness in `Examples.lean`,**
   and where possible a theorem showing the witness is as strong as the class
   permits (the shape of `contracting_implies_const`,
   `ThermodynamicCover.phase_locked`). An uninhabitable class makes its theorems
   vacuous just as surely as an inconsistent axiom did.
3. **Do not strengthen a class to close a gap.** Add a predicate and prove
   theorems about it (the `IsRestrictionResonance` pattern), so the gap is
   visible rather than absorbed.
4. **Treat the "what it takes" column as a hypothesis to be checked, not a plan
   to be executed.** Recorded estimates have now been wrong — pointing at the
   *wrong obstacle*, not merely being pessimistic — on O8, O10, O11, O14, O16 and
   O20. Grep the pinned Mathlib before believing any blocker.
5. **Verify every reference online before committing it.** No fabricated or
   unverified citations. (`AGENTS.md` §4.)
6. **Compile gate on every manuscript change:** overfull hboxes checked against
   `HEAD` rather than assumed, zero undefined references or citations, page
   counts recorded.
7. **Build gate on every Lean change:** zero `sorry`, zero warnings, `lake build`
   clean, and `#print axioms` on every new result reporting only `propext`,
   `Classical.choice`, `Quot.sound`.

### New, and binding from this replan

8. **The publication is not a changelog.** `main.tex` and `supplementary.tex`
   state the theory's current state only. No retraction narration, no "earlier
   drafts claimed X", no "we had recorded Y; that was a misdiagnosis", and **no
   appendix or supplementary section collecting such material** — the supplement
   is part of the publication and is covered by this rule exactly as the main
   text is. Changelog-like information belongs in the repo: `CHANGELOG.md`, Lean
   docstrings, `tasks/lessons.md`, this ledger and its archives.

   **The test** is not "is this about our past" but *does this sentence still
   make sense to a reader who has never seen a previous draft?* A refutation of
   an axiom shape is a permanent mathematical fact and stays. "Earlier drafts of
   this work declared five axioms" is autobiography and goes. See P1–P3.

9. **An edge in Figure 1 is a claim, and claims get checked.** A node whose
   status is marked and an arrow that is an unlabelled black line is a document
   that is honest about its premises and silent about its inferences. Every
   arrow is now either a Lean theorem or a named hypothesis in `Chain.lean`, and
   the figure says which. Do not add a link to the chain without adding its
   edge. See C1.

---

## Where the development stands — 2026-08-31

**Lean.** 14,696 lines across 21 modules. Zero `sorry`. Zero declared axioms.
`Examples.lean` is 4,580 lines and carries 20 witness sections plus §6.1 and
§17.1; `Chain.lean` is 757 lines and carries the composition. `lake build`
clean, 17,616 jobs.

**Manuscript.** `main.tex` 93 pages, overfull 16; `supplementary.tex` 15,
overfull 8; merged arXiv build 50 pages, overfull 0. Six figures, a methods
section, and Table S1 carrying the claim-by-claim identifier map.

*(Figures as of the start of 2026-08-31; the current figures are in the C and P
pass records at the end of this file.)*

**Nothing is public.** No version of this work is on arXiv or under review as of
2026-08-31. This matters to P3: because no withdrawn claim has ever been
published, there is **no scholarly obligation to narrate any withdrawal**, and
the discoverability question that would otherwise complicate rule 8 does not
arise. Every marker in P3's inventory can simply go. If a version is posted
later, prior-version differences are handled by the arXiv per-version comment
field plus `CHANGELOG.md` — never by reintroducing narration into the manuscript.

**The eight defects of the 2026-08-30 frame are all closed** (W1–W8, plus O10 and
O16). The frame table from that ledger is in the archive; it is not reproduced
here because no row of it is open.

---

## The frame — read this before picking up an item

The decision of 2026-08-30 stands and is reaffirmed: **write the ambitious
framework paper**, accept that its readership is the EM-field / resonance
community, and do not split it. Two further decisions were taken 2026-08-31:

* **No split.** A methodology paper on axiom hygiene and an audit paper are both
  real papers and both stay recorded under *Beyond this paper*. They are not
  scheduled and this paper is not to be carved up to make room for them.
* **Focus the paper on the field-theoretic framework.** The formalization is the
  paper's method and its warrant; it is not its subject. Where a choice arises
  between saying more about Lean and saying more about the field, say more about
  the field.

### What is actually good about the framework, and why it is worth defending

Recorded here because it is the rationale for the two decisions above, and
because every item below is in service of it.

1. **It answers the combination problem structurally rather than by fiat.** Most
   theories of consciousness need some story about why many local processes make
   one experience, and most supply it by stipulation or by a measure. This
   framework's answer is that the field is *the only variable in the system that
   is defined everywhere at once* — weak per synapse, modulatory in its effect on
   individual neurons, and integrative in its spatial reach. Unity is not
   asserted of the field; it is what a field *is*. That is a real structural
   argument and very few rivals have one.
2. **Unity is given a mathematical meaning rather than a metaphorical one.** The
   sheaf-theoretic step is not decoration. "Local states glue to one global
   section" is a precise condition that can fail, and the development exhibits
   both a cover on which it holds and the hypotheses under which it does not.
   Compare "integration" in IIT, which is a number, or "broadcast" in GWT, which
   is a metaphor about a workspace.
3. **It is a scale-bridging commitment, not a correlate claim.** The framework
   names a mechanism that runs from microscopic dissipation to a macroscopic
   order parameter and says what happens at each scale change. Correlate-hunting
   theories are unfalsifiable in the specific way that they can absorb any new
   measurement; this one cannot, because the coarse-graining step and the
   identification step are separable and the second is stated as empirical.
4. **It has one prediction that is its own.** The sleep-inertia timescale
   mismatch — recovery tracking the slow astrocytic/CSF variable through the
   bifurcation, giving a *delayed sigmoid* rather than the exponential a purely
   electrical account predicts. Different functional form, fittable,
   discriminating. Its known weakness is recorded under *Open, ranked* below.
5. **The weak joints are located, not hidden.** The EM identification is marked
   empirical; the step to experience is marked stipulation. A framework that
   says where it would break is doing something most of this literature does not.

**What is good is therefore also what the paper currently underplays.** Point 1
is presently one clause inside a paragraph that is otherwise about withdrawing
a claim, which is exactly the failure rule 8 exists to prevent. P3 is not
cosmetic: the space the changelog occupies is space the field argument needs.

**Venue.** Primary target **PRX Life**; presubmission inquiry rather than a cold
submission. Fallbacks in order: *J. R. Soc. Interface* → *Neuroscience of
Consciousness* → *Entropy*. On hold at the user's instruction, not withdrawn.

---

## Work items — the C/P pass (all closed 2026-08-31)

C1 first, because C2 and C3 are attempts to convert specific edges and C1 is what
makes an edge a thing that exists. P1 before P3, because the gate is what stops
the rewrite from being undone. Otherwise the two parts are independent and
either may be done first.

Record each pass in this file under a dated heading in the style of the archive
(what was built / non-vacuity / what it does *not* establish / manuscript
updates / gates).

---

### C1 — `Chain.lean`: make the chain compose, or make its gaps unremovable

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** One new module, `PhysicsOfConsciousness/Chain.lean`, in which
      every arrow of Figure~1 is either a Lean theorem or a **named hypothesis**,
      and one theorem composes them end to end.

**Why.** This is the paper's largest unbacked claim, and it is in the
load-bearing paragraph. The "What is new here" section says formalization
guarantees "that no link can quietly borrow from another, that a hypothesis
cannot be smuggled in as a definition." **The development does not establish
that.** Verified against the import graph, not the prose:

* `Phase8_SelfConsistency` — the entire `K_c = 2D` bifurcation development, which
  is node n7 — has exactly one importer, `PhysicsOfConsciousness.lean:21`, the
  root aggregator. It is a **leaf**. Nothing consumes it.
* `Phase2_MeshConvergence` (n5) and `Phase3_PredictiveThermodynamics` (n4) are
  imported only by `Examples.lean`. Their witnesses are consumed; their theorems
  are not.
* The one apparent n7 → n9 connection is not one. `Phase6_ReflexiveTopology`
  imports `Phase8_ContinuousField` and uses `critical_coupling D`, which is
  `noncomputable def critical_coupling (D : ℝ) : ℝ := 2 * D`
  (`Phase8_ContinuousField.lean:336`). The Self theorem consumes **the numeral
  `2 * D`**, not the bifurcation theorem. `self_of_supercritical` would prove
  exactly what it proves if `Phase8_SelfConsistency.lean` were deleted.

So the honesty of this development is **per-node, not per-edge**, and the
manuscript claims otherwise. That is a correctness problem in the paper's
central methodological claim, and it is fixable.

**The design.** `Chain.lean` sits above everything and imports every phase. The
import order permits this with no restructuring: `Phase8_SelfConsistency` imports
`Phase8_ContinuousField`; `Phase6_ReflexiveTopology` imports `Phase5_GlobalSection`
and `Phase8_ContinuousField`; nothing imports `Chain`. **Do not rewire existing
modules' imports to achieve composition** — that risks cycles and touches files
that are currently clean. Compose at the top.

The module contains, for each of the ten edges n0→n1 … n9→n10:

* either a theorem whose hypothesis is the previous node's conclusion and whose
  conclusion is the next node's hypothesis;
* or a `Prop`-valued **named hypothesis**, with a docstring saying what would be
  needed to discharge it and why it is not discharged.

Then one theorem — `chain` — takes the named hypotheses as arguments and
produces n9 (the Self). n10 is stipulation and stays outside the theorem;
`Chain.lean` should say so in a docstring rather than encode it.

**Why the named-hypothesis half is the point, not a concession.** A gap recorded
in prose can be softened by a later edit. A gap that is an argument to `chain`
cannot: remove it and the build fails. This converts the paper's claim from
*trust our prose* to *count the arguments*, which is a claim the reader can check
in one command. State the count in the manuscript.

**Expected outcome, to be checked rather than assumed.** Roughly: n0→n1 is not an
edge at all (n0 is vocabulary, and the figure should stop pretending otherwise —
see C5); n7→n9 becomes a theorem (C2); n5→n7 is an attempt (C3); n1→n2, n2→n3,
n3→n4, n4→n5, n6→n7 and n8→n9 stay named hypotheses. If more edges turn out to be
reachable than that, take them; if fewer, record which and why.

**Do not manufacture edges.** An edge whose "theorem" is a definitional unfolding
or a restatement is worse than a named hypothesis, because it looks like content.
The n7→n9 link is currently exactly that failure and C2 is what fixes it.

**Done when.** `Chain.lean` builds clean, `chain` typechecks, the named
hypotheses are counted, and `#print axioms chain` reports only the three.

---

### C2 — Make the n7 → n9 edge consume a theorem instead of a numeral

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** Restate the Self theorem so its hypothesis is *the coherent
      order parameter exists*, not *K exceeds the number 2D*.

**Why.** Recorded in C1: this edge is the manuscript's one claimed cross-link
between Derivation 6 and Derivation 7, and it runs through a definition. Closing
it converts the strongest formalized result in the development (the bifurcation)
from a leaf into a premise of the Self.

**It is reachable, and cheaply — checked, not estimated.**
`critical_coupling_is_threshold_unique` (`Phase8_SelfConsistency.lean:1542`) is a
conjunction whose *first* component is

```
K ≤ critical_coupling D → ∀ r, 0 ≤ r → r = selfConsistency K D r → r = 0
```

Its contrapositive gives what is needed: a **non-zero** non-negative fixed point
forces `critical_coupling D < K`. So from "a coherent order parameter exists"
one derives `K > K_c`, then `resonanceRate_lt_one`
(`Phase6_ReflexiveTopology.lean:511`), then `ReflexiveBoundary.self_unique`. The
edge is genuine: n7's conclusion implies n9's contraction hypothesis.

**What it takes.** In `Chain.lean`, a theorem of roughly the shape

```
theorem self_of_coherent_order_parameter
    (hD : 0 < D) (hK : 0 ≤ K) (hτ : 0 < τ)
    (hr : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r = selfConsistency K D r)
    (rb : ReflexiveBoundary X)
    (h_lip : LipschitzWith (resonanceRate K D τ) rb.predict) :
    ∃! s, rb.predict s = s
```

`self_of_supercritical` (`Phase6_ReflexiveTopology.lean:543`) stays where it is —
it is the correct statement of its own claim and nothing is gained by moving it.
The new theorem is the *edge*, and it belongs in `Chain.lean` because that is
where the composition lives.

**Non-vacuity.** The hypothesis must be discharged by an instance, not only
satisfied in principle: exhibit a supercritical `K, D` for which
`supercritical_fixed_point_existsUnique` supplies `hr`, and check that the
resulting Self is the one §10's witness already builds. If the two do not line
up, that is a finding and it goes in the pass record.

**Done when.** `Phase8_SelfConsistency` has a second importer that consumes a
theorem from it, and the manuscript's Derivation 6 sentence about the connection
to Derivation 7 cites `self_of_coherent_order_parameter` rather than asserting
the link.

---

### C3 — Attempt the n5 → n7 edge: mesh limit ⟹ `ContinuousNeuralField`

- [x] **Done 2026-08-31 — attempted and refused, with the refusal proved.** Pass
      record at the end of this file.

- [x] **Objective.** A constructor `ContinuousNeuralField.ofMeshLimit`, so the
      coarse-graining theorem *produces* the structure the field results are
      stated over.

**Why.** W3's record states it plainly: `ContinuousNeuralField` is "posited as a
structure, not produced by any theorem." That is the gap between n5 (a theorem
about an energy functional) and n7 (theorems about a continuous field). Right now
the manuscript's coarse-graining step and its bifurcation step are about two
objects with no formal relation.

**Risk-flagged, and the flag is the deliverable if the attempt fails.** The
recorded blocker is O14(B), propagation of chaos, which is genuinely a research
programme — verified again: the pinned Mathlib has **zero** files mentioning
`Wasserstein`, `McKean`, `empiricalMeasure`, mean-field or chaos, only the
weak-convergence topology. But O14 was reassessed on 2026-08-31 and found to be
running two statements together, and standing rule 4 applies: the recorded
blocker is a hypothesis. The question this item asks is narrower than O14(B):
**does building the structure require the dynamical limit, or only the kernel?**
`ContinuousNeuralField` (`Phase8_ContinuousField.lean:51`) is a structure over a
measure space; if its fields are kernel-and-energy data rather than trajectory
data, `ofMeshLimit` may be reachable without any limit theorem about the
dynamics.

**Timebox it.** If the structure's fields turn out to demand the dynamical limit,
**stop**, and record the finding as the sharpest available statement of what
O14(B) costs — that is a better outcome than a forced constructor. Do not
weaken `ContinuousNeuralField` to make the constructor go through; standing rule 3.

**Done when.** Either the constructor exists and is witnessed, or the pass record
states exactly which field of `ContinuousNeuralField` cannot be produced from a
mesh limit and why, and C1 records n5→n7 as a named hypothesis citing that
finding.

---

### C4 — Name the remaining edges precisely

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** For each edge C1 leaves as a named hypothesis, a docstring
      that says what the hypothesis asserts *physically*, what would discharge
      it, and whether the obstacle is Mathlib, the modelling, or the physics.

**Why.** A named hypothesis called `h5` is not better than prose. A named
hypothesis whose docstring says "the coarse-grained kernel of the finite system
converges to the kernel the continuum theorems assume; blocked by the dynamical
mean-field limit, for which the pinned Mathlib has nothing" is a research agenda
a reader can act on, and it is the honest content of the framework's incompleteness.

**Distinguish three kinds and label them,** because they are not equally serious:

* **Formalization gap** — true, provable, nobody has done it in Lean.
* **Modelling assumption** — an idealisation the framework adopts knowingly (the
  von Mises density, positive symmetric couplings).
* **Physical commitment** — could be false of cortex (the EM identification).

The manuscript currently blurs the first two. A reader who cannot tell "we did
not prove this" from "we assumed this and it might be wrong" cannot evaluate the
framework, and the second is much the more interesting admission.

**Done when.** Every named hypothesis in `Chain.lean` carries a docstring with
its kind, and the three counts are stated in the manuscript.

---

### C5 — The paper side of the chain: figure, claim, table

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** Make the manuscript say what C1–C4 established, and stop
      saying what they refuted.

**What it takes.**

* **Figure~1's arrows get a status.** Ten `\draw[arr]` edges are currently
  identical black lines between eleven status-coloured boxes — the exact visual
  form of the defect. Solid for a theorem edge, dashed for a named hypothesis,
  with the key extended. The nodes already carry their statuses and need no
  change.
* **n0 is not a chain node.** The figure draws `n0 → n1` as an inference, and the
  box itself says n0 is "consumed by no theorem." An arrow out of a node nothing
  consumes is a contradiction inside one figure. Set n0 aside as a labelled
  setting box with no arrow, or drop it from the figure and keep it in prose.
* **Rewrite the §"What is new here" claim** — the sentence beginning "no link can
  quietly borrow from another." Replace with what is true after C1: the
  development declares no axioms, every physical postulate is a class field its
  models discharge, every class is inhabited, and the chain composes to a single
  theorem with *n* named hypotheses, each labelled by kind. That is a stronger
  claim than the current one because it is checkable, and it is the claim the
  work actually supports.
* **Table~1's last row currently spans n7, n8 and n9 in one cell.** After C2 the
  n7→n9 step is a theorem and deserves its own row rather than a clause.
* **Table~S1's status column** should be generated from `Chain.lean` rather than
  maintained by hand, or if that is too much machinery, checked against it in the
  same pass. A hand-maintained status table is how the n7→n9 claim got into the
  paper in the first place.

**Done when.** No sentence in either document claims a cross-link that
`Chain.lean` does not carry, and Figure~1 distinguishes its two kinds of arrow.

---

### P1 — The gate: `scripts/check_prose.py` and a pre-commit hook

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** Make rule 8 mechanical, so it survives the next agent that
      is tempted to explain itself in the manuscript.

**Why.** This is the same argument the development makes about axioms: a
constraint that lives in prose is negotiable, and one that fails the build is
not. The changelog problem was not introduced by carelessness — every marker was
added in good faith, one honest correction at a time, by passes that were doing
exactly what their items asked. That is why it needs a gate rather than a
cleanup.

**What it takes.** A small Python script, checked by the existing tooling
(`ruff`, `mypy` strict, `bandit`, `vulture`, `xenon` — `AGENTS.md` §2), wired
into `.pre-commit-config.yaml` as a `repo: local` hook. Follow the existing block
exactly: `entry: bash -c '…'`, `pass_filenames: false`. The existing hooks are
all `types: [python]`; this one is not, and must be `files: ^(main|supplementary)\.tex$`.

**Scope: both publication files.** `main.tex` **and** `supplementary.tex`. The
supplement is part of the publication and rule 8 covers it identically.

**The pattern list**, from the inventory in P3 — case-insensitive, and each
should be justified in a comment rather than dumped in a regex:
`earlier draft`, `earlier version`, `an earlier`, `no longer`, `until recently`,
`we had recorded`, `have since been`, `previously`, `formerly`, `the old`,
`withdraw*`, `retract*`, `misdiagnos*`.

**No allowlist.** The original design for this item had a `% CHANGELOG-OK`
escape for the axiom-soundness section. **That was wrong and is dropped.** §2.1's
finding — an axiom constraining a symbol it does not itself bind is inconsistent;
here are three concrete refutations; here is the rule that prevents it — is a
permanent fact about formalization practice and survives being stated
atemporally. It is *stronger* stated that way: a methodological result rather
than a confession. An allowlist with one entry becomes an allowlist with twenty,
and the gate erodes to nothing. If a rewrite genuinely cannot be done without a
marker, that is a finding to record here, not a flag to add.

**Watch the false positives.** "no longer" and "previously" have legitimate
non-autobiographical uses (a sequence that is no longer monotone; a quantity
previously defined in the same document). Expect a handful. Resolve each by
rewording rather than by widening the escape hatch, and record any that resisted.

**Done when.** The hook fails on the current `HEAD` of both files, and passes
after P3.

---

### P2 — `CHANGELOG.md`, so the narration has somewhere to go

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** Create the repo-side destination rule 8 presupposes. There
      is currently **no `CHANGELOG.md`** in this repository.

**Why.** P3 removes 64 statements, some of which are worth keeping — not for the
reader of the paper, but for anyone reading the repository, including future
agents. Deleting them without a destination loses the audit trail that is one of
this project's genuine assets. The archived ledgers hold the full record already;
`CHANGELOG.md` is the *findable* summary of it.

**What it takes.** Root-level `CHANGELOG.md`, in reverse-chronological order,
covering at minimum: the five-axioms-to-zero-axioms transition and the three
inconsistent axioms; the Derivation 3 invalid inference and its replacement by
Still et al.; Derivation 4's demotion from derivation to empirical commitment;
the frustration/positivity contradiction; W5's redesign of the Self theorem; W1's
discharge of the equilibrium hypothesis. Each entry: what was claimed, what is
claimed now, and a pointer to the archived pass record.

Sources are already written — the W1–W8 pass records in
`_archive/todo_2026-08-31_pre-composability-replan.md`. This is transcription and
compression, not new writing.

**The other two destinations need no work.** Lean docstrings already carry the
technical half (`Phase3_KLBound`'s header on why the inference is invalid,
`Phase2_SimplicialBridge.lean:360`), and `tasks/lessons.md` exists. Where a
removed passage is technical, prefer the docstring; `CHANGELOG.md` is for what a
reader of the repository needs.

**Done when.** `CHANGELOG.md` exists and every passage P3 removes is either
recoverable from it, already in a Lean docstring, or judged not worth keeping —
with the third case listed in the pass record so the judgement is reviewable.

---

### P3 — Rewrite the 64 marker sites

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** Both publication files state the current theory only.

**The inventory, counted 2026-08-31** (occurrences, not lines):

| marker | `main.tex` | `supplementary.tex` |
|---|---|---|
| `no longer` | 8 | 7 |
| `earlier draft` | 8 | 5 |
| `until recently` | 4 | 1 |
| `we had recorded` | 3 | 1 |
| `the old` | 3 | 3 |
| `previously` | 3 | 3 |
| `have since been` | 3 | 1 |
| `earlier version` | 2 | 0 |
| `an earlier` | 2 | 0 |
| `withdraw` / `withdrawn` / `withdraws` | 4 | 2 |
| `misdiagnosis` | 1 | 0 |
| **total** | **41** | **23** |

**The rewrite.** Each site becomes a present-tense scope statement, or is
deleted. Worked examples of the two kinds:

* Table~1's caption reads *"Earlier drafts carried five axioms, three of them
  inconsistent."* → delete the sentence. The cross-reference to §2.1 already
  there does the work, and §2.1 after its own rewrite makes the point in the
  general form.
* Derivation 3 currently states the old argument, withdraws its final step and
  says why. → State Still's bound and what follows from it. Then, as a
  *scope* paragraph rather than a retraction: the weaker entropy-production bound
  in §3 of the supplement yields `σ ≥ 0` and no limit may be read off it, because
  `σ` relaxes to a positive NESS value. That is the same mathematical content
  with the autobiography removed, and it is shorter.

**§2.1 is rewritten, not exempted.** It is the section most tempted to narrate
and it is the one that loses least by not doing so. Keep: the refutation, the
three concrete cases, the general rule, the observation that the failure mode
leaves the build green and is not discussed in the applied-formalization
literature. Drop: that these were *our* axioms in *our* earlier drafts. The
finding does not depend on whose axioms they were.

**Order the work by section, not by marker,** and expect the section to get
shorter and better each time. The space recovered goes to the field argument —
see *What is actually good about the framework*, point 1, which is currently one
clause inside a withdrawal paragraph and should be a paragraph of its own.

**Done when.** P1's hook passes on both files, page counts and overfull-hbox
counts are recorded against `HEAD`, and no passage was deleted without P2's
destination check.

---

### P4 — Write the rule down where agents will read it

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** `AGENTS.md` gains rule 8 as a numbered section.

**Why.** `AGENTS.md` has four sections and is the file every agent reads first.
Rule 8 is exactly as binding as §4's anti-hallucination gate for references and
belongs beside it. The gate (P1) catches violations; the rule explains them, and
an agent that understands the rule writes the right sentence the first time.

**What it takes.** A short §5 — *The publication is not a changelog* — stating
the rule, the test ("does this sentence still make sense to a reader who has
never seen a previous draft?"), the three repo destinations, and a pointer to
`scripts/check_prose.py`. Say explicitly that the supplement is covered.

**Done when.** `AGENTS.md` §5 exists and P1's hook message points at it.

---

## Work items — the next pass, ranked 2026-08-31 (after C1–C5, P1–P4)

Written at the end of the C/P session. Two of these convert the objections the
previous ledger recorded-but-did-not-schedule into work with an actual
deliverable; the rest are what the session itself generated.

Take ONE at a time. **S1 and F1 first**: both are manuscript-only, both are
already true, and both strengthen the paper's weakest public claims at zero
formal cost. S2 is the one with real payoff and real cost.

**S1 and F1 are closed (2026-08-31). F2 is next** — it is the item that tries to
close the gap F1 has now located exactly, and F1's pass record narrowed what F2
has to attack.

---

### S1 — The sleep-inertia prediction, restated as a parameter-free collapse

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** Replace "recovery is a delayed sigmoid" with a claim that a
      one-timescale account and a generic saturating gate cannot both make.

**Why the current claim is weak.** Any two-timescale model with a slow gate
produces a delayed sigmoid, so the prediction discriminates against a purely
electrical account and against nothing else. That is the objection, and it is
correct.

**What the mathematics already gives, unused.** The framework does not merely
predict a *shape*; it predicts a *relation between two separately measurable
quantities*, with no free parameters.

* `circularOrderParameter_vonMises` (`Phase8_SelfConsistency`, §8): the order
  parameter of the von Mises density at concentration `a` is exactly the Bessel
  ratio `R(a) = I₁(a)/I₀(a)`.
* `fixedPoint_iff_selfReproducing`: `r` solves the self-consistency equation iff
  the density it induces has order parameter `r`.

So at every instant of the recovery, the phase distribution's **concentration**
`a(t)` and its **order parameter** `r(t)` are not independent: `r = R(a)`. Both
are measured from the same data. Three consequences, in increasing sharpness:

1. **Shape.** The instantaneous phase density is von Mises. Testable directly.
2. **Collapse.** Plotting `r(t)` against `a(t)` for the whole recovery must fall
   on the single curve `r = I₁(a)/I₀(a)` — the *same* curve across subjects and
   sessions, whatever each one's `K(t)` does. No fitted parameters at all.
3. **Threshold.** Since `a = Kr/D`, the measured ratio `a(t)/r(t)` **is** `K(t)/D`,
   and the framework says coherence departs from zero exactly as it crosses
   **2**. The threshold is read off the data rather than fitted.

**Be exact about what this tests.** It tests the von Mises stationary density
(a declared modelling input, O13) together with the mean-field closure. It does
*not* test the value `2D` independently of that ansatz. Say so; it is still a
falsifiable, parameter-free prediction, and it is a much better one than a
functional form.

**Done when.** The prediction section states the collapse and the `a/r = 2`
crossing, names the two theorems, and scopes what the test is a test *of*. No
Lean. — **Done.** It also states the estimator independence the collapse needs,
which the item did not anticipate; see the pass record.

---

### F1 — Frustration: promote the division from a docstring to a claim

- [x] **Done 2026-08-31.** Pass record at the end of this file.

- [x] **Objective.** Narrow the unfrustrated objection from "the framework
      describes the wrong system" to "the framework's *final step* describes the
      wrong system", which is a much better position and is true.

**Verified, not estimated** (2026-08-31, standing rule 4):

* `dV_dt_le_zero` (`Phase3_CombinatorialThermodynamics:152`) carries **no**
  positivity hypothesis. Neither do `is_kuramoto_trajectory_exists` /
  `_unique`, `dynamic_potential_antitone`, `dynamic_potential_tendsto` or
  `velocity_sq_tendsto_zero`.
* `phase_locked_minimizes_potential`, `potential_min_implies_phase_locked`,
  `potential_min_iff_phase_locked`, `ThermodynamicCover.A_pos` and
  `kuramoto_tendsto_global_minimum` all do — the last needing the strictly
  stronger uniform bound `0 < a ≤ A i j`, since `a` enters the Łojasiewicz
  constant.

So **the entire dissipative half of the chain is frustration-agnostic**, and
exactly one step is not: the identification of the limit. `Phase4_KuramotoDynamics`
already says this in a docstring at line 250. The manuscript does not.

**What it takes.** A paragraph in Derivation 5 stating the division, with the two
lists. Optionally a named Lean result restating `dV_dt_le_zero` for a signed `A`,
so the frustration-agnostic half is citable rather than merely observable.

**Done when.** The manuscript states which half of the chain survives frustration
and which does not, by name. This is a *scoping* item; F2 is the one that tries
to close the gap. — **Done**, but the item's premise was half stale: the
manuscript already carried a subsection stating the division. What it did not
carry was the *locus*. See the pass record.

---

### F2 — Where content could live: gluing that is obstructed rather than unique

- [x] **Done 2026-08-31.** The natural repair was formalized and gives a negative
      answer for oscillator phases. Pass record at the end of this file.

- [x] **Objective.** Test whether frustration can be admitted by weakening the
      overlap condition, and find out what the obstruction is if it cannot.

**The objection, in its sharpest form.** With `A > 0` the minimisers of the
coupling potential are the phase-locked configurations — a single orbit under
global phase rotation. One minimum, one global section, one Self. There is a
unity, and there is nothing for it to be a unity *of*.

**Why the obvious repair does not obviously work.** Frustration gives many local
minima, but they are *not* phase-locked — twisted and splay states are the point.
`LocalSectionSynchronization.section_agrees_of_phase_eq` fires on patches at
*equal* phases, so under frustration it has nothing to fire on, and Derivation 5's
gluing has no compatible family to glue.

**The move worth testing.** Weaken agreement-on-overlaps to **agreement up to a
phase**. A family that agrees up to a phase on each overlap is a cocycle, not a
compatible family; it glues iff the cocycle is a coboundary, and the obstruction
is a class in `H¹` of the cover. Content would then be carried by *which class*,
not by which minimum — and a unity that can be about something is a unity with a
non-trivial obstruction rather than a unique section.

This would also be the first place in the development where the sheaf machinery
does something a partition of unity could not, which is worth having on its own.

**Timebox it, and the failure is the deliverable.** If no overlap condition of
this shape can be satisfied by a frustrated cover, that is a theorem, and it says
**unity and content are in genuine tension in this framework** — a far more
interesting finding than the memory-capacity scoping W3 settled for. Record it
either way; do not weaken `ThermodynamicCover` to make something go through
(standing rule 3).

**Done when.** Either a frustrated cover with an `H¹` obstruction exists and is
witnessed, or the pass record states exactly which condition cannot be met and
why, and the manuscript says which.

---

### F3 — Give the obstruction physical data, or stop at the no-go

- [x] **Done 2026-09-01.** Cortical phase singularities provide measured winding
      data, but require an integer local-lift obstruction rather than F2's
      circle-valued patch offsets. Pass record at the end of this file.

- [x] **Objective.** Decide whether the theory has a biologically meaningful
      source of overlap transition functions that are not differences of the
      Kuramoto patch phases.

F2 proves that ordinary locked, twisted and splay phase fields all give
`offset i j = φ i - φ j`, hence a coboundary and no content label. A non-trivial
Čech class would require a circle-valued torsor/bundle or comparable
gauge/transition model on the cover, a proper nerve-indexed complex, and suitable
nerve topology. Do not build
that structure merely because Lean can: first name the measured or dynamical
quantity its transition functions represent and explain how cortex generates
them. If no such quantity is part of the framework, the F2 no-go is the final
result and the memory/content claim stays outside the chain.

---

### F4 — Formalize the measured phase-lift loop obstruction

- [x] **Done 2026-09-01.** The discrete measured-loop obstruction and a winding-one
      witness are formalized; content remains an empirical question outside the
      chain. Pass record at the end of this file.

- [x] **Objective.** Replace the candidate topology with the discrete object the
      measurements directly support: integer transitions between local
      real-valued lifts on an electrode loop, and winding around an amplitude-zero
      singularity.

F3 found a physical referent but not a content theorem. The formal target is the
implication from non-zero winding to failure of a global real lift, not a
non-zero class manufactured as free data. Do not add F4 to `chain`.

### F5 — Put the loop on a cortical cover and test content

- [x] **Done 2026-09-01.** The punctured cortical domain, analytic-phase
      measurement map and controlled content-decoding protocol are specified.
      Pass record at the end of this file.

- [x] **Objective.** Fix the cover domain (the cortex with the singularity set
      removed) and its measurement map before building a full nerve-indexed
      integer complex; then test whether winding number, singularity location or
      rotation direction predicts discriminable content after controlling for
      task and arousal.

F4 proves the finite-loop obstruction and deliberately does not manufacture the
ambient cover. Until both the cover and the content-sensitive test are specified,
do not identify a topological sector with phenomenal content and do not add this
branch to `chain`.

---

### S2 — The critical exponent: a square-root foot on the recovery curve

- [x] **Done 2026-09-01.** `E`'s second-order expansion and the mean-field
      exponent `β = 1/2` are theorems in `Phase8_CriticalExponent.lean`, the
      exponent theorem is witnessed on the coherent branch rather than left as
      an eventually-clause, and the prediction section states the square-root
      foot with the non-zero crossing speed it needs. Pass record at the end of
      this file.

- [x] **Objective.** A signature of the sleep-inertia recovery that needs the
      *bifurcation* and not merely a saturating nonlinearity.

**The claim.** Near threshold the coherent branch behaves as
`r ∝ (K − K_c)^{1/2}` — the mean-field pitchfork exponent `β = 1/2`. If `K(t)`
crosses `K_c` approximately linearly in time, then just after onset
`r(t) ∝ (t − t₀)^{1/2}`: the recovery curve has a **square-root cusp at its foot,
with infinite initial slope**. An exponential has finite initial slope. A logistic
has finite initial slope. *Any* delayed sigmoid from a generic saturating gate has
finite initial slope. This is the discriminator the objection asks for.

**What it takes, checked rather than estimated.** One missing ingredient, and the
file already names it. `Phase8_SelfConsistency.lean:115` records
`E(a) = 1/2 − a²/16 + O(a⁴)` as **not formalized**, and notes nothing in the file
needs it. It is what this item needs. Given it, the derivation is three lines of
algebra on results that exist: `coherent_iff_sRatio_eq` gives `D/K = E(a)` for a
non-zero solution; substituting the expansion gives `a² = 8(K − K_c)/K`; and
`r = aD/K` carries it to `r`.

Formalizing the expansion is a Taylor computation on two interval integrals —
expand `exp(a cos θ)` and integrate term by term over `[-π, π]`, where the moments
of `cos` are standard. Uniform convergence on a compact interval is what justifies
the interchange. **Grep the pinned Mathlib before believing any of this is hard**;
the previous six recorded blockers were wrong about the obstacle, not merely
pessimistic.

**Flag the modelling assumption in the manuscript, not around it.** The
square-root foot needs `K(t)` to cross the threshold with non-zero speed. That is
an assumption about the slow variable, it is weaker than the assumptions the
current prediction already makes, and it must be stated.

**Done when.** `E`'s second-order expansion is a theorem, the exponent `1/2` is a
theorem, and the prediction section states the square-root foot with its
assumption.

**Scope change (2026-09-01).** The formalization-gap scoping plan
(`tasks/2026-09-01_formalization-gaps-scoping.md`) recommended adding a SymPy
expansion check to S2's scope as a cross-check of the algebra.  Decided against:
the Lean proof (`field_simp`/`ring`/`nlinarith`/`positivity`) already certifies
the algebra below the error threshold a SymPy check would catch; an independent
cross-check on a *less* rigorous system would add confidence for readers who
distrust Lean, but the cost of maintaining a second verification path for a
result the formalization already owns outweighs it.  The 1-hour budget goes to
the Fokker-Planck SymPy notebook instead, which checks algebra the
formalization never touches (the stationary density derivation).

---

### S3 — No hysteresis, which is already a theorem

- [x] **Done 2026-09-01.** No-hysteresis paragraph in the `main.tex`
      prediction section. Pass record below.

- [x] **Objective.** Bank the discriminator the development has and does not use.

`supercritical_solution_set` proves the non-negative solutions of the
self-consistency equation are exactly `{0}` below threshold and `{0, r}` above it.
There is never a range of `K` carrying two distinct *positive* solutions, so the
branch has no fold and the transition is continuous rather than first-order. The
prediction: **no hysteresis loop** between the descent into sleep and the recovery
from it — the same `r(K)` curve is traversed in both directions.

That rules out a real class of rivals, including ignition-style accounts with a
first-order transition, and it costs no new Lean.

**The caveat is load-bearing and goes in the same sentence.** Hysteresis is about
coexisting *stable* branches, and the development proves nothing about stability
— `0` remains a solution above threshold. This is a statement about the solution
set, not about dynamical selection. State it that way or not at all.

**Done when.** The prediction section carries it with its caveat.

---

### T1 — The chain is not a chain: decide the shape

- [x] **Done 2026-09-01.** Figure~1 redrawn as a DAG: n1 and n2 are two
      independent roots into n3, the n1 → n2 arrow removed, and the caption
      states the two-root structure. Pass record below.

- [x] **Objective.** `E12` is logically equivalent to its own conclusion. Figure 1
      currently marks the arrow dashed and explains in the caption. That is
      honest, and it defers the structural question.

Either exhibit a genuine n1 → n2 edge — none is apparent, since the capacity bound
mentions no vacuum manifold and the `π₀` obstruction mentions no entropy — or
redraw the figure as the DAG it is: n1 → n3 directly, n2 → n3 separately, two
roots rather than one line. The second is probably right and changes the paper's
opening picture, which is why it is an item rather than an edit.

---

### T2 — Rank the eight hypotheses by cost, and take the two cheapest

- [x] **Done 2026-09-03, and not in the direction the item asked.** The two
      cheapest hypotheses were cheap because they were *weak*: `E34` and `E78`
      both concluded `Nonempty (SomeStructure)` and both were already provable
      by ignoring their premises. Lowering the count by proving them would have
      made the development weaker. They are strengthened instead, and the count
      stays eight. Pass record below.

- [x] **Objective.** Drop the count. It is the paper's checkable number, so
      lowering it is a checkable improvement.

Two candidates, both bounded:

* **`E78`, first half.** `ThermodynamicCover.ofConvergentTrajectory` already
  builds the equilibrium field from a convergent trajectory. What is missing is
  the passage from a coherent order parameter to initial data in that basin.
* **`E34`.** Landauer's heat and Still's dissipated work are two accounts of one
  physical quantity that no theorem here identifies: `heat_dissipation` is
  `T · Δ boltzmann_entropy` of the bath, `dissipatedWork` is `W − ΔF` over one
  drive step. Building a bipartite environment whose Landauer heat *is* a
  predictive structure's dissipated work is a formalization task, not a research
  problem.

---

### T3 — Generate Table S1's status column from `Chain.lean`

- [x] **Done 2026-09-01.** `simulations/check_tableS1.py` validates the
      status column against `Chain.lean`, wired into
      `.pre-commit-config.yaml` as `check-table`. Pass record below.

- [x] **Objective.** C5 checked it by hand and recorded why. Record the cost of
      generating it so the decision stays reviewable.

**Why it matters more than it looks.** Table S1 is a table with a row per *node*.
It has nowhere to record a claim about an *edge*, which is exactly how the false
n7 → n9 claim survived a hand check for as long as it did.

---

### T4 — A leaf detector, so the C1 audit is a script and not a memory

- [x] **Objective.** *(Delivered 2026-09-02; the gate was red on the tree that
      added it and is green as of 2026-09-03. See the T4 and V1 records below.)* C1's defect was found by reading the import graph. Nothing
      stops it recurring.

A module can be imported and have none of its *theorems* consumed —
`Phase8_SelfConsistency` was in exactly that state, and after C2 exactly one of
its theorems is consumed. A script that reports, per module, how many of its
public results are named anywhere outside itself and its own witnesses would have
found C1's defect mechanically. Same argument as P1: a constraint that lives in
prose is negotiable.

Cheap approximation: extract declaration names per module, grep the rest of the
tree for each. Wire it in beside `check-prose`.

---

### T5 — A mechanistic witness beyond `chain_hypotheses_jointly_satisfiable`

- [x] **Done 2026-09-03.** `E12` now uses the proved double-well kink, `E23`
      uses the non-surjective refreshed one-bit register, and `E45` uses the
      genuinely moving uniform-grid energy sequence translated to converge to
      the joint witness's coupling strength 3. The existing `E34` and `E78`
      witnesses remain. Pass record at the end of this file.

- [x] **Objective.** *(Partly overtaken 2026-09-03: `E34` and `E78` are now
      discharged in the joint witness by `landauerSystem` — a predictive
      structure whose dissipated work is `§1`'s Landauer heat — and by
      `trioCover3` — a cover reached by relaxation at coupling 3. What remains
      of this item is `E12`, `E23` and `E45`.)* At the time this item was opened,
      the joint witness took the
      vacuum manifold empty, the register a bit, and the coarse-graining
      sequence constant. It proves the eight hypotheses are not jointly
      contradictory, which is what it was for, and it proves nothing more.

A witness in which `E12`, `E23` and `E45` are satisfied non-trivially — a real
double well, a real absorbing register, a real refining mesh — would say
considerably more. Rank below everything above; the current witness is honest
about being mathematical.

---

## Audit findings — added 2026-08-31, ranked by effect on the paper

These items come from a read-only audit of the Lean-to-manuscript claim surface.
They outrank S2–S3 and T2–T5 because they concern what the headline composition
actually proves. Take them one at a time in this order.

### A1 — Preserve the glued state across Unity → Self

- [x] **Done 2026-08-31.** `chain` now concludes `UnifiedSelf`; pass record at
      the end of this file.

- [x] **Objective.** Replace the current n8 → n9 passage, which uses `Unity X`
      only to synthesize `Nonempty (GlobalSection X)`, with a statement about the
      particular section produced by the cover.

`chain` currently forgets the unique section compatible with the local family
and lets Banach produce an unrelated fixed point. The target edge must name the
glued section and require or derive `rb.predict s = s`; otherwise Lean proves
coexistence of a unity and a Self, not that the unified state becomes reflexive.
Do not close this by merely adding equality as an opaque hypothesis without
changing the node shape and the manuscript claim.

### A2 — Reclassify `chain` as conditional composition

- [x] **Done 2026-08-31.** Reader-facing descriptions now consistently call
      `chain` a conditional composition schema with eight assumed arrows. Pass
      record at the end of this file.

- [x] **Objective.** Make the figure, theorem description and Table S1 say that
      `chain` is a composition schema with eight assumed arrows, not a derivation
      of the physical narrative from finite capacity.

Four arrows supply whole structures, `E12` is equivalent to its conclusion, and
`E45` relates objects for which the development defines no common dynamics. The
machine-checked gain is exact dependency accounting. Preserve that gain without
using “the chain composes” as shorthand for physical derivation.

### A3 — Separate satisfiability from mechanistic non-vacuity

- [x] **Done 2026-08-31.** The witness is now named
      `chain_hypotheses_jointly_satisfiable`; publication claims use only its
      satisfiability scope. Pass record at the end of this file.

- [x] **Objective.** Rename or rescope `chain_nonvacuous` and its manuscript use.

The empty vacuum, constant coarse-graining sequence and directly supplied
predictive/cover structures prove joint satisfiability only. T5 may later build a
mechanistic toy witness, but until then the present theorem must not be evidence
that the cross-domain implications are realized by one mechanism.

### A4 — Remove “guaranteed by phase-locking” from Theorem 5

- [x] **Done 2026-09-01.** Theorem 5, Figure 1 and the main derivation now state
      overlap compatibility as an independent physical hypothesis. Pass record
      at the end of this file.

- [x] **Objective.** Restate the displayed theorem so overlap compatibility is an
      independent physical hypothesis.

`LocalSectionSynchronization.section_agrees_of_phase_eq` is a class field and no
dynamics derives it. The implementation notes disclose this, but the headline
supplementary theorem currently says phase-locking guarantees agreement.

### A5 — Align scale-bridging language with the scalar no-go

- [x] **Done 2026-09-01.** The manuscripts now separate scalar energy
      convergence, the posited continuum kernel and its empirical EM
      identification. Pass record at the end of this file.

- [x] **Objective.** Remove every remaining claim that
      `mesh_refinement_convergence` produces a continuum coupling kernel.

It converges one scalar energy. `edge_region` has no `M × M` product structure,
and the vertex-supported candidate is invisible to the continuum functional on
an atomless substrate. Treat a genuine kernel limit as new architecture, not as
the remaining propagation-of-chaos lemma.

### A6 — Mark the Self contraction as an independent modelling postulate

- [x] **Done 2026-09-01.** Figure 1, Table 1, Theorem 6 and Table S1 now name the
      Lipschitz law as an independent modelling postulate. Pass record at the
      end of this file.

- [x] **Objective.** Change the Reflexive Topology status from “Theorem
      (witnessed)” to a conditional status that names the Lipschitz assumption.

Coherence recovers only `K > 2D`; `E89` separately assumes that `rb.predict` has
the Kuramoto linear relaxation rate. The witness was designed to realize that
constant and does not derive self-model dynamics from oscillator dynamics.

---

## Open, ranked — carried forward, none blocking

Carried from the O10/O16 record. Nothing here is scheduled ahead of C1–C5 and
P1–P4.

1. **(A) The static order-parameter link.** — **[Done 2026-09-02, claim corrected 2026-09-03]** `incoherent_orderParameters_agree` in `Examples.lean` (`lake build` clean) proves the two order parameters agree *at one configuration*: two sites in antiphase give `order_parameter_complex = 0`, which is `circularOrderParameter (vonMisesDensity 0)`. That is what it is worth — the quantities are the same kind of object and are normalised alike — and it is not a general static identity, so it does not by itself reduce the remaining distance to propagation of chaos. `main.tex` says exactly this; the first write-up said the mean-field limit was thereby the *only* remaining gap, which the theorem does not support.
2. **`section_agrees_of_phase_eq`** — the `LocalSectionSynchronization` hypothesis
   that synchronised patches agree where they overlap. **Read and fenced
   2026-09-03; still a hypothesis, and it will stay one.** `Examples.lean` §20
   proves the categorical condition equivalent to the pointwise one — the two
   patches assign the same mass to every site they share
   (`restrict_eq_iff_densityOn_eqOn`) — and exhibits data the rest of the
   structure admits and this hypothesis rejects: one phase, two profiles
   differing at the shared site (`overlap_agreement_fails`). What is *not*
   available is a derivation, and the reason is structural rather than
   difficulty: the abstract form of "the local law is a function of the phase"
   is the class field itself, so there is nothing above it to derive it from.
   See the W6 record for why it is *not* "the move W1 made".
3. **The PRX Life presubmission inquiry** — **[Closed as decided-not-doing, 2026-09-02]** Per the author's instruction: not sending a presubmission inquiry. Direct submission at a later date, or not.

**The sleep-inertia prediction is weaker than the manuscript implies.** This is
now items **S1, S2 and S3** above; the diagnosis below is kept because it is why
they exist. Any two-timescale model with
a slow gate produces a delayed sigmoid, and the paper concedes it uses only the
*existence and continuity* of the coherent branch, not `K_c = 2D`. So the
prediction discriminates against a one-timescale electrical account and against
nothing else. Either sharpen it — find a quantitative signature that needs the
bifurcation rather than merely a saturating nonlinearity — or scope the claim in
the discussion to what it is. Do not schedule this ahead of C1–C5 and P1–P4; do
not let the discussion keep overselling it either.

**The unfrustrated-uniqueness objection.** Now items **F1 and F2** above; the
diagnosis below is why they exist, and F1's verified split is the part of it that
turned out to be better news than this paragraph assumed.
Every "where does it land" theorem carries `h_pos : ∀ i j, sys.A i j > 0`
(`Phase4_KuramotoDynamics.lean:274`), an unfrustrated ferromagnet whose potential
has one minimum up to global phase. In that regime the global section and the
Self are unique — so there is a unity, but nothing for it to be a unity *of*, and
no capacity for the framework to carry content. W3 confronted this as a memory
question and scoped it honestly; the sharper form is that it is a question about
whether the coherent state can be *about* anything. It is the deepest objection
a referee will raise. The honest position is that the framework's theorems
describe the unfrustrated regime and its account of content requires the
frustrated one. Say that; do not pretend the gap is only about memory capacity.

---

## Low value — both done

Closed 2026-08-31; pass record in the archive. Neither changed a claim of the
paper, only the scope of two it already made.

- **O10 (remainder). Done.** `Phase8_ContinuousField.lean` §9. The item was wrong
  about what it reached: given the operator, `hasFDerivAt_quadratic_of_affine`
  gives the derivative as a functional, but `is_coupling_gradient_flow` wants a
  gradient *vector*, so the adjoint was needed too.
- **O16. Done.** `Examples.lean` §6.1. The recorded obstacle
  (`taylor_mean_remainder_lagrange` per cell) was obsolete: Mathlib carries the
  *composite* trapezoidal bound. What was missing was the identification of
  `discreteEnergy` with `trapezoidal_integral`.

---

## Closed as decided-not-doing — do not re-rank without recording a reason

Carried unchanged. Full reasoning in the archives.

- **O12 — Noether.** `SymmetryInvariantAction` has no dynamics, so no conserved
  quantity can attach to it. The obstacle is structural, not difficulty. See W6.
- **O13 — deriving the von Mises stationary density from the SDE.** Needs the
  Fokker–Planck operator, existence and uniqueness of stationary solutions, and
  spectral stability; confirmed absent from Mathlib by grep. Keep the density as
  a **declared modelling input** and cite the mean-field literature. This is a
  standard ansatz, not a hidden gap — and after C4 it is labelled a *modelling
  assumption*, which is the right label.
- **O14(B) — the dynamical mean-field limit.** Propagation of chaos for the
  finite Kuramoto system: a research programme, not a task. Re-verified
  2026-08-31 — the pinned Mathlib has **zero** files mentioning `Wasserstein`,
  `McKean`, `empiricalMeasure`, mean-field or chaos; only the weak-convergence
  topology (`LevyProkhorovMetric`, `Portmanteau`, `Prokhorov`, `Tight`), so weak
  convergence can be *stated* and none of the estimates exist. **O14(A) is
  separate and is ranked above.** C3 tested whether the *structure* needs (B) or
  only the kernel and found the question is prior to both: the coarse-graining
  theorem produces a **scalar**, not a kernel, and the natural vertex-sited
  repair is provably invisible to the continuum functional
  (`vertexKernel_fieldCorrelation_eq_zero`). (B) is untouched by that and stays
  closed; what it is *not* is the first obstacle on this edge.
- **O15 — `lim D_KL = 0`.** Superseded and closed by W4, which replaced the
  inference rather than weakening the sentence.
- **O17 — the step from the hardware results to "von Neumann architectures cannot
  be conscious."** Informal, and `main.tex` says so. The measure-theoretic half
  (`fieldCorrelation_sited_eq_zero`) says a finitely-sited kernel is invisible to
  a functional that ignores null sets — a fact about the functional, not about
  the architecture, and real silicon is not a measure-zero set. Do not let the
  Corollary or Conclusion lean on it.
- **O18 — global section ↔ unity of experience.** The framework's core
  stipulation, fenced by the Russellian-monism framing. **Kept deliberately.** Not
  a defect; recorded so it is not mistaken for one.
- **Splitting the paper.** Decided 2026-08-31 at the user's instruction: not now.
  The two candidate papers stay recorded below.

---

## Beyond this paper — recorded, not scheduled

Two papers exist in this repository that are not the framework paper, and neither
is blocked by anything above. Recorded so the decision to defer them is
deliberate rather than forgotten.

1. **A formalization paper.** The Kuramoto development on its own —
   well-posedness, Barbălat (absent from Mathlib), dissipation, the `K_c = 2D`
   bifurcation, the Bessel ratio monotonicity by the fold-then-cross route, which
   may be a new proof of a known result. Consciousness in one motivating sentence
   or none. Target **ITP** / **CPP**, or **JAR** for the full library. Nearly
   free: the Lean is done. Separately, upstreaming Barbălat's lemma and the Bessel
   ratio monotonicity into Mathlib is a weekend and a permanent citable
   contribution.
2. **The audit paper.** Three axioms each proving `False` from one shared root
   cause; a conjecture false via `diam ∅ = 0`; two potentials never chained, one
   provably unbounded below; a threshold predicate sensitive to substrate mass; a
   witness emptied by the 0/1 metric; the Lévy–Prokhorov negative result. Six
   errors that survived prose review. The finding is independent of whether the
   framework is right, which is what makes it robust. Target **BBS** (high
   variance, and the commentary format suits it), or *Neuroscience of
   Consciousness*, or a philosophy-of-science venue. **Note:** P3 removes this
   material from `main.tex`, and P2 moves it to `CHANGELOG.md` — which makes it
   *more* available to this paper, not less, since it is then in one place rather
   than scattered across 64 sites in a manuscript.

---

## Pass record

### C1 — `Chain.lean` — 2026-08-31

**What was built.** `PhysicsOfConsciousness/Chain.lean`, 546 lines, one new
module sitting above every phase and imported only by the root aggregator. No
existing module's imports were touched, so no phase file acquired a dependency
and no cycle was possible.

It contains, in order: nine node predicates (`Capacity`, `LeavesVacuum`,
`Dissipates`, `PredictiveBound`, `CoarseGrains`, `FieldRealizes`, `Coherent`,
`Unity`, `Self`); eight node theorems saying each node is reached once its own
link's hypotheses are in hand; nine `Prop`-valued named hypotheses `E12 … E89`,
one per unproved arrow; and `chain`, which takes the nine as explicit arguments
and concludes `Self rb`.

**The count, which is the deliverable.** `#check @chain` shows nine arguments of
type `E..`, each an implication between two node predicates. Labelled by kind
(C4's classification, done in the same pass because the docstrings had to say
something):

| edge | kind | why |
|---|---|---|
| `E12` n1→n2 | formalization gap | see the finding below — it is not an inference at all |
| `E23` n2→n3 | formalization gap | the defect locus is not related to a state space anywhere |
| `E34` n3→n4 | formalization gap | Landauer heat and Still's `W_diss` are never identified |
| `E45` n4→n5 | modelling assumption | selection against nonpredictive memory constrains the coupling matrix; no formal relation exists between the two objects |
| `E56` n5→n6 | physical commitment | the load-bearing joint; could simply be false |
| `E67` n6→n7 | physical commitment | cortex operates above `K_c`; a measurement, not a proof |
| `E78` n7→n8 | formalization gap | half reachable via `ofConvergentTrajectory`; the other half is `section_agrees_of_phase_eq` |
| `E89` n8→n9 | modelling assumption | the nonlinear self-model contracts at the linearised rate |
| `E79` n7→n9 | expected dischargeable | C2 |

Four formalization gaps, two modelling assumptions, two physical commitments, one
expected to become a theorem.

**Three findings, none of them the one the item predicted.**

1. **n1 → n2 is not an edge, and n0 is not the only non-node.** `Capacity sys` is
   a theorem with *no hypotheses*, so `E12 : Capacity sys → LeavesVacuum vac phi`
   is logically equivalent to its own conclusion. Assuming it is assuming n2
   outright. The capacity bound mentions no vacuum manifold and the `π₀`
   obstruction mentions no entropy: **n1 and n2 are two independent starting
   points of the document, not two links of one chain.** The item expected n0→n1
   to be the figure's only fake arrow; n1→n2 is a second one, and it is worse,
   because n0 at least announces itself as vocabulary.
2. **The edge n1 actually has is n1 → n3, and the figure does not draw it.**
   Finiteness is what turns "some state is unreachable" into "the update is
   many-to-one" (`is_erasure_of_not_surjective`), and Landauer does the rest.
   `dissipation_of_unreachable` records it. It skips n2 entirely.
3. **The empirical commitment enters the formal chain as an identification of two
   real numbers.** `FieldRealizes L K D` is `0 < D ∧ 0 ≤ K ∧ L = K`: the
   continuum limit of the discrete coupling energy *is* the mean-field coupling
   constant. Nothing stronger is statable, because no formal object in this
   development denotes cortex. Everything else the manuscript says about n6 —
   electromagnetic, endogenous, the field EEG measures — is carried by prose and
   by no theorem. That is not a defect to fix; it is the exact size of the joint,
   and the manuscript should say it.

**A design decision worth recording.** Four of the nine edges deliver a
*structure* rather than a proposition (`E34` and `E78` conclude
`Nonempty (PredictiveDissipation …)` and `Nonempty (ThermodynamicCover X)`).
This is deliberate. `PredictiveDissipation.nonpredictive_le_dissipation` and
`global_section_from_thermodynamics` are theorems *of* their classes, so an edge
whose conclusion was the bare inequality or the bare gluing statement would be
provable by ignoring its hypothesis — a manufactured edge of exactly the kind the
item warned against. What n4 and n8 assert is that the substrate *carries* the
structure, and that is what the hypotheses now say.

**Non-vacuity.** Partial, and the shortfall is recorded rather than papered over.
The four numerically-contentful edges (`E56`, `E67`, `E79`, and `CoarseGrains`
itself) are exhibited satisfied at `D = 1`, `K = 3`, where `K_c = 2`. The other
five relate structures rather than numbers, and a witness for them is a witness
for the whole chain — a substrate carrying a `ThermodynamicCover`, a
`ReflexiveBoundary` and a `PredictiveDissipation` at once. That is buildable
(`Examples.lean` §10 and §17.1 have two of the three, and `constResonance` makes
the Lipschitz hypothesis free) and it is **not built**. It is the next
non-vacuity task; see *Open, ranked*.

**What this does not establish.**

* Not that nine is the right number. It is the number this factorisation
  produces; a different set of node predicates gives a different one. What is not
  negotiable is that the gaps are arguments rather than sentences.
* Not that the chain is sound end to end for cortex. Every one of the nine is
  undischarged.
* Not n10. The stipulation is outside `chain` deliberately, and the module
  docstring says why: encoding it would make it look like the same kind of object
  as the rest.

**Gates.** `lake build` clean, 17,616 jobs (was 17,614). Zero `sorry`, zero
warnings, zero declared axioms. `#print axioms chain` reports exactly
`[propext, Classical.choice, Quot.sound]`. Lean now 14,485 lines across 21
modules. `Phase8_SelfConsistency` has a second importer for the first time
(`Chain.lean`, consuming `supercritical_fixed_point_existsUnique`) — the first
half of C2's *done when*, reached as a side effect; C2's substance is unaffected
and the item stays open.

**Manuscript.** Untouched in this pass. C5 is where the figure, the "what is new
here" claim and Table~1 are brought into line, and it now has three findings to
carry rather than one.

### C2 — the n7 → n9 edge — 2026-08-31

**What was built.** Three theorems in `Chain.lean` and one manuscript paragraph.

* `supercritical_of_coherent` — a coherent order parameter forces
  `critical_coupling D < K`. Contrapositive of
  `fixed_point_eq_zero_of_le_critical`: at or below threshold the only
  non-negative solution of `r = R(K, r)` is `r = 0`, so a strictly positive one
  puts `K` above threshold. Four lines. The item's estimate was right and, for
  once, right about the obstacle as well.
* `self_of_coherent_order_parameter` — Derivation 6 with its threshold hypothesis
  replaced by Derivation 7's conclusion. `self_of_supercritical` stays where it
  is, unchanged.
* `chain` now routes its last step through this theorem, so **`E79` is gone** and
  the named-hypothesis count is **eight**, not nine. The sign conditions
  `supercritical_of_coherent` needs (`0 < D`, `0 ≤ K`) are already carried by n6,
  which is where they belong.

**Non-vacuity — and it went further than the item asked.** The item asked for a
supercritical `K, D` discharging the hypothesis and a check that the resulting
Self is §10's. Both done (`cortexCoherent`, `cortexHasSelf_of_coherent`,
`cortexHasSelf_of_coherent_eq`: the Self is `cortexState`, by
`cortexPredict_fixed_unique`). While assembling them it became clear the *whole*
chain was witnessable, so `chain_nonvacuous` was built too: **all eight named
hypotheses hold simultaneously**, on `Cortex`, with `boolStatMech` as the
register, `frozenSystem` as the predictive structure, `trioCover` as the cover and
`cortexReflexive` as the reflexive boundary. Every piece already existed in
`Examples.lean`; what is new is that they satisfy the *edges* at once. This
closes the open item C1's record had just opened, in the same session, which is
why that item does not appear under *Open, ranked*.

That result is worth more than the edge itself. Eight implications between eight
different structures is exactly the shape in which joint unsatisfiability hides,
and an unsatisfiable premise proves its conclusion for no reason at all. It is a
mathematical witness, not a cortical one — the register is a bit, the vacuum
manifold is empty, the coarse-graining sequence is constant — and the record says
so.

**What this does not establish.** Not that the chain is sound for cortex: all
eight hypotheses remain undischarged as claims about a brain. Not that n7 is
*needed* by anything outside `Chain.lean` — `Phase8_SelfConsistency`'s other
theorems are still consumed by nothing but this module and the witnesses.

**Manuscript.** `main.tex` §"The contraction rate is $K$ and $D$, not a numeral"
(Derivation 6). The closing clause claimed Derivation 6 was connected to
Derivation 7; C1 showed that claim was false as it stood. It is replaced by the
precise statement: `self_of_supercritical` takes `K > K_c`, `K_c` unfolds to
`2D`, so that statement is insensitive to whether the bifurcation is proved,
while `self_of_coherent_order_parameter` takes the existence of the coherent
order parameter and recovers the inequality from it. One P3 marker (`previously`)
disappeared as a side effect.

**Gates.** `lake build` clean, 17,616 jobs, zero `sorry`, zero warnings, zero
declared axioms. `#print axioms` on `chain`, `chain_nonvacuous`,
`self_of_coherent_order_parameter` and `supercritical_of_coherent` reports exactly
`[propext, Classical.choice, Quot.sound]`. `Chain.lean` 650 lines; it now imports
`Examples` for the witnesses. `main.tex` 87 pages (was 86), overfull 18
(unchanged against `HEAD`), zero undefined references or citations.

### C3 — the n5 → n7 edge — 2026-08-31

**Outcome: the constructor is not built, and the reason is a theorem rather than
a timebox expiring.** The item asked whether `ContinuousNeuralField.ofMeshLimit`
needs the dynamical limit or only the kernel. Neither. Two findings, in
`Chain.lean` §9.

**1. The structure asks for nothing.** `ContinuousNeuralField M` is
`omega : M → ℝ`, `K : M → M → ℝ`, `tau : ℝ` and no conditions at all.
`ofMeshLimit` would typecheck with any kernel whatever, mesh-related or not, so
it would be an edge whose proof is a definitional unfolding — the manufactured
edge C1 warns about. `continuousNeuralField_free` records this. **Standing rule 3
applies in an unexpected direction here:** the risk was weakening the class to
make the constructor go through, and the class turned out to be too weak already.

**2. The coarse-graining theorem does not produce a kernel — this is the real
finding, and it is one level earlier than the recorded blocker.**
`mesh_refinement_convergence` converges the discrete coupling *energy*, one real
number per triangulation, to `∫_S f dμ`; `total_weight_eq_setIntegral` sums the
edge weights to the same scalar. Both integrate the pair structure away.
`ContinuousNeuralField.K` is a function of two continuum points and nothing in
the development produces one from discrete data. The reason is structural:
`TriangulatedManifold.edge_region : V → V → Set M` is a subset of `M`, **not of
`M × M`**, so the discrete side has no product structure to pass to a limit.

**3. The obvious repair is blocked, and the block is proved.** The natural
candidate places each weight at its pair of embedded vertices. `vertexKernel` is
that kernel; `vertexKernel_apply_embedding` shows it genuinely carries the
weights (at an embedded pair it takes the triangulation's value, given injective
embedding); and `vertexKernel_fieldCorrelation_eq_zero` shows it contributes
**exactly zero** continuum coupling energy on any substrate whose measure has no
atoms. A finite set is null and the functional ignores null sets. Spreading the
weights over cells instead needs a product decomposition of `M × M`, which the
triangulation does not provide.

This is `fieldCorrelation_sited_eq_zero` — Derivation 8's hardware result —
arriving from the other side. There it says discrete hardware registers nothing
in the field functional; here it says a *discretization's* kernel registers
nothing either. The same fact cuts against the framework's own coarse-graining
step, which is worth stating plainly and is the kind of thing a per-node audit
never surfaces.

**Consequence for the chain.** None structurally: `chain` never mentions a
continuum kernel. `E56` identifies the coarse-graining limit `L` with the
mean-field coupling *constant* `K`, a real number. That was written before this
pass and it turns out to be the only shape available. What changes is the
manuscript: "discrete couplings coarse-grain to a continuous kernel" (n5's box in
Figure 1, and Table 1's row) claims more than the theorem gives. **C5 must fix
that wording**; it is now the third finding C5 carries.

**What this does not establish.** Not that a kernel limit is impossible — a
different discrete object, carrying regions in `M × M`, might have one. It says
the objects this development has cannot produce it, and that O14(B) is not the
first obstacle on this edge.

**Gates.** `lake build` clean, 17,616 jobs, zero `sorry`, zero warnings.
`#print axioms` on all three new results reports exactly the three.
`Chain.lean` 757 lines. Manuscript untouched in this pass.

### C4 and C5 — naming the edges, and the paper side — 2026-08-31

C4's Lean half was done inside C1 (the docstrings had to say something, and
"formalization gap / modelling assumption / physical commitment" is what they
say). Its manuscript half is the same sentence C5 rewrites, so the two are
recorded together.

**Figure 1.** Arrows now carry a status, and the picture that resulted is the
finding.

* **Dashed** — a named hypothesis of `chain`. **Solid** — a Lean theorem.
  **Dotted** — the stipulation, which is a hypothesis of nothing.
* **n0 has no arrow.** A box whose own text says it is consumed by no theorem
  cannot have an inference leaving it. It stays as a labelled setting box, set
  apart by extra vertical space.
* **Two theorem arrows were added, and neither is one the figure drew:**
  n1 → n3 (finiteness straight to Landauer, skipping the boundary) and n7 → n9
  (the coherent order parameter to the Self, skipping unity). They are drawn as
  curves down the right-hand side.
* So: **every arrow the original figure drew is dashed, and both solid arrows are
  ones it did not draw.** That sentence is now the caption's centre, and it is a
  more interesting claim than the one the figure used to make.
* n5's box was corrected per C3: the limit is a scalar, and no theorem produces a
  kernel. n6's "that kernel" became "that coupling", in the figure, in Table 1,
  in Table S1 and in the abstract.

**The "what is new here" claim.** The old sentence — "no link can quietly borrow
from another, a hypothesis cannot be smuggled in as a definition" — asserted
exactly what C1 showed the development did not establish. It is replaced by four
things a reader can check in one command each: no declared axioms; every physical
postulate a class field with an inhabited class; the chain composing to one
theorem with eight named hypotheses, counted by kind; and those eight jointly
satisfiable (`chain_nonvacuous`). A second paragraph states the two refuted
arrows rather than repairing them silently.

**Table 1** gained a seventh row: the n7 → n9 step is a theorem now and had been
a clause inside the last row. The n5 row's wording was corrected and the n7/n8
row split from it.

**Table S1** was checked against `Chain.lean` rather than generated from it —
generation would need a Lean-to-LaTeX pass, which is machinery this paper does
not otherwise need and which would have to be maintained. Two rows were added:
one for `chain` itself (the eight hypotheses, by name and by kind, plus the two
theorem arrows and the `E12` finding) and one for C3's negative result. Every
existing row's status was compared against the node predicates; none needed
changing, because Table S1 is a per-node table and the per-node statuses were
already right. **That is exactly why the n7 → n9 error survived**: a table with a
row per node has nowhere to record a false claim about an edge.

**One more sentence was corrected outside C5's list.** The supplement said
`self_of_supercritical` derives the fixed point "from $K > K_c$ rather than from a
numeral". `critical_coupling` unfolds to `2 * D`, so that was the wrong way
round; the sentence now states the distinction and names the theorem that makes
it true. The abstract's "Starting from the Poincaré group" was corrected for the
same reason the figure's n0 arrow was removed.

**Gates.** `main.tex` 88 pages (was 86 at the start of the session), overfull 18
— unchanged against `HEAD` — zero undefined references or citations.
`supplementary.tex` 15 pages, overfull 0, unchanged; its two undefined references
are cross-references into the main text and resolve only in the merged build, as
before. Merged arXiv build: **48 pages (was 46), overfull 0, zero undefined
references.** `lake build` clean, 17,616 jobs.

**What is left of the C-series.** Nothing. C1–C5 are closed. The manuscript now
says what the development establishes about its own composition, and the two
places where it said more have been corrected rather than softened. The P-series
(P1–P4, the changelog gate and the rewrite) is untouched and is the next work.

### P1–P4 — the gate, the destination, the rule, and the rewrite — 2026-08-31

**P1 — the gate.** `simulations/check_prose.py`, 13 patterns, each justified in a
comment rather than dumped into one regex. No allowlist. It fails on `HEAD` with
**63** markers (the ledger counted 64; C2 and C5 had already removed one) and
passes after P3. Wired into `.pre-commit-config.yaml` as `check-prose`, selecting
on `files: ^(main|supplementary)\.tex$` rather than `types: [python]`, with
`pass_filenames: false`, following the existing `repo: local` block exactly.

**One deviation from the item, recorded.** The item named
`scripts/check_prose.py`. The script is at `simulations/check_prose.py` instead,
because every existing quality hook is `cd simulations && uv run …` and the
tooling gate of `AGENTS.md` §2 is defined by that path. A second directory would
need either five duplicated hook entries or a second `uv` project; neither is
worth it for one file. Verified under the full set: `ruff`, `ruff-format`,
`mypy --strict`, `bandit`, `vulture`, `xenon --max-absolute B`, `tach` — all
clean. (`bandit`, `vulture` and `xenon` are not spawnable as console scripts in
this environment and were run as `python -m`; that is a pre-existing property of
the venv, not of this change, and the hook itself invokes `uv run python`.)

**False positives, as predicted, and resolved by rewording.** Three: "the older
bound", "the old argument" and "no longer only empirical" — two of which were
comparisons *within* the document and one of which was a scope statement. Each
was reworded. None resisted; the escape hatch was not needed and is not there.

**P2 — `CHANGELOG.md`**, 286 lines, reverse chronological. Nine entries, each in
the form *Claimed / The problem / Claimed now / Record*. It covers the chain
composition and the n7→n9 claim; the coarse-graining scalar finding; W5, W1, W3
and W4; the five-axioms transition with all three refutations; and the four
further defects that survived prose review. It states what it is not: not the
complete record (the archives are), and not a list of everything that changed —
only of **claims that were made and are no longer made**, which is the list worth
being able to find.

**P4 — `AGENTS.md` §5**, stating the rule, the test, the destinations, the gate,
and why there is no allowlist.

**P3 — the rewrite. 63 sites, all closed, `check_prose.py` exits 0.**

Worked by section rather than by marker, as the item asked. The two kinds it
predicted both occurred, and a third turned up:

* **Delete.** Table 1's and Table S1's captions each carried "Earlier drafts
  carried five axioms, three of them inconsistent". Both are gone; the
  cross-reference to the soundness section survives and now points at the general
  finding.
* **Restate as scope.** Derivation 3's retraction paragraph became *What the
  entropy-production bound does not give*: same mathematics, no autobiography,
  and shorter. The supplement's "Theorem 3, in its earlier form, is withdrawn"
  became *What the bound above does not support*.
* **Restate as a counterfactual, which is the form that lost nothing.** Several
  passages were about why a *shape* is wrong — a class carrying a global section,
  a boundary carrying its predictive map as free data, a metric under which every
  contraction is constant. Each becomes "were the class to carry X, the theorem
  would say only Y; it carries neither." That is stronger than the confession it
  replaces, because it is a statement about the mathematics rather than about us,
  and it survives being read by someone who has never seen a draft.

**§2.1 was rewritten, not exempted**, as the item required. What it keeps: the
refutation, all three concrete cases with their arithmetic, the general rule, and
the observation that the failure leaves the build green and is undiscussed in the
applied-formalization literature. What it loses: that the axioms were ours. The
finding does not depend on whose they were, and stated impersonally it reads as a
methodological result rather than a confession — which is what it is.

**The space recovered went where the item said it should.** *What is actually
good about the framework*, point 1 — unity is what a field is, because the field
is the only variable defined everywhere at once — was one clause inside the
paragraph that withdrew the word "primary". It is now its own paragraph, *Why
reach is the property that matters*, in the scaling section: the combination
problem answered structurally, the contrast with IIT's number and GWT's metaphor,
and the observation that this is what the empirical commitment is carrying — if
the coupling is realized by something not defined everywhere at once, the
framework loses the property that distinguishes it, not merely a mechanism.

**Destination check.** Every deleted passage is recoverable from `CHANGELOG.md`
except three, judged not worth keeping and listed here so the judgement is
reviewable: (i) that Table~1's caption once named a count of axioms — the count
is in `CHANGELOG.md`, the caption sentence carried nothing else; (ii) "we record
the correction because it changed what the theorem says rather than how it is
stated" — a sentence about the act of correcting; (iii) "Confronting the
discrepancy is the honest course, so we do it here rather than in a footnote" —
kept, in fact, since it is about this document rather than a previous one.

**Gates.** `check_prose.py` exits 0 on both files. `main.tex` 88 pages, overfull
**16** — two fewer than `HEAD`'s 18 — zero undefined references or citations.
`supplementary.tex` 15 pages, overfull 0. Merged arXiv build **48 pages, overfull
0, zero undefined references**. `lake build` clean, 17,616 jobs, untouched by
this pass.

**Where the ledger stands.** C1–C5 and P1–P4 are all closed. Nothing in the
"Work items" section is open. What remains is the *Open, ranked* list, none of
which was blocking, and the presubmission inquiry, which the item explicitly
sequenced after P3 — the changelog was the first thing an editor would have
noticed, and it is gone.


---

### S1 — the parameter-free collapse — 2026-08-31

**What was built.** Manuscript only; no Lean. Four new paragraphs in
Section~\ref{sec:prediction}, placed after *What the alternative predicts* so
that they answer the objection the shape comparison invites rather than
pre-empting it, plus one extended sentence in *What would falsify it* and one
clause each in the abstract and the introduction.

**The claim now made.** The shape claim is stated and then conceded to be weak in
the manuscript's own voice — any two-timescale account with a slow saturating
gate produces a delayed sigmoid. What the framework contributes past that is a
relation between two separately measurable quantities with no fitted parameter:
at every instant of the recovery the concentration `a(t)` and the coherence
`r(t)` of the phase distribution must satisfy `r = I₁(a)/I₀(a)`. Three tests of
increasing sharpness are stated — shape (the instantaneous distribution is von
Mises), collapse (the whole recovery falls on one fixed curve, the *same* curve
for every subject, since the curve contains no subject-specific quantity), and
threshold (`a = Kr/D` identically, so the measured ratio `a/r` **is** `K/D`, and
it must exceed 2 wherever coherence is non-zero and approach 2 at onset).

**Theorems named.** `circularOrderParameter_vonMises` for the order parameter of
the von Mises density being exactly the Bessel ratio;
`fixedPoint_iff_selfReproducing` for self-consistency being exactly the condition
that the density reproduces its own order parameter; and
`fixed_point_eq_zero_of_le_critical` for the threshold half, which the item did
not name but which is what makes `a/r > 2` a consequence rather than a
restatement.

**One thing the item did not anticipate, and it is the load-bearing caveat.**
The collapse is *empty* under the standard estimator. Maximum-likelihood and
moment estimation of a von Mises concentration both choose `â` so that
`I₁(â)/I₀(â)` is the observed resultant length, by construction — so fitted that
way the data reproduce the predicted curve whatever they are. The manuscript now
says this and says what to do instead: estimate `a` from a functional other than
the resultant length (the log-density of a von Mises is affine in `cos θ`, so a
regression of the log-histogram on `cos θ` returns `a` as a slope), and take `r`
as the resultant length of the same sample. Those are genuinely different
statistics of the same data, and the prediction is that they agree through `R`.
Without this paragraph the item would have shipped an unfalsifiable test.

**What it does not establish.** The test is a joint test of the von Mises
stationary density (a declared modelling input, O13) and the mean-field closure
that makes `a` proportional to `r`. It does *not* test `K_c = 2D` independently
of that ansatz: the `a/r = 2` crossing follows from the same density the collapse
assumes, so a failure of the collapse and a failure of the threshold are one
failure and not two. The manuscript states this in its own paragraph rather than
in a subordinate clause. Nothing here connects `circularOrderParameter` to
`order_parameter_complex` — that remains the mean-field limit, open item (A) —
so the quantity the experimenter measures over finitely many sites is related to
the quantity the theorem is about by an assumption, not by a lemma.

**Manuscript updates.** Abstract: the delayed-sigmoid clause now carries "and,
more sharply, the concentration and the coherence of the phase distribution must
collapse onto a single parameter-free curve". Introduction: the same, spelled
out, with the reason the shape claim alone is not enough. Falsification list:
three new entries, two of which are testable with no reference to the
sleep-inertia setting at all.

**Gates.** `check_prose.py` exits 0 on both files. `main.tex` **91 pages,
overfull 16, zero undefined references or citations** — the overfull *set* is
identical to `HEAD`'s, checked by rebuilding `HEAD`'s `main.tex` in a scratch
tree and diffing the magnitudes rather than comparing counts (one new overfull
box did appear, at the maximum-likelihood sentence, where an inline equation
gave TeX no break point; it was reworded, not tolerated). `supplementary.tex`
untouched. Merged arXiv build **49 pages, overfull 0, zero undefined
references**. No Lean change, so the build gate is inherited unchanged.

---

### F1 — where the positivity actually enters — 2026-08-31

**The item's premise was half wrong, and the correction is the finding.** F1 said
`Phase4_KuramotoDynamics`'s docstring states the division and "the manuscript
does not". The manuscript did: `main.tex` already carried a subsection
*Geometric frustration, and the regime our theorems actually cover* with both
lists, and the supplement carried the same paragraph and a Table S1 row. What
neither carried was the **locus**, and the locus is the whole of what narrows the
objection.

**The locus, verified rather than estimated** (standing rule 4). Positivity is
not a hypothesis distributed through the development. It is a **field of one
class**: `ThermodynamicCover.A_pos` (`Phase5_GlobalSection:128`). Grepping every
site where the sign of `A` is constrained returns that field, the three
minimization results of `Phase4_KuramotoDynamics` that feed it
(`phase_locked_minimizes_potential`, `potential_min_implies_phase_locked`,
`potential_min_iff_phase_locked`), and the uniform bound `0 < a ≤ A i j` in
`Phase5_EquilibriumBridge` and `kuramoto_tendsto_global_minimum`. Nothing else.
All of them sit at node n8 or in what builds it. So the constraint enters the
chain at **one node and the edge into it**, and at no point upstream.

Re-verified this pass and all confirmed: `dV_dt_le_zero`
(`Phase3_CombinatorialThermodynamics:152`) — the Lyapunov identity the entire
descent argument rests on — carries **no** sign hypothesis, and neither do
`is_kuramoto_trajectory_exists`/`_unique`, `dynamic_potential_antitone`,
`dynamic_potential_tendsto` or `velocity_sq_tendsto_zero`.

**What the manuscript now says.** Three changes, all prose.

1. The frustration subsection states the locus: positivity is a class field, so
   it is demanded at the gluing node and nowhere before it. The old closing
   sentence — "the system in which memory is grounded and the system our theorems
   describe are not the same system" — was the *broad* concession, and it is
   replaced by the narrow one: the mean-field reduction of Derivation 7 has no
   sign structure to be frustrated at all, its coupling being a scalar; **one
   step**, the gluing of Derivation 5, describes an unfrustrated system, and
   every step before it does not care.
2. The surviving list gained `dV_dt_le_zero` and `dynamic_potential_tendsto`,
   the first of which is the load-bearing omission — a reader could otherwise
   believe descent itself needed positivity.
3. A new paragraph *The step that carries the positivity* in Derivation 5, so
   the constraint is named where it enters rather than only in the limitations
   section 12 pages earlier.

The closing open-question paragraph now says where an answer would have to act:
not on the dynamics, which is already sign-indifferent, but on the overlap
condition — under frustration the minima are twisted and splay states, so
`section_agrees_of_phase_eq` has nothing to fire on. That is F2's target stated
in the manuscript's own voice.

**The optional Lean was not written, and that is the right call.** The item
offered "a named Lean result restating `dV_dt_le_zero` for a signed `A`, so the
frustration-agnostic half is citable rather than merely observable". It is
already citable: `dV_dt_le_zero` quantifies over `sys : KuramotoSystem V` with
`A` unconstrained, so a signed system is an instance and no restatement adds
anything a reader could not check from the signature. Writing one would have
been a second name for one theorem.

**What this does not establish.** The memory-capacity claim is still unsupported
and is still scoped out of the chain — locating the constraint is not lifting it.
No frustrated `ThermodynamicCover` exists, and none can, since `A_pos` is a
field. Whether a weaker overlap condition admits one is F2 and is open.

**Gates.** `check_prose.py` exits 0 on both files. `main.tex` **93 pages,
overfull 16, zero undefined** — overfull *set* identical to `HEAD`'s by scratch
rebuild and magnitude diff. Three new overfull boxes did appear, all of them runs
of long `\texttt` identifiers with no break point; two were fixed by replacing a
list of five names with a description plus two names, one by dropping a name the
sentence did not need. `supplementary.tex` 15 pages, overfull **8**, 4 undefined
references — both figures **identical to `HEAD`**, verified by the same scratch
rebuild; the undefined references are `sec:soundness` and `sec:scaling`, which
live in `main.tex` and resolve only in the merged build. (The ledger's standing
line had recorded "overfull 0" for the standalone supplement; that figure was
wrong and is corrected above.) Merged arXiv build **50 pages, overfull 0, zero
undefined**. No Lean change.

---

### F2 — twisted gluing and the obstruction — 2026-08-31

**What was built.** `Phase5_GlobalSection.sheaf_glue_unique` generalizes the
probability-specific gluing lemma to an arbitrary sheaf of types, with the old
lemma retained as its specialization. `Phase5_TwistedGluing.lean` defines a
restriction-compatible action of `Phase = ℝ/2πℤ`, twisted local families,
phase cochains, cocycles, coboundaries and the deliberately more modest
`PhaseObstruction` quotient. A family with
coboundary offsets glues after one rotation per patch
(`gluesUpToPhase_of_isCoboundary`); conversely gluing forces a coboundary when
the action is free on pairwise overlaps (`isCoboundary_of_gluesUpToPhase`). The
holonomy lemmas locate where a non-zero class could survive: the cover nerve
must have missing triple intersections, or the action must fail to be free.

**The result of the test.** The natural frustrated-Kuramoto candidate does not
produce such a class. Any configuration supplies absolute patch phases `φ i`,
so its offsets are `φ i - φ j` and are a coboundary
(`isCoboundary_of_phaseField`). The headline wrapper
`gluesUpToPhase_of_phaseField` concludes that locked, twisted and splay phase
fields all glue after patchwise rotation. Frustration alone therefore supplies
no non-trivial phase obstruction and no content label.

**Why there is no non-trivial witness.** One can insert an arbitrary cocycle as
the `offset` field, but that would make the desired content free data. A physical
non-zero Čech class needs transition or gauge data not determined by oscillator
phases, a state presheaf on which those transitions act non-trivially, a proper
nerve-indexed complex, and a cover with suitable topology. The framework names no biological
quantity that supplies those transitions. F3 records that modelling decision;
until it is answered, the negative theorem is the honest endpoint.

**Manuscript.** The geometric-frustration discussion and Table S1 now report the
no-go and distinguish the formal location of an obstruction from a derivation of
one. The supplement records both directions of the gluing/coboundary result and
states that a gauge model would be a new physical input.

**Audit follow-up.** A1–A6 were added above, ranked by effect on the paper. A1 —
the fact that `chain` discards the particular section produced by Unity before
constructing an unrelated Banach fixed point — is the next highest-priority Lean
task.

**Lean gates.** `lake build` completed successfully, 17,618 jobs, with no
warnings. `#print axioms` on `gluesUpToPhase_of_phaseField`,
`gluesUpToPhase_of_isCoboundary` and `isCoboundary_of_gluesUpToPhase` reports
only `propext`, `Classical.choice` and `Quot.sound`. `check_prose.py` exits 0.
Both publication files compile twice: `main.tex` is 93 pages with 16 overfull
boxes and zero undefined references; `supplementary.tex` is 15 pages with 8
overfull boxes and the same three standalone cross-document undefined-reference
warnings (`sec:soundness` twice and `sec:scaling`) recorded before this pass.

---

### A1 — the glued state is the Self — 2026-08-31

**Defect closed.** The old `chain` used `Unity X` only through
`nonempty_globalSection_of_unity`, discarded the section produced by the cover,
and let Banach choose an unrelated fixed point. It therefore proved coexistence
of Unity and a Self rather than reflexivity of the unified state.

**What was built.** `IsUnifiedBy T s` states that `s` restricts to every local
state of the thermodynamic cover `T`. `UnifiedSelf rb` carries a cover and a
section that is both unified in that sense and the unique fixed point of
`rb.predict`; `unifiedSelf_self` forgets the cover and recovers the old endpoint.
`chain` now concludes `UnifiedSelf`. Its `E89` argument supplies a particular
`T` and `s`, the unification equation, the Lipschitz law, and `predict s = s`.
Banach supplies uniqueness. The physical identification is therefore explicit
and counted as part of the modelling assumption rather than silently lost.

**Witness.** The trajectory-derived `trioCover` cannot witness this statement:
its glued profile is `(2,1,3)`, while the reflexive map's fixed point is
`cortexState`, with mass concentrated at `mid`. The joint witness now uses the
earlier two-patch `cortexCover`, whose local states are restrictions of
`cortexState`; the equality is definitional, and `cortexPredict_fixed` plus
`cortexPredict_fixed_unique` provide the reflexive half. Thus n8 and n9 are the
same state on the witness rather than merely states on the same type.

**What remains assumed.** No field dynamics proves that a cover's glued section
is fixed by the avatar read-out. `E89` now says that equality out loud alongside
the independent Lipschitz-rate postulate. A1 closes a formal-composition defect,
not the physical bridge. A6 remains open for the corresponding status wording.

**Manuscript.** The central methodology paragraph now calls `chain` a
conditional composition theorem, states its `UnifiedSelf` endpoint, and limits
`chain_nonvacuous` to joint satisfiability. Derivation 6 explains that `E89`
carries the state identification, and Table S1 uses the same scope.

**Gates.** The red interface test initially failed because `IsUnifiedBy`,
`UnifiedSelf` and `unifiedSelf_self` did not exist; it passes after the change.
`lake build` completes 17,618 jobs with zero warnings. `#print axioms` on
`unifiedSelf_self`, `chain` and `chain_nonvacuous` reports only `propext`,
`Classical.choice` and `Quot.sound`. `check_prose.py` and `git diff --check`
pass. Both publications compile twice: main 93 pages, 16 overfull and zero
undefined references; supplement 15 pages, 8 overfull and the same three
standalone cross-document undefined-reference warnings.

---

### A2 — conditional composition, not physical derivation — 2026-08-31

**Scope corrected.** The abstract, opening paragraph, formalization introduction,
Figure~1 caption, conclusion and supplement now call the result a conditional
composition schema rather than a deductive chain from basic principles. The
figure states the decisive count directly: all eight vertical arrows are
assumptions. The theorem paragraph and Table~S1 already named the eight
hypotheses after A1; they were retained and checked for agreement.

**What the formalization establishes.** `chain` provides machine-checked
dependency accounting: given `E12` through `E89`, their conclusions compose to
`UnifiedSelf`. It does not derive those cross-domain arrows from finite capacity.
In particular, `E12` is equivalent to its own conclusion, four arrows supply
whole structures, and `E45` relates quantities for which the development defines
no shared dynamics.

**What was not changed.** The Lean theorem is correctly typed for conditional
composition and required no redesign. No status of an individual node changed,
and no reference was added.

**Gates.** The text-level red test failed on three unconditional formulations:
“establishing a deductive chain,” “verification of our deductive chain,” and the
caption “the deductive chain.” All three are absent after the rewrite, while
both the main theorem paragraph and Table~S1 retain “conditional composition.”
`check_prose.py` and `git diff --check` pass. Both publications compile twice:
main is 94 pages with 16 overfull boxes and zero undefined references or
citations; the standalone supplement is 16 pages with its unchanged 8 overfull
boxes and three cross-document undefined-reference warnings.

---

### A3 — joint satisfiability is not mechanistic non-vacuity — 2026-08-31

**What changed.** The headline theorem `chain_nonvacuous` is renamed
`chain_hypotheses_jointly_satisfiable`. Its type and proof are unchanged: it
still concludes the same `UnifiedSelf` by discharging `E12` through `E89` on one
toy substrate. The docstring now makes the limit part of the public interface:
the empty vacuum and constant coarse-graining sequence prove consistency, not a
mechanism.

**Publication scope.** The main text and Table~S1 use the new name and say only
that the eight hypotheses are simultaneously consistent. Neither treats the
witness as evidence for cortical realization. Historical pass records retain
the old identifier where they document the declaration that existed at the time.
T5 is retitled around the missing mechanistic witness rather than around making
a theorem called “nonvacuous” less degenerate.

**What this does not establish.** No new witness was built. A single dynamics
still does not generate the vacuum exit, predictive system, continuum coupling,
cover and reflexive map. Constructing such a toy model, if useful, remains T5.

**Gates.** The red interface test failed because
`chain_hypotheses_jointly_satisfiable` did not exist. After the rename it passes,
and `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`.
`lake build` completes 17,618 jobs with zero warnings; the Lean sources contain
no `sorry`; `check_prose.py` and `git diff --check` pass. Both publications
compile twice: main is 94 pages with 16 overfull boxes and zero undefined
references or citations; the standalone supplement is 16 pages with its
unchanged 8 overfull boxes and three cross-document undefined-reference warnings.

---

### A4 — overlap compatibility is independent — 2026-09-01

**Claim corrected.** Displayed Theorem~5 now states the sheaf result at its exact
scope: an overlap-compatible family of local states glues uniquely. It explicitly
identifies compatibility as an independent physical hypothesis and says that
phase-locking does not imply it. Figure~1, Table~1 and the opening of Derivation~5
use the same separation: the dynamics supplies synchronized phases; the class
field `section_agrees_of_phase_eq` supplies compatible sections.

**Implementation account.** The supplementary implementation paragraph now
distinguishes `thermodynamic_equilibrium` from
`LocalSectionSynchronization.section_agrees_of_phase_eq`. The convergence bridge
can discharge the former on its explicit basin; no theorem in the development
discharges the latter. Table~S1 already said the overlap obligation was untouched
and required no status change.

**What this does not establish.** No biological mechanism for overlap agreement
is proposed, and no Lean declaration changes. The sheaf theorem proves existence
and uniqueness from compatibility; it does not explain why cortical local states
are compatible.

**Gates.** The red text test failed at the displayed theorem, Figure~1 and the
opening of Derivation~5, each of which presented phase-locking as sufficient for
gluing. Those formulations are absent after the rewrite. `check_prose.py` and
`git diff --check` pass. Both publications compile twice: main is 94 pages with
15 overfull boxes and zero undefined references or citations; the standalone
supplement is 15 pages with its baseline 8 overfull boxes and three
cross-document undefined-reference warnings. No Lean source changed in A4; the
clean 17,618-job build from A3 remains the applicable Lean gate.

---

### A5 — scalar convergence does not produce a kernel — 2026-09-01

**Claim corrected.** The scale bridge now has three explicitly different layers:
`mesh_refinement_convergence` proves convergence of one scalar energy; a
continuum coupling kernel is introduced as a modelling input; and identifying
that kernel with endogenous cortical EM coupling is an empirical commitment.
Figure~1, the scaling section, its boxed commitment, Table~S1 and the supplement
all use this separation.

**The obstruction retained.** A kernel limit is not relabelled as the remaining
propagation-of-chaos problem. `TriangulatedManifold.edge_region` supplies subsets
of `M`, not product-structured cells in `M × M`; the vertex-supported candidate
is invisible to the continuum functional on an atomless substrate. New discrete
architecture is required before a kernel limit can be stated, and only then does
the separate dynamical mean-field question arise.

**What this does not establish.** No kernel construction or field dynamics was
added. The EM identification remains the framework's empirical commitment, now
without borrowing support from the scalar convergence theorem.

---

### A6 — the Self contraction law is a modelling postulate — 2026-09-01

**Status corrected.** Figure~1 and Table~1 classify the Self step as a
conditional theorem plus modelling postulate. Displayed Theorem~6 and Table~S1
state the division precisely: coherence recovers `K > K_c`, which makes
`resonanceRate K D τ < 1`; it does not prove that the avatar-mediated map is
Lipschitz at that rate. `E89` supplies the Lipschitz law independently, alongside
the identification of the glued state with the fixed point.

**Witness scope.** The three-site read-out realizes the stipulated rate at the
chosen parameters. This proves that the assumptions are satisfiable; designing
the witness to have that contraction factor does not derive self-model dynamics
from oscillator dynamics.

**What remains theorem.** Given the Lipschitz hypothesis, Banach supplies the
unique fixed point. Above threshold the stipulated rate is usable; at or below
threshold `not_contractingWith_resonanceRate` shows this Banach route is
unavailable. Neither result says that a Self cannot exist below threshold.

**Gates for A5 and A6.** The red text test found the kernel claim in the scaling
scope and empirical commitment, and the unconditional Self status in the main
section and Table~S1. Those formulations are absent after the rewrite.
`check_prose.py` and `git diff --check` pass. Both publications compile twice:
main is 93 pages with its A4 baseline of 15 overfull boxes and zero undefined
references or citations; the standalone supplement is 15 pages with its
baseline 8 overfull boxes and three cross-document undefined-reference warnings.
No Lean source changed in A5 or A6; the clean 17,618-job build from A3 remains
the applicable Lean gate.

---

### F3 — cortical phase singularities as physical transition data — 2026-09-01

**Decision.** The F2 no-go remains correct for circle-valued offsets computed as
differences of absolute Kuramoto patch phases, but it is not the end of the
physical-data question. Cortical phase singularities supply a measured
topological observable: the integer winding of phase around a loop enclosing an
amplitude-zero point. The corresponding overlap data are integer multiples of
`2π` between local real-valued lifts of a circle-valued phase, not the
circle-valued pair offsets represented by `PhaseObstruction`.

**Evidence and reference gate.** Townsend, Solomon, Chen, Pietersen, Martin,
Solomon and Gong, “Emergence of Complex Wave Patterns in Primate Cerebral
Cortex,” *Journal of Neuroscience* 35(11), 4657–4662 (2015), explicitly compute
the winding number around phase singularities in multielectrode primate LFP maps
and relate complex waves to spiking (DOI `10.1523/JNEUROSCI.4509-14.2015`). Xu,
Long, Feng and Gong, “Interacting Spiral Wave Patterns Underlie Complex Brain
Dynamics and Are Related to Cognitive Processing,” *Nature Human Behaviour*
7(7), 1196–1215 (2023), report task-dependent spiral locations and rotation
directions that classify cognitive tasks (DOI `10.1038/s41562-023-01626-5`).
Authors, titles, years and venues were independently checked against the primary
journal record and PubMed before both references were added.

**Manuscript scope.** The main text and supplement now distinguish the measured
lift obstruction from F2's deliberately simpler quotient. The evidence supplies
a physical candidate and a cognitive correlate; it does not show that winding
sectors encode phenomenal content. Table S1 therefore says “empirical candidate,”
keeps the memory/content claim outside the chain, and adds no theorem status.

**What remains.** F4 records the SRR follow-up: formalize failure of a global
real lift on the cortex minus its singularity set, using a proper nerve-indexed
integer complex, then specify a content-sensitive empirical test. No Lean code
was changed in F3 because formalizing the old circle-valued obstruction more
deeply would formalize the wrong physical object.

**Gates.** `check_prose.py` and `git diff --check` pass. Both publications compile
twice. Main is 94 pages with 15 overfull boxes and zero undefined references or
citations; the standalone supplement is 15 pages with its baseline 8 overfull
boxes and three cross-document undefined-reference warnings (`sec:soundness`
twice and `sec:scaling`). No Lean source changed; the clean 17,618-job build from
A3 remains the applicable Lean gate.

---

### F4 — the measured phase-lift loop obstruction — 2026-09-01

**What was built.** `Phase5_PhaseLifts.lean` represents an electrode loop by one
integer transition per adjacent overlap. `loopWinding` is their finite sum and
`HasGlobalLift` says that they are consecutive differences of one real-phase
unwrapping, including the closing edge. The headline theorem
`loopWinding_eq_zero_of_hasGlobalLift` proves those differences telescope to
zero; `not_hasGlobalLift_of_loopWinding_ne_zero` is the experimentally usable
contrapositive.

**Non-vacuity.** `threeElectrodeWinding` records two zero transitions and one
branch-cut crossing. Its winding is proved equal to one, and
`threeElectrodeWinding_not_hasGlobalLift` proves that no global unwrapping
produces it. The witness is non-trivial precisely because its obstruction is
non-zero.

**What it does not establish.** The theorem is the finite nerve-loop calculation,
not a construction of Čech cohomology on cortex. It does not derive singularities
from Kuramoto dynamics, prove their stability, or associate winding with
phenomenal content. F5 owns the ambient-cover construction and content-sensitive
empirical test. Nothing from this branch is added to `chain`.

**Manuscript.** The geometric-frustration section, supplementary implementation
account and Table S1 now distinguish three results: F2's no-go for circle-valued
differences of absolute patch phases; F4's positive integer lift obstruction;
and the still-open empirical identification of a winding sector with content.

**Gates.** The red scratch test first failed because
`Phase5_PhaseLifts.lean` did not exist; after implementation the same three API
tests pass. `lake build` completes 17,620 jobs with zero warnings and the Lean
sources contain no `sorry`. `#print axioms` on
`loopWinding_eq_zero_of_hasGlobalLift`,
`not_hasGlobalLift_of_loopWinding_ne_zero` and
`threeElectrodeWinding_not_hasGlobalLift` reports only `propext`,
`Classical.choice` and `Quot.sound`. `check_prose.py` and `git diff --check`
pass. Both publications compile twice: main is 94 pages with 15 overfull boxes
and zero undefined references or citations; the standalone supplement is 15
pages with its baseline 8 overfull boxes and three cross-document
undefined-reference warnings.

---

### F5 — the cortical cover and content test — 2026-09-01

**Domain and measurement.** The cortical surface is $M$; at each time the
band-limited analytic signal is $z=Ae^{i\phi}$, the preregistered singularity set
is $Z_t$, and the phase is measured on the punctured domain
$M^\ast_t=M\setminus Z_t$ by $q_t=z/|z|:M^\ast_t\to S^1$. A trial-independent
electrode or source-space cover supplies local real lifts. Their differences on
connected overlaps, divided by $2\pi$, are the integer transitions consumed by
`loopWinding`. Finite-resolution amplitude thresholds, loop geometry and
cross-scale persistence criteria are fixed from baseline or training data rather
than content labels.

**Content-sensitive test.** A preregistered nested comparison asks whether signed
winding, source-localized singularity position, rotation direction and lifetime
improve held-out prediction of trial-level content labels beyond stimulus, task,
behavioural response, eye movement and arousal. Generalization is tested across
participants and sessions; permutations stay within task, stimulus and arousal
strata; and replication changes or removes the motor report. A null increment
rejects this proposed content role.

**What this does not establish.** The protocol makes the claim falsifiable but
supplies no data. Even a positive result would be a controlled association, not
an identity between winding and phenomenal content. No full nerve-indexed
integer complex was built before the measurement protocol warranted it, no Lean
declaration changed, and this branch remains outside `chain`.

**Gates.** The red text test failed because the manuscript did not name the
punctured domain, measurement map, controlled comparison or task/arousal
stratification; all four checks pass after the specification. `check_prose.py`
and `git diff --check` pass. Both publications compile twice: main is 95 pages
with the unchanged 15 overfull boxes and zero undefined references or citations;
the standalone supplement is 15 pages with its unchanged 8 overfull boxes and
three cross-document undefined-reference warnings (`sec:soundness` twice and
`sec:scaling`). No Lean source changed, so the clean 17,620-job F4 build remains
the applicable Lean gate.

---

### S2 — the critical exponent — 2026-09-01

**The estimate was right, for once.** The item said the missing ingredient was
`E(a) = 1/2 - a²/16 + O(a⁴)`, that Mathlib should be grepped before believing it
hard, and that given it the rest is three lines of algebra. All three held.
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` differentiates
the cosine moments `vmMoment n a = ∫_{-π}^{π} cosⁿθ e^{a cos θ}` under the
integral, dominated by the constant `exp (|a| + 1)` on the unit ball around the
parameter; differentiation raises the cosine power by one, so two applications
give `ContDiff ℝ 2`. `vonMisesSRatio_eq_moments` writes `E = 1 - M₂/M₀`, whose
denominator is positive, and `taylor_isLittleO_univ` finishes it.

**The remainder is `o(a²)`, not `O(a⁴)`, and that is deliberate.** The stronger
form needs a fourth derivative and nothing needs the stronger form. The moments
at zero are elementary — `2π, 0, π, 0, 3π/4` — and give `E(0) = 1/2`,
`E'(0) = 0` by the symmetry that kills the odd moments, and `E''(0) = -1/8`.
The docstring of `Phase8_SelfConsistency` §7, which recorded the expansion as
unformalized, now points downstream and says which form was proved.

**The exponent.** `coherent_solution_critical_exponent` substitutes the
expansion into `coherent_iff_sRatio_eq`. Writing `a = Kr/D`, rearranging
`E(a) = D/K` gives `K - 2D = K a² (1/8 - 2q(a))` with `q` the normalized
remainder, and `K → 2D` along positive coherent solutions with `r → 0` sends
`q → 0` and `r²/(K - 2D) → 1/D`. It is stated over a filter rather than a
curve, so it constrains every such family and privileges no path.

**A defect found and closed in the same pass.** The hypotheses are an
eventually-clause, and an eventually-clause is vacuously true on the bottom
filter, so as written the theorem was worth exactly nothing until a family
satisfying it existed. This is A3's lesson — satisfiability is not
non-vacuity — and it is closed the way F4 closed its own: with a witness in the
module. `coherentBranch` selects the unique positive solution above threshold
through `supercritical_fixed_point_existsUnique`,
`coherentBranch_tendsto_zero` reads `coherent_branch_continuous_at_threshold`
as a limit along `𝓝[>] (2D)`, and `coherentBranch_critical_exponent`
discharges every hypothesis on it.

**What this does not establish.** Stationary-solution asymptotics, and nothing
more. No stability, no dynamical selection — `r = 0` remains a solution above
threshold — and no time course. The step from the branch `r(K)` to a recovery
curve `r(t)` is carried by the adiabatic separation the section already assumes
plus one new assumption, that `K(t)` crosses `2D` at non-zero speed. Both are
stated in the manuscript rather than around it: the assumptions paragraph now
lists four things and not three.

**What the manuscript gains.** The delayed sigmoid is a shape any two-timescale
account with a slow saturating gate can produce, and the new paragraph says so
before saying what the bifurcation adds: a square-root cusp with *infinite*
initial slope at the foot. An exponential, a logistic and any smooth gate
composed with a branch leaving zero linearly all have finite initial slope. The
cusp belongs to the pitchfork, not to the two-timescale structure. The
falsification paragraph gains the matching line — a finite initial slope takes
the bifurcation and leaves the two-timescale account standing — Derivation 7
gains the derivation in outline, and Table S1's threshold row gains the rate.

**Gates.** `lake build` clean, 17,622 jobs, zero `sorry`, zero warnings; the
21 new declarations each report only `propext`, `Classical.choice`,
`Quot.sound`. Two diagnostics the incoming file carried are gone: a `ring` that
was falling back to `ring_nf` on a filter equality (fixed by `convert … using 2`)
and two deprecated lemma names. `check_prose.py` and `git diff --check` pass.
Both publications compile twice: main is 98 pages with the unchanged 15 overfull
boxes and zero undefined references or citations; the standalone supplement is
16 pages with its unchanged 8 overfull boxes and the three baseline
cross-document undefined references. The merged arXiv build is 52 pages with
zero overfull boxes and zero undefined references.

**Left open.** S3, the no-hysteresis discriminator, is the natural next item and
costs no Lean; it is untouched here to keep this pass one change.

---

## Post-review — from Claude Opus 4 (Fable) on OpenRouter, 2026-09-01

A 1000-word high-level review plus ten critical bullet points was commissioned
via `hermes chat -q` with the assumption that S3, T1–T5 are all completed. The
full text is at `~/claude_opus_review.txt` on this machine. The
review closed four points already addressed by prior C/P/A passes (n0→n1 arrow
removed in C5; n5→n7 gap documented in C3; sharpened labels in C5; O14(B)
already in the closed-items section). Seven items are genuinely new or press on
settled questions and are recorded below.

Take ONE at a time. R1 and R2 first — both make the existing Lean say what it
already says more clearly, cost no new formalization, and address the questions
a PRX Life referee will raise first.

---

### R1 — Formalise the EM identification as a predicate, not only as prose

- [x] **Objective.** *(Delivered 2026-09-02; the fourth "done when" condition —
      the manuscript stating what the predicate demands — closed 2026-09-03. See
      the R1 record and the V1 record below.)* Introduce `IsEMFieldCoupling` (or a similarly named `Prop`)
      whose fields are the necessary conditions the framework places on the
      posited continuum kernel, so that the step from `ContinuousNeuralField` to
      `exhibits_phase_transition` is mediated by a checkable hypothesis rather
      than by a paragraph in the manuscript.

**Why.** The identification of the continuum kernel with the cortical EM field
is the framework's central empirical commitment and the place it is most easily
wrong. Currently it lives entirely in prose — the scaling section's boxed
statement, the four falsification conditions, and the empirical-commitment cell
of Table S1. A Lean predicate whose fields are *what the kernel must be*
(continuous, defined on a domain of positive measure, modulatory in effect on
individual sites, of sufficient coupling strength) would make the physical
requirement a formal hypothesis of `chain`'s `E56` rather than an annotation
beside it. The predicate can remain uninhabited by a cortical witness — that is
the empirical question — but its failure conditions would be the points at which
a future model must supply data rather than argument. Do not weaken
`ContinuousNeuralField` to make the predicate trivial; standing rule 3.

**What it takes.** One module (`Phase9_EMIdentification.lean` or similar)
sitting above `Phase8_ContinuousField`, defining the predicate and proving
that the toy witness's kernel satisfies the non-cortical conditions (positivity,
continuity, domain with measure). The manuscript then cites the predicate
rather than only the prose paragraph.

**Risk.** This makes the gap *more* visible rather than less — the predicate
will have a field for the coupling strength and `E56` will say the witness's
value is `K = 3`, which is not cortex. That is the point: the framework should
count its empirical commitments, not blur them.

**Done when.** The predicate exists, `chain`'s `E56` references it, the
witness kernel discharges the non-cortical fields, and the manuscript's weakest
paragraph (the EM identification) states what the predicate demands rather than
what the prose paragraph says.

---

### R2 — State propagation of chaos (O14(B)) in the manuscript as an open problem

- [x] **Done 2026-09-01.** Propagation of chaos named as the gap between the stationary
      threshold theorems and any trajectory statement: one sentence in
      Derivation 4's closing paragraph, one at the close of supplement §7. Pass record below.

- [x] **Objective.** Add one sentence to Derivation 4's closing scope paragraph
      naming the dynamical mean-field limit as the gap between the stationary
      threshold theorems and a trajectory statement, with a pointer to the
      literature that would close it.

**Why.** O14(B) is recorded in the closed-items section of this ledger but is
invisible in the manuscript. A referee who reads `K_c = 2D` as a claim about
*trajectories* rather than about a stationary density will — correctly —
object that no lemma relates the two. The manuscript currently says the station-
ary density is an input and no Fokker–Planck operator exists. That is honest.
What it does not say is *what would be needed* to close the gap: McKean–Vlasov
propagation of chaos for the finite Kuramoto system, which is a research
programme, not a lemma. Naming it exactly, with a reference, turns a silent
debt into a known one.

**What it takes.** One sentence at the end of Derivation 4 and one sentence in
the supplement at the close of §7, each naming propagation of chaos as the
missing link. No Lean.

**Done when.** A reader who goes from Derivation 4's scope paragraph to a
Lacker or a Sznitman reference knows exactly what is not proved.

---

### R3 — Clarify what the Self is, beyond a Banach fixed point

- [x] **Done 2026-09-01.** `UnifiedSelf` clarified with four numbered distinctions in the
      ``The fixed point is the glued state'' paragraph. Pass record below.

- [x] **Objective.** One paragraph in Derivation 6 or the Discussion that states
      what ``the Self'' means in the formalization: the unique global section
      fixed by the avatar-mediated read-out. Distinguish this from (i) the first-
      person experience it is stipulated to be (n10, outside the chain),
      (ii) the mere existence of a fixed point of some map on some metric space,
      and (iii) any claim about a conscious self in the psychological sense.

**Why.** The review's sharpest observation: a Banach fixed point is a purely
mathematical object, and the manuscript's language around ''the Self'' can be
read as smuggling phenomenology into the formal result. The current text
(§Reflexive topology) states the Banach theorem, names the object, and says
n10 is stipulation. What it does not say is what *within the formalisation*
the Self denotes — the particular section that is both glued from the cover
and fixed by the avatar. A1 guarantees this identity; the manuscript should
name it as the content of the conditional composition's endpoint.

**What it takes.** A short paragraph in Derivation 6, after the contraction
law is introduced, stating that `UnifiedSelf` is the composition's endpoint
and that within Lean it means the unique section satisfying two properties
(the unification equation and the fixed-point equation). Then a sentence that
this is not a consciousness claim — n10 is. No Lean.

**Done when.** A reader who checks `Chain.lean`'s `UnifiedSelf` finds the
manuscript's description thereof and sees a statement about which formal
object is meant, not a claim about what it feels like to be it.

---

### R4 — Specify the measurement protocol behind the sleep-inertia prediction

- [x] **Done 2026-09-01.** A ``How to measure it'' paragraph giving the LFP/MEG estimates
      for $a$ and $r$ and the volume proxy for $K(t)$. Pass record below.

- [x] **Objective.** State in the prediction section which neural observables
      carry the quantities the prediction constrains, and how the parameter-
      free collapse would be measured in practice.

**Why.** The prediction is the paper's own falsifiable claim, and it is
presented in functional form — `r(t)`, `a(t)`, `K(t)` — without identifying
what in cortex supplies each. The review pressed this correctly: a referee
wants to know what signal to record. The candidate is LFP phase for `r` and
`a` (the circular resultant length and the von Mises concentration of the
instantaneous phase distribution across sites) and extracellular volume
fraction or astrocytic calcium imaging as a proxy for `K(t)`. The collapse
prediction `r = I₁(a)/I₀(a)` ties the two LFP-derived quantities together
and the `a/r` threshold ties both to the volume proxy. Saying this would
move the prediction from a mathematical statement to an experiment design.

**What it takes.** One paragraph in the prediction subsection (after the
collapse is stated) specifying the recording modality (multisite LFP, source-
reconstructed MEG/EEG with sufficient cortical coverage), the estimator for
`a` (the regression-based log-density slope, not the ML estimate — S1's pass
record explains why), and the candidate slow variable (extracellular volume
fraction via diffusion MRI or astrocytic calcium via fibre photometry). No Lean.

**Done when.** A referee can write the preregistration from the manuscript
alone, without emailing the author.

**Risk.** Specifying the protocol constrains the prediction to a recording
modality the author may not have access to. That is a cost, and it is the
right cost: a prediction without a protocol is a formalism.

---

### R5 — Qualify the hardware suboptimality claim to its proven scope

- [x] **Done 2026-09-01.** Both `rigid_is_strictly_suboptimal` and
      `fieldCorrelation_sited_eq_zero` explicitly scoped at the hardware
      section opening; ~5\% drift sentence in the Fig.~4 caption. Pass record below.

- [x] **Objective.** Adjust the Rigid hardware section, the hardware figure
      caption and the Corollary so that every statement about suboptimality is
      explicitly scoped to (a) the functional that registers zero for finitely-
      sited architectures, and (b) architectures not wired to the best-
      correlated pair.

**Why.** `rigid_is_strictly_suboptimal` derives suboptimality for any
realizable coupling whose wiring misses the best-correlated pair; it does
not derive it for every rigid architecture. The simulation shows a ~5 % drift
over 2000 steps at frozen phases — a direction, not convergence. The manu-
script currently wraps these as a Corollary whose title ``Continuous topology
beats rigid'' reads as unconditional. The review flagged this, and the gap
between the ``demonstrably suboptimal under matched resource and specified
drift conditions'' and the current wording is the right size for this item.

**What it takes.** Rewrite the Corollary's first sentence to name the
functional and the wiring condition. Add one sentence to the caption of
Fig. 4 stating the 5 % figure and that it reports drift direction, not
convergence. No Lean; the theorems are correctly stated and need no change.

**Done when.** A reader who reads the Corollary first and then the theorems
finds no mismatch in their scope.

---

### R6 — Revisit the ``no allowlist'' rule in `check_prose.py`

- [x] **Done 2026-09-01.** Zero-allowlist reaffirmed in `check_prose.py`'s docstring, no
      concrete case having arisen against it. Pass record below.

- [x] **Objective.** Reopen P1's design decision: whether a zero-allowlist gate
      loses critical narrative context that is not recoverable from Lean
      docstrings or CHANGELOG.md.

**Why.** The review pointed out that some scientific narratives legitimately
require a chronological frame: explaining *why a claim had to be* weakened is
not autobiography if the reason is general enough to interest a reader who
has never seen a draft. The current rule treats every retrospective sentence
as contamination. The P1 pass record anticipated this objection in the
negative — ``The finding does not depend on whose axioms they were'' — and
that reasoning holds for the three concrete refutations in §2.1. The question
is whether it holds for every future edit. A single escape hatch with a
justifying Lean docstring (not a `% CHANGELOG-OK` comment) would be a
checkable middle ground.

**What it takes.** Add a `--allow-hash` mechanism (or equivalent) to
`check_prose.py` that permits a matching `@changelog:` annotation in a Lean
docstring. Gate the annotation behind a review step: the curator or the
author must approve it. Record the first instance if one arises; if none
arises after six months of edits, remove the mechanism as unused. No Lean
change to the publication files; only the script and its documentation.

**Risk.** An allowlist with one entry becomes an allowlist with twenty — this
is the argument P1 made and it is still true. The item is worth doing only
if there is a concrete case the current rule makes worse. The review provided
none; this item is an invitation to watch for one rather than to build the
mechanism pre-emptively.

**Done when.** The script has the mechanism OR a pass record in this ledger
saying the question was revisited and the zero-allowlist decision reaffirmed
with a reason tied to a concrete case. Either outcome is a close.

---

 ### R7 — Expand the theory landscape to acknowledge alternative formalisations of unity

- [x] **Done 2026-09-01.** Dynamic Core and predictive-binding paragraph added after the
      IIT/GWT comparison. Pass record below.

- [x] **Objective.** One paragraph in the Introduction or the Discussion that
      names the Dynamic Core hypothesis (Edelman & Tononi) and predictive-
      processing accounts of perceptual binding as alternative approaches to
      formalising unity, states briefly why each is distinct from the sheaf-
      theoretic gluing proposed here, and clarifies that the contribution is
      the formal-language framing, not a claim that other accounts of binding
      are wrong.

**Why.** The manuscript contrasts its global section with IIT's Φ and GWT's
broadcast, which are the two rivals the consciousness literature expects to
hear about. It does not mention the Dynamic Core (which shares the phase-
synchrony premise) or predictive-processing accounts of binding (which share
the information-theoretic framing). The review noted this narrows the
paper's position unnecessarily: acknowledging nearest neighbours costs one
paragraph and makes the sheaf-theoretic contribution sharper by contrast.

**What it takes.** One paragraph, placed after the IIT–GWT comparison, naming
each alternative and the single dimension on which the present framework
differs (formalisation as warrant for the chain's consistency; availability of
a parameter-free empirical prediction). No Lean.

**Done when.** A reader familiar with the Dynamic Core or predictive binding
recognises their own view in the paragraph and sees why the present framework
is not the same claim in different language.

---

### R8 — Close the optimal-wiring loophole with a dynamic misalignment argument

- [x] **Done 2026-09-01.** Dynamic-misalignment paragraph added after the
      rigid-suboptimality derivation, closing the static loophole by
      non-stationarity. Pass record below.

- [x] **Objective.** Add an argument to the hardware section stating that even
      an architecture wired to the best-correlated pair at one instant will
      drift out of alignment under a non-stationary phase field, so the
      condition ``the wiring misses the optimal pair'' will hold at most
      transiently.

**Why.** `rigid_is_strictly_suboptimal` derives suboptimality only when the
fixed wiring misses the current best-correlated pair. A static phase field
could evade this by being wired to precisely that pair. But cortex is not
static: the phase field evolves on sub-second timescales (Section 4), and
a rigid routing matrix cannot track it. The review pressed this correctly:
a loophole that closes under dynamics is not a loophole at all, and stating
the argument makes the theorem stronger than it looks in the static case.

**What it takes.** One paragraph in the Corollary section, after the static
theorem is stated, observing that `rigid_gap > 0` at one instant implies
nothing about the next; that over any interval of non-zero length the field
explores more than one correlation structure; and that the wiring therefore
misses some optimal pair at almost every instant. This is a qualitative
argument — it does not need a formal ergodic theorem — and no Lean change.
The manuscript already cites the Kuramoto timescales; the paragraph connects
them to the rigidity analysis.

**Risk.** An informal argument next to a formal one can be read as a
confession that the formal one is incomplete. The paragraph must say plainly
that it is an informal extension, not a theorem.

**Done when.** A reader who notices the static loophole finds the dynamic
closing paragraph on the same page.

---

### R9 — Argue that a modulatory field can cross the threshold

- [x] **Done 2026-09-01.** Modulatory-field paragraph after the falsification conditions,
      with the columnar-aggregation arithmetic for $K > K_c$. Pass record below.

- [x] **Objective.** One paragraph in the EM identification section that
      explains how a strictly modulatory field — one that biases spike timing
      by 1–3 ms without driving any cell to fire — can nonetheless supply the
      coupling strength `K` needed to cross `K_c = 2D`, answering the
      ``fields are too weak'' objection (Pockett, Vöröslakos) on arithmetic
      rather than on principle.

**Why.** The review's core observation: the manuscript concedes the field's
modulatory role and its ~1–5 mV/mm magnitude, but never shows that this
suffices for `K > 2D`. A referee who accepts the field's existence and its
weak effect per synapse can still reject the framework because the threshold
is never demonstrated to be reachable. The answer need not be a formal
calculation — the framework's coupling constant `K` is a mean-field parameter
aggregated over `~10⁴–10⁵` synapses per cortical minicolumn, so a modulatory
bias of 1–3 ms on each of thousands of synapses yields a collective
coupling that the per-synapse magnitude understates. A one-paragraph scaling
argument (per-synapse biasing × columnar divergence → effective `K`) would
turn a concession into a positive case.

**What it takes.** One paragraph in the scaling section, after the four
falsification conditions, that states the arithmetic: estimate the number of
synapses per effective degree of freedom, multiply by the per-synapse
entrainment window, and compare the product to `D`. Cite the relevant
cortical-column literature (Mountcastle, Hawkins) and state the range of
`K` values this would imply. This is a back-of-the-envelope calculation,
not a theorem, and must be marked as such.

**Done when.** A referee who objects ``1 mV/mm cannot carry the coupling
the theory needs'' finds a paragraph that says ``here is the arithmetic by
which it might; the measurement that would check it is X.''

**Risk.** The back-of-the-envelope number could be wrong by an order of
magnitude, which is worse than having no number. The paragraph must
explicitly invite the measurement rather than defend the estimate.

---

### R10 — State the thermodynamic barrier to simulating continuity in silicon

- [x] **Done 2026-09-01.** Thermodynamic-barrier paragraph (the Landauer bound for a
      discretised continuum simulation) before the sleep-inertia section. Pass record below.

- [x] **Objective.** Define the minimum Landauer heat cost a silicon
      architecture would incur to approximate a continuous coupling with
      sufficient resolution to satisfy `exhibits_phase_transition`, and
      state this as a falsifiable prediction about neuromorphic efficiency.

**Why.** The review's sharpest challenge: the current jump from ``finitely-
sited architectures register zero coupling energy in the continuum
functional'' to ``von Neumann architectures cannot be conscious'' is marked
as an informal argument. What is missing is the *positive* statement of
what such an architecture would have to pay to simulate continuity. If the
cost is bounded (a handful of Watts) the functionalist objection survives;
if it scales with required resolution to unphysical power densities, the
argument is strengthened. The framework's own results
(`fieldCorrelation_sited_eq_zero`, `rigid_gap`) supply the ingredients:
a finitely-sited kernel is invisible, and to be visible it must be spread
over cells of positive measure, each of which is a physical degree of
freedom that dissipates `k_B T` per Landauer erasure. The product —
number of cells × refresh rate × `k_B T` — is a lower bound on the
thermodynamic cost of simulating a continuum coupling. The number matters
less than the method: the framework supplies a way to compute it, and a
rival that cannot match it has no physical warrant for consciousness.

**What it takes.** A paragraph in the hardware corollary that derives the
bound: a discretisation with `N` cells of diameter `d` must refresh each
cell at the Nyquist rate of the field dynamics, and each refresh of a cell
that forgets (Landauer) costs at least `k_B T \ln 2`. The product grows
with the spatial and temporal resolution the continuum theorems require.
State the bound parametrically — `N`, `d`, refresh rate — and note that
for cortical parameters the bound is far below cortical metabolic costs,
while for a GPU-scale discretisation it may exceed the device's cooling
capacity. This is an estimate, not a theorem, and must be marked as such.

**Risk.** A rough calculation can be attacked on every parameter value. The
point is the existence of a *principled* bound, not any specific number.

**Done when.** A functionalist who claims ``silicon can be conscious because
it can simulate any continuum'' must first answer whether it can pay the
thermodynamic cost the bound states.

---

### R11 — Chart the Fokker–Planck path to the von Mises density

- [x] **Done 2026-09-01.** Fokker--Planck route (SDE → FP → McKean--Vlasov) added to the
      ``What remains not established'' paragraph, citing Sakaguchi and
      Strogatz--Mirollo. Pass record below.

- [x] **Objective.** Add a paragraph (in Derivation 7 or the supplement)
      stating the precise mathematical route from the stochastic Kuramoto
      SDE to the von Mises stationary density, so a reader sees exactly
      what gap the ``input'' label covers and what would close it.

**Why.** The review's observation: the von Mises stationary density is
taken as an input, its Fokker–Planck derivation is absent from Mathlib,
and the manuscript says only that Mathlib lacks the operator. A referee
who works in stochastic thermodynamics will want to know whether this is a
routine computation that nobody has done in Lean, or a genuinely open
problem (spectral stability of the Fokker–Planck operator, which is harder).
Naming the route — write the SDE, write the FP equation for the N-particle
density, factorise by exchangeability in the mean-field limit, apply the
known stationary solution of the resulting McKean–Vlasov equation, cite
Sakaguchi 1988 or Strogatz–Mirollo 1991 — would tell the reader that the
gap is formalization work, not mathematical discovery. The same paragraph
should state that nothing in this file depends on closing it: the threshold
`K_c = 2D` is proved conditional on the density, and conditional statements
are honest.

**What it takes.** Three to four sentences in Derivation 7's opening or
closing paragraph. No Lean.

**Done when.** A stochastic-processes referee who objects ``you assume the
stationary density'' finds a paragraph that says ``here is the route that
would derive it; it is standard in the literature and nobody has written it
in Lean; the theorem below is conditional on it and is stated as such.

---

## Pass record — 2026-09-01: manuscript-only clearout (S3, T1, T3, R2–R11)

All 13 open manuscript-only items from the post-review and pre-review queues
were closed in one session. No Lean code was touched.

### Closed

* **S3** — No hysteresis paragraph added to `main.tex` prediction section.
* **T1** — Figure~1 redrawn as a DAG (two independent roots n1, n2 → n3; n1→n2
  arrow removed). Caption states the two-root structure.
* **T3** — `simulations/check_tableS1.py` validates the status column against
  `Chain.lean`; wired into `.pre-commit-config.yaml` as `check-table`.
* **R2** — Propagation of chaos named as the gap between stationary threshold
  theorems and trajectory statements: one sentence in Derivation 4 closing
  paragraph (`main.tex`), one in supplement §7 close.
* **R3** — `UnifiedSelf` clarified with four numbered distinctions (what it
  means within Lean / not n10 / not any Banach fixed point / not psychological
  Self) in the existing ``The fixed point is the glued state'' paragraph.
* **R4** — Measurement protocol paragraph (``How to measure it'') specifying
  LFP/MEG estimates for $a$ and $r$ and the volume-proxy for $K(t)$.
* **R5** — Corollary scoping: explicit qualification of both `rigid_is_strictly_suboptimal`
  and `fieldCorrelation_sited_eq_zero` at the hardware section opening; ~5\%
  drift sentence in Fig~4 caption.
* **R6** — Zero-allowlist reaffirmed in `check_prose.py` docstring (no concrete
  case having arisen).
* **R7** — Dynamic Core and predictive-binding paragraph added after the
  IIT/GWT comparison.
* **R8** — Dynamic misalignment paragraph added after the rigid-suboptimality
  derivation, noting the static loophole closed by non-stationarity.
* **R9** — Modulatory-field paragraph added after the falsification conditions,
  giving the columnar-aggregation arithmetic for $K > K_c$.
* **R10** — Thermodynamic-barrier paragraph (Landauer bound for discretised
  continuum simulation) added before the sleep-inertia section.
* **R11** — Fokker--Planck derivation route (SDE → FP → McKean--Vlasov) added
  to the ``What remains not established'' paragraph, citing Sakaguchi and
  Strogatz--Mirollo.

### Gates (all clean)

* `main.tex` compiles: **62 pages, overfull 12, zero undefined.**
* `supplementary.tex` compiles: **19 pages** (was 15–16 with the new propagation-of-chaos paragraph).
* `check_prose.py` exits 0 on both files.
* `check_tableS1.py` exits 0.
* Prose check on supplementary.tex: passes.
* No Lean code touched; the applicable Lean gate (17,622 jobs, build clean) is inherited unchanged.


### T4 — leaf detector — 2026-09-01

**What was built.** `simulations/check_leaves.py`, a Python script that extracts top-level theorem/def/structure declarations per Lean module and greps the rest of the tree (excluding `Examples.lean` and `PhysicsOfConsciousness.lean`) for consumption. Reports modules whose *theorems* are referenced by nothing outside themselves and the witness module.

**Current leaves.** Three modules were reported as leaves: `Phase3_MeasureThermodynamics`, `Phase5_PhaseLifts` and `Phase5_TwistedGluing`. The last two are deliberate (F2 and F4 results not wired into `chain`). `Phase3_MeasureThermodynamics` may need a consumer; recorded here rather than fixed blind.

**Two defects in this pass, both repaired 2026-09-03 (V1 record).** The script exits 1 when it finds a leaf, and it found three — so the gate was *red on the tree that added it*, and every later Lean commit could only land because `pre-commit` is not installed here (`.git/hooks/pre-commit` does not exist) and there is no CI. A gate committed red is either inert or a permanent block; neither is a check. Second, the search ran over raw file text, so a name appearing in a *docstring* counted as consumption — which is the C1 shape itself, prose about a module standing in for use of it. Stripping comments exposes two further leaves, `Phase3_KLBound` and `Phase8_CriticalExponent`.

**Why module-level, not declaration-level.** C1's defect was per-module: a module imported for its *types* but none of whose theorems were consumed. Per-declaration reporting drowns the signal in noise.

**Wired into `.pre-commit-config.yaml`** as `check-leaves`, matching on `\.lean$`.

**Gates.** `ruff`, `mypy --strict` clean on the script. `lake build` untouched (17,624 jobs).


### R1 — `IsEMFieldCoupling` predicate — 2026-09-01

**What was built.** `PhysicsOfConsciousness/Phase9_EMIdentification.lean` defining a `structure IsEMFieldCoupling (sys : ContinuousNeuralField M) (K D : ℝ) : Prop` with four fields: `kernel_continuous`, `domain_positive_measure`, `coupling_nonneg`, `noise_pos`.

A witness `em_constant_kernel_is_em_field_coupling` on ℝ with a constant kernel (`K = 1`, `D = 1`) discharges the non-cortical conditions. `#print axioms` reports only the three.

**Integration into `Chain.lean`.** `E56` now takes a `ContinuousNeuralField` argument and returns `(FieldRealizes L K D ∧ Nonempty (IsEMFieldCoupling sys K D))`. `chain` threads the kernel through. The joint witness `chain_hypotheses_jointly_satisfiable` provides a trivial `cortexNeuralField` with a `MeasureSpace` instance (counting measure on `Site`) and a proof `cortexNeuralField_isEMFieldCoupling`. `#print axioms` on both witness proofs reports only the three.

**A `MeasureSpace` instance** was added for `Cortex` to satisfy the `[MeasureSpace X]` constraint `chain` and `E56` now carry.

**What this does not establish.** Not that cortex satisfies any condition. Not that continuity on ℝ is sufficient for the analysis theorems on a compact cortical manifold. `chain`'s `E67` retains the same interface and ignores the kernel predicate, because the threshold question depends only on the real-number sign conditions.

**Gates.** `lake build` clean, 17,624 jobs (was 17,620). `#print axioms` on both `em_constant_kernel_is_em_field_coupling` and `cortexNeuralField_isEMFieldCoupling` reports only `[propext, Classical.choice, Quot.sound]`. Zero `sorry`. `check_leaves.py` does not list `Phase9_EMIdentification` — the `IsEMFieldCoupling` structure is consumed by `Chain.lean`. `check_prose.py` and `check_tableS1.py` pass (no manuscript changes in this pass).

**Three corrections to this record, made 2026-09-03 (V1 record).** (i) The pass was *not* warning-free and the warnings were *not* pre-existing: adding `[MeasureSpace X]` beside the existing `[MeasurableSpace X]` created an instance diamond that the `overlappingInstances` linter flagged in both `chain` and `e56_of_eq`, and giving `e56_of_eq` an `X` pulled three unused section variables into it. Standing rule 7 says zero warnings; this pass had three. (ii) "The predicate is deliberately uninhabited for the physical case" is contradicted by `cortexNeuralField_isEMFieldCoupling` in the same commit. What is true is weaker and worth saying plainly: no object in the development denotes cortex, so no witness is a cortical witness. (iii) The predicate as first written did not constrain the identification. `coupling_nonneg` and `noise_pos` were about the free scalars `K` and `D`; the only condition on `sys` was continuity of its kernel, so the identically-zero field discharged it — and that is the field the `Cortex` witness used.


### V1 — audit of T4, R1 and (A), and the repairs — 2026-09-03

**Why.** The three preceding passes were verified rather than trusted: `lake
build` re-run from the committed tree, `#print axioms` re-run on every new
result, every gate re-run, and each ledger claim checked against what the code
does. The build claims held exactly — 17,624 jobs, exit 0, zero `sorry`, only
`propext`, `Classical.choice`, `Quot.sound`. Five things did not, and are fixed
here.

**1. Standing rule 7 was violated and the record said otherwise.** R1 introduced
three build warnings and the record called them pre-existing. `chain` carried
`[MeasurableSpace X]` and `[MeasureSpace X]` together, which puts two σ-algebras
on `X` that nothing forces to agree; the linter is right that this is a diamond
and it was not there before R1. **Fix:** `chain` takes `[MeasureSpace X]`
and `[BorelSpace X]`, the measurable structure coming from the measure, and
`e56_of_eq` is stated over its own `M` instead of borrowing `X` and its three
unused section variables. Build is warning-free.

**2. The predicate did not constrain the identification.** With `K` and `D` free
scalars and only continuity asked of the kernel, a field coupling *nothing*
satisfied it — and did, in the `Cortex` witness. **Fix:** `IsEMFieldCoupling` is
now stated over a `StochasticNeuralField` and has six fields, of which three are
new and load-bearing: `domain_probability` (the substrate is normalised, the
hypothesis `mean_field_coupling` needs to be a strength rather than a size),
`coupling_is_mean_field` (`K` *is* the kernel averaged over both arguments), and
`no_site_dominates` (no single site contributes more than half of `K` — the
manuscript's *modulatory* claim, in formal dress, and the condition a
vertex-supported kernel fails). `noise_is_field_noise` ties `D` to `sys.D`, so
`noise_pos` is now derived from the field rather than assumed.
`not_isEMFieldCoupling_of_zero_kernel` is kept as the regression: the old
witness is no longer accepted. The `Cortex` witness is a uniform kernel of
strength 3 on the three sites under normalised counting measure, so `K = 3` and
`D = 1` are produced by the field instead of declared beside it, and
`cortexNeuralField_exhibits_phase_transition` falls out.

**3. The second conjunct of `E56` was inert.** `chain` bound it and used only
`.1`. **Fix:** `exhibits_phase_transition_of_isEMFieldCoupling` (Phase 9) and
`em_field_exhibits_phase_transition` (Chain) consume it together with `E67` to
conclude `exhibits_phase_transition` for the field `E56` names — a statement
about a substrate, which `FieldRealizes`'s three reals cannot express. The
identification hypothesis now has a consumer.

**4. R1's fourth "done when" was not met.** `Phase9`/`IsEMFieldCoupling` appeared
nowhere in the publication. **Fix:** `main.tex` §"What the formal statement
demands" states the five conditions a model must exhibit and names the
regression and the consumer; Table S1's EM row reads "Conditions formalized; the
identification itself not derived" instead of "Not formalized and not derived",
which had stopped being true.

**5. The leaf gate was red and could be fooled by prose.** See the two paragraphs
added to the T4 record. **Fix:** `check_leaves.py` strips Lean comments before
searching, so a docstring mention no longer counts as consumption, and carries
`ALLOWED_LEAVES` — the five modules that are leaves today, each with its reason
— failing on any leaf outside that set *and* on any recorded entry that has
since acquired a consumer, so the baseline cannot rot quietly. Two of the five
(`Phase3_KLBound`, `Phase8_CriticalExponent`) were invisible before the comment
stripping.

**Also.** `(A)`'s manuscript sentence claimed agreement at the incoherent state
made propagation of chaos the *only* remaining gap; one configuration does not
support that, and both `main.tex` and the ranked item now say what the theorem
says. The `vulture` hook had been unrunnable since the repository was renamed
(console-script shebangs pointed at the old path) and, once runnable, walked
`.venv` into a `RecursionError`; `[tool.vulture] exclude = [".venv/"]` in
`simulations/pyproject.toml` fixes the second, reinstalling the scripts the
first. It now reports six pre-existing findings in `empirical_collapse.py`,
`fermi_estimate_check.py` and `mesh_refinement.py` — untouched here, since
`empirical_collapse.py` has uncommitted work in it.

**Not done, deliberately.** The `MeasureSpace Cortex` instance stays in
`Chain.lean` rather than moving to `Examples.lean` where standing rule 2 would
put a witness: a global measure instance on `Cortex` would enter instance
resolution for `Examples.lean`'s own measure-theoretic proofs, and the risk is
not worth the tidiness. `pre-commit` is still not installed on this machine, so
every gate here is manual; installing it would make `vulture`'s six findings
block the next Python commit, which is the author's call rather than this pass's.

**Gates.** `lake build` clean, 17,624 jobs, **zero warnings**, zero `sorry`.
`#print axioms` on all twelve of the results touched or added
(`isEMFieldCoupling_const`, `em_unitInterval_isEMFieldCoupling`,
`exhibits_phase_transition_of_isEMFieldCoupling`, `IsEMFieldCoupling.noise_pos`,
`IsEMFieldCoupling.domain_positive_measure`, `em_field_exhibits_phase_transition`,
`cortexVolume_singleton_le`, `cortexNeuralField_isEMFieldCoupling`,
`cortexNeuralField_exhibits_phase_transition`,
`not_isEMFieldCoupling_of_zero_kernel`, `chain`,
`chain_hypotheses_jointly_satisfiable`) reports only the three.
`check_leaves.py`, `check_prose.py`, `check_tableS1.py` exit 0; `ruff`,
`ruff format --check` and `mypy --strict` clean on `check_leaves.py`.
Compile gate against `HEAD`: `main.tex` 13 overfull hboxes against 14, 66 pages
against 66, zero undefined references or citations; `supplementary.tex` 9
against 9, 21 pages against 21.


### T2, standing item 2, and V1's loose ends — 2026-09-03

**The item asked for the wrong thing, and the record should say so first.** T2
read: rank the eight named hypotheses by cost and discharge the two cheapest,
because "the count is the paper's checkable number, so lowering it is a
checkable improvement." The two cheapest were `E34` and `E78`, and they were
cheap for a reason the item did not anticipate. Both concluded
`Nonempty (SomeStructure)` — a predictive dissipation structure, a thermodynamic
cover — and both structures were already inhabited at the types the joint
witness uses. `fun _ => ⟨frozenSystem⟩` and `fun _ => ⟨cortexCover⟩` were proofs
of them, and they were the proofs the joint witness had been using since C1.
Executing T2 as written would have taken the count from eight to six by proving
two things that say nothing, and the number the manuscript offers a reader would
have got *better* while the development got worse. So the pass did the opposite:
it strengthened both edges until the old discharges fail, and left the count at
eight. Standing rule (todo.md:257) is the authority for that choice — "a
restatement is worse than a named hypothesis, because it looks like content" —
and V1's repair of `IsEMFieldCoupling` is the precedent for the shape.

**E34 — Landauer's heat is the budget Still's bound is drawn against.**

New module `PhysicsOfConsciousness/Phase3_LandauerBridge.lean` (309 lines).
`erasedEntropy t = entropy id - entropy t`, with `erasedEntropy_nonneg`,
`erasedEntropy_pos_of_erasure`, and `erasedEntropy_eq_zero_of_injective`.
`PredictiveDissipation.ofLandauer` builds a predictive structure from a finite
register with a bipartite environment: `thermalEnergy` is the system's
temperature, `dissipatedWork` is `heat_dissipation t`, and `still_bound` — the
irreducible postulate of `Phase3_PredictiveThermodynamics` — is **derived** from
`landauer_bound`. One postulate at that joint instead of two.

What the constructor asks for is the identification
`(nonpredictiveInfo μ κ).toReal ≤ erasedEntropy t`: the memory that fails to
predict is no larger than the entropy the update destroys. Nothing derives it —
`μ`, `κ` and `t` are otherwise unrelated — and it is not free:
`nonpredictive_eq_zero_of_injective` shows a *reversible* register cannot pay for
a single wasted bit, which is the Norton–Shenker distinction arriving from the
informational side.

`Examples.lean` §18.5 is the witness. It needed the *value* of the mutual
information of §18's two-bit law, which §18 had proved non-zero and finite and
never computed: `klDiv_corrJoint = ENNReal.ofReal (log 2)`, via the explicit
density against the product law (`corrJoint_eq_withDensity`),
`Measure.rnDeriv_withDensity`, and `integral_fintype`. Then
`erasedEntropy (fun _ : Bool => true) = log 2` — the register of the chain
witness erases exactly one bit — so the identification holds with **equality**
and `landauerSystem_tight` records that the bound is attained.

`E34` now reads: a dissipating register carries a predictive structure whose
thermal scale is its own temperature, whose dissipated work is its own Landauer
heat, and whose wasted memory is non-zero. `frozenSystem_not_of_eraser` is the
regression: dissipated work `0` against a Landauer heat of `log 2`, and no waste
at all. `e34_boolEraser` discharges the strengthened edge on the one-bit eraser,
and the joint witness uses it.

**E78 — a cover that is reached, at the coupling the coherent regime names.**

`ThermodynamicCover.IsReachedByRelaxation T c` (`Phase5_EquilibriumBridge.lean`):
`c` is a floor on the cover's coupling matrix, and the cover's phase field is the
limit of a Kuramoto trajectory on that matrix started inside §7's basin.
`ofConvergentTrajectory_isReachedByRelaxation` proves the constructor produces
covers satisfying it, at its own `a`.

`E78` now reads `Coherent K D → ∃ T, T.IsReachedByRelaxation K`. The conclusion
mentions `K`, so it cannot be discharged uniformly in `K` by whatever cover is
lying around. `Examples.lean` §17.2 supplies the witness: `trioCover3`, the same
three sites and the same initial data as §17.1 at coupling `3`. The numerical
content does not change and the reason is worth recording — excess and threshold
both scale with the coupling, so `2·excess < a` reduces to `cos ½ > ¾` at every
strength. Two fences: `trioCover_not_reachedByRelaxation_three` (a cover that
*is* reached, at unit coupling, fails the floor at `K = 3`) and `cortexCover`,
which meets no relaxation condition at all and was the old discharge.

`trioSync` is now `trioSyncOf trioLimit`, the phase field being the only thing
§17.2 needs to vary; the overlap-agreement proof does not mention the phase,
which is why the parameter costs nothing.

**What E78 still does not do.** It is not derived. Nothing produces initial data
in the basin from a coherent order parameter, and the scale mismatch — n7 is
about a continuum mean field, `ThermodynamicCover` about a finite index set — is
where the edge sits. The strengthening makes that mismatch visible in the type
rather than in a paragraph.

**A seam this pass exposed and did not close.** `chain` takes the cover from
`e78` only to produce `Unity X` and lets `e89` produce a cover of its own; the
joint witness now uses `trioCover3` for the first and `cortexCover` for the
second. Nothing forces them to be the same cover. `UnifiedSelf` is about the
section `e89` names, so the conclusion is unaffected, but "the unity that is
witnessed" and "the unity that is glued" are not tied together by the type.
Recorded, not fixed.

**Standing item 2 — `section_agrees_of_phase_eq`, read and fenced.**

`Examples.lean` §20. `restrict_eq_iff_densityOn_eqOn` proves the categorical
condition equivalent to the pointwise one: two patch sections have the same
restriction to their overlap exactly when they assign the same mass to every site
they share. So Derivation 5's second physical hypothesis says that patches at a
common phase carry a common local density where they meet, and nothing is hidden
in the sheafification. `overlap_agreement_fails` exhibits what it excludes: §4's
two-patch cover, one phase, two profiles differing at the shared site — every
other requirement of `LocalSectionSynchronization` met, this one false.

It stays a hypothesis, and the honest reason is structural. Stated abstractly,
"the local law is a function of the phase" *is* the class field: the only way to
compare two patches' laws is the restriction maps, so there is nothing above the
field to derive it from. What §20 adds is that the field is a claim about
densities rather than about sheaf machinery, and that it is a restriction rather
than a formality. Note also what it does not say — the three-patch witness
carries three pairwise-different profiles and satisfies it, because they differ
only off the overlaps. Agreement on overlaps is consistency, not sameness, which
is the room F2's content question lives in.

**V1's three loose ends.**

1. **`Phase3_MeasureThermodynamics` had no consumer.** It has one now, and the
   consumer is a statement worth having: at counting measure on a finite
   register its `continuous_entropy` *is* `boltzmann_entropy`, its
   `is_dissipative` is non-injectivity, and its `landauer_heat_bound` is
   `T · erasedEntropy t` (`Phase3_LandauerBridge` §3, four theorems ending in
   `measure_heat_pos_of_erasure`, which fires `dissipative_implies_heat` on an
   erasure). The two statements of Derivation 2 are checked against each other
   rather than coexisting. `ALLOWED_LEAVES` drops from five entries to four.
2. **`vulture`'s six findings.** Already repaired in the working tree before this
   pass; `uv run vulture .` exits 0 and the fix in `mesh_refinement.py` is a
   transcription check rather than a deletion.
3. **`pre-commit` was not installed.** It is installed —
   `.git/hooks/pre-commit` exists — and `pre-commit run --all-files` passes all
   ten hooks. Every gate below therefore also ran automatically.

**Gates.** `lake build` clean, **17,626 jobs**, zero warnings, zero `sorry`.
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` on all
sixteen results touched or added (`erasedEntropy_eq_zero_of_injective`,
`nonpredictive_eq_zero_of_injective`, `PredictiveDissipation.ofLandauer`,
`landauer_heat_bound_count_eq`, `measure_heat_pos_of_erasure`, `klDiv_corrJoint`,
`memory_toReal`, `erasedEntropy_boolEraser`, `landauerSystem`,
`landauerSystem_tight`, `frozenSystem_not_of_eraser`,
`ofConvergentTrajectory_isReachedByRelaxation`, `trioCover3`,
`trioCover3_reachedByRelaxation`, `trioCover_not_reachedByRelaxation_three`,
`e34_boolEraser`, `chain`, `chain_hypotheses_jointly_satisfiable`).
`#check @chain` still lists eight `E..` arguments.
`check_leaves.py`, `check_prose.py`, `check_tableS1.py` exit 0; `ruff`,
`ruff format --check`, `mypy --strict`, `bandit`, `vulture`, `xenon`, `tach`
clean. Compile gate against `HEAD`: `main.tex` **13 overfull hboxes against 13**,
69 pages against 68, zero undefined references or citations;
`supplementary.tex` 9 against 9, 22 pages against 21, and its 26 undefined
citations are the pre-existing ones (the supplement cites the main
bibliography).

**Manuscript.** `main.tex`: a paragraph in the introduction on what a named
hypothesis has to demand and why bare existence is not enough, with both
regressions named; a Derivation 3 paragraph on Landauer's heat as Still's budget,
the reversible-register fence, and the attained bound; a Derivation 5 paragraph
on the pointwise reading of the compatibility hypothesis and the data it
excludes; two Table 1 rows extended. `supplementary.tex`: an implementation note
under the Landauer section covering the bridge and the counting-measure
specialisation; the same pointwise reading added to the Derivation 5 note; three
Table S1 rows extended. `CHANGELOG.md` carries the claim that is no longer made.

### T5 — non-trivial structural-edge witnesses — 2026-09-03

**Red.** Three compile-time examples required witnesses of `E12 Bool
(DynamicalVacuum wellV) kink`, `E23 (DynamicalVacuum wellV) kink (fun _ : Bool
=> true)`, and `E45 Bool Bool Bool t5_refiningEnergy 3`. `lake env lean
PhysicsOfConsciousness/Chain.lean` failed on the three unknown witness names.

**Green.** `t5_e12_doubleWell` consumes `kink_leaves_vacuum`, whose field joins
the two distinct minima of `wellV` and crosses the barrier. The same premise is
threaded into `t5_e23_absorbingRegister`; its refreshed one-bit update has an
unreachable state and is the eraser already charged by `e34_boolEraser`.
`t5_refiningEnergy` uses the uniform triangulations and tent integrand of
`Examples.lean` §6, translated by a constant so its proved continuum limit is
3. `t5_refiningEnergy_moves` proves its first two approximants differ, fencing
the former constant-sequence discharge. The joint witness now uses all three.

**Scope.** This closes the requested non-triviality defect in each remaining
edge witness. It does not turn the conditional schema into a physical
derivation: the types still do not identify the double well, bit register,
refining mesh, and cortical cover as one physical object. The theorem therefore
retains the deliberately narrow name `chain_hypotheses_jointly_satisfiable`.

**Gates.** `lake build` clean, 17,626 jobs. `#print axioms` on all five new
results and `chain_hypotheses_jointly_satisfiable` reports only `propext`,
`Classical.choice`, and `Quot.sound`. All ten pre-commit hooks pass, including
the prose, Table S1, and leaf-module gates. `git diff --check` passes and
`tasks/todo.md` has no unchecked boxes.
