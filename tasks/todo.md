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

Those are C1–C5 and P1–P4 below. They are the whole of the open work.

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

**Lean.** 13,939 lines across 20 modules. Zero `sorry`. Zero declared axioms.
`Examples.lean` is 4,580 lines and carries 20 witness sections plus §6.1 and
§17.1. `lake build` clean, 17,614 jobs.

**Manuscript.** `main.tex` 86 pages, overfull 18; `supplementary.tex` 15,
overfull 8; merged arXiv build 46 pages, overfull 0. Six figures, a methods
section, and Table S1 carrying the claim-by-claim identifier map.

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

## Work items — take ONE at a time, in this order

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

- [ ] **Objective.** For each edge C1 leaves as a named hypothesis, a docstring
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

- [ ] **Objective.** Make the manuscript say what C1–C4 established, and stop
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

- [ ] **Objective.** Make rule 8 mechanical, so it survives the next agent that
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

- [ ] **Objective.** Create the repo-side destination rule 8 presupposes. There
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

- [ ] **Objective.** Both publication files state the current theory only.

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

- [ ] **Objective.** `AGENTS.md` gains rule 8 as a numbered section.

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

## Open, ranked — carried forward, none blocking

Carried from the O10/O16 record. Nothing here is scheduled ahead of C1–C5 and
P1–P4.

1. **(A) The static order-parameter link.** Connect `order_parameter_complex`
   (`Phase4`, the empirical average `(1/N) ∑ e^{iθⱼ}`) to `circularOrderParameter`
   (`Phase8`, an integral against a density) for a *fixed configuration*. This is
   a quadrature statement of the kind `Examples.lean` §6.1 proved for
   `discreteEnergy`, not a limit theorem about a dynamics. Cheapest true instance:
   the incoherent state, where both are `0` and the discrete one exactly so, by
   the vanishing of a sum of `N`-th roots of unity. **It has a claim attached** —
   it would establish that the dynamical limit (B) is *all* that stands between
   Derivation 7's threshold theorems and the finite system. Note that C1 and C3
   may change this item's shape; re-read it after C3.
2. **`section_agrees_of_phase_eq`** — the `LocalSectionSynchronization` hypothesis
   that synchronised patches agree where they overlap. Unchanged in rank and in
   shape. See the W6 record for why it is *not* "the move W1 made".
3. **The PRX Life presubmission inquiry** — on hold at the user's instruction as
   of 2026-08-31, not withdrawn. Do it after P3: the changelog is the first thing
   an editor would notice.

**The sleep-inertia prediction is weaker than the manuscript implies, and this is
not yet an item.** Recorded here so it is not lost. Any two-timescale model with
a slow gate produces a delayed sigmoid, and the paper concedes it uses only the
*existence and continuity* of the coherent branch, not `K_c = 2D`. So the
prediction discriminates against a one-timescale electrical account and against
nothing else. Either sharpen it — find a quantitative signature that needs the
bifurcation rather than merely a saturating nonlinearity — or scope the claim in
the discussion to what it is. Do not schedule this ahead of C1–C5 and P1–P4; do
not let the discussion keep overselling it either.

**The unfrustrated-uniqueness objection, likewise recorded and not scheduled.**
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
