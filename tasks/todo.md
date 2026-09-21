# Working ledger

**Superseded ledgers are read out of git history, not kept in the tree**
(AGENTS.md §5). The M/W/X/Y/Z/G ledger — publication alignment, the winding
state, the amplitude field, the winding rows' scope limits, conditional-to-
falsifiable, and the cover and the region — closed in full, is
`8d8ce0f:tasks/todo.md`. The P submission-readiness items and the pass records
before it are `dde1a36:tasks/todo.md`. The R research programme (R1–R12) is
live in `tasks/research_programme.md`.

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

- [ ] **C5 — Decline super-Turing computation, in the publication.** Real-valued
      weights buy unbounded capacity only at infinite precision, and any `D > 0`
      destroys it. The paper's own noise floor is the reason, which makes one
      sentence in `sec:gpu` or `sec:scope` cheaper than the objection it
      pre-empts. Present tense: what the noise regime costs an analog account,
      not what anyone once hoped for it.

### What is electromagnetic, and what is not

- [ ] **C6 — Say the development is substrate-neutral.** `sec:unconditional`
      claims substrate-independence for five results; the conditional chain
      E56–E89 is equally substrate-neutral modulo calibration, and
      `Phase9_EMIdentification`'s own scope note says so. Stating it costs
      nothing, widens the audience, and is more accurate than the present
      silence. Lands in `sec:scope`, with the `no_site_dominates` vacuity on a
      nonatomic substrate named where Table S1's E56 row already discusses the
      predicate.

- [ ] **C7 — Separate EM falsification from field falsification.** The
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

- [ ] **C8 — The deadline bound, quantitative.** The highest value per line in
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

- [ ] **C9 — Landauer forced by the memory budget, not chosen by the
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

- [ ] **C10 — The interconnect corollary.** Contrapositive of `card_ball_le`:
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

- [ ] **D4 — The resource-matched comparison `Phase7_Rigidity` §3 lacks.** C2
      supplied the prerequisite floor; this is the thing it was a prerequisite
      for. **The sign of the result is not predictable and this item is not to
      be written as though it were.** Once `b` is a real number the comparison
      may well come out ambiguous, or favourable to the machine candidate. That
      is a reason to do it — a comparison whose outcome is assumed is not a
      comparison — and a reason not to promise in advance what it shows. Note
      that §3's two existing comparisons are neutralized by controls this
      repository supplies against itself (`fieldCorrelation_cellKernel`,
      `no_forced_gap_of_best_wired`), and those controls stay.

- [ ] **D5 — Say the asymmetry in the publication.** Once D1 and D2 exist,
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
