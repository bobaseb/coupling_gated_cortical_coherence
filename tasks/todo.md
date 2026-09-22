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

- [ ] **G1 — Bootstrap the delay exponent over replicas.**
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

- [ ] **G2 — Larger-N and tighter-threshold delay runs.**
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

- [ ] **G3 — Fix the installed-energy inconsistency: derive stored field
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

- [ ] **G4 — Reframe the "unconditional results" with Kuramoto citations.**
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
          2014 (survey on synchronization), Wiley, Strogatz & *Girvan* 2006
          (twisted/winding states, r=0).
      (c) For K_c = 2D (main:150), add Strogatz & Mirollo 1991 and
          Acebrón 2005 alongside Sakaguchi 1988.
      (d) Correct the propagation-of-chaos scope: cite Dai Pra & den Hollander
          1996 and Bertini, Giacomin & Pakdaman 2010. Replace "is a research
          programme rather than a lemma" with a properly scoped sentence in the
          supplement.
      (e) Verify all new references via web search before commit.
      **Verify:** `check_prose` and `check_hedging` pass; new citations are in
      `.bib`; all verified via web search.

- [ ] **G5 — Add neural inertia literature and operationalise the emergence
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
          *discriminating* content is the spatial onset pattern — coherence
          should nucleate in regions of highest κ (mode density × field
          strength), not uniformly.
      (b) Rewrite §9.3 as a concrete protocol sketch: manipulate emergence
          rate v via propofol infusion rate (within-subject, multiple rates);
          measure time-to-response as the observable (not ΔK); specify that
          the discriminating test is the *spatial* signature (high-density
          ECoG or Neuropixels), not the exponent alone.
      (c) State the competing null: any supercritical bifurcation gives ~0.5.
          The field hypothesis predicts *where* coherence nucleates (high-κ
          regions) and that onset correlates with local field amplitude.
          A synaptic-only model predicts onset at hub nodes of the connectome.
          These are distinguishable with high-density intracranial recordings.
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

- [ ] **G9 — Thermodynamic section: derive continuous dissipation rate for
      maintaining coherence.**
      *Review concern: Major §6.* The thermodynamic chain states its own regime
      is "two-bit systems with interaction energies of order k_BT" and that
      "cortex is not in it." The reviewer says to cut it.
      **Preferred alternative: derive a non-trivial bound that applies at the
      cortical scale.**
      **Action:**
      (a) *New derivation (Lean + simulation):* In the non-equilibrium steady
          state of the noisy Kuramoto system, maintaining phase order r > 0
          requires continuous entropy production. Derive a lower bound on the
          dissipation rate: Ẇ_diss ≥ f(D, r, K). The key insight is that noise
          D continuously destroys coherence and coupling K continuously restores
          it, so the system must dissipate at a rate proportional to the noise
          power times the maintained order.
          - Lean: extend `Phase8_ContinuousField.lean` (`entropy_production_rate`
            already exists). The theorem should say: if a noisy Kuramoto system
            maintains time-averaged order ⟨r⟩ ≥ r₀ > 0 with noise D, then the
            time-averaged dissipation rate satisfies Ẇ ≥ h(D, r₀).
          - Simulation: verify numerically in `dynamic_ramp.py` or a new script
            that the bound is tight to within an order of magnitude.
      (b) *Fallback:* If the Lean derivation proves too ambitious for this
          revision cycle, compress §7 to a paragraph in the main text citing
          the Landauer bound, its macroscopic slack, and the continuous-
          dissipation open question. Move the full chain to the supplement.
          State the open question: "a non-trivial thermodynamic bound on
          cortical coherence maintenance is an open problem."
      (c) *Thermodynamic speed limits (stretch goal):* Use thermodynamic
          uncertainty relations (TURs) to bound the ramp speed dK/dt by the
          entropy production rate σ̇. This would connect the dynamic
          bifurcation delay directly to metabolic cost. If achieved, this is
          the section's strongest result and justifies its place in the main
          text.
      **Verify:** If (a): `lake build` passes, audit footprint unchanged,
      new theorem has Table S1 row, simulation validates the bound. If (b):
      §7 is ≤ 1 paragraph in main text, full chain in supplement.

- [ ] **G10 — GPU/LLM section: derive non-trivial attention-rank bound.**
      *Review concern: Major §6.* Current theorems are pigeonhole
      (`card_le_card_tokens`) and basic DAG reachability
      (`mask_ball_subset_le`). The reviewer calls these trivial.
      **Preferred alternative: prove a non-trivial approximation bound.**
      **Action:**
      (a) *New derivation (Lean):* An attention matrix A = softmax(QKᵀ/√d_k)
          has effective rank ≤ d_k. A full-rank continuous spatial coupling
          kernel K(x,y) (e.g. exponential decay) has Mercer eigenvalues
          λ_1 ≥ λ_2 ≥ … The approximation error of a rank-d_k projection is
          bounded below by Σ_{i>d_k} λ_i. This is a genuine structural
          limitation of attention relative to continuous-field coupling.
          - Lean: add to `Phase6_Locality.lean` or a new
            `Phase6_AttentionRank.lean`. The theorem should say: for any
            rank-d attention map on N positions, the L²-approximation error
            against a kernel with eigenvalue tail Σ_{i>d} λ_i is at least
            that tail sum.
          - This is the spectral approximation theorem (Eckart-Young-Mirsky)
            applied to the kernel-vs-attention comparison. Non-trivial because
            it gives a *quantitative* gap, not just "digital can't do it."
      (b) *KV-cache information bottleneck (secondary):* Formalize that
          emitting token y_t ∈ V transmits at most log₂|V| bits about the
          internal state, bounding the channel capacity of the output interface.
          This strengthens `card_le_card_tokens` from a counting bound to an
          information-theoretic one.
      (c) *Fallback:* If neither Lean derivation lands in this revision cycle,
          compress §6 to a paragraph in the main text and move the full
          analysis to the supplement. State: "the causal mask and token
          cardinality impose structural limits; the quantitative gap between
          low-rank attention and full-rank spatial coupling is an open
          formalization target."
      **Verify:** If (a): `lake build` passes, audit footprint unchanged,
      new theorem has Table S1 row. If (c): §6 is ≤ 1 paragraph in main text.

---

### P3 — Biological realism, prose, and minor concerns

- [ ] **G11 — Heterogeneous-frequency control on the delay scaling.**
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

- [ ] **G14 — Minor citations and data availability.**
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

*To be filled as items complete. Format: G# — date — outcome — proof hook
results.*
