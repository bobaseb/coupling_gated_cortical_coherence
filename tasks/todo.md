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

**Ordering.** C1 and C3 are the highest value per line — C1 because the theorems
are nearly assembled, C3 because it fixes a real asymmetry in how `sec:gpu`
reads. C2 is the foundation the resource-matched comparison needs and should
precede any strengthening of `Phase7_Rigidity` §3. C4 is independent. C5–C7 are
publication-only and can go in one editorial pass.

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
