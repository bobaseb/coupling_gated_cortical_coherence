# Physical unity — U0 outline (2026-09-25)

Design note for the U block of `tasks/todo.md`. Working record, not publication
prose.

## Vehicle (decisions for the author)

- **New manuscript, same repository.** Start from scratch in a new directory
  (`unity/main.tex`, confirmed by the author 2026-09-25; own bibliography,
  own macro file), reusing the
  Lean library and simulation scripts as they are. The claims differ enough
  that editing the current paper into this one would reproduce the hedging it
  accumulated.
- **Do not archive the current paper.** `main.tex`, `supplementary.tex` and
  their PDFs are linked from `README.md` and `index.html`, and are wired into
  `check-pdf-freshness`, `check-figures`, `check-arxiv-freshness`,
  `check-table-coverage` and `check_tableS1.py`. Moving them buys nothing and
  breaks five gates. Freeze it instead, post it (arXiv) as the technical
  companion, and cite it for the synchrony-vs-content results. Whether it also
  goes to *Neuroscience of Consciousness* after N19 is the author's call.
- **Venue:** open until U3 and U7 are settled. The paper is theory plus a test
  protocol; pick the venue once it is known whether the kernel-tail result
  (U2) survives the numerics.

## Thesis

Human conscious experience is unified; unity requires that agreement between
the brain's local descriptions of a shared situation be **physically
enforced** — produced and maintained by a coupling in which graded states of
one region continuously pull the others toward agreement. Current AI
hardware computes agreement instead: its digital abstraction makes the
content level causally closed and insensitive to graded physical state, so
agreement there is routed, never enforced. The paper states this as a premise,
motivates it from human data, derives what follows, and specifies the
measurements that could refute it on either substrate.

## Premise P, and why the first formulation failed

U7 as first written ("closure excludes enforcement") is **false**. A GPU
running a consensus algorithm, or a Kuramoto simulation, has a closed logical
level whose dynamics `g` contracts overlap discrepancy. Contraction of
discrepancy at the content level is computable, so it cannot separate the
substrates. The separating property sits one level down:

- A digital system's content map is **locally constant** in micro state on
  its operating set (every micro state away from a switching threshold):
  noise margins restore every sub-threshold perturbation to the same logical
  value, per bit, toward that bit's own value. Its only physical restoring
  forces are *local self-agreement*. Cross-region influence exists only
  through logical transitions.
- A field-coupled system's content in region B depends **continuously and
  non-trivially** on the graded micro state of region A, and that dependence
  drives the two toward agreement.

So:

> **P (physical unity).** A system's contents are unified only if the content
> of each region depends continuously on the graded physical state of the
> regions it overlaps, through a coupling that contracts their disagreement.

P is an explicit **rejection of functionalism about unity**: a perfect
simulation of the field reproduces `g` and fails P. That is the paper's
substantive, contestable commitment, and it is stated as such, on the same
footing as IIT's axioms or the workspace's identification of consciousness
with broadcast. The simulation objection is answered head-on, not in a
footnote.

## Definitions (for the Lean and the text)

- System: micro dynamics `f : X → X`, regions `A_i`, micro state per region
  `x_i`.
- Content coarse-graining `π_i : X → C_i`; overlaps as in the decodability
  cover (companion paper, `Phase5_ContentCover`).
- **Closed:** there is `g` with `π ∘ f = g ∘ π`.
- **Margin (digital abstraction):** each `π_i` is locally constant *on an
  open operating set `M`* — every micro state in `M` has a neighbourhood on
  which `π_i` is constant — and correct operation keeps `f x ∈ M`. Not
  "locally constant everywhere": on a connected micro-state space (a voltage
  continuum) that forces `π_i` to be constant, so the margin can only hold
  off the thresholds.
- **Graded dependence:** `π_j ∘ f` is not locally constant in `x_i` for
  overlapping `i ≠ j`.
- **Physically enforced agreement:** graded dependence, and the overlap
  discrepancy contracts under `f` for sub-threshold perturbations as well as
  logical ones.

## Results

Reused from the companion (proved; Lean names as in the library):

1. Synchrony does not fix content; compatibility is separate
   (gluing, `section_agrees_of_disjoint`, `glue_unique_of_disjoint`).
2. Choosing the cover can empty any agreement claim (D3); the decodability
   cover is the answer, and applies to cortex and machine alike.
3. Deadline: agreement cannot arrive before the causal cone allows
   (`not_reconstructs_of_outside_past`, `Phase6_Locality.lean:432`); a
   full-support kernel reaches every site in one round
   (`not_outside_past_of_isFullSupport`, `:602`); a causal mask never reaches
   forward at any depth (D1); the wiring a deadline costs (`card_ball_le`, C10).
4. Worst-case chaining through overlapping patches (V3) and the locked
   spectral route (V4, `compatible_of_patch_nerve`).

New targets:

5. **Margin theorem (U7, revised).** If `π_j` has a margin on `M`, `f` is
   continuous and `f x ∈ M`, then no sufficiently small perturbation of any
   one region at `x` changes the next content; graded dependence fails, so P
   fails. Proved: `Phase10_PhysicalUnity.not_physicallyEnforced_of_margin`,
   with the margin discharged for any finite word of thresholded continuous
   quantities (`not_physicallyEnforced_of_bits`). Small and true. Its content
   is not the proof but the observation that the margin is exactly what
   digital engineering designs in.
6. **Typical-case agreement (U1–U2).** `Var(θ_a − θ_b) = D·R_eff(a,b)` in the
   harmonic approximation; logarithmic decay on a 2D sheet with short-range
   coupling, distance-independent agreement with a power-law tail slower
   than `r^−4`. Gives the field a role about kernel shape, not strength.
   Proved without the approximation (`Phase10_AgreementResistance`):
   Rayleigh monotonicity, the direct-edge cap and the Lipschitz transfer to
   content; the identity itself and the log growth are numerical (U3).
7. **Unity window (U8).** Lower edge from result 3, upper edge from the
   relaxation rate of result 6.

## Tests

- **Graded cross-region dependence in cortex.** Sub-threshold perturbation of
  region A (weak tACS/tDCS, micro-stimulation below the behavioural threshold)
  shifts the content decoded in overlapping region B, gradedly and toward
  agreement. The weak-field literature (`frohlich2010`, `anastassiou2015`)
  supplies the mechanism class.
- **Agreement as attractor on both substrates (U10).** Perturb one region;
  measure restoration of agreement and its rate. In a transformer: activation
  patching below and above the scale at which the logical trajectory changes.
- **Field causal-cone signature (U9).** Re-agreement faster than axonal
  conduction plus synaptic delay.
- **Kernel tail (U2).** Tail exponent of the effective coupling kernel.

## What would sink it

- Cortical content turns out effectively digital: sub-threshold perturbations
  in A leave decoded content in B unchanged (content states behave as
  locally constant coarse-grainings). Then P denies unity to humans and P is
  false.
- Discrepancy vs distance on the sheet grows linearly, not logarithmically
  (U3): the field-tail route to cortical-scale agreement fails.
- A system P classifies as unified by construction (coupled pendulums, analog
  circuits) — acceptable, since P is necessary, not sufficient; stated, not
  hidden.
- **Split-brain is two-edged (U16).** Behavioural disunity is disunity of
  access; whether the phenomenal field divides is contested. If it does not,
  callosotomy removes the main information route while unity survives on
  residual graded subcortical coupling — close to the dissociation U15
  wants, provided unity is preserved out of proportion to the residual
  information flow. Either way the carrier is not a field (too weak across
  hemispheres), so P is stated as graded coupling of any kind (synaptic
  coupling is graded: postsynaptic potentials, sub-threshold spike-timing
  shifts) and fields are one realization.
- **Protecting P by the access/phenomenal distinction would make it
  unfalsifiable (U17).** The observations that count as evidence about the
  phenomenal field are declared before testing and accepted when they go
  against P.
- The margin theorem is too weak to bite on real GPUs because content-relevant
  graded leakage exists (U13) — then the claim narrows to idealised digital
  hardware and says so.

## Section plan (target ~7,000 words)

1. Introduction — the thesis and P on page one; three numbered claims.
2. Synchrony is not unity (result 1, compressed from the companion).
3. Unity as agreement, and the cover problem (result 2, decodability cover).
4. Physical enforcement versus routed agreement (P, definitions, result 5,
   the simulation objection).
5. How far a physical coupling enforces agreement (results 4, 6; kernel tail).
6. The unity window (results 3, 7).
7. Current AI systems (margin theorem applied; causal mask; what would pass:
   analog, in-memory, neuromorphic).
8. Tests and what would sink the thesis.
9. Limitations — the only section where scope disclaimers live (see the H
   gates).

## Open questions for the author

1. New directory name and whether the companion is submitted anywhere besides
   arXiv.
2. Whether the self-reconstruction material has any place here (current
   answer: no; unity only).
3. Human evidence for P beyond the weak-field literature — the premise needs
   brain-side motivation that does not mention machines; this is the thinnest
   part of the outline. Current answer: human data can falsify P (a
   sub-threshold perturbation of A leaving B's decoded content unchanged) but
   cannot confirm it against functionalism, because in brains graded coupling
   and information flow always co-vary: anaesthesia and split-brain remove
   both. Confirmation needs a dissociation (U15). If none is possible even in
   principle, the paper presents P as a philosophical commitment with
   falsifiable consequences, not an empirical finding.
