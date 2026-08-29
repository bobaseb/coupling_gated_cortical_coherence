# Physics of Consciousness - Formalization To-Do

The following tasks focus on expanding the Lean 4 formalization to cover claims that are currently unformalized or only conditionally proven.

## P0: Mesh Refinement Convergence (Phase 2) — PENDING
* **Objective:** Formalize the proof for `mesh_refinement_convergence` in `Phase2_SimplicialBridge.lean`, which currently sits in the "Conjectures" section.
* **Verdict (Aug 2026):** Not feasible in Lean today without building substantial measure-theoretic Riemann-sum approximation infrastructure (partition-of-unity, compactness, uniform-continuity) that doesn't exist in Mathlib. The current type signature is also too weak (quantifies over all triangulations without a sequence structure). A concrete 1D formalization building on the Python simulation would be a reasonable intermediate target.
* **Covered by:** Python simulation `simulations/mesh_refinement.py` — computes continuous Kuramoto potential via Riemann sum, confirms O(1/N²) convergence. Run with `python simulations/mesh_refinement.py`.
* **Doc-comment updated:** The conjecture doc-string now explicitly describes the numerical validation and lists infrastructure gaps.

## P1: KL Bound Formalization (Derivation 3) — DONE
* **Objective:** Provide a full Lean 4 implementation of the KL Bound from Derivation 3.
* **Implementation:** `PhysicsOfConsciousness/Phase3_KLBound.lean`
  * `ProbDist V` — discrete probability distribution structure
  * `KL(P, Q)` — Kullback-Leibler divergence for finite state spaces
  * `KL_nonneg` — Gibbs' inequality (theorem, proved via `Real.log_le_sub_one_of_pos`)
  * `discrete_entropy_rate` — entropy production rate σ = Q/T
  * `kl_bound_axiom` — irreducible axiom: σ ≥ KL/Δt
  * `structural_resonance_bound` — theorem: KL ≤ Δt·σ (bridges to Phase 8 gradient descent)
* **Table 1 updated:** Row changed from "Unformalized" to "Axiom + Theorem" in `main.tex`
* **Supplementary updated:** Disclaimer removed, formalization cited in `supplementary.tex`

---

## Opus 5 Deep Evaluation — 2026-08-28

Full audit via `anthropic/claude-opus-5`: Lean build, `#print axioms`, file inspection, prose analysis. Findings organized below for pre-arxiv remediation.

### Narrative & Argumentation

**Strongest moves:**
- `main.tex:67-69` names the Norton/Shenker objection then answers it structurally (non-injectivity on physical state space with globally injective Liouville evolution). The one place Lean actually delivers: `landauer_from_reversibility` is axiom-free.
- `main.tex:55` footnote pre-empts "math theatre" by conceding the Poincaré group is illustrative, not hardcoded.
- `main.tex:108-112` converts framework into falsifiable claims (propofol phase-disruption, sleep inertia timescale).
- `main.tex:132` uses Russellian monism to fence off qualia — doesn't overclaim.

**Weakest links — structural:**
| Issue | Location | Why it hurts |
|---|---|---|
| Identifying sheaf global section of finite measures with unity of experience is stipulation, not derivation — hard-problem gap reappears | `main.tex:92` | Undermines the core explanatory thesis |
| "Continuous" vs "discrete lattice" vs "rigid" never formalized — both couplings are `V → V → ℝ` on one `Fintype` | `Phase7:63-69` | Hardware corollary cannot logically follow |

**Weakest links — fixable before arxiv:**
| Issue | Location | Fix |
|---|---|---|
| Table 1 caption claims "only pointwise vacuum minimization" remains axiom — 5 axioms live, 4 outside Axioms.lean | `main.tex:51` | Update caption to match code reality |
| Cerebellum-as-GPU cites tononi2015 — IIT's own argument borrowed while IIT subordinated at line 92 | `main.tex:117` | Qualify or find independent support |
| Supplementary claims Phase4 proves minimality "strictly when K > K_c" — K_c doesn't appear in that file | `supplementary.tex:59` | Correct claim or add K_c |

**Literature positioning:** Adequate breadth, thin depth. IIT and GWT get one clause each at line 92 — no engagement with Φ, exclusion, or their critiques. FEP best-handled (lines 74-76 give mechanism). 47 bibitems, zero uncited.

**Prose/Lean alignment gaps:**
| Prose claim | Lean reality |
|---|---|
| "Landauer... Theorem" (Table row 42) | Same file declares `landauer_heat_eq` as axiom |
| "Gradient flow... Theorem" (row 45) | Ph8 theorems over abstract inner-product space never linked to `entropy_production_rate` |
| "Theorem" (row 47) | Hides 2 axioms + class field asserting conclusion |
| "Strictly when K > K_c" (supp.tex:59) | K_c absent from Phase4 |
| Self achieves entropy minimum (supp.tex:73) | Ph6 is Banach fixed-point, no entropy term |

### Lean Code Issues

| # | Finding | Location |
|---|---|---|
| 1 | Table 1 claims one axiom; five are live, four outside `Axioms.lean` | `main.tex:51` |
| 2 | `KL_nonneg` never used; `structural_resonance_bound` docstring falsely claims it combines Gibbs | Phase3_KLBound:42,105 |
| 3 | `is_strictly_suboptimal` smuggles conclusion — theorem restates premise | Phase7:9 |
| 4 | Phase7 formalizes nothing continuous or rigid — both couplings on one `Fintype` | Phase7:63-69 |
| 5 | `h_mean` assumes every competitor shares `Omega_avg`, grants minimality by hypothesis | Phase8:74-76 |
| 6 | Phase8 two disconnected halves — `entropy_production_rate` never meets abstract `S`/`gradS` theorems | Phase8:27 vs 164-200 |
| 7 | `thermodynamic_equilibrium` asserts phase-minimality as class field, not result | Phase5:30-35 |
| 8 | `MetricSpace` + `ContractingWith (1/2)` never instantiated — Self proof is symbolic | Phase6:84,87 |
| 9 | `phase_locked_minimizes_potential` proves only `cos ≤ 1` — no dynamics, no K_c | Phase4:73-86 |
| 10 | `mesh_refinement_convergence` is `def … : Prop`, unproven, self-admittedly mis-typed | Phase2:103 |
| 11 | Dead: `Basic.lean` empty namespace imported; `_archive/` has 15 stale `.lean` files | repo root |
| 12 | 7 unused decls (`spontaneous_symmetry_breaking`, `dV_dt_le_zero`, `exhibits_phase_transition`, etc.) | various |
| 13 | `exists_better_coupling_allocation` is `lemma` but cited as "our theorem" in prose | Phase7:63 / main.tex:121 |
| 14 | Blanket `import Mathlib` in 5 files alongside targeted imports — inconsistent | various |

### Priority Actions Before Arxiv — STATUS 2026-08-29

| Prio | What | Status |
|---|---|---|
| 🔴 | Fix Table 1 caption to accurately count axioms (1→5) | **DONE** — `main.tex:51` caption now names all five live axioms and their files, notes the three declared-but-unused ones in `Axioms.lean`, points readers at `#print axioms`, and warns that some results carry physical content in hypotheses |
| 🔴 | Rename `exists_better_coupling_allocation` citations from "theorem" to "lemma" | **DONE** — `main.tex:121` and `supplementary.tex` now call it a lemma and name its theorem wrapper `continuous_beats_rigid_topology` |
| 🔴 | Disclaim that "discrete"/"continuous" are not formalized in Lean | **DONE** — scope disclaimer added to the `Phase7_HardwareComparison.lean` file header and the `continuous_beats_rigid_topology` doc-string; matching paragraphs added to `main.tex` (Corollary) and `supplementary.tex` (Theorem 7) |
| 🟠 | Table 1 row for Derivation 3 KL bound | **DONE** (in P1) — row reads "Axiom + Theorem" |
| 🟠 | Fix `supplementary.tex:59` claim about K_c in Phase4 | **DONE** — now states what Phase 4 actually proves (both directions of the static potential-minimum characterization, for all positive couplings) and says explicitly that K_c is absent from Lean and validated numerically instead |
| 🟠 | Delete `Basic.lean` and `scratch.lean` | **DONE** — `Basic.lean` deleted and its import removed from `PhysicsOfConsciousness.lean`; `scratch.lean` did not exist |
| 🟡 | IIT/GWT critical engagement | **DONE** — `main.tex` Derivation 5 gained two paragraphs: IIT (Φ intractability, revisions, exclusion falling out of gluing rather than being postulated, and the Aaronson-style mirror objection against our own criterion) and GWT (Block's access/phenomenal gap, our field as the missing substrate, and the falsifiable cost of the commitment). Five bibitems added: `aaronson2014`, `block1995`, `herculanohouzel2009`, `lange1975`, `yu2015` |
| 🟡 | Note that Lean theorems carry physical content in hypotheses | **DONE** — stated in the Table 1 caption, in the supplementary Overview, and per-file: `Phase5_GlobalSection.lean` (`thermodynamic_equilibrium` is a class field, not a result), `Phase8_ContinuousField.lean` (`h_mean` restricts the comparison class to fields of equal mean drift) |

### Additional fixes made in the same pass

* **Phase 3 KL bound docstring corrected** — `structural_resonance_bound` no longer claims to combine Gibbs' inequality; it is documented as a rearrangement of `kl_bound_axiom`. A new theorem `discrete_entropy_rate_nonneg` now genuinely combines `KL_nonneg` with the axiom to derive σ ≥ 0, which also makes `KL_nonneg` a live dependency rather than dead code.
* **Phase 8 file header** — documents that the concrete half (`entropy_production_rate`) and the abstract half (`gradient_flow_implies_entropy_decrease` et al.) are not linked, and what linking them would require.
* **Cerebellum claim re-sourced** — neuron-count and circuit-architecture claims now cite Herculano-Houzel and Lange; cerebellar agenesis cites Yu et al.; the `tononi2015` citation is kept but explicitly scoped to the anatomical observation, not the Φ-based explanation.
* **Table 1 rows sharpened** — Landauer row distinguishes the axiom-free reversibility core from `landauer_bound`'s dependence on `landauer_heat_eq`; Least Action row flagged "Theorem (abstract)"; Hardware row flagged "Conditional Theorem".

**Verification:** `lake build` succeeds (17,598 jobs). `main.tex` and `supplementary.tex` compile with zero undefined references or citations. `main.pdf` and `arxiv_submit/ax.tar` regenerated.

### Not addressed (deliberately deferred)

| # | Finding | Why deferred |
|---|---|---|
| — | Sheaf global section ↔ unity of experience is stipulation, not derivation (`main.tex:92`) | This is the framework's core philosophical commitment, not a fixable defect; the Russellian-monism framing at `main.tex:132` already fences it. Would require a substantive rewrite of the thesis, not an edit |
| 11 | `_archive/` has 15 stale `.lean` files | Not built, not imported, not cited; harmless as version history |
| 12 | 7 unused declarations (`spontaneous_symmetry_breaking`, `dV_dt_le_zero`, `exhibits_phase_transition`, …) | Expository value; the three unused axioms are now flagged as such in the Table 1 caption |
| 14 | Blanket `import Mathlib` in 5 files alongside targeted imports | Cosmetic; no effect on correctness or on build time in a cached tree |
