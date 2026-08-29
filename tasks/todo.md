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


---

## Opus 5 Soundness Audit — 2026-08-29

Full re-read of all 13 Lean files hunting axiom smuggling, circular definitions,
and vacuous statements. **Every finding below was mechanically verified** by
compiling an exploit against the then-current tree; the exploit files live in the
session scratchpad and each one compiled to a proof of `False` or of the negation
of the stated claim.

### CRITICAL — three of the five live axioms were individually inconsistent

Each of these, *on its own*, proved `False` — and therefore `2 + 2 = 5`. Every
theorem depending on them was vacuous, while `lake build` stayed green and
`#print axioms` reported them as ordinary named postulates.

| Axiom | Defect | Refutation |
|---|---|---|
| `spontaneous_symmetry_breaking_pointwise_min` | `PotentialEnergy` was **implicit** and occurred only in the hypothesis `PotentialEnergy phi = V v0` | Instantiate it with `fun _ => V v0`; hypothesis closes by `rfl`; conclusion holds for arbitrary `phi`. With `V = v²`, `v0 = 0`, `phi = const 1`: `1 = 0` |
| `landauer_heat_eq` | Pinned the **free class field** `heat_dissipation` for *every* `StatisticalMechanics` instance | Instance on `Unit` with `heat_dissipation = 0`, `temperature = 1`, bath `{false} → univ : Finset Bool` gives `0 = log 2` |
| `kl_bound_axiom` | Asserted `σ ≥ KL P Q / dt` for **all** `P`, `Q`, while `σ` is one real fixed by a class field and `KL` is unbounded above | `Thermodynamics Bool` with `heat_dissipation = 0`; `P` a point mass, `Q` uniform gives `0 ≥ log 2` |

**Root cause, common to all three:** an axiom constraining a symbol it does not
itself bind — an implicit argument, or a field of a class it quantifies over.

**Same defect, exploit not mechanized:** `phase_invariant_periodic` and
`sync_to_section_eq` pin free fields of `LocalSectionSynchronization` across all
instances. Refutable as soon as the probability presheaf has two distinct global
sections; constructing those needs the sheafification machinery, so this one is
reported on structural grounds rather than by a compiled counterexample.

### Fixes applied

* **Design rule adopted** (recorded in `Axioms.lean` §5): *a physical postulate
  that mentions a class field must be a field of that class, never a standalone
  `axiom` quantified over all instances.*
* `spontaneous_symmetry_breaking_pointwise_min` → **deleted**. `ActionPrinciples`
  now defines `PotentialEnergy` as `∫ x, V (phi x) ∂mu`, which makes the former
  assumed fields `potential_const` and `potential_bound` *derivable*, and turns
  the postulate into the theorem `pointwise_vacuum_of_global_min` (proved from
  `integral_eq_zero_iff_of_nonneg`). Conclusion is now `∀ᵐ` rather than `∀` —
  the old `∀ x` form was itself part of why the axiom was false.
* `landauer_heat_eq` → field `StatisticalMechanics.heat_eq`.
* `kl_bound_axiom` → field `StructuralResonance.kl_bound`, on a new class that
  carries the system's own `P_ext`, `Q_int`, `transition` and `dt` rather than
  quantifying over all distributions.
* `phase_invariant_periodic`, `sync_to_section_eq` → fields of
  `LocalSectionSynchronization`.
* **Result: the development declares zero axioms.** `#print axioms` on every
  headline theorem now reports only `propext`, `Classical.choice`, `Quot.sound`.

### Non-vacuity — new `PhysicsOfConsciousness/Examples.lean`

Moving postulates into classes is only progress if the classes are inhabitable;
an uninhabitable class is as vacuous as an inconsistent axiom. Witnesses built:

* ✓ `StatisticalMechanics Bool` — one-bit erasure with a real bath and a genuinely
  bijective `U`, discharging `heat_eq`. Includes a worked `example` showing
  `landauers_principle` fires on it (erasure ⇒ strictly positive heat).
* ✓ `StructuralResonance Bool` — perfectly resonant system, `KL = 0`.
* ✓ `ActionPrinciples Unit ℝ …` — scalar field on a one-point spacetime.
* ✗ `LocalSectionSynchronization` / `ThermodynamicCover` — **no instance exists.**
  Derivation 5's gluing results are conditional on structures not yet shown to be
  realizable. Flagged "unwitnessed" in Table 1 and stated plainly in the
  supplementary. **This is now the largest open gap in the formalization.**

Before this pass, the only `instance` in the entire development was a
`DecidableEq` helper — not one physical structure was ever inhabited.

### Other verified findings

| # | Finding | Status |
|---|---|---|
| A | `mesh_refinement_convergence` is **refutable**, not merely unproven: nothing forces `edge_region` to cover `M`, and `Metric.diam ∅ = 0 < δ`, so the all-empty triangulation forces `|0 - ∫f| < ε` for all ε | Doc-comment rewritten as an explicit warning; refutation compiled |
| B | The same definition has a **dead binder**: `∀ (TM : TriangulatedManifold M)` binds `TM`, but the body writes `TriangulatedManifold.V M`, resolved by *instance search*. `TM` is never used — confirmed via `#print` | Documented |
| C | Two different Kuramoto potentials. `dV_dt_le_zero` proves descent for `kuramoto_potential` (with the ω term, in `Phase3`); `phase_locked_minimizes_potential` characterises the minimum of `kuramoto_potential_dynamic` (without it, in `Phase4`). They are never chained — and `kuramoto_potential` is **unbounded below** when any ωᵢ ≠ 0, so it has no minimum to attain | Documented on the definition |
| D | `defect_inevitability` proved the *opposite* of its name — that extendable boundary configurations are trivial, not that defects are inevitable | Renamed `contractible_interior_forces_trivial_boundary`; supplementary corrected |
| E | `TriangulatedManifold` never links `complex`/`embedding` to `edge_region`, so `edge_weight` integrates over an unconstrained set and `weight_symm` just unfolds an assumed field | Documented; Table 1 row downgraded to "Theorem (weak)" |

### Manuscript updates

* New subsection **"Soundness of the formalization"** (`\label{sec:soundness}`)
  reporting the inconsistencies, the root cause, the uniform fix, the design rule,
  and the non-vacuity witnesses — including the `ThermodynamicCover` gap.
* Table 1 rebuilt: no axiom column left standing; rows marked
  "Theorem + instance postulate", "Theorem (abstract)", "Theorem (weak)",
  "Conditional theorem", "Theorem (unwitnessed)".
* Supplementary: Overview, Theorem 1, Theorem 2, Derivation 3 and Theorem 5
  implementation notes all corrected.

**Verification:** `lake build` succeeds (17,600 jobs). All three exploit files
now fail to compile (`unknown identifier`, and for `heat_eq` the pleasing
`Fields missing: heat_eq`). `main.tex` and `supplementary.tex` compile with zero
errors and zero warnings.

### Remaining open

1. **Build a `ThermodynamicCover` instance.** Highest priority — without it,
   Derivation 5 is conditional on a structure of unknown realizability.
2. Link Phase 8's abstract gradient-flow theorems to `entropy_production_rate`.
3. Restate `mesh_refinement_convergence` correctly (sequence of triangulations,
   covering condition, `edge_region` tied to the simplicial data).
4. Chain the two Kuramoto potentials via the rotating-frame reduction.
5. Formalize a genuine continuous/discrete distinction if the hardware corollary
   is to be more than an informal argument.
