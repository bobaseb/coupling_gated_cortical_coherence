# Physics of Consciousness - Formalization To-Do

The following tasks focus on expanding the Lean 4 formalization to cover claims that are currently unformalized or only conditionally proven.

## P0: Mesh Refinement Convergence (Phase 2) — DONE (2026-08-29)
* **Objective:** Formalize the proof for `mesh_refinement_convergence` in `Phase2_SimplicialBridge.lean`, which sat in the "Conjectures" section.
* **Superseded verdict (Aug 2026):** an earlier pass judged this infeasible without Riemann-sum infrastructure missing from Mathlib. That was wrong in two ways. The infrastructure needed is finite additivity plus a modulus-of-continuity estimate, both available; and the original statement was not just unproven but *false*, so no amount of proof effort would have closed it. See "Mesh Refinement Convergence — 2026-08-29 — DONE" at the end of this file.
* **Implementation:** `PhysicsOfConsciousness/Phase2_MeshConvergence.lean` — `Mesh`, the fixed-mesh error bound, the sequence limit, `IsRegularTriangulation`, and `mesh_refinement_convergence` as a theorem. Witnessed on the uniform partition of `[0,1)` in `Examples.lean` §6.
* **Covered by:** Python simulation `simulations/mesh_refinement.py` — computes continuous Kuramoto potential via Riemann sum, confirms O(1/N²) convergence. The Lean theorem proves convergence, not the rate. Run with `python simulations/mesh_refinement.py`.

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
| A | `mesh_refinement_convergence` is **refutable**, not merely unproven: nothing forces `edge_region` to cover `M`, and `Metric.diam ∅ = 0 < δ`, so the all-empty triangulation forces `|0 - ∫f| < ε` for all ε | **RESOLVED 2026-08-29** — false `def` deleted; restated and proved in `Phase2_MeshConvergence.lean` |
| B | The same definition has a **dead binder**: `∀ (TM : TriangulatedManifold M)` binds `TM`, but the body writes `TriangulatedManifold.V M`, resolved by *instance search*. `TM` is never used — confirmed via `#print` | **RESOLVED 2026-08-29** — the replacement theorem uses its binder; checked with `pp.explicit` |
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

1. ~~**Build a `ThermodynamicCover` instance.**~~ **DONE 2026-08-29** — see below.
2. ~~Link Phase 8's abstract gradient-flow theorems to `entropy_production_rate`.~~ **DONE 2026-08-29** — see below.
3. ~~Restate `mesh_refinement_convergence` correctly (sequence of triangulations,
   covering condition, `edge_region` tied to the simplicial data).~~ **DONE
   2026-08-29** — restated *and proved*; see below.
4. Chain the two Kuramoto potentials via the rotating-frame reduction.
5. Formalize a genuine continuous/discrete distinction if the hardware corollary
   is to be more than an informal argument.
6. **Prove the limit `lim_{t→∞} D_KL(P ‖ Q) = 0`** asserted in supplementary
   Theorem 3. Phase 8 §7 now gives monotone descent of σ along the coupling
   gradient flow, and `Phase3_KLBound` gives `D_KL ≤ Δt·σ` — but the two together
   do **not** force the limit to be zero. Monotone and bounded below only yields
   convergence to *some* infimum, which may be positive; and even σ → 0 would
   need the KL bound to be tight, not just an upper bound. Closing it needs a
   coercivity or Łojasiewicz-type estimate on σ (a lower bound on ‖∇σ‖ away from
   the minimiser), plus a statement relating the σ-minimiser to `KL = 0`. Neither
   exists in the development. Currently flagged as unformalized in
   `supplementary.tex:47`; the prose must keep saying so until this is done.

---

## ThermodynamicCover Witness — 2026-08-29 — DONE

Closes the item flagged as "the largest open gap in the formalization": every
class carrying a physical postulate is now inhabited, so no headline theorem is
vacuous for want of an instance.

### What was built — `PhysicsOfConsciousness/Examples.lean` §4

| Declaration | What it is |
|---|---|
| `Site` | Three-element inductive type (`left`, `mid`, `right`), discrete topology, `MeasurableSpace := borel Site`, so `BorelSpace` holds by `rfl` |
| `Cortex` | `TopCat.of Site` — declared `abbrev`, not `def`, so the measurable/Borel instances resolve through the `↥Cortex` coercion |
| `TriangulatedManifold ↥Cortex` | `edge_region u v = {u, v}` — the one gap the class leaves open (`edge_region` untied to `complex`) is closed *in this instance* |
| `patch : Bool → Opens ↥Cortex` | Two **overlapping** patches: `{x ≠ right}` and `{x ≠ left}` |
| `patch_cover` | `iSup patch = ⊤` |
| `patch_overlap` | Intersection is exactly `{mid}` — the gluing is a real two-patch gluing across a nonempty overlap, not a relabelled single section |
| `phaseMeasure t` | `(1 + cos t)⁺ • δ_mid` as a `FiniteMeasure ↥(⊤ : Opens ↥Cortex)` |
| `phaseMeasure_mass` | Total mass is `(1 + cos t)⁺` |
| `phaseMeasure_not_const` | **`phaseMeasure 0 ≠ phaseMeasure π`** — the invariant measure genuinely depends on the phase |
| `phaseMeasure_periodic` | `cos (x − y) = 1 → phaseMeasure x = phaseMeasure y`, via `Real.cos_eq_one_iff` + `Real.cos_add_int_mul_two_pi` |
| `globalSect t` | Germ family of `phaseMeasure t` under `TopCat.Presheaf.toSheafify` — an actual section of the sheafified probability presheaf |
| `cortexSync` | `LocalSectionSynchronization Cortex`. `sync_to_section_eq` holds by `rfl` because the local sections *are* defined as restrictions |
| `cortexCover` | `ThermodynamicCover Cortex`, uniform unit coupling |
| `example` | `global_section_from_thermodynamics` fires on `cortexCover`: the two patch-local sections glue to a unique global section |

### Why the witness is not degenerate

Two hazards were specifically avoided, since a bad witness proves nothing:

* **A constant `phase_invariant_measure`** would satisfy `phase_invariant_periodic`
  for trivial reasons. `phaseMeasure_not_const` rules that out: the family varies
  with phase, so the periodicity field is discharged by a real argument about
  `cos`, not by `rfl`.
* **A one-patch or disjoint-patch cover** would make the sheaf gluing vacuous.
  The cover has two patches with a nonempty intersection (`patch_overlap`).

`thermodynamic_equilibrium` is also *derived*, from
`phase_locked_minimizes_potential`, not assumed as a hypothesis of the example.

### What it does *not* establish

The phase field is constant (every patch already locked at 0), which is exactly
what makes the equilibrium obligation dischargeable. The witness shows the class
is inhabitable — it does not show that a cortex is an instance of it. Getting a
physical system into that configuration remains the informal dynamical argument
in the manuscript.

### Manuscript updates

* `main.tex:49` — Table 1 row for Derivation 5 changed from "Theorem
  (unwitnessed)" to "Theorem + instance postulate", now citing the witness.
* `main.tex:53` — caption's "Unwitnessed" legend replaced; it now states that
  every postulate-carrying class is inhabited, so no row is vacuous.
* `main.tex:73–75` — Soundness subsection rewritten: describes the substrate,
  the overlapping cover, the phase-indexed measure, the non-constancy result,
  and a new paragraph separating what witnesses establish (non-vacuity) from
  what they do not (that a cortex is such an instance).
* `supplementary.tex:66` — the "no instance of `ThermodynamicCover` has been
  constructed" caveat replaced by the discharged obligation and its details.
* `Examples.lean` header — coverage table now reads ✓ on all four classes.

**Verification:** `lake build` succeeds (17,600 jobs).
`#print axioms cortexCover` / `cortexSync` / `global_section_from_thermodynamics`
/ `phaseMeasure_not_const` / `patch_cover` each report only
`[propext, Classical.choice, Quot.sound]`. `main.tex` and `supplementary.tex`
compile with no new warnings (Table 1 caption trimmed to keep the float on the
page). `arxiv_submit/ax.tar` regenerated and its merged `main.tex` compiles clean.

---

## Phase 8 Gradient-Flow Link — 2026-08-29 — DONE

Closes open item 2. Phase 8 previously had two halves that never met: a concrete
σ (`entropy_production_rate`) over a measure space, and abstract descent theorems
about a Fréchet-differentiable `S` on an inner-product space *with the gradient
supplied as data*. Nothing said σ has a gradient, so the manuscript's claim that
structural resonance drives σ downhill was an informal identification.

### What was built — `Phase8_ContinuousField.lean` §7

The idea: fix the phase field and read σ as a function of the **coupling kernel**.
On a finite substrate the kernels form `EuclideanSpace ℝ (M × M)`, σ becomes a
quadratic functional, and its derivative is computable in closed form.

| Declaration | What it is |
|---|---|
| `CouplingSpace M` | `EuclideanSpace ℝ (M × M)` — kernels as a real inner-product space |
| `drift sys theta K x` | `ω x + ∑ y, K (x,y) · sin(θ_y − θ_x)` |
| `sigmaOfKernel sys theta K` | `∑ x, (1/D)·drift²` — σ as a functional of `K` |
| `sensRow theta x` | Row `x` of the phase-mismatch matrix as a vector; pairing against it extracts the coupling part of the drift |
| `drift_eq_inner` | The drift is **affine** in `K`: `ω x + ⟪sensRow x, K⟫`. This is what makes σ quadratic |
| `gradSigma sys theta K` | `∂σ/∂K(a,b) = (2/D)·drift(a)·sin(θ_b − θ_a)` |
| **`hasFDerivAt_sigmaOfKernel`** | **σ is Fréchet differentiable with gradient `gradSigma`** — the fact the abstract half assumed |
| `StochasticNeuralField.withKernel` | Replaces a field's kernel |
| **`sigmaOfKernel_eq_entropy_production_rate`** | **The bridge.** When `volume = Measure.count`, the functional being differentiated *is* `entropy_production_rate`. Without this the results would be about a re-definition of σ, not σ |
| `sigmaOfKernel_nonneg` | σ ≥ 0, so the descent cannot run away |
| `is_coupling_gradient_flow_sigmaOfKernel` | A trajectory moving against `gradSigma` satisfies §6's `is_coupling_gradient_flow` — differentiability discharged, not hypothesised |
| `entropy_production_antitone_of_gradient_flow` | σ is non-increasing along its own gradient flow, stated on `entropy_production_rate` |
| **`structural_resonance_decreases_entropy_production`** | The manuscript's Derivation 3 claim, now a theorem about `entropy_production_rate`: coupling relaxing down the σ gradient at any rate `c > 0` drives σ down |

### Non-vacuity — `Examples.lean` §5

Three ways the link could still be hollow, each ruled out on a two-site substrate
(`Duo`, counting measure, phases `0` and `π/2`, `D = 2`):

| Hazard | Ruled out by |
|---|---|
| `volume = Measure.count` might be unsatisfiable alongside the other instances | `duo_volume` — holds by `rfl` |
| `gradSigma` might be identically zero, making "descent" trivial | `duo_grad` — off the diagonal it is `e^{-t}` |
| The flow hypothesis might have no non-constant solution | `duoFlow_hasDerivAt` exhibits one; `duoFlow_not_const` shows it moves |

`sigma_duoFlow` computes σ along the flow in closed form as `e^{-2t}`, and a
`StrictAnti` example confirms the descent is strict, not `Antitone` satisfied by
a constant. The diagonal entries stay fixed, correctly: a site has no phase
mismatch with itself, so its gradient component vanishes.

### Scope — stated in the file header and the manuscript

* **Finite substrates only.** The continuum case needs differentiation under the
  integral sign with respect to the kernel, which is not developed.
* **Fixed phase field.** This is plasticity of the coupling at frozen phases, not
  joint (θ, K) dynamics.
* `phase_locked_achieves_minimum_entropy` is untouched and still conditional on
  its `h_mean` hypothesis.
* The limit `lim D_KL = 0` is still *not* formalized: monotone descent plus
  `D_KL ≤ Δt·σ` does not force the limit to be zero without a coercivity or
  Łojasiewicz-type estimate.

### Manuscript updates

* `main.tex:47` — Table 1 Least Action row moved from "Theorem (abstract)" /
  "not yet linked" to "Theorem", citing the derivative and the bridge.
* `main.tex` Derivation 5 (continuous field) — new paragraph with the closed-form
  derivative as a displayed equation, the bridge lemma, the descent theorem, the
  two scope limitations, and the `Examples.lean` §5 exercise.
* `supplementary.tex:47` — the "not yet linked to the discrete entropy production
  rate" sentence replaced by what is now proved, plus an explicit statement that
  the `lim D_KL = 0` half remains unformalized and why.
* `Phase8_ContinuousField.lean` header — "two halves **not yet connected**"
  rewritten as a three-part structure description plus a Scope section.
* `Examples.lean` header — coverage note extended to mention §5.

**Verification:** `lake build` succeeds (17,600 jobs). `#print axioms` on
`hasFDerivAt_sigmaOfKernel`, `sigmaOfKernel_eq_entropy_production_rate`,
`structural_resonance_decreases_entropy_production`,
`entropy_production_antitone_of_gradient_flow`, `duoFlow_hasDerivAt` and
`sigma_duoFlow` each report only `[propext, Classical.choice, Quot.sound]`.
Both manuscripts compile with no new warnings (Table 1 needed two trims — the
row and one caption sentence — to keep the float on the page).
`arxiv_submit/ax.tar` regenerated and its merged `main.tex` compiles clean.

---

## Mesh Refinement Convergence — 2026-08-29 — DONE

Closes open item 3, and goes past it: the statement was not only restated but
proved, and the finding recorded as (A) in the soundness audit — that
`mesh_refinement_convergence` was *refutable*, not merely unproven — is now
retired.

### The old statement, and why it had to go

`Phase2_SimplicialBridge.lean` carried `mesh_refinement_convergence` as a
`def … : Prop` in a "Conjectures" section. Two independent defects, both
verified:

* **Refutable.** Nothing required `edge_region` to cover `M`, and
  `Metric.diam ∅ = 0 < δ`. The triangulation whose edge regions are all empty
  satisfied the mesh hypothesis while contributing `0`, forcing `|0 - ∫f| < ε`
  for every `ε > 0` — false for any `f` with `∫ f ≠ 0`.
* **Dead binder.** `∀ (TM : TriangulatedManifold M)` bound `TM`, but the body
  wrote `TriangulatedManifold.V M`, resolved by *instance search*. `TM` was
  never used.

The `def` is deleted. `Phase2_SimplicialBridge.lean` keeps a note recording both
defects and pointing at the replacement; the `TriangulatedManifold` doc-string
now points at `IsRegularTriangulation` instead of at a false conjecture.

### What was built — `PhysicsOfConsciousness/Phase2_MeshConvergence.lean` (new)

| Declaration | What it is |
|---|---|
| `Mesh M` | Finitely many pairwise disjoint measurable cells. Measure-free; `support` records what it covers rather than assuming it is all of `M` |
| `Mesh.riemannSum μ val` | `∑ᵢ μ(cellᵢ)·val i` |
| `Mesh.setIntegral_support` | Finite additivity over the cells |
| **`abs_riemannSum_sub_setIntegral_le`** | **The error bound.** If `\|val i − f x\| ≤ ε` throughout cell `i`, then `\|riemannSum − ∫_support f\| ≤ ε·μ(support)`. Stated at *fixed* mesh — the mesh size enters only through the hypothesis |
| `tendsto_riemannSum` | Convergence along a sequence of meshes of common support, given the sampling error is eventually uniformly small |
| `tendsto_riemannSum_of_tendsto_fineness` | The concrete form: uniformly continuous integrand, `m n → 0`, values averaged from two points within `m n` of the cell |
| `dist_le_of_mem_closure` | A point in the closure of an `r`-small set is within `r` of it — what lets vertices on cell boundaries be sample points |
| `sum_sum_of_symm` | Symmetric `g` with `g u u = 0`: `∑ᵤ∑ᵥ g = 2·∑_{u<v} g` |
| **`sum_sum_mul_of_symm`** | **`½ ∑ᵤ∑ᵥ w(u,v)·φ(u) = ∑_{u<v} w(u,v)·(φu+φv)/2`.** The manuscript's half-sum samples only the *first* endpoint and is not symmetric; this shows it is exactly the midpoint rule over unordered edges. Without it, reading the double sum as a Riemann sum is a category error |
| **`IsRegularTriangulation TM S`** | The conditions `TriangulatedManifold` leaves open: `measurable_region`, `no_self_region`, `face_of_complex`, `anchored`, `disjoint_region`, `covers = S`. A *predicate*, not a strengthening of the class — existing instances are unaffected |
| `meshOfTriangulation` | One cell per unordered edge `u < v` |
| `support_meshOfTriangulation` | The mesh covers exactly `S` |
| `discreteEnergy TM μ f` | `½ ∑ᵤ∑ᵥ μ(R u v)·f(embedding u)` — the manuscript's quantity |
| `discreteEnergy_eq_riemannSum` | It *is* the mesh's midpoint Riemann sum |
| **`mesh_refinement_convergence`** | **The theorem.** Along a sequence of regular triangulations of `S` with fineness `→ 0`, `discreteEnergy → ∫_S f` for uniformly continuous `f` |

### Design points worth recording

* **`anchored` uses `closure`, not membership.** Cells are disjoint, so a vertex
  shared by two edges belongs to at most one of them — in the half-open
  partition of an interval it is a boundary point of both. Requiring
  `embedding u ∈ edge_region u v` would have made the class uninhabitable for
  the intended examples, which is the same failure mode as an inconsistent
  axiom, just quieter.
* **The covered region is named `S`.** Finitely many small cells cannot cover an
  unbounded space, so the old `= univ` form was unsatisfiable for every concrete
  example.
* **The binder is live.** `set_option pp.explicit true in #check
  @mesh_refinement_convergence` shows `TM n` passed to `TriangulatedManifold.V`,
  `edge_region` and `discreteEnergy`.

### Non-vacuity — `Examples.lean` §6

The regularity conditions pull against each other (disjoint yet covering, every
vertex anchored to each of its edges), so an instance is the only proof they are
simultaneously satisfiable.

| Declaration | What it is |
|---|---|
| `gridCell N i` | `[i/N, (i+1)/N)` |
| `gridComplex N` | Faces are sets of pairwise-consecutive vertices — a real constraint, not `univ` |
| `gridTriangulation N` | `N+1` vertices embedded at `i/N`; `edge_region` non-empty only on consecutive pairs |
| `gridRegular N (hN : 0 < N)` | `IsRegularTriangulation (gridTriangulation N) (Ico 0 1)`. `covers` is proved via `⌊x·N⌋₊`; `disjoint_region` via `Set.Ico_disjoint_Ico` |
| `grid_mesh_refinement` | The convergence theorem instantiated: `discreteEnergy (gridTriangulation (n+1)) volume f → ∫_{[0,1)} f` for any uniformly continuous `f` |
| `gridCell_measure` | Cells have measure `1/N` — not empty |
| `tent_energy_one`, `tent_energy_two` | For `x ↦ \|x − ½\|`: `½` at `N = 1`, `¼` at `N = 2` |

The last pair is the point: the approximations genuinely move with `N`, so the
limit is not being reached by a constant sequence. The fineness `1/(n+1)` also
tends to zero rather than being zero from the start.

### What it does *not* establish

* The witness is **one-dimensional**. Nothing here witnesses the manifold-valued
  `DiscreteThermodynamics`, whose edge weights integrate a stress-energy
  magnitude over a genuinely 2- or 3-dimensional region.
* **Convergence, not the rate.** `simulations/mesh_refinement.py` measures
  O(1/N²); the Lean bound is `ε·μ(S)` with `ε` a modulus of continuity, which
  for a Lipschitz integrand gives O(mesh size). The O(1/N²) midpoint-rule error
  term needs a second derivative, which is not developed.
* `TriangulatedManifold` itself still imposes no geometry. The conditions live
  in the predicate, so every result that needs them says so in its hypotheses.

### Manuscript updates

* `main.tex:48` — Table 1 row for Electrodynamic Discretization moved from
  "Theorem (weak)" / "`edge_region` unconstrained" to "Theorem", citing the
  convergence result and its witness. (Row trimmed to keep the float on the
  page.)
* `main.tex` Soundness subsection — new paragraph on this defect, noting it is
  the kind `#print axioms` cannot catch: a false *conjecture* rather than a bad
  axiom. Covers the refutation, the dead binder, the four changes to the
  statement, the closure-vs-membership point, the midpoint-rule identification,
  the witness, and the fact that the rate is not proved.
* `supplementary.tex` — new implementation note in the Kuramoto section
  explaining how the discrete coupling matrix comes from the triangulation, that
  mesh refinement was a false conjecture and is now a theorem, and the two
  limitations above.

**Verification:** `lake build` succeeds (17,602 jobs), no warnings from the new
code. `#print axioms` on `mesh_refinement_convergence`,
`abs_riemannSum_sub_setIntegral_le`, `discreteEnergy_eq_riemannSum`,
`support_meshOfTriangulation`, `gridRegular`, `grid_mesh_refinement`,
`tent_energy_one`, `tent_energy_two` and `gridCell_measure` each report only
`[propext, Classical.choice, Quot.sound]`. `main.tex` and `supplementary.tex`
compile with no undefined references and no float overflow.
`arxiv_submit/ax.tar` regenerated; its merged `main.tex` compiles clean.

### Remaining open (updated)

1. ~~Chain the two Kuramoto potentials via the rotating-frame reduction.~~
   **DONE 2026-08-29** — see below.
2. Formalize a genuine continuous/discrete distinction if the hardware corollary
   is to be more than an informal argument.
3. Prove the limit `lim_{t→∞} D_KL(P ‖ Q) = 0` asserted in supplementary
   Theorem 3 (needs a coercivity or Łojasiewicz-type estimate on σ).
4. **Prove the O(1/N²) rate for mesh refinement.** `Phase2_MeshConvergence`
   bounds the fixed-mesh error by `ε·μ(S)` with `ε` a modulus of continuity,
   which for a Lipschitz integrand gives O(mesh size) — one order short of the
   O(1/N²) that `simulations/mesh_refinement.py` measures. Closing it needs the
   midpoint-rule error term, i.e. a `C²` integrand and a second-derivative
   bound on each cell, then summing. Mathlib has the Taylor machinery
   (`taylor_mean_remainder_lagrange`), so this is bounded work on top of what
   already exists — the harder half is stating the extra regularity on the
   integrand without weakening the current theorem, which should stay as the
   continuous-integrand case.
5. **A mesh witness beyond one dimension.** `Examples.lean` §6 witnesses
   `IsRegularTriangulation` with the uniform partition of `[0,1)`. Nothing
   witnesses the manifold-valued `DiscreteThermodynamics`, whose edge weights
   integrate a stress-energy magnitude over a genuinely 2- or 3-dimensional
   region. Substantially harder than the 1D case: the `covers` obligation in 1D
   is a one-line `⌊x·N⌋₊` argument, whereas a planar triangulation needs the
   cells constructed *and* proved to cover — barycentric coordinates on a
   half-open simplex, or a product mesh of half-open boxes as a cheaper
   intermediate step that at least exercises the 2D geometry. Until this is
   done, the mesh results are honest only for one-dimensional substrates, which
   is what the file header and both manuscripts say.

---

## Rotating-Frame Reduction — 2026-08-29 — DONE

Closes open item 1, and retires finding (C) of the soundness audit: the
development carried two Kuramoto potentials that were never chained.

### The gap

| Where | What it proves | About which functional |
|---|---|---|
| `dV_dt_le_zero` (`Phase3_CombinatorialThermodynamics`) | Lyapunov descent `V̇ = -∑ᵢ θ̇ᵢ²` along trajectories | `kuramoto_potential` = `-½∑∑Aᵢⱼcos(θᵢ-θⱼ) - ∑ωᵢθᵢ` |
| `phase_locked_minimizes_potential`, `potential_min_implies_phase_locked` (`Phase4_KuramotoDynamics`), and Phase 5's `ThermodynamicCover` | The minimum is attained exactly at phase-locked configurations | `kuramoto_potential_dynamic` = `-½∑∑Aᵢⱼcos(θⱼ-θᵢ)` |

Two different functionals in two different files, with nothing connecting them —
so the manuscript sentence "the phase-locked state minimises the Lyapunov
potential of the system" was, read literally, about neither result.

The gap is not cosmetic, and this is now proved rather than asserted:
`kuramoto_potential_unbounded_below` shows that as soon as one `ωᵢ ≠ 0` the full
potential has **no minimum at all** — take `θ = c·ω` and let `c → ∞`; the
frequency term drops without bound while the cosine sum stays inside
`±½∑ᵢⱼ|Aᵢⱼ|`. So the descent theorem and the minimisation theorem could not have
been about the same object.

### What was built — `PhysicsOfConsciousness/Phase4_RotatingFrame.lean` (new)

| Declaration | What it is |
|---|---|
| `kuramoto_potential_eq_dynamic_sub` | The two potentials differ exactly by `∑ ωᵢθᵢ`. The cosine halves agree because `cos` is even and the two definitions write the difference in opposite orders |
| `KuramotoSystem.reduced` | Same coupling, all frequencies zero — definitionally the `⟨fun _ => 0, A, A_symm⟩` that Phase 5's `ThermodynamicCover` already used |
| **`kuramoto_potential_reduced`** | **On the reduced system the two potentials coincide.** This is the identity that lets `dV_dt_le_zero` speak about the functional Phases 4 and 5 use |
| **`kuramoto_potential_unbounded_below`** | **No minimum exists when some `ωᵢ ≠ 0`**: for every `C` there is a `θ` with `V(θ) < C`. Proved, not asserted in a doc-string |
| `rotate Ω θ` | The change of variables `θᵢ(t) ↦ θᵢ(t) - Ω t` |
| **`is_kuramoto_trajectory_rotate`** | **The reduction.** For `ω ≡ Ω`, a trajectory of `sys` maps to a trajectory of `sys.reduced` |
| `rotate_sub`, `is_phase_locked_rotate` | Phase differences and phase-locking are frame-invariant |
| `order_parameter_complex_shift`, `order_parameter_r_sq_shift`, `order_parameter_r_sq_rotate` | The order-parameter magnitude is frame-invariant: a uniform shift multiplies `r` by `e^{-iΩt}`, which `normSq` kills |
| **`dynamic_potential_descent`** | **`dV_dt_le_zero` transported through the frame**: `d/dt V_dyn(rotate Ω θ t) = -∑ᵢ (velocity)²` |
| `dynamic_potential_deriv_nonpos` | The corollary actually wanted: the dynamic potential is non-increasing along trajectories |
| **`rotating_frame_chain`** | **End to end.** Rotated trajectory solves the zero-frequency equations ∧ dynamic potential descends ∧ if the rotated configuration minimises it then the *original* phases are locked ∧ `r² = 1` |

### Non-vacuity — `Examples.lean` §7

The chain restricts to identical frequencies *and* to configurations at the
potential minimum. Both are real restrictions, so the chain is worth nothing
until something satisfies them.

| Declaration | What it is |
|---|---|
| `pairSystem Ω` | Two oscillators (`Bool`), unit coupling, common frequency `Ω` |
| `pairTrajectory Ω` | The synchronized trajectory `θᵢ(t) = Ω t` |
| `pairTrajectory_is_trajectory` | It solves the Kuramoto ODEs |
| `rotate_pairTrajectory` | In the rotating frame it sits at the origin — where `phase_locked_minimizes_potential` puts the minimum |
| **`pair_rotating_frame_chain`** | **`rotating_frame_chain` with every hypothesis discharged** |
| `example` (potential difference) | The full potential differs from the dynamic one by `2Ω·(Ωt)` here — the frame change is doing real work, not a no-op |
| `example` (unboundedness) | `kuramoto_potential_unbounded_below` fired on `pairSystem 1`: the hypothesis `∃ i, ωᵢ ≠ 0` is satisfiable |

### What it does *not* establish

* **Identical frequencies only.** A genuine spread `ωᵢ ≠ ωⱼ` leaves residual
  detunings `ωᵢ - Ω` in the reduced system, to which
  `kuramoto_potential_unbounded_below` still applies. There is no reduction to a
  zero-frequency system in that case, and phase-locking then depends on the
  coupling exceeding `K_c`.
* **`K_c` is still absent from Lean.** Nothing here formalizes the
  synchronization transition; that remains numerical
  (`simulations/kuramoto.py`), as Table 1 says.
* **Minimality is still a hypothesis, not a dynamical conclusion.**
  `rotating_frame_chain` takes "this configuration minimises the dynamic
  potential" as input. Getting there from an arbitrary initial condition needs
  a convergence argument (LaSalle or similar) that is not developed.

### Updates elsewhere

* `Phase3_CombinatorialThermodynamics.lean` — the `kuramoto_potential`
  doc-string said the gap "is not formalized here". Rewritten to describe the
  chain, and to point at `kuramoto_potential_unbounded_below` for the claim it
  previously only asserted.
* `main.tex:117` — the Lyapunov claim now says *which* functional is minimised
  and points at the soundness section.
* `main.tex` Soundness subsection — new paragraph on this defect, noting it is
  a third kind: not an inconsistent axiom, not a false conjecture, but a
  bookkeeping gap across files where each half is individually correct. Covers
  the unboundedness result, the reduction, the frame-invariance of the
  observables, the witness, and the identical-frequency restriction.
* `main.tex` Table 1 — new row "Kuramoto Lyapunov descent → Theorem". Several
  cells and the caption trimmed to keep the float on the page.
* `supplementary.tex` §Macroscopic Scaling — new implementation note for
  `Phase4_RotatingFrame.lean`.

**Verification:** `lake build` succeeds (17,604 jobs), no warnings from the new
code. `#print axioms` on `kuramoto_potential_eq_dynamic_sub`,
`kuramoto_potential_reduced`, `kuramoto_potential_unbounded_below`,
`is_kuramoto_trajectory_rotate`, `is_phase_locked_rotate`,
`order_parameter_r_sq_shift`, `dynamic_potential_descent`,
`dynamic_potential_deriv_nonpos`, `rotating_frame_chain`,
`pairTrajectory_is_trajectory` and `pair_rotating_frame_chain` each report only
`[propext, Classical.choice, Quot.sound]`. `main.tex` and `supplementary.tex`
compile with zero errors, zero undefined references and no float overflow.
`arxiv_submit/ax.tar` regenerated; its merged `main.tex` compiles clean.

### Remaining open (updated)

1. ~~Formalize a genuine continuous/discrete distinction if the hardware
   corollary is to be more than an informal argument.~~ **DONE 2026-08-29** —
   see below.
2. Prove the limit `lim_{t→∞} D_KL(P ‖ Q) = 0` asserted in supplementary
   Theorem 3 (needs a coercivity or Łojasiewicz-type estimate on σ).
3. Prove the O(1/N²) rate for mesh refinement (midpoint error term; needs a
   `C²` integrand and a second-derivative bound per cell).
4. A mesh witness beyond one dimension.
5. Convergence to the potential minimum (LaSalle-type argument; Mathlib has no
   invariance principle).

---

## Hardware Rigidity and the Continuum Separation — 2026-08-29 — DONE

Closes open item 1, and retires findings #3 and #4 of the Opus 5 deep
evaluation (`is_strictly_suboptimal` smuggles the conclusion; Phase 7
formalizes nothing continuous or rigid).

### The two defects

| # | Defect | Why it mattered |
|---|---|---|
| 3 | `is_strictly_suboptimal A θ` — "some pair carries weight while a better-correlated pair exists" — was a *hypothesis*. `continuous_beats_rigid_topology` therefore proved "suboptimal allocations can be improved", which is nearly a tautology dressed as a hardware result | The physical claim (silicon is *stuck*) entered as an assumption |
| 4 | `A_rigid` and `A_flex` are both `V → V → ℝ` on one `Fintype`. No continuity, no manifold, no lattice | The corollary about continuous vs. discrete hardware could not follow from anything in the file |

Both are now addressed, in the two different ways that are actually available —
and they are different results, which the file says explicitly.

### What was built — `PhysicsOfConsciousness/Phase7_Rigidity.lean` (new)

**§1–2. Rigidity as a support constraint (finite, resource-matched).**

| Declaration | What it is |
|---|---|
| `totalCorrelation θ A` | `∑ᵢ∑ⱼ Aᵢⱼ cos(θⱼ-θᵢ)` — the quantity Phase 7 increases |
| `RealizableIn S R A` | Valid coupling, budget `R`, **and zero on every pair the architecture has no wire for**. This is the formal content of "rigid": weights tunable, wiring not |
| **`totalCorrelation_le_of_realizable`** | **A rigid architecture cannot beat its own best wire**: if every wired pair has correlation ≤ `M`, no realizable coupling exceeds `R·M` |
| `exists_realizable_pair` | The bound is attained — whole budget on one wired pair |
| **`rigid_is_strictly_suboptimal`** | **The hypothesis is now derived.** If the substrate's best-correlated pair is one the wiring misses, every realizable coupling at positive budget satisfies `is_strictly_suboptimal` |
| **`rigid_gap`** | Quantitative: an unconstrained reallocation of the *same* budget gains at least `R·(best unwired − M) > 0` |

**§3. Continuity as a measure-theoretic distinction (genuinely typed).**

| Declaration | What it is |
|---|---|
| `fieldCorrelation μ θ K` | `∫∫ K(x,y) cos(θy-θx) dμ dμ` — the continuum analogue, matching Phase 8's setting |
| `SitedOn F K` | All coupling originates at one of finitely many sites: `F : Finset X` |
| **`fieldCorrelation_sited_eq_zero`** | **On an atomless substrate a finitely-sited kernel contributes exactly zero** — whatever weights it carries, whatever the phase field does |
| `patchKernel U c`, `patchKernel_symm`, `patchKernel_nonneg` | A valid field coupling of strength `c` across a region `U` |
| `fieldCorrelation_patchKernel` | The patch achieves `c·μ(U)²` |
| **`sited_architecture_below_field_optimum`** | **The separation**: `Finset X` against a positive-measure set |

### Non-vacuity — `Examples.lean` §8

| Declaration | What it is |
|---|---|
| `rigidWiring` | Three sites, wired only between `0` and `1` |
| `rigidPhases` | `0` and `2` in phase, `1` in antiphase — so the one wire joins the maximally *anti*-correlated pair and the perfect pair `(0,2)` is unwired |
| `exists_rigid_coupling` | The architecture can spend its whole budget and the best it buys is `-1` |
| **`rigid_architecture_is_beaten`** | **`is_strictly_suboptimal` derived, gap exactly `2`** — the full swing from anti-correlation to correlation |
| `rigid_architecture_beaten_by_phase7` | `exists_better_coupling_allocation` fires with *no assumed hypothesis* |
| `pointArchitecture` | A thousand units of coupling weight, all at the origin of ℝ |
| **`pointArchitecture_field_zero`** | **Registers exactly zero**, for every phase field |
| `patch_field_one` | The unit patch registers `1` |

### What it does *not* establish

* **§1–2 turns on wiring support, not continuity.** An architecture whose wires
  *do* reach the best pair is not beaten by this argument. The result is honest
  and resource-matched, but "continuous" does no work in it.
* **§3 is not resource-matched.** A measure-zero substrate carries zero resource
  in the `μ⊗μ` sense as well as zero correlation, so the comparison is not
  like-for-like. What it establishes is that the continuum coupling energy is
  *blind* to a finitely-sited architecture — a statement about which functional
  such an architecture can register in, not a proof that digital hardware
  computes worse. The file header says this in as many words.
* **No manifold structure, no lattice geometry.** Neither result formalizes the
  spatial layout of silicon or of cortex.
* The step from either result to "von Neumann architectures cannot experience
  unified consciousness" remains an informal argument, now with two verified
  steps under it rather than one.

### Updates elsewhere

* `Phase7_HardwareComparison.lean` — `sum_sym_pair` made public (reused by the
  new file). The scope disclaimer rewritten: it still says what this file does
  not formalize, and now points at what does.
* `main.tex` Corollary section — the "what this does and does not establish"
  paragraph replaced. It now names both objections, says how each was answered,
  and states the limits of each answer.
* `main.tex` Table 1 — the Continuous vs. Rigid Topology row moves from
  "Conditional" to "Theorem", citing the new file. Two cells trimmed to keep the
  float on the page.
* `supplementary.tex` §Topological Rigidity — new implementation note and a
  rewritten scope caveat.

**Verification:** `lake build` succeeds (17,606 jobs), no warnings from the new
code. `#print axioms` on `totalCorrelation_le_of_realizable`,
`exists_realizable_pair`, `rigid_is_strictly_suboptimal`, `rigid_gap`,
`fieldCorrelation_sited_eq_zero`, `fieldCorrelation_patchKernel`,
`sited_architecture_below_field_optimum`, `rigid_architecture_is_beaten`,
`rigid_architecture_beaten_by_phase7`, `pointArchitecture_field_zero` and
`patch_field_one` each report only `[propext, Classical.choice, Quot.sound]`.
`main.tex` and `supplementary.tex` compile with zero errors, zero undefined
references and no float overflow. `arxiv_submit/ax.tar` regenerated; its merged
`main.tex` compiles clean.

### Remaining open (updated)

1. Prove the limit `lim_{t→∞} D_KL(P ‖ Q) = 0` asserted in supplementary
   Theorem 3 (needs a coercivity or Łojasiewicz-type estimate on σ).
2. Prove the O(1/N²) rate for mesh refinement (midpoint error term; needs a
   `C²` integrand and a second-derivative bound per cell).
3. A mesh witness beyond one dimension.
4. Convergence to the potential minimum (LaSalle-type argument; Mathlib has no
   invariance principle).
5. **The critical coupling threshold `K_c = 2D`** — the last row of Table 1 that
   is not a theorem, and the one gap every other file's scope note points at.
   See "Open: Critical Coupling Threshold" at the end of this file.
6. **A resource-matched continuum comparison.** `Phase7_Rigidity` §3 separates a
   finitely-sited architecture from a field patch, but not at equal resource —
   the sited architecture has zero `μ⊗μ` resource. A comparison with real
   content would fix a budget in a common currency (say, total dissipated power)
   and show what each substrate buys with it. That needs a physical cost model
   the development does not have, and is closer to new physics than to new Lean.


---

## Critical Coupling Threshold `K_c = 2D` — part (a) COMPLETE 2026-08-29

Dimensional fix done, part (a) done in **both directions** (subcritical
2026-08-29, supercritical 2026-08-29 — see the final section of this file);
part (b) untouched and staying that way. Recorded here because three files defer to it in their scope
notes (`Phase3_CombinatorialThermodynamics`, `Phase4_RotatingFrame`,
`Phase8_ContinuousField`) and it is the only Table 1 row still marked
"Numerical", yet it appeared in no open item.

### Current state in Lean — the value itself is still a stipulation

| Declaration | What it is | What is proved about it |
|---|---|---|
| `critical_coupling D := 2 * D` | A named real number | Nothing |
| `mean_field_coupling sys := ∫ x, ∫ y, sys.K x y` | The kernel averaged over both arguments | `mean_field_coupling_const` — on a probability substrate a constant kernel has strength exactly that constant |
| `exhibits_phase_transition sys` (needs `[IsProbabilityMeasure volume]`) | `mean_field_coupling sys > critical_coupling sys.D` | `exhibits_phase_transition_const_iff` — reduces to `K > 2D` for constant kernels; witnessed both ways in `Examples.lean` §9 |

`critical_coupling` is no longer inert: `subcritical_fixed_point_eq_zero'` in the
new `Phase8_SelfConsistency.lean` is stated in terms of it (see below). What is
still true is that nothing is connected to `order_parameter_r_sq`,
`is_phase_locked`, `is_continuous_kuramoto_trajectory`, or any dynamics — the
new theorem is about the self-consistency equation, not about a trajectory. `2 * D` is a *stipulation*
in the Lean source; the content lives entirely in `simulations/kuramoto.py`,
which sweeps `K` and plots the measured order parameter against a drawn line at
`2D`.

### The dimensional defect — FIXED 2026-08-29

`exhibits_phase_transition` compared `∫ₓ∫_y K(x,y)` against `2D`. For a constant
kernel `K` on a substrate of measure `m` that integral is `K·m²`, so the
comparison tracked the substrate's *size* rather than its coupling and was
satisfiable by any kernel at all by inflating `m`.

**Fix:** `Phase8_ContinuousField.lean` now factors the left-hand side out as
`mean_field_coupling sys := ∫ x, ∫ y, sys.K x y` and requires
`[IsProbabilityMeasure (volume : Measure M)]` on `exhibits_phase_transition` —
the normalization the mean-field derivation of `K_c = 2D` is carried out in.
Two lemmas keep the definition honest rather than merely well-typed:

* `mean_field_coupling_const` — under the hypothesis, a constant kernel has
  mean-field strength exactly that constant. No factor of substrate size.
* `exhibits_phase_transition_const_iff` — the predicate reduces to `K > 2D`,
  the inequality the physics is about.

**Witnessed in `Examples.lean` §9.** `Cell` is a two-site substrate carrying the
*normalized* counting measure `(1/2)·count`; `cellVolume_prob` discharges the
probability hypothesis (so it is satisfiable at all), and the predicate holds of
`cellSys 3` at `D = 1` and fails for `cellSys 1` — it is neither vacuous nor
trivially true. The converse half matters more: `duoWeak_inflated` exhibits, on
the unnormalized `Duo` substrate of §5, a system coupled at `K = 1/2` against a
threshold of `1` — a factor of two *below* threshold — whose unnormalized double
integral is `2 > 1`. That system satisfied the old predicate. Mass was doing the
work, not coupling.

This also retires finding #12 of the Opus 5 evaluation (`exhibits_phase_transition`
flagged as an unused declaration): it now has two theorems and two witnesses.

**What is still not proved:** everything below. `critical_coupling` remains a
stipulation, unconnected to any trajectory or order parameter; the scope note on
the definition now says so in the source. Table 1 still reads "Numerical".

Manuscript: new paragraph in `main.tex` §Soundness ("A fourth defect was
dimensional…") and a `Phase8_ContinuousField` implementation note under
supplementary Theorem 4.

### What `K_c = 2D` actually is

For the noisy mean-field Kuramoto model with identical frequencies, the
stationary density of the Fokker-Planck equation at order parameter `r` is
`ρ(θ) ∝ exp((K r / D) cos θ)`, and self-consistency requires

    r = I₁(Kr/D) / I₀(Kr/D)

where `I₀`, `I₁` are modified Bessel functions. The right side has slope
`Kr/(2D)` at `r = 0`, so `r = 0` is the only solution when `K < 2D` and a
positive solution branches off when `K > 2D`. That is the whole content of the
threshold.

### Split the work — the reachable half and the unreachable half

**(a) Reachable: the self-consistency equation as real analysis.** Define

    R(K, r) := (∫_{-π}^{π} cos θ · exp((K r / D) cos θ) dθ)
             / (∫_{-π}^{π} exp((K r / D) cos θ) dθ)

and prove: for `K < 2D` the only `r ∈ [0,1]` with `r = R(K,r)` is `r = 0`; for
`K > 2D` there is an `r > 0` with `r = R(K,r)`. This is self-contained hard
analysis over Mathlib's integral API — no SDEs, no operator theory. It needs the
derivative of `R` in `r` at `0` (which is `K/(2D)`, the Bessel ratio's slope),
plus enough concavity or a monotonicity argument to rule out or produce a
crossing. Mathlib has no `Real.besselI`, so the Bessel ratio would have to be
handled directly as a ratio of integrals — which is probably easier than building
Bessel theory, since only the value and first derivative at `0` are needed.

Delivered on its own, (a) turns `K_c = 2D` into a **theorem about the
self-consistency equation**, with the stationary-density ansatz remaining a
postulate. Per the design rule in `Axioms.lean` §5 that postulate must be a
**field of a class** carrying the system's own stationary density, never a
standalone axiom — the shape that made three earlier axioms inconsistent. And,
per `Examples.lean`, the class then needs a witness or the theorem is vacuous:
the uniform density at `r = 0` is the obvious one, and a non-trivial witness
above threshold would need the positive root from (a) itself.

**(b) Not currently reachable: deriving the ansatz.** Getting from the SDE
`dθ = (ω + K·mean-field) dt + √(2D) dW` to that stationary density needs the
Fokker-Planck equation, existence and uniqueness of its stationary solution, and
the spectral argument that the uniform state loses stability at `K = 2D`. Mathlib
has Brownian motion but no Fokker-Planck operator, no stationary-measure theory
for SPDEs, and no bifurcation theory. This is a research-scale formalization
project, not a task.

### Recommendation — superseded

The dimensional fix and part (a) — both directions — are done. What remains is
(b), which stays untouched: it needs the Fokker-Planck operator,
stationary-measure theory for SPDEs and bifurcation theory, none of which
Mathlib has.

---

## Self-Consistency Equation (part (a)) — 2026-08-29 — DONE

`PhysicsOfConsciousness/Phase8_SelfConsistency.lean`, 400 lines, imported by
`PhysicsOfConsciousness.lean`. Zero `sorry`; every declaration depends only on
`propext`, `Classical.choice`, `Quot.sound`.

### What landed

Part (a) as scoped above, at the **sharp** threshold rather than the crude one.

| Declaration | Statement |
|---|---|
| `vonMisesZ`, `vonMisesM`, `vonMisesS`, `vonMisesC2` | `∫_{-π}^{π}` of `e^{a cos θ}` against `1`, `cos θ`, `sin²θ`, `cos 2θ` — i.e. `2π I₀`, `2π I₁`, and `2π I₂` |
| `besselRatio a` | `vonMisesM a / vonMisesZ a`, i.e. `I₁(a)/I₀(a)` as a ratio of integrals. Mathlib has no `Real.besselI`, and building one is unnecessary: only the ratio is ever needed |
| `vonMisesM_eq_mul_vonMisesS` | **`∫ cos θ·e^{a cos θ} = a ∫ sin²θ·e^{a cos θ}`.** Integration by parts with `u = sin`, `v = -e^{a cos}`; exact, since `sin (±π) = 0` kills the boundary term |
| `vonMisesC2_nonneg` | **`I₂(a) ≥ 0` for `a ≥ 0`** — the substantive result; see the proof sketch below |
| `vonMisesS_le_half_vonMisesZ` | `E_a[sin²θ] ≤ 1/2`, the same statement rearranged through `sin²θ = 1/2 - cos 2θ/2` |
| `besselRatio_le_half_self` | `R(a) ≤ a/2` |
| `subcritical_fixed_point_eq_zero'` | **For `0 ≤ K < critical_coupling D` and `D > 0`, the only `r ≥ 0` with `r = R(K,r)` is `r = 0`.** |
| `selfConsistency_zero` | `r = 0` *is* a solution, always — so the uniqueness theorem is about a non-empty solution set. §6 exercises the theorem on it |
| `subcritical_fixed_point_eq_zero`, `besselRatio_le_self` | The crude `K < D` versions from `sin² ≤ 1`. Kept deliberately: they localize the missing factor of two to a single pointwise bound |

`subcritical_fixed_point_eq_zero'` is the first theorem anywhere in the
development that mentions `critical_coupling`.

### The proof of `I₂(a) ≥ 0`, since it is the whole content

The predicted route was "handle the Bessel ratio directly as a ratio of
integrals," and that worked, but the useful decomposition turned out to be
different from the one anticipated. Two steps, no series and no Bessel theory:

1. **Integration by parts** turns `R` into `a · E_a[sin²θ]`. Bounding
   `E_a[sin²θ] ≤ 1` is immediate and gives a threshold at `D`.
2. **The factor of two is exactly `E_a[sin²θ] ≤ 1/2`,** equivalently `I₂(a) ≥ 0`.
   Fold `[-π, π]` onto `[0, π/4]` twice: `θ ↦ -θ` (evenness), then
   `θ ↦ π - θ`, which turns `e^{a cos θ}` into `e^{-a cos θ}` and leaves
   `cos 2θ` alone, then `θ ↦ π/2 - θ`, which flips the sign of `cos 2θ` and
   swaps `cos θ` for `sin θ`. What is left is
   `∫₀^{π/4} cos 2θ · (2 cosh(a cos θ) - 2 cosh(a sin θ)) dθ`,
   where both factors are visibly non-negative: `cos 2θ ≥ 0` on `[0, π/4]`, and
   `0 ≤ sin θ ≤ cos θ` there with `cosh` increasing in `|·|`.

Mathlib supplied every piece: `intervalIntegral.integral_deriv_mul_eq_sub`,
`integral_comp_neg`, `integral_comp_sub_left`, `Real.cos_two_pi_sub`,
`Real.cos_pi_div_two_sub`, `Real.sin_le_sin_of_le_of_le_pi_div_two`,
`Real.cosh_le_cosh`, `intervalIntegral_pos_of_pos_on`. No new analysis
infrastructure was needed, and the "sized in weeks" estimate above was wrong by
about an order of magnitude — recorded because the same estimate was wrong in
the same direction for mesh refinement.

### Independently checked numerically

Quadrature over `a ∈ [0, 20]` confirms `|M - a·S| / Z < 1.4e-15`,
`S - Z/2 ≤ -3.9e-13` (equality only at `a = 0`, as it should be), and
`min C₂ ≥ -1.4e-16`. This was a sanity check on the statements, not part of the
proof; it is not committed.

### What is still open, stated precisely

1. ~~**The supercritical direction.**~~ **DONE 2026-08-29** — and the estimate
   in this bullet was wrong. No second-order expansion was needed; continuity of
   `E(a) = 𝔼_a[sin²θ]` at `a = 0` plus the intermediate value theorem suffices.
   See the final section of this file.
2. **The ansatz — this is item (b) and stays out of reach.** The von Mises
   density is an input. Per the design rule in `Axioms.lean` §5 it must become a
   field of a class carrying the system's own stationary density if it is ever
   assumed in Lean rather than in prose; at present it is assumed in prose only,
   which is why the file declares no class and no axiom.
3. **The link to the dynamics.** `selfConsistency` touches neither
   `is_continuous_kuramoto_trajectory` nor `order_parameter_r_sq`. Until it does,
   `exhibits_phase_transition` still stands on the ansatz.

### Manuscript

* Table 1 row for `K_c` is now "Theorem (partial)" with the Lean column naming
  `Phase8_SelfConsistency` and stating what is assumed. Verified the table still
  fits the page — the first two phrasings overflowed it.
* `main.tex` Derivation 4: two new paragraphs, one giving the argument and one
  separating the three things it does not establish.
* `supplementary.tex`: a `Phase8_SelfConsistency.lean` implementation note under
  Theorem 4, and the Phase 4 note's "we do not formalize" corrected to "we
  formalize in one direction only."
* Both documents compile with zero warnings and zero errors.

---

## Open: Inventory of what is assumed rather than derived — 2026-08-29

Compiled by re-reading all 17 Lean files against the manuscript. The
development declares zero `axiom`s, and that is worth exactly as much as the
list below is short. An assumption that has moved into a class field, a theorem
hypothesis, or an unconstrained structure field is still an assumption; it has
only become *locatable*. This section is the location list, so that no future
pass has to rediscover it, and so that the ones worth attacking are separated
from the ones that are honest modelling choices.

Ordering within each group is by how much of a headline claim rests on the
assumption, not by difficulty.

### A. Instance obligations — postulates carried as class fields

These follow the `Axioms.lean` §5 design rule: each is an obligation a model
discharges, not a global assertion. All four classes are inhabited, so nothing
downstream is vacuous. The open question for each is whether the *witness* is
strong enough to mean anything.

| # | Assumption | Where | Witness | Verdict |
|---|---|---|---|---|
| A1 | `StatisticalMechanics.heat_eq` — dissipated heat equals `T` times the bath's entropy change | `Phase3_CombinatorialThermodynamics:307` | `boolStatMech` (`Examples` §1), a real one-bit erasure with a bijective `U` | Irreducible physical postulate; witness is non-degenerate (it reproduces `ΔQ = k_B T ln 2`). **Leave.** |
| A2 | `StructuralResonance.kl_bound` — `σ ≥ D_KL(P‖Q)/Δt` for the system's own distributions | `Phase3_KLBound:129` | `boolResonance` **and `boolDetuned`** (`Examples` §2) | **DONE 2026-08-29.** The perfectly-resonant witness (`KL = 0`) is joined by the one-bit eraser against a point-mass environment: `KL = log 2 > 0`, `σ = log 2 > 0`, and `boolDetuned_tight` proves the bound holds with *equality*, so it is attained and cannot be strengthened. |
| A3 | `LocalSectionSynchronization.phase_invariant_periodic` and `sync_to_section_eq` | `Phase4_MacroscopicScaling:56,61` | `cortexSync` (`Examples` §4) | Marked `[MODELLING]` in the source and derivable in principle from invariant-measure theory. The witness sets `phase ≡ 0` and discharges `sync_to_section_eq` by `rfl` — i.e. the local sections *are* restrictions by construction. Non-vacuous but weak. |
| A4 | `ThermodynamicCover.thermodynamic_equilibrium` — the cover's phase configuration already minimizes the Kuramoto potential | `Phase5_GlobalSection:43` | `cortexCover` (`Examples` §4) | **This is where Derivation 5's physics lives.** Lean proves "given a cover at the minimum, the sections glue"; getting there is the informal argument. The witness has constant phase, which is what makes the obligation dischargeable. Stated plainly in `Phase5`'s header and the supplementary. |

### B. Physical content carried in theorem hypotheses

Not axioms, not class fields — restrictions on the statement, which is the
easiest kind of assumption to overlook when reading a theorem name.

| # | Assumption | Where | Effect |
|---|---|---|---|
| B1 | `h_contracting : ContractingWith (1/2) predict`, plus `[MetricSpace (GlobalSection X)]`, `[CompleteSpace …]`, `[Nonempty …]` | `Phase6_ReflexiveTopology:87` | See §D1 — the largest gap in the list. |
| B2 | `h_mean` — the comparison class is restricted to fields of equal mean drift | `Phase8_ContinuousField`, `phase_locked_achieves_minimum_entropy` | The phase-locked state minimizes σ *among fields with the same mean drift*, not among all fields. Documented on the theorem. |
| B3 | `hvol : volume = Measure.count` | `Phase8_ContinuousField` §7, three theorems | The σ/gradient-flow link holds for **finite** substrates only. The continuum case needs differentiation under the integral sign in the kernel. Documented. |
| B4 | Identical natural frequencies `ω ≡ Ω` | `Phase4_RotatingFrame` | The rotating-frame reduction is exact only here. A frequency spread leaves residual detunings and the chain breaks. Documented in three files. |
| B5 | `h_min : ∀ phi', TotalEnergy phi ≤ TotalEnergy phi'` | `Phase1_Primitives`, `spontaneous_symmetry_breaking` | *Existence* of a global energy minimizer is assumed, not derived. No compactness or direct-method argument anywhere in the development. |
| B6 | `[IsProbabilityMeasure (volume : Measure M)]` | `Phase8_ContinuousField`, `exhibits_phase_transition` | Added deliberately (see the dimensional-fix section above); recorded here for completeness, not as a defect. |

### C. Unconstrained structure fields — data that ought to be determined

Fields that are free data where the physics says they should be forced by
something else in the same structure. These are definitional gaps: no theorem is
false because of them, but theorems about them say less than their names suggest.

| # | Gap | Where | Consequence |
|---|---|---|---|
| C1 | `TriangulatedManifold` never relates `complex` / `embedding` to `edge_region` | `Phase2_SimplicialBridge` | **DONE 2026-08-29.** `DiscreteThermodynamics` now carries `region` + `regular : IsRegularTriangulation TM region` as fields, so its edge weights are integrals over a geometrically constrained family. `TriangulatedManifold` itself is left as bare data on purpose — see the new section at the end of this file. |
| C2 | `ReflexiveBoundary.auto_resonance` is an arbitrary function of the global section | `Phase6_ReflexiveTopology:54` | Nothing constrains the avatar's state to track the field's. No theorem in the development mentions it. |
| C3 | `DiscreteThermodynamics.scalar_magnitude` is arbitrary subject only to non-negativity | `Phase2_SimplicialBridge:42` | The map from a stress-energy tensor to a scalar is modelling, not derivation. |

### D. Structures with no witness at all

An uninhabited class makes its theorems vacuous exactly as an inconsistent axiom
did — this is the failure mode the 2026-08-29 soundness audit was built to catch,
and `Examples.lean` closed it for Phases 1, 3, 4, 5 and 8. It is **not** closed
for the following.

1. **`ReflexiveBoundary` / `PredictiveModel` — Derivation 6, the Self.**
   **DONE 2026-08-29** — `Examples.lean` §10. `reflexive_topology_implies_self`
   is still the Banach fixed-point theorem with every physical commitment in a
   hypothesis, but the hypotheses are now known to be jointly satisfiable: a
   metric on `GlobalSection Cortex`, a completeness proof, `Nonempty` from
   `globalSect 0`, and a `ReflexiveBoundary` whose `auto_resonance` is the
   presheaf restriction rather than an arbitrary function. The residual weakness
   is recorded *as a theorem*: `contracting_implies_const` proves every
   contraction is constant under the 0/1 metric supplied, so the fixed point is
   that constant. Upgrading this needs a metric built from the measure-theoretic
   structure of `GlobalSection` (Prokhorov), which is a real project.

2. **`SymmetryInvariantAction` — and there is no Noether theorem.**
   **Prose fix DONE 2026-08-29.** The class still has one field, no instance and
   no consumer; that is now what `main.tex:87` says. The claim that invariance
   "dictates the conservation of energy and momentum via Noether's theorem" is
   qualified in place, and the footnote's "naturally emerge" is replaced by a
   statement that the formalization supplies vocabulary, not content, naming the
   three instance-free classes (`ContinuousSymmetryGroup`,
   `SymmetryInvariantAction`, `PseudoRiemannianManifold`). Proving an actual
   Noether theorem over Mathlib remains a project in itself and is not started.

3. **`VacuumManifold` is an empty class.** **DONE 2026-08-29** — deleted, with a
   comment in its place recording why. `supplementary.tex:26` claimed Derivation 1
   was formalized "by defining a `VacuumManifold`"; it now names `DynamicalVacuum`,
   which is the definition the theorems actually use.

4. `PlasticNeuralField`, `StochasticMatrix`, `PseudoRiemannianManifold` — no
   instances either, but nothing headline rests on them. Low priority.

### E. Steps that remain informal in prose

Recorded so the manuscript's claims and the Lean's claims stay separable.

1. ~~**`K_c = 2D`, supercritical direction.**~~ **DONE 2026-08-29.**
   `Phase8_SelfConsistency` now proves both directions and packages them as
   `critical_coupling_is_threshold`. What replaces this item, at a much smaller
   scale: of the coherent branch only *existence* is proved — not uniqueness, not
   dynamical selection, not continuity in `K`, so a discontinuous jump at
   threshold is not excluded — and `K = 2D` exactly is covered by neither
   theorem.
2. **The von Mises stationary density** is assumed in prose only — it is not
   even a class field. If it is ever assumed *in Lean*, the §5 design rule
   requires it to be a field of a class carrying the system's own stationary
   density. Deriving it is item (b): Fokker-Planck, stationary-measure theory for
   SPDEs, bifurcation theory. Out of reach.
3. **`lim_{t→∞} D_KL(P‖Q) = 0`** — supplementary Theorem 3. Monotone descent of
   σ plus `D_KL ≤ Δt·σ` does not give it: monotone-and-bounded yields *some*
   infimum, possibly positive, and the KL bound would additionally have to be
   tight. Needs a Łojasiewicz/coercivity estimate on σ and a statement relating
   the σ-minimizer to `KL = 0`. This is audit item #6 and is still open.
4. **Hardware.** The resource-matched content is the wiring-support result and
   the continuity content is the measure-theoretic one; the step from either to
   "von Neumann architectures cannot experience unified consciousness" is
   informal, and `main.tex` says so.
5. **Mesh refinement rate.** Lean proves convergence; the `O(1/N²)` rate is
   numerical only (`simulations/mesh_refinement.py`).

### Suggested order of attack — items 1–5 DONE 2026-08-29

1. ~~**C1**~~ — done. See "Regularity, the Self, and three smaller gaps" below.
2. ~~**D1**~~ — done, with its residual weakness proved rather than asserted.
3. ~~**D2**~~ — done (prose only, as recommended).
4. ~~**D3**~~ — done.
5. ~~**A2**~~ — done; the new witness also shows the bound is *tight*.
6. ~~Everything in E stays open and stays stated as open.~~ E1 closed
   2026-08-29; E2–E5 stay open and stay stated as open.

Remaining from this inventory: A3, A4 (weak-but-real witnesses), B1–B6
(hypotheses, all documented), C2, C3, D4, and E2–E5.

---

## Regularity, the Self, and three smaller gaps — 2026-08-29 — DONE

Items 1–5 of the inventory's suggested order of attack, in one pass. Zero `sorry`,
zero warnings, `#print axioms` on every new result reports only `propext`,
`Classical.choice`, `Quot.sound`. Both documents compile.

### C1 — `DiscreteThermodynamics` now carries its geometry

**What changed structurally.** `IsRegularTriangulation` and the two symmetric-double-sum
lemmas moved from `Phase2_MeshConvergence.lean` into `Phase2_SimplicialBridge.lean`, next
to the class they constrain. The predicate was generalized from `[PseudoMetricSpace M]` to
`[TopologicalSpace M]` (no metric is needed to *state* it — diameters only enter in the
convergence file) and its unused `[Fintype TM.V]` binder dropped.
`DiscreteThermodynamics` gained two fields:

```lean
region  : Set M
regular : IsRegularTriangulation TM region
```

**A signature change that was forced, not cosmetic.** `TM` and `I` had been *instance*
arguments of `DiscreteThermodynamics`, and neither appears in the resulting type
`DiscreteThermodynamics M`. So no projection out of a value could recover them: writing a
witness failed with `failed to synthesize TriangulatedManifold ℝ` even with the instance
supplied explicitly via `@`, because the structure-instance elaborator re-synthesizes
rather than unifies. They are now explicit parameters and the type reads
`DiscreteThermodynamics TM I`. Without this the structure was unusable on any space
carrying more than one triangulation — which is every space the convergence theorem is
about.

**What the geometry buys — three theorems that could not be stated before.**

* `weight_self` — `w(u,u) = 0`. The coupling matrix has zero diagonal, which is the
  precondition for reading `½ ∑ᵤ ∑ᵥ` as a sum over unordered edges.
* `face_of_weight_ne_zero` — `w(u,v) ≠ 0 → {u,v} ∈ complex.faces`. The discretization
  cannot invent a coupling between vertices the triangulation does not join. This is the
  statement the old class made unstatable, since nothing tied `edge_region` to `complex`.
* `total_weight_eq_setIntegral` — `½ ∑ᵤ ∑ᵥ w(u,v) = ∫_region |T|`. Nothing counted twice
  (`disjoint_region`), nothing dropped (`covers`). This is the precise sense in which the
  coupling matrix is *derived* from the continuum rather than posited, and it is what the
  everywhere-empty triangulation violates.

**Witness — `Examples.lean` §6.** `DiscreteThermodynamics` had **no instance anywhere**
before this pass; every theorem about `edge_weight` was conditional on a structure not shown
realizable, which the audit had not flagged. `gridThermo N` discretizes a constant unit
stress-energy on the uniform grid of `[0,1)`, reusing `gridRegular`. Checked non-degenerate:
`gridThermo_edge_weight` gives each consecutive edge weight exactly `1/N`, and
`gridThermo_total` gives `½ ∑∑ w = 1` for every `N`.

**What it does not establish.** The witness is one-dimensional and its tensor is constant,
so nothing here exercises a 2- or 3-dimensional edge region or a spatially varying
stress-energy. `TriangulatedManifold` is *still* bare data, deliberately: it is the data, and
regularity is a property. The difference from before is that the one structure claiming to
derive physics from it now requires the property instead of hoping for it.

**Deduplication.** `support_meshOfTriangulation` in `Phase2_MeshConvergence` is now one line
over the moved `iUnion_lt_edge_region` rather than a repeated proof.

### D1 — the Self is witnessed, and the witness's weakness is a theorem

`Examples.lean` §10, on the three-site cortex of §4. `gsMetric` (the 0/1 metric on
`GlobalSection Cortex`), `gsComplete` (Cauchy ⟹ eventually constant), `Nonempty` from
`globalSect 0`, `cortexReflexive` with `auto_resonance` the *presheaf restriction* to the
avatar region — not an arbitrary function, which is the C2 gap shown to be avoidable even
though the class does not force it. `cortexHasSelf` then applies
`reflexive_topology_implies_self`, and `cortexFixedPoint` names the fixed point.

The honest part is `contracting_implies_const`: under the 0/1 metric **every**
`ContractingWith K` map with `K < 1` is constant. So the contraction hypothesis is
discharged here in the only way it can be, and the "Self" this witness produces is the
constant section. Stated as a proved theorem rather than a caveat so it cannot be read past.
Upgrading needs a metric from the measure-theoretic structure of `GlobalSection` — the
Prokhorov metric `Phase6`'s header names, which nothing constructs.

Derivation 6 also gained a Table 1 row (`Theorem (conditional)`); it had none.

### D2 — the Noether sentence

`main.tex:87` no longer says the invariance "dictates the conservation of energy and
momentum via Noether's theorem" full stop. It says what Noether's theorem does physically,
then states that the Lean invariance is a class field with no instance, that no conserved
quantity is constructed, and that nothing downstream depends on one. The footnote's
"necessary physical symmetries, conserved quantities, and phase space constraints naturally
emerge" — which was simply false — is replaced by a statement that the formalization
supplies vocabulary rather than content, naming the three instance-free classes.

### D3 — `VacuumManifold`

Deleted, with a comment in its place saying why (an empty marker class asserts nothing, so
nothing could rest on it, and its presence implied a notion of vacuum manifold the
development does not have). `supplementary.tex:26` claimed Derivation 1 was formalized "by
defining a `VacuumManifold`"; it now names `DynamicalVacuum`, which is what the theorems use.

### A2 — a `StructuralResonance` witness that does work

`boolDetuned` (`Examples.lean` §2): the one-bit eraser of §1 driven by a point-mass
environment against uniform internal statistics. `KL = log 2 > 0`, `σ = log 2 > 0`, and
`boolDetuned_tight` proves `KL = Δt · σ` — **equality**. So the postulate is not merely
satisfiable, it is attained: it cannot be strengthened to a strict inequality, and this
witness compares two positive numbers rather than a positive number to zero.

It is a `def`, not an `instance`, because `boolResonance` already occupies
`StructuralResonance Bool`; the two theorems are applied to it explicitly.

### Manuscript

* `main.tex`: Table 1's Phase 2 row records the partition and face-support results; a new
  Derivation 6 row; the Derivation 6 section states what §10 does and does not establish;
  the Axiom 1 section and its footnote rewritten (D2). The table dropped to `\scriptsize` —
  the new row pushed the float over the page.
* `supplementary.tex`: the Phase 2 note gains a paragraph on the three new theorems and the
  grid witness; the Derivation 3 note records the tight witness; the Derivation 6 note
  records the witness and the 0/1-metric limitation; the `VacuumManifold` reference fixed.
* Both compile; the pre-existing count of overfull hboxes is unchanged.

---

## Supercritical Direction of `K_c = 2D` — 2026-08-29 — DONE

Item E1 of the inventory, and the last remaining half of part (a) of the
critical-coupling item. `PhysicsOfConsciousness/Phase8_SelfConsistency.lean`
gains a §6 (the old §6 becomes §7); the file is now 700 lines. Zero `sorry`,
zero warnings, `#print axioms` on every new result reports only `propext`,
`Classical.choice`, `Quot.sound`. `lake build` clean (17,608 jobs). Both
documents compile with the overfull-hbox counts unchanged from `HEAD`
(main 20, supplementary 14).

### The estimate in the previous section was wrong, and by a lot

That section said the supercritical direction "needs a *lower* bound
`R(a) ≥ a/2 - C a³` — a second-order expansion of the Bessel ratio, not a
monotonicity argument. Nothing above helps." Every clause of that is wrong
except the last three words of the second one.

What is actually needed is *qualitative*. The integration-by-parts identity of
§2 already writes

    R(a) = a · E(a),    E(a) := S(a)/Z(a) = 𝔼_a[sin²θ]

and §5 is the statement `E(a) ≤ 1/2`. The supercritical half is the statement
that `E` is *close to* `1/2` near the origin — which is just continuity of `E`
at `0` together with `E(0) = 1/2`, the latter because the weight is constant
there, so `E(0)` is the mean of `sin²` against Lebesgue measure on `[-π, π]`.
Given `K > 2D`, `D/K < 1/2`, so continuity puts `E > D/K` on a neighbourhood of
the origin, hence `R(K, r) = (Kr/D)·E(Kr/D) > (Kr/D)·(D/K) = r` for all small
`r > 0`. At the far end `R ≤ 1` always, since `R` is a mean of `cos θ`. The
intermediate value theorem does the rest.

**This is the third time the difficulty estimate in this file has been wrong in
the same direction** (mesh refinement, the subcritical half, this). Recorded in
`tasks/lessons.md` as a pattern: for an *existence* claim, a qualitative limit
plus IVT usually beats a quantitative expansion; the expansion is only needed if
the root's location or its uniqueness is wanted.

### What landed

| Declaration | Statement |
|---|---|
| `continuous_vonMisesZ`, `continuous_vonMisesM`, `continuous_vonMisesS` | The three moments are continuous in the concentration. Three lines each, from `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`; no dominated-convergence argument is written by hand |
| `vonMisesZ_zero`, `vonMisesC2_zero`, `vonMisesS_zero` | `Z(0) = 2π`, `C₂(0) = 0`, `S(0) = π` |
| `vonMisesSRatio` | `E(a) = S(a)/Z(a)`, with `continuous_vonMisesSRatio` and `vonMisesSRatio_zero : E(0) = 1/2` |
| `besselRatio_eq_mul` | `R(a) = a · E(a)` — the §2 identity with the slope factored out. Both bounds on `R` in the file now go through this form |
| `vonMisesM_le_vonMisesZ`, `besselRatio_le_one` | `R(a) ≤ 1`, from `cos θ ≤ 1`. This is what makes the map undershoot at `r = 1` |
| `continuous_selfConsistency` | `r ↦ R(K, r)` is continuous |
| `supercritical_fixed_point_exists` | **For `K > critical_coupling D`, there is an `r` with `0 < r ≤ 1` and `r = R(K, r)`** |
| `critical_coupling_is_threshold` | The two halves in one statement |
| `exhibits_phase_transition_coherent` | **A substrate satisfying `exhibits_phase_transition` admits a positive stationary order parameter** |

### Why `exhibits_phase_transition_coherent` matters more than its one-line proof

Before this pass, `critical_coupling` was a named real number with one theorem
mentioning it, and `exhibits_phase_transition` compared `mean_field_coupling`
against it — so *satisfying the predicate implied nothing*. It now implies the
existence of a coherent solution of the self-consistency equation. The proof is
`supercritical_fixed_point_exists sys.h_D_pos h`, one line, because
`exhibits_phase_transition` unfolds definitionally to the theorem's hypothesis;
the content is that the two definitions were finally made to meet.

The scope note on `critical_coupling` in `Phase8_ContinuousField.lean` — which
read "`critical_coupling` is a *stipulation* in this development, not a result"
— is rewritten accordingly, and now says precisely what *is* still assumed (the
von Mises density) and what is still unconnected (the trajectories).

### Non-vacuity

§7 discharges the hypotheses of each half at concrete values: `K = 3`, `D = 1`
is above `critical_coupling 1 = 2` and a coherent solution exists; the same
`K = 3` with `D = 2` is below `critical_coupling 2 = 4` and only `r = 0`
survives. The pair matters — a threshold theorem whose hypotheses can only be
discharged on one side is half vacuous.

### Independently checked numerically

Trapezoid quadrature over `[-π, π]`: `E(0) = 0.5` to machine precision; the
positive root of `r = R(Kr/D)` is `r ≈ 0.7242` at `(K, D) = (3, 1)` and
`r ≈ 0.3037` at `(2.1, 1)`; and `R(Kr/D) - r < 0` for all `r ∈ (0, 1]` at
`(3, 2)` and `(1.9, 1)` — i.e. no positive root below threshold, matching the
subcritical theorem, and the two Lean examples land on the two sides. A sanity
check on the statements, not part of the proof; not committed.

### What is still open, stated precisely

1. **Only existence of the coherent branch.** Not uniqueness, not that it is the
   dynamically selected solution, and not that it varies continuously with `K` —
   so nothing here rules out a discontinuous jump at threshold rather than the
   continuous (supercritical, in the technical sense) bifurcation the literature
   describes. Getting continuity of the branch needs a monotonicity or implicit
   function theorem argument on `R`, neither of which is present: `R` is never
   shown increasing anywhere in the file.
2. **`K = 2D` exactly** is covered by neither theorem.
3. **The ansatz — item (b), unchanged and out of reach.** The von Mises density
   is an input. Fokker-Planck, stationary-measure theory for SPDEs, bifurcation
   theory.
4. **The link to the dynamics — unchanged.** `selfConsistency` touches neither
   `is_continuous_kuramoto_trajectory` nor `order_parameter_r_sq`. This is now
   the *only* thing standing between `exhibits_phase_transition` and a statement
   about a trajectory, and it is the item worth attacking next in this area.

### Manuscript

* `main.tex`: Table 1's `K_c` row records both directions (status stays
  "Theorem (partial)" — the density is still assumed); the Soundness section's
  fourth-defect paragraph no longer says the threshold "remains a stipulation
  unconnected to any trajectory or order parameter"; Derivation 4 gains a
  paragraph giving the supercritical argument and has its "three things are not
  established" paragraph rewritten around what is actually left.
* `supplementary.tex`: the Phase 4 note's "K_c … is not formalized in Lean" —
  which was already stale — corrected; the `Phase8_ContinuousField` note's
  "in one direction only" corrected to both, and the predicate's new consequence
  recorded; the `Phase8_SelfConsistency` note gains the supercritical theorem,
  its proof sketch, and the sharpened scope list; the rotating-frame note's
  "`K_c`, which is not formalized" corrected.
* Both compile with zero errors, zero undefined references, and the same
  overfull-hbox counts as `HEAD`.

---

## Open items — consolidated ledger, 2026-08-29

Everything still open in one place, gathered from the Opus 5 evaluation, the
soundness audit, the assumption inventory and the sections above, so that no
future pass has to reconstruct the list by reading the whole file. Items are
grouped by whether they are *reachable now*, *reachable with real work*, or
*out of reach with current Mathlib*; within each group they are ordered by how
much of a headline claim rests on them.

Nothing here is a defect in what is currently proved. These are the places where
the Lean says less than the prose would like it to, and every one of them is
already stated as such in a doc-string and in the manuscript. The purpose of the
list is to keep it that way.

### Group 1 — reachable now

| # | Item | Where | What it takes |
|---|---|---|---|
| ~~**O1**~~ | **DONE 2026-08-29** — see the final section of this file. ~~**`selfConsistency` names a fixed-point equation but nothing in Lean says it is about an order parameter.**~~ The reading "`r` is the mean of `cos θ` under the density it induces" lives entirely in the doc-string; `selfConsistency K D r` is literally `besselRatio (K * r / D)` and could be any function of `r` for all the Lean knows | `Phase8_SelfConsistency` §4 | Define the von Mises *density* `e^{a cos θ}/Z(a)`, prove it is a probability density on `[-π, π]`, define the continuum order parameter `∫ e^{iθ} ρ(θ) dθ` mirroring `order_parameter_complex`, and prove it equals `besselRatio a` — real part `R(a)`, imaginary part `0` by oddness. Then a fixed point of `selfConsistency` is exactly a density reproducing its own order parameter. This is the cheapest item on the list and it is the one that makes the file's central definition non-tautological |
| **O2** | **C2 — `ReflexiveBoundary.auto_resonance` is an arbitrary function of the global section.** Nothing constrains the avatar's state to track the field's, and no theorem in the development mentions the field | `Phase6_ReflexiveTopology:54` | `Examples.lean` §10 already shows the presheaf restriction is a legal choice, so the constraint is known satisfiable. Either add a predicate `IsRestrictionResonance` and a theorem that uses it, or state as a theorem what goes wrong without it. Do **not** strengthen the class to a field without checking rule §3 of `PhysicsOfConsciousness/AGENTS.md` |
| ~~**O3**~~ | **DONE 2026-08-29.** ~~**B5 — existence of a global energy minimizer is a hypothesis, never a witness.**~~ `spontaneous_symmetry_breaking` takes `h_min : ∀ phi', TotalEnergy phi ≤ TotalEnergy phi'` as given; no compactness or direct-method argument exists anywhere in the development | `Phase1_Primitives` | Exhibit one system where `h_min` is discharged rather than assumed — the `unitAction` witness of `Examples.lean` §3 is on a one-point spacetime, where the minimizer is whatever minimizes `V` pointwise, so this may be a short addition. That would make the theorem non-vacuous in the same sense the other witnesses do. A general direct-method argument is Group 2 |
| ~~**O4**~~ | **SUBSUMED 2026-08-30 by O5** — `ThermodynamicCover.phase_locked` answers the same question one class up, and what remains of it is recorded as **O19** in the final section. ~~**A3 — the `LocalSectionSynchronization` witness is weak.**~~ `cortexSync` sets `phase ≡ 0` and discharges `sync_to_section_eq` by `rfl`; the local sections *are* restrictions by construction | `Phase4_MacroscopicScaling:56,61`, `Examples` §4 | ~~A witness with a non-constant phase field, or a proof that no such witness exists under the current class shape (which would be the more useful outcome, as `contracting_implies_const` was for D1)~~ — the second outcome is what happened |
| ~~**O5**~~ | **DONE 2026-08-30 — see "A cover with a non-constant phase" at the end of this file.** The answer has a negative half: `ThermodynamicCover.phase_locked` proves the class shape *forbids* a phase field that is non-constant modulo `2π`, and `ThermodynamicCover.glued_section_eq` proves the glued section is the invariant measure the cover already carried. ~~**A4 — the `ThermodynamicCover` witness has constant phase**, which is what makes `thermodynamic_equilibrium` dischargeable at all. This is where Derivation 5's physics lives~~ | `Phase5_GlobalSection:43`, `Examples` §4, §13 | ~~Same shape as O4: a cover at a non-trivial minimum of the Kuramoto potential.~~ Done both ways: the witness in §13 and the impossibility proof in `Phase5_GlobalSection` |
| ~~**O6**~~ | **DONE 2026-08-29.** ~~**D4 — four classes still have no instance:**~~ `PlasticNeuralField`, `StochasticMatrix`, `PseudoRiemannianManifold`, `ContinuousSymmetryGroup`. Nothing headline rests on them, but rule §2 of the Lean `AGENTS.md` applies to them as much as to the others | `Phase8_ContinuousField:155`, `Phase3_CombinatorialThermodynamics:192`, `Phase1_Primitives:47,123` | Each is a short witness. `StochasticMatrix` on `Bool` and `PlasticNeuralField` on the `Duo` substrate of `Examples` §5 are both nearly free. Alternatively delete what is unused, as `VacuumManifold` was |
| **O7** | **C3 — `DiscreteThermodynamics.scalar_magnitude` is arbitrary subject only to non-negativity.** The map from a stress-energy tensor to a scalar is modelling, not derivation | `Phase2_SimplicialBridge:42` | Probably *leave*, but say so in the source: if it is a modelling choice, mark it `[MODELLING]` the way `Phase4_MacroscopicScaling`'s fields are, so it is not mistaken for an oversight. Listed here so the decision gets recorded either way |

### Group 2 — reachable, but real work

| # | Item | What it takes |
|---|---|---|
| ~~**O8**~~ | **DONE 2026-08-30 — see "The coherent branch is a single point" at the end of this file.** All three gaps are closed. `K = 2D` is covered (`fixed_point_eq_zero_of_le_critical`), a discontinuous jump at threshold is excluded (`coherent_branch_continuous_at_threshold`), and **uniqueness** is now `vonMisesSRatio_strictAntiOn` — `E` is strictly *decreasing* on `[0, ∞)`, which is more than the injectivity the level-set form asked for. The route recorded here was not the route taken and was the harder one: no derivative of `E`, no differentiation under the integral sign, and the covariance never appears. Fold `[-π, π]` onto `[0, π/2]` first (the reflection *is* the `X ↦ -X` symmetrisation the tilt was supposed to beat), then cross at the mean instead of integrating over a square. `besselRatio_strictMono` (`R` strictly increasing on `ℝ`) came out of the same argument with no fold, and closed the separate "Monotonicity of `R`" gap the file header carried | `Phase8_SelfConsistency` §7 | Done |
| ~~**O9**~~ | **DONE 2026-08-30 — see "The Self's metric" at the end of this file.** ~~**B1 — the Self's metric is 0/1, and `contracting_implies_const` proves that forces the fixed point to be constant.**~~ The metric is now the uniform distance between the densities of the measures the sections glue to, `massEquiv` proves global sections *are* those measures, and `relax_dist` gives a non-constant map contracting by exactly `1/2` with a unique fixed point. Two premises of the recorded plan were wrong and are corrected there: `isIso_toSheafify` is for the *Grothendieck* sheafification, not `TopCat.Presheaf.sheafify`, which has no adjunction in Mathlib; and `μ ↦ ½μ + ½μ₀` is **not** a Lévy–Prokhorov contraction on a discrete substrate | 
| **O10** | **B3 — the σ/gradient-flow link holds for finite substrates only** (`hvol : volume = Measure.count`) | Differentiation under the integral sign with respect to the kernel. Mathlib has `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the work is in the domination hypotheses |
| **O11** | **B2 — `h_mean` restricts the comparison class** to fields sharing the phase-locked state's mean drift, so minimality is Jensen alone | Model how `Omega_avg` varies with the competitor field. Stated as the honest scope on the theorem; removing it changes what is claimed |
| **O12** | **D2 — there is still no Noether theorem.** The class is now inhabited (`Examples.lean` §11, a `ℤ₂` action on a double well, with symmetry breaking exhibited), but no conserved quantity is constructed and no theorem consumes a symmetry group | **Estimate corrected 2026-08-29 — see "Noether: a feasibility probe" at the end of this file.** "A project in itself" is right for the *field-theoretic* theorem and wrong for point mechanics, which was prototyped end to end in one session (~200 lines, zero `sorry`). The structural obstacle is not difficulty: `SymmetryInvariantAction` has **no dynamics**, so no conserved quantity can be attached to it at all |
| ~~**O19**~~ | **DONE 2026-08-30 — see "The gluing produces its object" at the end of this file.** ~~Derivation 5's gluing is a uniqueness theorem, not an emergence theorem~~ Both global-object fields are removed from `LocalSectionSynchronization`; `probability_glue_unique` isolates the sheaf condition, `ThermodynamicCover.invariantMeasure` constructs the section, and `sync_to_section_eq` is now a theorem. `Examples.lean` §14 is a cover whose glued section is neither of the profiles it was built from | ~~Restate `LocalSectionSynchronization` …~~ done as described; the estimate "touches a class every downstream file uses" was right about the blast radius and wrong about the cost — see the section for why |
| **O21** | **§10's germ–measure dictionary is built at `⊤` only.** `density`, `massEquiv` and `sectionOfMass` all speak about sections over `⊤`, so `Examples.lean` §14's patch-local sections have to be written as restrictions of global measures even though nothing in the class requires it. Opened 2026-08-30 by O19 | Generalise `massMeasure`/`sectionOfMass` to an arbitrary open `U` — `stalkMass` and `massAt` are already stated at arbitrary opens, so this is bookkeeping — and rebuild §14's local sections directly. Small; Group 1 really, listed here only because it was opened alongside O19 |
| **O20** | **PARTLY DONE 2026-08-30 — see "A dynamics that runs" at the end of this file.** Uniqueness of trajectories is proved on all of `ℝ` (`is_kuramoto_trajectory_unique`, from `kuramotoField_lipschitz`), and `Examples.lean` §15 exhibits a trajectory that starts unsynchronised and converges to the potential's global minimum with `r² → 1`. Parts (a-existence), (b), (c), (d) and (e) remain open in general. ~~Nothing in the development runs a dynamics into the minimum.~~ `ThermodynamicCover.thermodynamic_equilibrium` *assumes* the cover sits at the potential minimum; `Phase4_RotatingFrame` says what that minimum is and `potential_min_iff_phase_locked` (2026-08-30) says exactly which configurations attain it, but no trajectory is shown to reach one. The only trajectory in the whole development is `pairTrajectory Ω t = Ω·t` (`Examples.lean` §7) — a rigid rotation that *starts* synchronised, so it never converges to anything. Neither is any solution shown to **exist**: `is_kuramoto_trajectory` is a predicate, and outside §7 nothing inhabits it | See the decomposition below — parts (a)–(c) are reachable now, (d) is blocked on Mathlib, and (e) is **false as usually stated** |

### Group 3 — out of reach with current Mathlib

| # | Item | Blocker |
|---|---|---|
| **O13** | **The von Mises ansatz** — deriving the stationary density from the SDE. This is part (b) of the critical-coupling item | Fokker–Planck operator, existence and uniqueness of stationary solutions, bifurcation theory. None in Mathlib |
| **O14** | **The link from `selfConsistency` to the dynamics.** O1 is done, so the fixed point is now the order parameter of a *density*; it is still not the order parameter of a *trajectory*. `circularOrderParameter` is an integral against a density, `order_parameter_complex` is an average over finitely many oscillators, and no theorem relates them | The mean-field limit — propagation of chaos for the finite Kuramoto system. This is a research programme, not a task. **With O1 done this is the only thing standing between `exhibits_phase_transition` and a statement about a trajectory**, and the doc-strings and manuscript now state the gap in exactly those terms |
| **O15** | **`lim_{t→∞} D_KL(P‖Q) = 0`** (supplementary Theorem 3, audit item #6). Monotone descent of σ plus `D_KL ≤ Δt·σ` does not give it: monotone-and-bounded yields *some* infimum, possibly positive, and the KL bound would additionally have to be tight | A Łojasiewicz or coercivity estimate on σ, plus a statement relating the σ-minimizer to `KL = 0`. Neither exists in the development. The prose must keep saying it is unformalized until it does |
| **O16** | **Mesh refinement rate.** Lean proves convergence; the `O(1/N²)` rate is numerical only | A Riemann-sum error expansion. The convergence proof does not carry the rate |
| **O17** | **Hardware.** The step from the wiring-support result and the measure-theoretic continuity result to "von Neumann architectures cannot experience unified consciousness" is informal | Not a formalization gap so much as a philosophical one; `main.tex` says so |
| **O18** | **Sheaf global section ↔ unity of experience is a stipulation, not a derivation** | The framework's core philosophical commitment, fenced by the Russellian-monism framing. Not a fixable defect; recorded so it is not mistaken for one |

---

## O1 — the self-consistency equation is about an order parameter — 2026-08-29 — DONE

`Phase8_SelfConsistency.lean` §7 (the non-vacuity section becomes §8). File is
now ~880 lines. Zero `sorry`, zero warnings, `#print axioms` on every new result
reports only `propext`, `Classical.choice`, `Quot.sound`. `lake build` clean
(17,608 jobs). Both documents compile with overfull-hbox counts unchanged from
`HEAD` (main 20, supplementary 14); Table 1 re-checked visually and still fits
its page with room to spare.

### The gap this closes

`selfConsistency K D r` is *defined* as `besselRatio (K * r / D)`. Everything
proved about it before this pass — subcritical uniqueness, supercritical
existence, the threshold — was a statement about fixed points of that function,
and nothing in the Lean source said the function had anything to do with an
order parameter. The reading that gives the equation its name lived entirely in
doc-strings. This is a mild version of the failure mode `AGENTS.md` §1 warns
about: not a laundered axiom, but a definition whose physical meaning was
carried by prose.

### What landed

| Declaration | Statement |
|---|---|
| `vonMisesDensity a θ := vonMisesWeight a θ / vonMisesZ a` | The actual density, not the unnormalized weight |
| `vonMisesDensity_pos`, `vonMisesDensity_integral_eq_one` | It is a probability density on `[-π, π]`. Without this, "the mean of `cos θ` under the density" is an abuse of language |
| `vonMisesDensity_zero` | At zero concentration the density is uniform, `1/(2π)` |
| `vonMises_mean_cos` | `E_a[cos θ] = R(a)` — the Bessel ratio read as a mean |
| `vonMises_mean_sin` | `E_a[sin θ] = 0`, by oddness. This is why the order parameter is real |
| `circularOrderParameter rho := ∫_{-π}^{π} e^{iθ} ρ(θ) dθ` | The continuum analogue of `Phase4`'s `order_parameter_complex` |
| `circularOrderParameter_vonMises` | **That average is exactly `besselRatio a`** |
| `fixedPoint_iff_selfReproducing` | **`r = R(K, r)` ⟺ the density `r` induces has order parameter `r`.** The equivalence the name promised |
| `incoherent_density_uniform` | The solution `r = 0` *is* the uniform density, order parameter `0` |
| `supercritical_coherent_density` | Above threshold there is a von Mises density whose own order parameter is positive |

Mathlib supplied everything: `intervalIntegral.integral_ofReal`,
`Complex.exp_mul_I`, `intervalIntegral.integral_comp_neg`,
`intervalIntegral.integral_mul_const`. The complex-valued interval integral
needed no special handling — split the integrand into real and imaginary parts
pointwise, then `integral_add` and `integral_ofReal`.

### What it does not establish

* **No link to `order_parameter_complex`.** That is `(1/N) ∑ e^{iθⱼ}` over a
  finite system; `circularOrderParameter` is an integral against a density.
  Relating them is the mean-field limit (propagation of chaos), which is O14 and
  stays out of reach. Said explicitly in the doc-string of
  `circularOrderParameter`, in the file header, in `main.tex` and in the
  supplementary — this is now the *whole* of what separates the threshold
  predicate from a statement about dynamics, and it is worth keeping it stated
  that sharply.
* **No trajectory anywhere.** `is_continuous_kuramoto_trajectory` and
  `entropy_production_rate` are still unmentioned in this file.
* **The ansatz is unchanged.** `vonMisesDensity` is *defined* to be the von
  Mises density; nothing derives it from the SDE. O13.

### Non-vacuity

§8 gains a third example: at `K = 3`, `D = 1` the density statement fires and
produces a positive-order-parameter density, alongside the existing pair of
examples on the two sides of the threshold.

### Manuscript

* `main.tex`: Table 1's `K_c` row records the density reading; Derivation 4 gains
  a paragraph on the identification and has its closing gap statement rewritten
  around the mean-field limit as the single remaining separation.
* `supplementary.tex`: the `Phase8_SelfConsistency` note gains the §7 results and
  a correspondingly sharpened scope sentence.

---

## O3 and O6 — the minimizer hypothesis and the last uninhabited classes — 2026-08-29 — DONE

`PhysicsOfConsciousness/Examples.lean` gains §11 and §12. Zero `sorry`, zero
warnings, `#print axioms` on every new result reports only `propext`,
`Classical.choice`, `Quot.sound`. `lake build` clean (17,608 jobs). Both
documents compile with overfull-hbox counts unchanged from `HEAD`; Table 1
re-checked visually and still fits its page.

### §11 — a double well, and three things it settles

`§3`'s existing `ActionPrinciples` witness is `V v = v²` on a one-point
spacetime. It proves inhabitability and nothing else: the vacuum is a single
point, so there is no symmetry to break, and on a one-point spacetime "almost
everywhere" and "everywhere" coincide, so the theorem's actual conclusion is
invisible. §11 uses `Bool` with `Measure.dirac true` — a probability measure
supported on one of two points — and the double well `V v = (v² - 1)²`, whose
vacuum manifold `{-1, 1}` is degenerate.

* **O3/B5 — `h_min` is discharged.** `spontaneous_symmetry_breaking` takes
  `h_min : ∀ phi', TotalEnergy phi ≤ TotalEnergy phi'` as a hypothesis, and no
  compactness or direct-method argument exists anywhere in the development.
  `wellSpike_global_min` proves it. The theorem is now applied at least once to a
  system where its own hypothesis is a fact rather than an assumption.
* **The `∀ᵐ` is proved necessary.** `wellSpike` sits at the vacuum on the support
  and at `0` off it. `wellSpike_ae_vacuum` holds; `wellSpike_not_everywhere_vacuum`
  proves the pointwise version *fails* for that same field. The doc-string on
  `pointwise_vacuum_of_global_min` had asserted that the old `∀ x` form was "one
  of the reasons the axiomatic formulation was unsound"; that is now a theorem,
  in the style of `contracting_implies_const`.
* **Symmetry breaking exhibited, not typed.** `signSymmetry` is the `ℤ₂` action
  `v ↦ ±v` (`G = ℤˣ`); `signInvariant` discharges `total_energy_invariant`
  because `(±v)² = v²` — the first instance of `SymmetryInvariantAction` in the
  development. `symmetry_swaps_vacua` shows the action exchanges the two minima,
  and `wellSpike_partner_same_energy` / `wellSpike_partner_ne` show the minimizer
  and its image have equal energy and differ: a symmetric functional with a
  non-symmetric minimizer.

**What §11 does not establish.** No conserved quantity, so no Noether theorem —
and `ℤ₂` is discrete, so there is no one-parameter family to differentiate along
even in principle. The `Continuous` in `ContinuousSymmetryGroup` is a name: the
class carries no continuity or homomorphism law, which is why the instance is
cheap and why it proves less than its name suggests. The spacetime is two points
with a Dirac measure, so no geometry is exercised.

### §12 — the last three structures

| Witness | Non-degeneracy |
|---|---|
| `boolStochastic : StochasticMatrix Bool` | The fair coin. Nothing consumes `StochasticMatrix`; the witness settles rule §2 rather than adding content |
| `duoPlastic : PlasticNeuralField Duo` | Reuses `duoFlow` from §5, so `duoPlastic_gradient_descent` proves `is_gradient_descent` with σ`(t) = e^{-2t}` — strictly decreasing, not `Antitone` discharged by a constant |
| `realMetric : PseudoRiemannianManifold 𝓘(ℝ,ℝ) ℝ` | The Euclidean form `g(u,v) = u·v`. Positive definite, so Riemannian rather than properly pseudo-Riemannian; the class asks only for symmetry and non-degeneracy, and a Lorentzian witness needs a 2-dimensional model |

**A Mathlib obstacle worth recording** (also in `tasks/lessons.md`):
`TangentSpace I x` is a plain `def`, so its `Mul`, `AddCommGroup` and `Module`
instances are *not* the ones instance search finds for `ℝ`, and writing the
`PseudoRiemannianManifold` field proofs inline fails with application-type
mismatches even though everything is definitionally equal — and `(u : ℝ)`
ascription does not repair it. The fix is to state the form and its two laws as
separate `ℝ`-typed lemmas (`realForm_apply`, `realForm_symm`, `realForm_nondeg`)
and pass those as the fields, where the defeq check succeeds.

### Manuscript

* `main.tex`: the Axiom 1 section no longer says `SymmetryInvariantAction` "has
  no instance in the development" — it describes the `ℤ₂` witness and what it
  does and does not establish; the footnote's claim that all three classes are
  instance-free is replaced by a statement that they are now inhabited but that
  no theorem consumes a symmetry group or a metric, so the section still supplies
  vocabulary rather than content. Table 1's first and third rows record the
  double-well witness and the proof that the a.e. cannot be strengthened.
* `supplementary.tex`: Theorem 1's implementation note gains the §11 witness, the
  discharged minimisation hypothesis, and the necessity of the almost-everywhere.

---

## Noether: a feasibility probe — 2026-08-29

Asked whether Noether's theorem is out of reach. It splits in two, and the two
halves have opposite answers. Recorded here because the O12 estimate said
"a project in itself" without distinguishing them, and half of that is wrong.

### Mathlib has nothing — and it does not matter

`grep` over all of Mathlib: **no** Euler–Lagrange equations, **no** calculus of
variations, no Noether (the `Noetherian` files are ring theory). But the
theorem does not need that infrastructure. Take the Euler–Lagrange equation as
the *definition* of a physical trajectory — which is standard, and is not
laundering, since it is a condition on the trajectory, not on the conclusion —
and Noether is a product rule.

### Prototyped end to end, ~200 lines, zero `sorry`

Not committed; it lives in the session scratchpad. All of the following compiles
and reports only `propext`, `Classical.choice`, `Quot.sound`.

| Result | Statement |
|---|---|
| `Lq`, `Lv` | The partial derivatives, **read off a supplied total derivative** `dL p : ℝ × ℝ →L[ℝ] ℝ` rather than posited as separate data. The only hypothesis on `L` is `∀ p, HasFDerivAt L (dL p) p` — plain differentiability |
| `ELTrajectory` | `q`, `v`, `a` with `q' = v`, `v' = a`, and `d/dt (∂L/∂v) = ∂L/∂q` |
| `noether` | **For a generator `X` with `∂L/∂q · X + ∂L/∂v · (X' · v) = 0`, the charge `∂L/∂v · X(q)` is constant along any EL trajectory.** Two lines from the product rule |
| `energy_conserved` | **`v · ∂L/∂v − L` is constant along any EL trajectory**, `L` having no explicit `t`-dependence. Three lines |
| `Lq_eq_zero_of_translation_invariant` | `L(q + c, v) = L(q, v)` for all `c` **implies** `∂L/∂q = 0` — derived by uniqueness of derivatives, not assumed. Momentum conservation then follows from `noether` with `X ≡ 1` |

Witnesses, chosen so the theorems are actually tested:

* **Harmonic oscillator** `L = v²/2 − q²/2`, trajectory `q = sin`, `v = cos`.
  `swing_moves` proves both coordinates genuinely vary, and `swing_energy` gives
  energy `= 1/2` at every time — so the conservation is a real cancellation, not
  a consequence of nothing moving. This is the lesson from `Examples.lean` §11
  applied in advance.
* **Free particle** `L = v²/2` with uniform motion: momentum conserved via the
  general theorem.
* **Negative checks**, so the symmetry predicate is not vacuously true: scaling
  (`X = id`) is *not* a symmetry of the free particle, and the oscillator has
  *no* translation symmetry — so momentum is genuinely not conserved there while
  energy still is. The two theorems are not proving the same thing.

### What stays out of reach — and it is the one the manuscript invokes

`main.tex` claims invariance under the **Poincaré group** dictates conservation
of energy and momentum. That is the field-theoretic Noether theorem: an action
functional over spacetime, invariance under a Lie group acting on fields, and a
conserved *current* with `∂_μ T^{μν} = 0`. It needs functional derivatives on
infinite-dimensional configuration spaces, field-theoretic Euler–Lagrange
equations, group actions on jet bundles, and the divergence theorem on
manifolds. Mathlib has none of it. The point-mechanics theorem above is one
degree of freedom and one time variable; the gap in generality is large and
would have to be stated, not glossed.

### The structural finding, which matters more than the estimate

**`SymmetryInvariantAction` cannot carry a Noether theorem, however much work is
done on it.** Its one field says `TotalEnergy` is invariant under a group action
on *static* field configurations. A conserved quantity is a statement about time
evolution — something is conserved *along a trajectory* — and the class has no
time, no Lagrangian, and no equation of motion. Noether needs three things: an
action, a notion of trajectory, and a symmetry. The development has only the
third. So the honest options are:

1. **Land the mechanics theorem as its own file**, stated at its own level of
   generality, and have `main.tex` say that Noether is proved for one degree of
   freedom while the Poincaré/field-theoretic version it invokes is not. This is
   a real theorem where there is currently only vocabulary.
2. **Leave it**, and keep the current prose, which already says plainly that
   there is no Noether theorem and that nothing downstream depends on one.

Option 1 introduces Lagrangian point mechanics, a topic the development does not
otherwise touch, so it is a scope decision rather than a formalization one.

---

## What to spend effort on next — ranking and plan, 2026-08-29

Written after a feasibility probe on Noether (previous section) raised the wider
question of which open item most strengthens the *paper*, as opposed to which is
most interesting to formalize. The two are not the same and this section records
the difference so a later pass does not re-litigate it.

### First, the verdict on Noether: it does not strengthen the paper — do not land it yet

The probe showed the point-mechanics theorem is cheap (~200 lines, done). It
should still stay in the scratchpad, for three reasons.

1. **Nothing downstream uses it.** The chain is symmetry breaking → defect →
   boundary → Landauer → resonance → Kuramoto → gluing → Self. Conservation of
   energy and momentum is never invoked again after the Axiom 1 section. Proving
   it adds a leaf, not a link.
2. **The generality gap would cost more than the theorem gains.** The prose says
   *Poincaré group acting on fields over spacetime*; the Lean would be
   `L : ℝ × ℝ → ℝ` — one degree of freedom, one time variable. A Table 1 row
   reading "Noether's theorem — Theorem" backed by that is exactly the "math
   theatre" charge `main.tex:55` pre-empts. The paper's main rhetorical asset is
   that its scope statements are exact; this would spend it.
3. **It cannot attach to what exists.** `SymmetryInvariantAction` has no
   dynamics, so nothing can hang off it (see the previous section). The mechanics
   theorem would be a parallel island, not a strengthening of Derivation 1.

Revisit only if a later pass gives the development a genuine field-theoretic
action functional and equations of motion — at which point the mechanics version
becomes the warm-up rather than the deliverable.

### The ranking, by how much headline claim rests on the item

| Rank | Item | Why it is where it is |
|---|---|---|
| ~~**1**~~ | ~~**O9 — the Self's metric** (Derivation 6)~~ — **DONE 2026-08-30, see the last section of this file** | The weakest headline claim and the first thing a hostile reviewer finds. The Self is a Banach fixed point whose *only* witness uses the 0/1 metric, and `contracting_implies_const` **proves** every contraction there is constant. So on the only model exhibited, the paper's Self *is* the constant section. The fix is a real theorem, not a rewording |
| **2** | **O5 — a `ThermodynamicCover` at a non-constant minimum** (Derivation 5) | "Unity of experience = global section" is *the* thesis. Its witness has constant phase, which is precisely what makes `thermodynamic_equilibrium` dischargeable. `Phase4_RotatingFrame` now characterises the potential minima in both directions, so the ingredients for a non-constant cover exist |
| **3** | **O8 — uniqueness of the coherent branch** (Derivation 4) | Would move Table 1's only "partial" row to full. Bounded and self-contained: it wants strict concavity of `R`, a third bound on the von Mises moments in the style of `Phase8_SelfConsistency` §5, whose machinery is known to work |

Everything else in the ledger is either documented scope (B-group), cosmetic
(O7), or out of reach (Group 3).

### O9 — the execution plan

**Goal.** Replace "the Self is the constant section" with "the Self is the fixed
point of a genuinely dissipative, non-constant self-prediction map," keeping
`contracting_implies_const` in place as the recorded reason the old witness was
weak.

**Verified available in Mathlib** (checked, not assumed):

* `CategoryTheory.GrothendieckTopology.isIso_toSheafify` —
  `Mathlib/CategoryTheory/Sites/Sheafification.lean:150` (and
  `ConcreteSheafification.lean:498`): if a presheaf is already a sheaf, the unit
  `toSheafify` is an isomorphism.
* Lévy–Prokhorov — `Mathlib/MeasureTheory/Measure/LevyProkhorovMetric.lean`.

**Route A (preferred).**

1. Prove `TopCat.Presheaf.IsSheaf (probabilityPresheaf_pre Cortex)`. On a finite
   discrete space measures are finite sums of point masses, so gluing a
   compatible family over an overlapping cover is summation. Use
   `isSheaf_iff_isSheafUniqueGluing_types`, the same entry point
   `global_section_from_thermodynamics` already uses.
2. `isIso_toSheafify` then gives `GlobalSection Cortex ≅ FiniteMeasure ↥(⊤ : Opens Cortex)`.
   Note `globalSect t` is *already defined* as
   `(toSheafify _).app (op ⊤) (phaseMeasure t)` (`Examples.lean:349`), so the
   forward map is in place; step 1 is exactly what supplies the inverse.
3. Transport the Lévy–Prokhorov metric across that iso.
4. Build `predict μ := ½ • μ + ½ • μ₀` and prove it a `ContractingWith (1/2)`
   map that is **not** constant, with fixed point `μ₀`.

**Two wrinkles, both real, recorded so they are not rediscovered.**

* **Only `ProbabilityMeasure` gets a genuine `MetricSpace`.**
  `levyProkhorovDist_metricSpace_probabilityMeasure` (line 336) needs
  `[BorelSpace Ω]` and is stated for `ProbabilityMeasure`;
  `instPseudoMetricSpaceFiniteMeasure` (line 296) gives only a
  **Pseudo**MetricSpace, and the presheaf is built on `FiniteMeasure`.
  `reflexive_topology_implies_self` needs a true `MetricSpace`, so separation
  (`dist = 0 → equal`) must be proved by hand for `FiniteMeasure`. On a discrete
  space this is easy: every set is closed, and for `ε` below the minimum
  inter-point distance `A^ε = A`, so Lévy–Prokhorov collapses to agreement on
  every set.
* **The substrate needs a metric.** `Site` currently carries only
  `TopologicalSpace Site := ⊥`; Lévy–Prokhorov needs a metric on the underlying
  space. The 0/1 metric on `Site` is fine — and note the irony worth stating in
  the source: 0/1 is a perfectly good metric on a three-point substrate, and the
  measures over it are then metrically rich. The mistake was never the 0/1
  metric as such; it was putting it on `GlobalSection` itself.

**The target is concrete.** `phaseMeasure t = (1 + cos t)⁺ • midDirac`
(`Examples.lean:322`) — the existing global sections are *scaled Diracs at
`mid`*. On that ray Lévy–Prokhorov reads off the mass, so `μ ↦ ½μ + ½μ₀` is
`c ↦ c/2 + c₀/2`: a manifest ½-contraction with fixed point `c₀`, non-constant
because `phaseMeasure_not_const` already proves the family varies.

**Route C (fallback, if the sheaf property walls up).** Do not metrize
`GlobalSection` at all. Generalize `reflexive_topology_implies_self` to take the
state space as a parameter — a complete metric space `S` with
`ReflexiveBoundary` carrying `state_of : GlobalSection X → S` — and witness it
with `S = LevyProkhorov (FiniteMeasure ↥⊤)` and the contraction above. This
avoids sheafification entirely and is arguably *more* honest, since a
sheafification was never a natural carrier for a metric; but it changes the
statement of a headline theorem, so it must be presented as a re-scoping and not
as a strengthening. **Do not take Route C silently** — if it is used, Table 1 and
the Derivation 6 prose both have to say that the fixed point is in a state space
mapped out of the global section, not in the global section itself.

*(Route B — pulling the metric back along `toSheafify` without inverting it —
does not work and should not be attempted: an injection `A → B` gives `B` no
metric; a map `B → A` is needed, which is what step 1 supplies.)*

**Manuscript consequences to plan for.** Table 1's Derivation 6 row currently
reads "Theorem (conditional)" with "witnessed, but the metric forces `predict`
constant"; on success it becomes a non-trivial witness and the parenthetical goes.
The Derivation 6 section of `main.tex` and the Derivation 6 note in
`supplementary.tex` both state the 0/1-metric limitation explicitly and both
would need rewriting. `Phase6_ReflexiveTopology.lean`'s header names the
Prokhorov metric as the thing "nothing constructs" — that sentence is the one to
delete last, as the check that the work is actually finished.

---

## The Self's metric — 2026-08-30 — O9 DONE

Ranked first in the previous section because it was the weakest headline claim:
the Self was a Banach fixed point on a space whose only metric was 0/1, and
`contracting_implies_const` **proved** that every contraction there is constant.
On the only model exhibited, the paper's Self *was* the constant section. It is
now the unique attractor of a non-constant map that contracts by exactly one half.

### Two premises of the execution plan were false

The plan is at "O9 — the execution plan" above. Both of its load-bearing Mathlib
citations turned out not to apply, and the corrections are worth more than the
plan was.

* **`isIso_toSheafify` is for a different sheafification.**
  `CategoryTheory.GrothendieckTopology.isIso_toSheafify` is about the
  plus-construction unit. The development uses `TopCat.Presheaf.sheafify` — the
  stalk-wise construction, sections being families of germs that are locally
  germs of honest sections. `Mathlib/Topology/Sheaves/Sheafify.lean` still has a
  literal `-- PROJECT functoriality, and that sheafification is the left adjoint`
  comment where the adjunction would be, so there is no `isIso_toSheafify` for
  it and nothing to invert. Route A step 2 could not have been executed as
  written.
* **`μ ↦ ½μ + ½μ₀` is not a Lévy–Prokhorov contraction here.** The plan noted the
  map is a manifest ½-contraction "on the ray of scaled Diracs" and treated that
  as sufficient; but `predict` has to be total on `GlobalSection`. Off the ray it
  fails: on a substrate whose distinct points are at distance 1, `thickening ε A
  = A` for `ε ≤ 1`, so two mass-5 point masses at *different* sites are at
  Lévy–Prokhorov distance exactly 1 both before and after applying the map. The
  contraction hypothesis would have been unprovable. Mathlib also proves no
  `CompleteSpace` instance for `LevyProkhorov`, and gives `FiniteMeasure` only a
  *pseudo*metric — the plan's first wrinkle — so the completeness hypothesis had
  no support either.

**Metric actually used: the uniform distance between densities.** On the
three-site substrate the distance between two sections is the largest difference
between the masses their measures put on a site — equivalent to the measures'
total variation, within a factor of the number of sites, but not equal to it. It
is complete, it makes the relaxation map an exact ½-contraction, and below scale
1 it agrees with Lévy–Prokhorov anyway (above it they genuinely differ, and no
equivalence is claimed or used). The manuscript,
the `Phase6_ReflexiveTopology.lean` header and `Examples.lean` §10 all state the
substitution and why it was made, rather than quietly renaming the metric.

### What was built (`Examples.lean` §10, rewritten)

Three stages, all axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

| Stage | Content |
|---|---|
| **Germ–measure dictionary** | `massCocone` — the cocone over `OpenNhds x` given by "mass carried at `x`", whose cocone law is exactly `massAt_res` (restriction preserves point masses). `stalkMass := colimit.desc` of it is the map out of the stalk the sheafification hides. `density` reads a section's germ at each site; `stalkMass_injective` (via `exists_germ_eq` + restriction to the smallest neighbourhood `{x}`, where a finite measure is one number) and `massMeasure` (prescribed point masses) give **`massEquiv : GlobalSection Cortex ≃ (Site → ℝ≥0)`** — the global sections of the probability sheaf *are* the finite measures on the substrate |
| **The metric** | `gsMetric := MetricSpace.induced Phi` — the uniform distance between densities. `gsComplete` proves completeness by exhibiting the limit section of a Cauchy sequence of densities, not by "Cauchy sequences are eventually constant". `exists_dist_lt_one` exhibits distinct sections at distance `1/2` — precisely the hypothesis `contracting_implies_const` needs and no longer has |
| **The Self** | `relax s := ½·s + ½·baseline`. `relax_dist` proves the contraction factor is **exactly** `1/2` (both inequalities), `relax_not_const` that it is not constant, `relax_fixed` names the fixed point and `relax_fixed_unique` proves it unique by hand. `cortexHasSelf` applies `reflexive_topology_implies_self` to it |

The 0/1 metric survives as `gsDiscreteMetric`, a plain `def` re-enabled only
inside a `section` by `attribute [local instance 10000]`, so
`contracting_implies_const` still compiles and still records why the old witness
was empty — while being unable to leak into the new development. A `show` in its
proof that only typechecks under the 0/1 metric doubles as the check that the
local instance really wins.

Also proved, as non-degeneracy: `Phi_globalSect` computes the density of the
phase-`t` family of §4 (mass `(1 + cos t)⁺` at the shared site), and
`dist_cortexSilent_cortexState = 2` — distances in this metric are amplitudes.

### What is still not established

`relax` is a modelling choice. Nothing in the development derives it from field
dynamics, and its contraction constant `1/2` is written into its definition
rather than read off an entropy production rate. That is the honest residue of
Derivation 6 and it is stated in `main.tex`, in `supplementary.tex` and in the
section header. **This is the natural next item on Derivation 6** — and it is
harder than O9 was, because it needs the σ-functional of Phase 8 to be evaluated
on sections rather than on couplings.

### Ranking update

O9 was ranked 1. The remaining ranking from the previous section stands, shifted
up: **O5** (a `ThermodynamicCover` at a non-constant minimum — "unity of
experience = global section" is the thesis, and its witness still has constant
phase) is now first, **O8** (uniqueness of the coherent branch, which would move
Table 1's only "partial" row to full) second. *(O5 was closed on 2026-08-30; see
the final section. **O8 is now first.**)* Note that O5 is now cheaper than
it was: §10's dictionary means a global section on `Cortex` can be *specified by
its densities* (`sectionOfMass`) instead of being manipulated through the
sheafification, which is what made §4's witness constant in the first place.

---

## A cover with a non-constant phase — 2026-08-30 — O5 DONE

Ranked first after O9 because "unity of experience = global section" is the
thesis and its only witness locked every patch at phase `0`, which is exactly
what made `thermodynamic_equilibrium` discharge. The item asked for "a cover at
a non-trivial minimum of the Kuramoto potential", with O4's proviso that a proof
that no such witness exists "would be the more useful outcome". That is what
happened. Both halves were built.

### The negative half, which is the result

`thermodynamic_equilibrium` demands a *global* minimum of the reduced Kuramoto
potential. `potential_min_implies_phase_locked` already proved every minimiser
is phase-locked; the converse was missing, so this pass added
`phase_locked_minimizes_potential'` (any locked configuration attains the same
value `-½ ∑ᵢⱼ Aᵢⱼ` that `phase_locked_minimizes_potential` computes at `θ ≡ 0`)
and with it `potential_min_iff_phase_locked` — the minimisers are *exactly* the
locked states, both directions in one statement.

Three consequences, in `Phase5_GlobalSection.lean`:

| Theorem | Content |
|---|---|
| `ThermodynamicCover.phase_locked` | **Every** instance is at a phase-locked configuration. Not assumed — forced by the equilibrium field. So a phase field can differ across patches only by multiples of `2π` |
| `ThermodynamicCover.invariant_measure_const` | `phase_invariant_periodic` then erases those differences: the family takes a single value on the range of `phase` |
| `ThermodynamicCover.glued_section_eq` | Any global section restricting to the cover's local sections **is** `phase_invariant_measure (phase i₀)` |

The last one is the point, and it is a statement about Derivation 5 rather than
about the witness. The existence half of `global_section_from_thermodynamics` is
not where the content is: `sync_to_section_eq` declares each local section to be
a restriction of a global measure the class already carries, so a global object
exists before any gluing happens. What the sheaf condition contributes is
**uniqueness** — no *other* global section restricts to the same local data.
Read as "a synchronised cover determines its global state uniquely" the theorem
is exact; read as "unity emerges from locally synchronised patches" it claims
more than the Lean supports. Both documents now say so.

**What would change that.** Not a better witness — a different structure, in
which `sync_to_section` is independent data and being a restriction of a common
measure is *proved* rather than declared. That is a genuine redesign of
`LocalSectionSynchronization` (rule §1 of the Lean `AGENTS.md` applies: the
current field is a modelling assumption, marked as such, not a defect), and it is
the natural next item on Derivation 5. It is listed as **O19** below.

### The positive half: `Examples.lean` §13

The strongest witness the present shape permits, strictly stronger than §4's on
three counts. Zero `sorry`, zero warnings, `#print axioms` on every new result
reports only `propext`, `Classical.choice`, `Quot.sound`.

| Piece | Content |
|---|---|
| `twistPhase` | `false ↦ 0`, `true ↦ 2π`. **Not the constant function** (`twistPhase_not_const`), still locked (`twistPhase_locked`), and `thermodynamic_equilibrium` is discharged through the new `phase_locked_minimizes_potential'` rather than through the `θ ≡ 0` special case |
| `richDensity` | Mass on *all three* sites, three different amounts (`richDensity_zero_not_uniform`: `2`, `1`, `3`), instead of §4's single scaled Dirac at the shared site. Still `2π`-periodic (`richDensity_periodic`) and still genuinely phase-dependent (`richDensity_not_const`). Built through §10's `sectionOfMass`, i.e. specified by its densities — which is exactly the cheapening the O9 write-up predicted |
| `densityOn` | §10's `stalkMass` read at an arbitrary open, not just `⊤`, so the *patch-local* sections are now inspectable. `densityOn_restrict` (by `rfl`) says restriction moves no mass |
| Non-degeneracy | `twisted_density_left = 2` at a site the other patch does not contain, `twisted_density_right = 3` likewise, and `twisted_overlap_agrees` computes the agreement on the shared site from two separately evaluated densities rather than getting it by construction |
| The conclusions | `cortexCoverTwisted_phase_locked` (forced), the `∃!` of `global_section_from_thermodynamics`, and `cortexCoverTwisted_glued`: the unique glued section is `richSection 0` |

Declared as `@[instance_reducible] def`s, not `instance`s: §4's pair are the
instances for `Cortex`, and a second pair would leave instance search silently
choosing between two different covers of one substrate. The
`instance_reducible` attribute is not cosmetic — without it `ThermodynamicCover.mk`
fails in the *kernel* with `Finset Bool` vs `Finset (LocalSectionSynchronization.I Cortex)`.

### Manuscript

Table 1's Derivation 5 row now names §13 and states that `glued_section_eq`
makes the content uniqueness rather than emergence. A new paragraph in
Derivation 5 of `main.tex` states the scope in full, and the Derivation 5 note in
`supplementary.tex` matches. Both documents compile with overfull-hbox counts
*identical to `HEAD`*, box for box (main 22, supplementary 14) — the long
`\texttt` identifiers in the new prose carry `\allowbreak` after each underscore,
which is what kept the count from rising by two in each document. Table 1 still
fits its page.

### What is still not established

The same thing §4 could not establish: nothing runs a dynamics. The cover is
*assumed* to be at the potential minimum; `Phase4_RotatingFrame` says what that
minimum is and `potential_min_iff_phase_locked` now says exactly which
configurations attain it, but no trajectory is shown to reach one — and outside
`Examples.lean` §7's rigid rotation, no trajectory is shown to *exist*. That gap
was not in the ledger before this pass. It is now **O20**, decomposed below.

### Ledger additions

Both are also entered in the Group 2 table of the consolidated ledger above.

| # | Item | Where | What it takes |
|---|---|---|---|
| **O19** | **Derivation 5's gluing is a uniqueness theorem, not an emergence theorem.** `sync_to_section_eq` declares each local section to be a restriction of a global measure, so the global object exists before the sheaf condition is used; `ThermodynamicCover.glued_section_eq` proves the glued section is that measure | `Phase4_MacroscopicScaling:56`, `Phase5_GlobalSection` | Replace `sync_to_section_eq` with independent local data plus a compatibility condition, and *prove* that a compatible family is the restriction family of a global measure. Group 2 in difficulty: the sheaf condition already gives the glued section; the work is in restating `LocalSectionSynchronization` so the physics (locally synchronised patches) is the hypothesis and the common measure is the conclusion. This is now the live gap on the framework's central thesis |
| **O20** | **Nothing runs a dynamics into the minimum.** Every Derivation 5 result is conditional on `thermodynamic_equilibrium`, and no trajectory is shown to reach the minimum — nor, outside `Examples.lean` §7's rigid rotation, to exist at all | `Phase4_KuramotoDynamics`, `Phase5_GlobalSection:43` | Split into five parts in the next section: (a) existence and uniqueness via Picard–Lindelöf, (b) convergence of `V(θ(t))`, (c) `∫ ∑ θ̇ᵢ² < ∞` — all reachable now — (d) convergence to an equilibrium, blocked on a LaSalle principle Mathlib does not have, and (e) reaching the *global* minimum, which is **false** without an arc condition on the initial data |

### O20 — running a dynamics, decomposed (added 2026-08-30)

Raised while writing up O5: every Derivation 5 result is conditional on the
cover *already* being at the potential minimum, and that hypothesis has now been
sharpened twice without ever being discharged. It was not in the ledger; it is
now **O20**. It is not one task, and the parts have very different feasibility,
so they are split here rather than left as one line a future pass has to
re-scope.

**Verified in Mathlib** (checked, not assumed):

* Picard–Lindelöf is present — `Mathlib/Analysis/ODE/ExistUnique.lean`,
  `exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` for
  existence and `ODE_solution_unique` / `ODE_solution_unique_univ` for
  uniqueness.
* ω-limit sets are present — `Mathlib/Dynamics/OmegaLimit.lean`, including
  `isInvariant_omegaLimit`, `nonempty_omegaLimit` and the compactness lemmas.
* **There is no Lyapunov theory and no LaSalle invariance principle.** A grep
  for `Lyapunov` over all of Mathlib returns nothing. `OmegaLimit.lean` gives the
  set-level API but nothing that concludes convergence from a decreasing
  functional.

| Part | Statement | Feasibility |
|---|---|---|
| **(a)** | **A Kuramoto trajectory exists and is unique.** The vector field `θ ↦ ω + ∑ⱼ Aᵢⱼ sin(θⱼ - θᵢ)` on `V → ℝ` is globally Lipschitz for finite `V` (each `sin` is 1-Lipschitz and the sum is finite), so Picard–Lindelöf applies with no local-in-time caveat | **Reachable now.** The bounded part is packaging `LipschitzWith` for the field and matching Mathlib's `HasDerivWithinAt`-on-`Icc` shape to `is_kuramoto_trajectory`'s `HasDerivAt`-on-`ℝ`. This is the cheapest part and it closes a real hole: `is_kuramoto_trajectory` is currently a predicate with exactly one inhabitant, and that one starts at its own limit |
| **(b)** | **`V(θ(t))` converges** along any trajectory of the reduced system. `dV_dt_le_zero` already gives the *exact* identity `V̇ = -∑ᵢ θ̇ᵢ²`, and `phase_locked_minimizes_potential` already proves `kuramoto_potential_dynamic` bounded below (by its value at `θ ≡ 0`, for `A > 0`) | **Reachable now**, and cheaper than it looks — both halves of "monotone and bounded below" are already theorems in the development. Needs `tendsto_atTop_ciInf` or the antitone-convergence lemma, plus antitonicity from the sign of the derivative |
| **(c)** | **`∫₀^∞ ∑ᵢ θ̇ᵢ² dt < ∞`**, hence `θ̇ → 0` along a subsequence | **Reachable**, directly from (b) and the exact identity: the integral telescopes to `V(0) - lim V`. Gives the honest weak form of "the dynamics runs into the critical set" without needing any dynamical-systems theory |
| **(d)** | **`θ(t)` converges to an equilibrium** | **Blocked.** This is LaSalle, and LaSalle is not in Mathlib. It would also need compactness, which the development does not have: `is_kuramoto_trajectory` is stated on `V → ℝ`, phases as unbounded reals, so there is no compact invariant set to appeal to. Fixing that means working on the torus or exhibiting an a-priori bounded invariant region first — a modelling change, not just a proof |
| **(e)** | **The limit is the *global* minimum** | **False as stated, and this is the part to get right in the prose.** Splay and twisted configurations are equilibria of the Kuramoto flow too, so no theorem of the form "every trajectory reaches the phase-locked state" is provable — it is not true. The provable statement is the standard arc condition: if all phases start within a half-circle, that arc is forward-invariant and the flow converges to consensus. That is the version the manuscript's causal chain actually needs, and it is the right target |

**What this means for the manuscript.** Nothing currently claimed is wrong —
`thermodynamic_equilibrium` is marked as a hypothesis in the class doc-string,
in Table 1's "instance postulate" status, and in both documents' Derivation 5
prose. But the phrase "a thermodynamic phase transition into unity" is doing
causal work that no Lean result supports at any strength, and part (e) is a
reminder that the strongest true version is conditional on initial data. If any
part of O20 lands, the prose gains a real claim; until then it should keep
saying that the minimum is assumed, not reached.

**Where it sits.** Parts (a)–(c) are Group 2 and, taken together, are probably
comparable in size to O5 was. Part (d) is Group 3 until Mathlib grows a LaSalle
principle. Part (e) is Group 2 but only after (d), and it needs the torus change.

### Ranking after this pass

1. **O8** — uniqueness of the coherent branch (Derivation 4). Would move Table 1's
   only "partial" row to full; bounded and self-contained; wants strict concavity
   of `R`, a third bound on the von Mises moments in the style of
   `Phase8_SelfConsistency` §5.
2. **O19** — the emergence/uniqueness gap just opened above. Larger, and it
   touches a class every downstream file uses, but it is the one remaining item
   that a hostile reviewer of the *thesis* (rather than of a lemma) would find.
3. **O20(a)–(c)** — run a dynamics, as decomposed above. Existence of a solution
   at all is the cheapest unclaimed result in the development, and (b) and (c)
   are near-free given `dV_dt_le_zero` and `phase_locked_minimizes_potential`.
   Ranked below O19 only because O19 is on the central thesis; ranked above O2
   because "the minimum is assumed, never reached" is the hypothesis every
   Derivation 5 result rests on.
4. **O2** — `auto_resonance` is unconstrained by the field (Derivation 6). Cheap,
   and `Examples.lean` §10 already shows the presheaf restriction is a legal
   choice.

O4 (the `LocalSectionSynchronization` witness is weak) is **subsumed**: it asked
the same question O5 did one class lower, and `ThermodynamicCover.phase_locked`
answers it for every cover at equilibrium. What remains of O4 is O19.

---

## The coherent branch — 2026-08-30 — O8 PARTLY DONE

Ranked first after O5. The item bundled three gaps in the doc-string of
`supercritical_fixed_point_exists` — uniqueness, continuity in `K`, and the
untouched case `K = 2D`. **Two are now closed and the third is sharpened into a
single precise statement.** Zero `sorry`, zero warnings, `#print axioms` on every
new result reports only `propext`, `Classical.choice`, `Quot.sound`. Both
documents compile with overfull-hbox counts identical to `HEAD`, box for box
(main 22, supplementary 14); Table 1 re-checked and still fits its page.

### The one new analytic input

Everything rests on upgrading §5's fold argument from `≥` to `>`.
`vonMisesC2_nonneg` proved `I₂(a) ≥ 0` by folding `[-π, π]` onto `[0, π/4]`,
where `foldB` is a product of two non-negative factors. Both factors are in fact
*strictly* positive on the open interval: `cos 2x > 0` for `x ∈ (0, π/4)`, and
`sin x < cos x` strictly there, so `cosh(a sin x) < cosh(a cos x)` for `a > 0`.
`intervalIntegral.intervalIntegral_pos_of_pos_on` then gives `vonMisesC2_pos`,
hence `E(a) < 1/2` and **`R(a) < a/2` for every `a > 0`**. Three lines of Mathlib
lookup (`Real.cosh_lt_cosh`, `Real.sin_lt_sin_of_lt_of_le_pi_div_two`,
`intervalIntegral_pos_of_pos_on`) and no new analysis.

### What that buys

| Theorem | Content |
|---|---|
| `fixed_point_eq_zero_of_le_critical` | **`K = 2D` settled.** For every `K ≤ 2D` — threshold included — `r = 0` is the only non-negative solution. This is the case where the naive picture would put a second fixed point, since after rescaling the map is tangent to the diagonal at the origin. The tangency is one-sided: strictness means the map falls below the diagonal for every `r > 0` and nothing crosses. **The bifurcation happens strictly after `K = 2D`, not at it** |
| `coherent_iff_sRatio_eq` | **The coherent branch is a level set.** For `r ≠ 0`, `r = R(K, r)` ⟺ `E(K r / D) = D/K`, where `E(a) = 𝔼_a[sin²θ]`. Pure algebra out of `besselRatio_eq_mul`; no analysis. This is the reformulation that makes the remaining question precise |
| `exists_sRatio_gap` | For any `a₀ > 0` there is `c > 0` with `E(a) ≤ 1/2 - c` for all `a ≥ a₀`. Two regimes, neither needing monotonicity: extreme value theorem on a compact interval, and the crude tail bound `E(a) = R(a)/a ≤ 1/a` beyond it |
| `coherent_branch_continuous_at_threshold` | **No jump.** For every `ε > 0` there is `δ > 0` such that on `(2D, 2D + δ)` *every* coherent solution has `r < ε`. The branch emerges from zero — which is what "supercritical bifurcation" means technically — and the statement is quantified over **all** solutions, so it does not presuppose the uniqueness it does not have |
| `critical_coupling_is_threshold` | Repackaged with three components instead of two, the first weakened from `K < 2D` to `K ≤ 2D`. The two regimes now exhaust `K ≥ 0` with no gap |

Four non-vacuity examples were added to §8, including the threshold case at
`D = 1, K = 2` — the configuration no previous theorem could speak about.

### What is still open, and why it is the hard part

**Uniqueness.** By `coherent_iff_sRatio_eq` it is exactly the injectivity of `E`
on `(0, ∞)`; strict monotonicity would give it, and `E` *is* strictly decreasing
(`E(0) = 0.5`, `E(1) ≈ 0.446`, `E(2) ≈ 0.349`, `E(4) ≈ 0.216`). Three obstacles,
recorded so a later pass does not rediscover them:

1. **The ledger's guess was one step too indirect.** It proposed strict concavity
   of `R` "in the style of §5". Concavity does imply `R(a)/a` decreasing, but it
   is a second-derivative statement about `R` when the thing actually wanted is a
   first-derivative statement about `E`. Differentiating the exponential family
   in its natural parameter gives `E'(a) = -Cov_a(cos²θ, cos θ)` directly, so the
   target is `Cov_a(cos²θ, cos θ) > 0` for `a > 0`.
2. **It needs differentiation under the integral sign** — the same obstacle
   recorded for O10. Mathlib has
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the work is the domination
   hypotheses, though here the domain is compact and the integrand entire, so it
   should be materially easier than O10's case.
3. **The covariance is not sign-definite pointwise, and this is the real
   obstacle.** Symmetrising with iid copies, `Cov(X², X) = ½𝔼[(X - X')²(X + X')]`
   with `X = cos θ`. The factor `(X + X')` changes sign on `[-1,1]²`, so no
   rearrangement or Chebyshev-association argument closes it — the tilt
   `e^{a(X + X')}` has to beat the region where `X + X' < 0`. Note also
   `E'(0) = 0` (at `a = 0` the measure is symmetric and `𝔼[X³] = 𝔼[X²]𝔼[X] = 0`),
   so no first-order argument at the origin will reach it either; the true
   behaviour is `E(a) = 1/2 - a²/16 + O(a⁴)`.

**Dynamical selection** is not an O8 item at all on reflection — it is O20. There
is no dynamics to select with.

### Ranking after this pass

1. **O19** — Derivation 5's gluing is uniqueness, not emergence. The one
   remaining item a hostile reviewer of the *thesis* would find.
2. **O20(a)–(c)** — run a dynamics. (a) alone (existence of a solution via
   Picard–Lindelöf) is the cheapest unclaimed result in the development.
3. **O8 uniqueness** — as decomposed above. Now well-scoped rather than vague,
   but obstacle 3 makes it the hardest of the three.
4. **O2** — `auto_resonance` is unconstrained by the field.

---

## The gluing produces its object — 2026-08-30 — O19 DONE

Ranked first after O8. The item asked whether Derivation 5's central theorem was
an emergence claim or merely a uniqueness claim, and the answer was the second:
`LocalSectionSynchronization` carried a *global* section as a class field, so
`global_section_from_thermodynamics` could only rule out competitors to an object
every instance had already supplied. **The two offending fields are gone, the
global section is now constructed, and one of the deleted fields comes back as a
theorem about the construction.** Zero `sorry`, zero warnings, `lake build` clean
(17,608 jobs). `#print axioms` on every new result — `probability_glue_unique`,
`global_section_from_thermodynamics`, `ThermodynamicCover.invariantMeasure`,
`ThermodynamicCover.sync_to_section_eq`, `ThermodynamicCover.invariantMeasure_unique`,
`LocalSectionSynchronization.ofInvariantMeasure`, and every §14 result — reports
only `propext`, `Classical.choice`, `Quot.sound`.

### The diagnostic was syntactic, and cheaper than the plan assumed

The ledger estimated this as Group 2 because it "touches a class every downstream
file uses". The blast radius was real — `Phase4_MacroscopicScaling`,
`Phase5_GlobalSection`, `Axioms.lean`, three sections of `Examples.lean`, both
documents — but the design question took one pass over the class, not an
investigation. **List the opens each field mentions.** A cover's fields should
mention `cover i` and `cover i ⊓ cover j`; a field mentioning `⊤` is supplying
the conclusion. Two did:

* `phase_invariant_measure : ℝ → (probabilityPresheaf X).obj (op ⊤)`, and
* `sync_to_section_eq`, declaring every local section to be its restriction.

Nothing about them was *unsound* — they were instance obligations, and every
witness discharged them, which is exactly why the defect survived the 2026-08-29
soundness audit that converted them from standalone axioms into fields. They cost
the theorem its reading, not its correctness.

### What replaced them

One field, strictly weaker, mentioning only a patch and an overlap:

```lean
section_agrees_of_phase_eq : ∀ i j, Real.cos (phase i - phase j) = 1 →
  map (homOfLE inf_le_left).op  (sync_to_section i) =
  map (homOfLE inf_le_right).op (sync_to_section j)
```

That is the physics of Derivation 5 stated locally: patches at a common phase
agree where they overlap. It remains a modelling assumption — nothing derives it
from the dynamics — but it presupposes no global object.

### What landed

| Declaration | Where | Content |
|---|---|---|
| `probability_glue_unique` | `Phase5_GlobalSection` | **The sheaf condition with the physics removed.** A compatible family over any cover of `X` glues to a unique section over `⊤`. No hypothesis mentions phases, coupling or equilibrium. The guts of the old `global_section_from_thermodynamics` proof, transported from `iSup cover` to `⊤`, now stated on its own so the division of labour is visible in the source |
| `global_section_from_thermodynamics` | `Phase5_GlobalSection` | **Unchanged statement, changed content.** Now a four-line application: equilibrium forces locking (`phase_locked`), locking gives compatibility (`overlap_agreement`), compatibility glues (`probability_glue_unique`) |
| `ThermodynamicCover.invariantMeasure` | `Phase5_GlobalSection` | The section the sheaf condition produces, as a `def`. This is the declaration that used to be a class field |
| `ThermodynamicCover.sync_to_section_eq` | `Phase5_GlobalSection` | **The old class field, verbatim in content, now a theorem.** Every local section *is* the restriction of one common measure — because the sheaf condition says so, not because an instance was required to name one |
| `ThermodynamicCover.invariantMeasure_unique` | `Phase5_GlobalSection` | The uniqueness half, stated on the constructed object |
| `LocalSectionSynchronization.ofInvariantMeasure` | `Phase4_MacroscopicScaling` | **The old class shape, as a constructor.** Takes the two deleted fields as arguments and builds an instance. Proof that the new class is genuinely weaker; §4 and §13 migrate to a one-line application each |
| `Examples.lean` §14 | new, ~180 lines | The witness that the change is not notational — below |

`ThermodynamicCover.invariant_measure_const` and
`ThermodynamicCover.glued_section_eq` are deleted: both were statements about
`phase_invariant_measure`. What `glued_section_eq` said survives where it is
true, as `cortexCoverTwisted_glued` in `Examples.lean` §13 — a fact about
witnesses built through `ofInvariantMeasure`, not about the theorem.

### §14, and why §4 and §13 could not have been strengthened into it

The two existing witnesses build their local sections by restricting one global
measure, because that is what the old class demanded; §13's
`cortexCoverTwisted_glued` computes that the gluing hands it straight back. §14
drops the constructor:

* two patches, two **independently chosen** mass profiles — `(2, 1, 7)` and
  `(5, 1, 3)` across the three sites (`patchW_ne`);
* they agree only where they are required to, at the shared site `mid`, where
  both put mass `1` (`glued_overlap_mass_false`, `glued_overlap_mass_true`) —
  which is what discharges `section_agrees_of_phase_eq`, by computing two
  numbers rather than by functoriality;
* the glued section has profile `(2, 1, 3)`
  (`glued_eq_sectionOfMass`, `cortexCoverGlued_invariantMeasure`);
* it is **neither** input (`gluedW_ne_leftW`, `gluedW_ne_rightW`), and — the
  stronger form — neither input restricts correctly to *both* patches
  (`leftW_glues_nothing`, `rightW_glues_nothing`), so neither is even a competing
  solution that uniqueness has to exclude.

Two small lemmas carry the section and are reusable: `restrict_eq_of_density_eqOn`
(two global sections restrict equally to `U` as soon as their densities agree on
`U`) and `restrict_restrict` (restriction is transitive **by `rfl`**, because in
a stalk-wise sheafification restriction is reindexing of a germ family). Both
follow from §10's dictionary; neither needed new Mathlib.

### What this does *not* establish

Unchanged, and both still instance obligations flagged as such:

* **The overlap agreement is assumed.** `section_agrees_of_phase_eq` is a
  modelling field. It is local, and it is weaker than what it replaced, but no
  dynamics derives it. Deriving it is what O13/O14 would need.
* **The minimum is assumed** — `thermodynamic_equilibrium`, i.e. **O20**, which
  is untouched by this pass. "A thermodynamic phase transition into unity" is
  still prose: no trajectory is shown to reach the minimum, and outside
  `Examples.lean` §7's rigid rotation none is shown to exist.
* **§14's local sections are still *defined* by restricting a measure on all of
  `Cortex`**, because §10's germ–measure dictionary is built at `⊤`. That is a
  limitation of the dictionary, not of the class: no measure is shared between
  the two patches, the instance stores only the restrictions, and the profiles
  differ off their own patches precisely so that neither can be mistaken for the
  global state. Building the dictionary at an arbitrary open would remove even
  this, and is a small self-contained task if a later pass wants it — call it
  **O21**, Group 1.

### Manuscript

`main.tex`: Table 1's "Phase synchronization to Unity" row rewritten; the table
caption corrected (two of the five former axioms are no longer class fields
either); the soundness-audit paragraph gains the note that both were later
removed; the §4 witness description now names the constructor's periodicity
hypothesis rather than the deleted field; and Derivation 5's scope discussion is
rewritten as four paragraphs — what the theorem now proves, what the old
structure proved and why that was less, §14 as the witness, and the two
hypotheses that still carry physical content. `supplementary.tex`: Derivation 5's
implementation note restructured from two sharpening results to three, with the
third describing the restatement and §14.

Both compile. Overfull hboxes: `main` 0 → 0, `supplementary` 14 → 13 (one fewer;
the three that appeared in the new paragraph were removed with `\allowbreak` and
`\-` break points, and shortening the paragraph above it removed one more).
Table 1 re-checked by rendering page 4: still fits, with room.

### Ranking after this pass

1. **O20(a)–(c)** — run a dynamics. Now the only remaining item on the framework's
   central claim: every Derivation 5 result is conditional on
   `thermodynamic_equilibrium`, and (a), existence of a Kuramoto trajectory via
   Picard–Lindelöf, is the cheapest unclaimed result in the development. (b) and
   (c) are near-free given `dV_dt_le_zero` and `phase_locked_minimizes_potential`.
   See the O20 decomposition above; (d) stays blocked on LaSalle and (e) is false
   as usually stated.
2. **O8 uniqueness** — injectivity of `E(a) = 𝔼_a[sin²θ]` on `(0, ∞)`. Well-scoped
   but obstacle 3 (the covariance is not sign-definite pointwise) is real.
3. **O2** — `auto_resonance` is unconstrained by the field (Derivation 6). Cheap.
4. **O21** — build §10's germ–measure dictionary at an arbitrary open rather than
   at `⊤`, which would let §14's local sections be written down directly instead
   of as restrictions. Small, and it removes the last caveat on the O19 witness.

---

## A dynamics that runs — 2026-08-30 — O20 PARTLY DONE

Ranked first after O19. The item is that every Derivation 5 result is
conditional on `thermodynamic_equilibrium` — the cover is *assumed* to sit at the
potential minimum — and that nothing in the development runs a trajectory into
one. Sharper still: `is_kuramoto_trajectory` was a predicate whose only
inhabitant, `Examples.lean` §7's rigid rotation, starts synchronised and
therefore never converges to anything.

**Two of the five parts move.** Uniqueness is proved in full generality;
convergence into the minimum is proved on a witness. Existence in general,
convergence in general, and the LaSalle part do not move, and the reasons are
recorded below so a later pass does not re-scope them. Zero `sorry`, zero
warnings, `lake build` clean. `#print axioms` on every new result reports only
`propext`, `Classical.choice`, `Quot.sound`.

### The general half — uniqueness, and why it is global

| Declaration | Where | Content |
|---|---|---|
| `kuramotoField` | `Phase3_CombinatorialThermodynamics` | `kuramoto_velocity` with the index bundled, so the state space is `V → ℝ` and Mathlib's ODE API applies |
| `kuramotoField_lipschitz` | `Phase3_CombinatorialThermodynamics` | **The field is globally Lipschitz**, constant `2 ∑ᵢⱼ \|Aᵢⱼ\|`. `sin` is 1-Lipschitz and `V` is finite, so there is no smallness or locality caveat; the natural frequencies drop out, being additive constants in `θ` |
| `is_kuramoto_trajectory_iff` | `Phase4_KuramotoDynamics` | The componentwise definition is the bundled integral-curve condition, by `hasDerivAt_pi` |
| `is_kuramoto_trajectory_unique` | `Phase4_KuramotoDynamics` | **Two trajectories agreeing at one instant agree on all of `ℝ`**, forwards and backwards. `ODE_solution_unique_univ` applies directly — no continuation argument, because the Lipschitz bound is global rather than on a ball |

### Why existence did *not* follow, which was the plan's one wrong premise

The O20 decomposition called (a) "the cheapest unclaimed result in the
development", on the strength of Picard–Lindelöf being present in Mathlib. It is
present, and it is not enough. **Mathlib has no global-in-time existence
theorem.** `IsPicardLindelof f t₀ x₀ a r L K` carries the field
`mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r`, so existence is proved
only on an interval whose length is bounded by the ball radius divided by the
field's sup norm. Checked, not assumed: a grep over `Mathlib/Analysis/ODE/`
finds `ODE_solution_unique_univ` for uniqueness on all of `ℝ` and nothing
corresponding for existence — the phrase "global solution" occurs once in the
directory, in that uniqueness theorem's doc-string.

For the Kuramoto field the hypothesis is satisfiable on *every* bounded
interval, since the field is bounded (`‖F θ‖ ≤ maxᵢ (\|ωᵢ\| + ∑ⱼ \|Aᵢⱼ\|)`) as
well as Lipschitz: take `r = 0` and `a = L·T`. So solutions on `[-n, n]` exist
for every `n`, and what is missing is only the gluing — by uniqueness the family
is coherent, and `β t := α_{⌈|t|⌉} t` is the solution. That is a real but
mechanical argument, and it is the whole of what stands between here and O20(a).
It is left undone rather than done badly; it is now the top of the ranking.

### The witness — `Examples.lean` §15

Rather than prove existence in general, exhibit a solution that does what the
manuscript's prose says. On two oscillators with unit coupling and zero natural
frequency the phase difference obeys the scalar equation `Δ̇ = -2 sin Δ`, which
is integrable. The trajectory is

```
Δ(t) = 2 arctan(c e^{-2t}),   θ_true = Δ/2,   θ_false = -Δ/2
```

and it is an exact solution of the full Kuramoto system on all of `ℝ`. The one
analytic input is `sin_two_arctan : sin (2 arctan u) = 2u/(1+u²)`, three lines
from `Real.sin_arctan` and `Real.cos_arctan`.

| Theorem | Content |
|---|---|
| `pairRelax_is_trajectory` | It solves the equations — `is_kuramoto_trajectory (pairSystem 0) (pairRelax c)` |
| `pairRelax_not_locked_at_zero` | At `c = 1` it **starts a quarter turn out of phase**: `cos Δ(0) = 0 ≠ 1`. Unlike §7's rigid rotation it has somewhere to go |
| `pairRelax_tendsto_locked` | `cos Δ(t) → 1` — the value `is_phase_locked` demands |
| `pair_order_parameter` | On two oscillators `r² = (1 + cos Δ)/2`, computed from `order_parameter_complex` |
| `pairRelax_order_parameter_tendsto` | **`r² → 1`**, the manuscript's own measure of unity |
| `pairRelax_potential_tendsto_min` | **The dynamic potential tends to its global minimum**, the value `phase_locked_minimizes_potential` names (`-2` here) |
| `pairRelax_unique` | By `is_kuramoto_trajectory_unique`, this is the *only* solution through its initial state — so the convergence is not a lucky choice among many |

### What is still open, stated precisely

* **O20(a), existence in general** — as above: the gluing of local solutions.
  Mechanical, and now the cheapest item on the list for real.
* **O20(b)/(c), convergence of `V(θ(t))` and `∫ ∑ θ̇ᵢ² < ∞` for an arbitrary
  trajectory.** Untouched by this pass. Still cheap given `dV_dt_le_zero` and
  `phase_locked_minimizes_potential`; §15 proves the conclusion on a witness by
  computing the limit directly, which is not the same theorem.
* **O20(d), convergence to an equilibrium** — still blocked on a LaSalle
  principle Mathlib does not have, and on the absence of a compact invariant set
  (`is_kuramoto_trajectory` lives on `V → ℝ`, phases as unbounded reals).
* **O20(e)** — still **false** as usually stated: splay and twisted
  configurations are equilibria, so "every trajectory reaches the phase-locked
  state" is not a theorem. The provable version is the arc condition, all phases
  starting within a half-circle. §15's witness satisfies it for every `c`, since
  `2 arctan` lands in `(-π, π)` — which is exactly why it converges, and the
  doc-string says so.

### Manuscript, and a table defect found while checking it

`main.tex`: a new Table 1 row, "Kuramoto dynamics run"; Derivation 5's closing
paragraph rewritten, since it asserted that no trajectory in the development
reaches the minimum or exists outside §7 — true when written this morning, false
now. `supplementary.tex`: a new "Trajectories that run" note under Derivation 3's
rotating-frame implementation section.

**Table 1 was silently losing the tail of its caption, and had been for some
time.** Adding a row surfaced it: `LaTeX Warning: Float too large for page by
212.6pt`. Checking `HEAD` showed the same warning at 136.2pt, so the defect
predates this pass — the final sentence of the caption ("…so no row is vacuous")
was absent from the compiled PDF, which `grep` over `pdftotext` output confirms.
A `table` float that overflows is not an overfull box and does not appear in the
hbox count, which is why the recorded check "Table 1 re-checked and still fits
its page" kept passing. Fixed by converting the table to `longtable`, which
breaks across pages with a repeated header; Table 1 now runs pages 4–5 and the
caption is complete. **Lesson for future passes: check `grep -i "too large"` on
the log, not just the overfull-hbox count.**

Overfull hboxes: `main` 0, `supplementary` 13 — both unchanged.

### Ranking after this pass

1. **O20(a)** — global existence by gluing the local Picard–Lindelöf solutions,
   as scoped above. Mechanical, bounded, and it removes the last reason
   `is_kuramoto_trajectory` could be called under-inhabited.
2. **O20(b)–(c)** — convergence of the potential along an *arbitrary* trajectory,
   and the integral bound. Near-free given `dV_dt_le_zero`; §15 does not
   substitute for them.
3. **O8 uniqueness** — injectivity of `E(a) = 𝔼_a[sin²θ]` on `(0, ∞)`. Obstacle 3
   (the covariance is not sign-definite pointwise) makes it the hardest.
4. **O2** — `auto_resonance` is unconstrained by the field (Derivation 6). Cheap.
5. **O21** — build §10's germ–measure dictionary at an arbitrary open.

---

## Global existence — 2026-08-30 — O20(a) DONE

Ranked first after the previous pass, and the estimate held: it is the gluing
argument the file already described, written out. Kuramoto trajectories now
**exist** through every initial state, on all of `ℝ`, and the initial value
problem is well-posed. Zero `sorry`, zero warnings, `lake build` clean
(17,608 jobs). `#print axioms` on each new result reports only `propext`,
`Classical.choice`, `Quot.sound`.

### What landed

| Declaration | Where | Content |
|---|---|---|
| `kuramotoField_norm_le` | `Phase3_CombinatorialThermodynamics` | **The field is globally bounded**, by `∑ᵢ\|ωᵢ\| + ∑ᵢⱼ\|Aᵢⱼ\|`. Crude on purpose: `\|sin\| ≤ 1` removes the phase dependence, and each row sum is bounded by the full matrix sum so no `max` over `V` is needed |
| `kuramoto_exists_on_window` | `Phase4_KuramotoDynamics` (private) | **A solution on every symmetric window** `(t₀ - T, t₀ + T)`, `T > 0`. Picard–Lindelöf, with `IsPicardLindelof` discharged by `of_time_independent` |
| `is_kuramoto_trajectory_exists` | `Phase4_KuramotoDynamics` | **A solution on all of `ℝ`** through any `(t₀, x₀)` |
| `kuramoto_cauchy_problem` | `Phase4_KuramotoDynamics` | `∃!` — existence and uniqueness in one statement |

### Why the cap in `IsPicardLindelof` was not binding

The previous pass recorded the obstacle correctly and drew the wrong conclusion
from it. `mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r` does bound a
local solution's lifetime by the ball radius `a` over the field's sup norm `L`
on that ball — but `a` is a *parameter of the hypothesis*, not a feature of the
field, and it may be chosen after `T`. For a field bounded on the whole state
space, `r := 0` and `a := L·T` satisfy the field for every `T` at once, so the
"local" existence theorem is already existence on an arbitrary bounded window.
That is `kuramoto_exists_on_window`, and it is where `kuramotoField_norm_le`
earns its place: the Lipschitz bound alone does not give it, because
`IsPicardLindelof` asks for a sup bound as a separate field.

The remaining step is the one the ledger described. Solutions `αₙ` on
`(t₀ - n - 1, t₀ + n + 1)`; coherence from `ODE_solution_unique_of_mem_Ioo` on
the shorter window (`s := fun _ => Set.univ`, so the "stay in the set"
hypotheses are `trivial`); and

    θ(t) := α_{⌈|t - t₀|⌉₊} (t)

glued. The one point worth recording is how the derivative is read off. Fix `t`
and `n := ⌈|t - t₀|⌉₊`. On `αₙ`'s *whole* window the index `⌈|s - t₀|⌉₊` ranges
over `0 … n+1`, not just `n`, so the eventual equality `θ =ᶠ[𝓝 t] αₙ` is not by
the index being locally constant — it is coherence applied in whichever
direction the comparison `⌈|s - t₀|⌉₊ ≤ n` falls, and both directions are
available because `|s - t₀| ≤ ⌈|s - t₀|⌉₊` covers one and membership in the
window covers the other. `HasDerivAt.congr_of_eventuallyEq` then transports
`αₙ`'s derivative to `θ`.

Total: ~110 lines including doc-strings, and each of the three pieces compiled
on its first attempt.

### What this does and does not buy

It removes the last sense in which `is_kuramoto_trajectory` could be called
under-inhabited. Before this pass the predicate had exactly two inhabitants in
the development — §7's rigid rotation and §15's relaxing pair — and every
theorem quantifying over trajectories was, for all the development established,
a theorem about those two. It is now inhabited exactly once per initial state,
which is the right size.

It says nothing about behaviour. Existence is not convergence: O20(b)–(d) are
untouched, and O20(e) is still false as usually stated. The one trajectory
proved to reach the minimum is still §15's.

### Manuscript

`main.tex`: Table 1's "Kuramoto dynamics run" row rewritten — the entry now
leads with well-posedness on `ℝ` and names `kuramoto_cauchy_problem`, and only
convergence for an arbitrary system is listed open. Derivation 5's closing
paragraph updated: §15's trajectory is no longer the development's only
evidence that the predicate is inhabited.

**A stale disclaimer found while checking, and fixed.** `main.tex:171` still
said that of the coherent branch "we prove existence only … not that it varies
continuously with `K`, so a discontinuous jump at threshold is not excluded …
Neither theorem covers `K = K_c` exactly." Both halves had been false since the
`coherent_branch_continuous_at_threshold` and `fixed_point_eq_zero_of_le_critical`
pass: line 165 of the same file, and the supplementary, describe both results at
length. The paragraph was corrected. This is the second time a "what remains not
established" paragraph has outlived the result that closed it — see the lesson
added for the check that catches it.

`supplementary.tex`: the "Trajectories that run" note rewritten — it previously
explained at length why global existence was *not* proved.

Compile gate, measured against a fresh build of `HEAD`'s sources in a scratch
directory rather than against the recorded numbers: overfull hboxes `main` 24 →
24, `supplementary` 13 → 13; zero undefined references or citations in either;
`grep -i "too large"` clean on both logs, and `pdftotext main.pdf | grep "so no
row is vacuous"` confirms Table 1's caption still survives to the last sentence.
Underfull hboxes in `main` went 32 → 37, which is the justification loosening on
five lines of new prose and nothing else. (The previously recorded "`main` 0"
was the arxiv-merged build, not this one; the honest baseline is the same
document at `HEAD`.)

### Ranking after this pass

1. **O20(b)–(c)** — convergence of `V(θ(t))` along an *arbitrary* trajectory,
   and `∫ ∑ θ̇ᵢ² < ∞`. Near-free given `dV_dt_le_zero`: `V` is non-increasing
   and bounded below on the reduced system, so it converges, and the integral
   bound is the same estimate. §15 computes the limit on a witness, which is not
   the same theorem. Now the cheapest item, and it is the first half of the only
   remaining reason Derivation 5's `thermodynamic_equilibrium` is an assumption.
2. **O8 uniqueness** — injectivity of `E(a) = 𝔼_a[sin²θ]` on `(0, ∞)`. Obstacle 3
   (the covariance is not sign-definite pointwise) makes it the hardest.
3. **O2** — `auto_resonance` is unconstrained by the field (Derivation 6). Cheap.
4. **O21** — build §10's germ–measure dictionary at an arbitrary open.
5. **O20(d)** — convergence to an equilibrium. Still blocked on LaSalle, which
   Mathlib does not have, and on the state space being unbounded.

---

## The potential converges, and the dissipation is finite — 2026-08-30 — O20(b)+(c) DONE

Ranked first after O20(a), and the "near-free given `dV_dt_le_zero`" estimate was
close but not right: there was one real obstacle, and it is worth recording
because it will recur. Zero `sorry`, zero warnings, `lake build` clean (17,608
jobs). `#print axioms` on all six new results reports only `propext`,
`Classical.choice`, `Quot.sound`.

### What landed — all in `Phase4_RotatingFrame.lean` §5

| Declaration | Content |
|---|---|
| `kuramoto_potential_eq_dynamic_of_zero_freq` | With `ω ≡ 0` the two potentials are one function |
| `dynamic_potential_differentiableAt` | The potential along a trajectory is differentiable |
| `dynamic_potential_hasDerivAt` | **The Lyapunov identity as a `HasDerivAt`**, not as a fact about `deriv` |
| `dynamic_potential_bounded_below` | `V ≥ -½ ∑ᵢⱼ \|Aᵢⱼ\|`, uniformly over configurations |
| `dynamic_potential_antitone` | **`V(θ(t))` is antitone in `t`** — the global statement `dynamic_potential_deriv_nonpos` does not make |
| `dynamic_potential_tendsto` | **O20(b): `V(θ(t))` converges along every trajectory**, and the limit bounds it below |
| `velocity_sq_continuous` | `t ↦ ∑ᵢ θ̇ᵢ²` is continuous |
| `dissipation_integral_eq` | **Energy dissipated = potential dropped**: `∫₀^T ∑ᵢ θ̇ᵢ² = V(θ 0) - V(θ T)` |
| `dissipation_integral_tendsto` | **O20(c): `∫₀^∞ ∑ᵢ θ̇ᵢ²` converges**, to the total drop, with every partial integral bounded by it |
| `rotating_frame_dissipation` | Both transported to a uniform-frequency system through §3 |

### The obstacle the plan missed: `deriv` cannot feed the FTC

`dV_dt_le_zero` concludes `deriv (fun t => V (θ t)) t = -∑ᵢ vᵢ²`. That is not
enough for either half. `deriv` is junk-valued — it is `0` where the function is
not differentiable — so an equation about it carries no differentiability
information, and both `antitone_of_deriv_nonpos` and
`intervalIntegral.integral_eq_sub_of_hasDerivAt` need differentiability as a
separate hypothesis. The fix is `dynamic_potential_hasDerivAt`: prove
`DifferentiableAt` directly (the potential is a finite sum of `const * cos` of
differences of the components), then `hasDerivAt_deriv_iff` plus `dV_dt_le_zero`
supplies the value. About 25 lines, and it is the whole of the difference
between the estimate and the work.

### Why zero natural frequencies, and why that is not a weakening

Both results need the potential *bounded below*, and by
`kuramoto_potential_unbounded_below` — already in the development —
no such bound exists as soon as one `ωᵢ ≠ 0`. So the restriction is not
conservatism, it is the only case where the statement is true, and it is exactly
the case §3's rotating-frame reduction produces from a uniform-frequency system.
`rotating_frame_dissipation` does that transport, in one line, since
`sys.reduced.omega i = 0` is `rfl`.

### What is still open, stated precisely

* **O20(d)** — convergence to an equilibrium. Unchanged: needs LaSalle, and a
  compact invariant set that `V → ℝ` does not supply.
* **The limit need not be the minimum.** `dynamic_potential_tendsto` gives *a*
  limit. Splay and twisted configurations are equilibria, so a trajectory
  resting at one converges to a value that is not the global minimum, and
  `potential_min_iff_phase_locked` therefore does not fire. This is the whole of
  what still separates the dynamics from `thermodynamic_equilibrium`.

### O22 — velocity tends to zero, via Barbalat (new, added 2026-08-30)

Writing the doc-string for `dissipation_integral_tendsto` surfaced an item the
ranking did not have, and it is **cheaper than anything else left**.

Finiteness of `∫₀^∞ g` with `g := ∑ᵢ θ̇ᵢ²` does *not* give `g → 0` — an
integrable function can spike forever on ever narrower intervals. The classical
bridge is **Barbalat's lemma**: an integrable, uniformly continuous function
tends to zero. Mathlib does not have it (checked). But:

* **The hypothesis holds here.** `g` is bounded, because `kuramotoField_norm_le`
  bounds the velocities; and `g' = 2∑ᵢ vᵢ v̇ᵢ` is bounded, because `v̇ᵢ =
  ∑ⱼ Aᵢⱼ cos(θⱼ-θᵢ)(θ̇ⱼ - θ̇ᵢ)` is a finite sum of bounded terms. Bounded
  derivative gives Lipschitz gives uniformly continuous.
* **The proof is elementary.** If `g ↛ 0` there are `ε > 0` and `tₙ → ∞` with
  `g(tₙ) ≥ ε`; uniform continuity gives a `δ` independent of `n` with `g ≥ ε/2`
  on `[tₙ, tₙ + δ]`; passing to a subsequence with disjoint windows, the partial
  integrals exceed `n·εδ/2 → ∞`, contradicting the uniform bound
  `dissipation_integral_tendsto` already supplies.

**This is strictly weaker than O20(d) and should not be confused with it.**
`θ̇ → 0` says the motion stops; it does not say *where*, and locating the limit
is what needs the compact invariant set. But "every trajectory's velocity tends
to zero" is a general statement about the dynamics of the kind the manuscript has
none of, and it is reachable with no missing library.

### Manuscript

`main.tex`: Table 1's dynamics row now records the convergence and the finite
dissipation, and says plainly that the limit is not shown to be the global
minimum. Derivation 5's closing paragraph gains the same, with the splay/twisted
counterexample named so the remaining gap is not mistaken for laziness.
`supplementary.tex`: the "Trajectories that run" note gains a paragraph covering
all six results, the `deriv`-vs-`HasDerivAt` point, and the Barbalat gap.

Compile gate: overfull hboxes `main` 24 → 24, `supplementary` 13 → 13; zero
undefined references or citations; `grep -i "too large"` clean; Table 1's caption
still ends with "so no row is vacuous" in the compiled PDF.

### Ranking after this pass

1. **O22** — Barbalat, hence `∑ᵢ θ̇ᵢ² → 0` along every trajectory. Scoped above.
   Self-contained, no missing library, and it is the last general statement about
   the dynamics reachable without a compactness argument.
2. **O8 uniqueness** — injectivity of `E(a) = 𝔼_a[sin²θ]` on `(0, ∞)`. Obstacle 3
   (the covariance is not sign-definite pointwise) makes it the hardest.
3. **O2** — `auto_resonance` is unconstrained by the field (Derivation 6). Cheap.
4. **O21** — build §10's germ–measure dictionary at an arbitrary open.
5. **O20(d)** — convergence to an equilibrium. Blocked on LaSalle and on the
   state space being unbounded.

## The motion stops — 2026-08-30 — O22 DONE

Ranked first after O20(b)+(c), and it landed as scoped: Barbalat's lemma is not
in Mathlib, so it is proved here, and applied. Zero `sorry`, zero warnings,
`lake build` clean (17,608 jobs). `#print axioms` on all twelve new results
reports only `propext`, `Classical.choice`, `Quot.sound`.

### What landed — `Phase4_RotatingFrame.lean` §6, plus a witness in `Examples.lean` §15

| Declaration | Content |
|---|---|
| `tendsto_zero_of_lipschitz_of_integral_le` | **Barbalat's lemma**, Lipschitz form: `g ≥ 0`, `g` Lipschitz, `∫₀^T g ≤ M` for all `T` ⟹ `g → 0`. General analysis, no Kuramoto |
| `velocity_abs_le` | Each `\|θ̇ᵢ\|` is bounded by the field bound, uniformly in the configuration |
| `trajectory_dist_le` | **A trajectory is Lipschitz in time**, with the field bound as constant |
| `velocity_sq_lipschitz` | **The dissipation rate is Lipschitz in `t`**, constant `\|V\|·4C³` with `C = ∑ᵢ\|ωᵢ\| + ∑ᵢⱼ\|Aᵢⱼ\|` |
| `velocity_sq_tendsto_zero` | **O22: `∑ᵢ θ̇ᵢ² → 0` along every trajectory** of a zero-frequency system |
| `velocity_tendsto_zero` | Each `θ̇ᵢ → 0` |
| `kuramotoField_tendsto_zero` | The field along the trajectory tends to `0` in the state space |
| `phase_deriv_tendsto_zero` | The same read off the trajectory: `deriv (θ · i) → 0` |
| `rotating_frame_velocity_tendsto_zero` | Transported to a uniform-frequency system through §3 — the *relative* motion stops |
| `pairRelax_velocity` | The witness's velocity in closed form, `-2u/(1+u²)` |
| `pairRelax_velocity_at_zero` | It is `-1` at `t = 0`: the witness is not already at rest |
| `pairRelax_velocity_sq_tendsto_zero` | O22 fired on the witness |

### The plan's proof was not the proof: compose Lipschitz estimates, do not differentiate

The scoping paragraph proposed bounding `g' = 2∑ᵢ θ̇ᵢ θ̈ᵢ` with
`θ̈ᵢ = ∑ⱼ Aᵢⱼ cos(θⱼ-θᵢ)(θ̇ⱼ - θ̇ᵢ)`, i.e. differentiating the dissipation rate
and bounding the derivative. Nothing here differentiates it. `g` is
`Q ∘ θ` for `Q φ = ∑ᵢ (kuramoto_velocity sys φ i)²`, and all three factors were
already in the development:

* `kuramotoField_norm_le` — the field is bounded by `C` on the *whole* state
  space, so `x ↦ x²` is `2C`-Lipschitz wherever it is evaluated;
* `kuramotoField_lipschitz` — the field is `2∑ᵢⱼ|Aᵢⱼ|`-Lipschitz in the
  configuration;
* and `θ` is `C`-Lipschitz in `t` because its derivative *is* the bounded field
  (`trajectory_dist_le`, mean value theorem via `lipschitzWith_of_nnnorm_deriv_le`
  — with the global bound there is no invariant region to construct).

Multiplying the three constants gives `|V|·4C³` and the whole estimate is
`abs_mul`, `abs_add_le`, `Finset.abs_sum_le_sum_abs`. The derivative route would
have needed the second derivative of the trajectory to exist, which costs a
bootstrap the plan did not budget.

### The general lemma, and why it needed no case split

`tendsto_zero_of_lipschitz_of_integral_le` is the standard window argument.
`F T = ∫₀^T g` is monotone (`g ≥ 0`) and bounded, so `tendsto_atTop_ciSup` gives
`F → ⨆ F` with `F T ≤ ⨆ F` — that one lemma is the whole of the "the tail carries
no mass" half, no Cauchy-sequence reasoning. A spike `g t ≥ ε` then holds
`g ≥ ε/2` across a window of width `δ` with `Kδ = ε/2`, so `∫ₜ^{t+δ} g ≥ εδ/2`,
against a tolerance of `εδ/4`.

The one wrinkle: `δ = ε/2K` is undefined for `K = 0` (a constant `g`, which the
statement does allow). Rather than a case split, `obtain ⟨K', hK'pos, hKK'⟩ :
∃ K', 0 < K' ∧ K ≤ K' := ⟨K + 1, …⟩` replaces `K` by a strictly positive constant
once and for all, and the rest of the proof never mentions `K` again. The
constant is existential in the conclusion anyway.

### Manuscript

`main.tex`: Table 1's dynamics row records Barbalat and `velocity_sq_tendsto_zero`,
and now says "where it stops is not proved" rather than the weaker claim about the
limit of the potential. Derivation 5's closing paragraph gains the same, phrased
so that the remaining gap is "comes to rest, but not necessarily at a global
minimum". `supplementary.tex`: the "Trajectories that run" note replaces its
"Mathlib does not have Barbalat, so this is a gap in the library" sentence with
the proof, the composition of the three Lipschitz estimates, and the witness.

Compile gate: overfull hboxes `main` 24 → 24, `supplementary` 13 → 13; zero
undefined references or citations; `grep -i "too large"` clean; Table 1's caption
still ends with "so no row is vacuous" in the compiled PDF.

### Ranking after this pass

1. **O8 uniqueness** — injectivity of `E(a) = 𝔼_a[sin²θ]` on `(0, ∞)`. Obstacle 3
   (the covariance is not sign-definite pointwise) makes it the hardest of the
   remaining items, and it is the one that would finish a named theorem rather
   than add a new one.
2. **O2** — `auto_resonance` is unconstrained by the field (Derivation 6). Cheap,
   and it removes a free class field rather than proving something new.
3. **O21** — build §10's germ–measure dictionary at an arbitrary open.
4. **O20(d)** — convergence to an equilibrium. Still blocked, and O22 does not
   move it: `θ̇ → 0` is the *hypothesis* LaSalle's argument starts from, not a
   substitute for the compact invariant set. The state space `V → ℝ` is
   unbounded, and the honest route is to quotient by the phase-shift symmetry and
   work on a torus — a change of state space, not a change of proof.

---

## The coherent branch is a single point — 2026-08-30 — O8 DONE

Ranked first, and it landed with more than was asked. The item wanted the
injectivity of `E(a) = 𝔼_a[sin²θ]` on `(0, ∞)`; what is proved is that `E` is
**strictly decreasing on `[0, ∞)`**, and — by the same argument run on a
different integrand — that the Bessel ratio `R` is **strictly increasing on all
of `ℝ`**, which closes the separate "Monotonicity of `R`" gap the file header had
carried since the file was written. Zero `sorry`, zero warnings, `lake build`
clean (17,608 jobs). `#print axioms` on all seventeen new results reports only
`propext`, `Classical.choice`, `Quot.sound`.

### The recorded obstacle was real, and the proof does not meet it

Three obstacles were recorded, all correct as far as they went, and all about a
route that is not the one taken:

1. `E'(a) = -Cov_a(cos²θ, cos θ)`, so the target is `Cov_a(cos²θ, cos θ) > 0`;
2. that identity needs differentiation under the integral sign;
3. the covariance is not sign-definite pointwise — symmetrised,
   `½𝔼[(X-X')²(X+X')]` with `X = cos θ` has an integrand changing sign with
   `X + X'`, so the tilt `e^{a(X+X')}` has to beat the region where it is
   negative.

Nothing in §7 differentiates anything, and no covariance appears. Obstacle 3 is
what points at the fix rather than away from it: the sign problem is exactly what
the reflection `X ↦ -X` repairs, and on `[-π, π]` that reflection is the fold
`θ ↦ π - θ` **already written in §5** for `I₂ ≥ 0`. Performing the symmetry as a
change of variables *before* forming the two-point difference costs one
substitution; performing it inside the double integral costs the tilt argument
that obstacle 3 says is hard.

### The two moves

The statement is kept as the two-point inequality `C₂(a)·Z(b) < C₂(b)·Z(a)` for
`0 ≤ a < b` — equivalent to `E(b) < E(a)` by `vonMisesS_eq`, with the `Z/2`
and `C₂/2` bookkeeping.

**Fold.** `vonMisesZ_eq_foldW` folds `Z` the same two ways §5 folds `C₂`
(evenness, then `θ ↦ π - θ`), landing both on `[0, π/2]` with
`W(a, x) = 2cosh(a cos x)`. There `cos x ∈ [0, 1]`, and
`crossIntegrand_nonneg` shows `cos 2x - cos 2y` and
`W(b,x)W(a,y) - W(a,x)W(b,y)` have the same sign — the first is `2(p² - q²)` and
the second `4(cosh(bp)cosh(aq) - cosh(ap)cosh(bq))` with `p = cos x`, `q = cos y`,
both governed by `p` against `q` alone. On `[-π, π]`, where `p, q ∈ [-1, 1]`,
`p² - q²` is *not* governed by `p - q`; the fold is precisely what buys that.

**Cross.** With both factors monovarying, the classical Chebyshev-association
argument would still integrate over a square — Fubini, a product measure, a
two-variable change of variables. Instead `foldA_mul_foldW_lt` takes `α` to be
the mean of `cos 2x` under `W(a, ·)` and `x₀ ∈ [0, π/2]` a point where
`cos 2x₀ = α` (`intermediate_value_Icc'`; `|α| ≤ 1` because `|cos 2x| ≤ 1`),
evaluates the pointwise inequality at `y = x₀`, and integrates in `x` alone. The
`W(b, x₀)` term is `∫cos 2x·W(a,x) - α∫W(a,x) = 0` by the choice of `α`, so what
survives is `W(a,x₀)·(∫cos 2x·W(b,x) - α∫W(b,x)) ≥ 0`, which is the result.
Strictness comes from `crossIntegrand_pos` on a subinterval missing `x₀`.

The whole analytic input is one identity: `2cosh X cosh Y = cosh(X+Y) + cosh(X-Y)`
(`Real.cosh_add`, `Real.cosh_sub`, `ring`) with `cosh` increasing in `|·|`, which
gives `cosh_mul_cosh_cross`: `cosh(ap)cosh(bq) ≤ cosh(bp)cosh(aq)` for
`0 ≤ a ≤ b`, `0 ≤ q ≤ p`. The sums compare because `(b-a)(p-q) ≥ 0`; the
differences because `bp - aq ≥ |ap - bq|`, which is `(b-a)(p+q) ≥ 0` and
`(a+b)(p-q) ≥ 0`.

### `R` came for free, and it was on the "not proved" list

Run the same crossing argument with `cos θ` in place of `sin²θ` and **no fold is
needed**: `R(a) = 𝔼_a[cos θ]` is the mean of the very variable the exponential
family is tilted by, so `(cos x - cos y)(e^{b cos x + a cos y} - e^{a cos x + b cos y}) ≥ 0`
holds on all of `[-π, π]²` — the sign of the exponential difference is that of
`(b-a)(cos x - cos y)` outright. `weightCross_nonneg` is four lines of
`Real.exp_le_exp`. `besselRatio_strictMono` needs no sign condition on `a` at
all.

### What landed — `Phase8_SelfConsistency.lean` §7 (new; old §7 → §8, §8 → §9)

| Declaration | Content |
|---|---|
| `foldW`, `vonMisesZ_eq_foldW`, `vonMisesC2_eq_foldA` | `Z` and `C₂` on `[0, π/2]` with `W(a,x) = 2cosh(a cos x)`. `foldA a x = cos 2x · foldW a x` by `rfl` |
| `integral_pos_of_pos_on_subinterval` | Continuous, `≥ 0` on `[A,B]`, `> 0` on some `(c,d)` ⟹ `∫ > 0`. Both crossing arguments need it, since the integrand vanishes at the crossing point |
| `cosh_mul_cosh_cross`, `cosh_mul_cosh_cross_lt` | `t ↦ cosh(bt)/cosh(at)` increasing on `[0,∞)`, as a product inequality. The only analytic input |
| `crossIntegrand_nonneg`, `crossIntegrand_pos` | The two folded factors have the same sign; strict off the diagonal (`Real.injOn_cos`) |
| `foldA_mul_foldW_lt` | The crossing argument, in folded coordinates |
| `vonMisesC2_mul_vonMisesZ_lt` | `I₂/I₀` strictly increasing: `C₂(a)Z(b) < C₂(b)Z(a)` |
| `vonMisesSRatio_strictAntiOn` | **`E` is strictly decreasing on `[0, ∞)`** |
| `vonMisesSRatio_injOn` | **O8: the injectivity `coherent_iff_sRatio_eq` asked for** |
| `weightCross_nonneg`, `weightCross_pos`, `vonMisesM_mul_vonMisesZ_lt` | The unfolded crossing argument on `[-π, π]` |
| `besselRatio_strictMono` | **`R` strictly increasing on `ℝ`** — the header's "Monotonicity of `R`" gap |
| `coherent_fixed_point_unique` | At most one positive solution of `r = R(K,r)` |
| `supercritical_fixed_point_existsUnique` | **Above threshold, exactly one coherent solution** |
| `supercritical_solution_set` | The non-negative solutions are exactly `{0, r}` above threshold (and `{0}` at or below, by `fixed_point_eq_zero_of_le_critical`) |
| `critical_coupling_is_threshold_unique` | `critical_coupling_is_threshold` with the coherent side sharpened to `∃!` |
| `coherent_concentration_strictMono` | `K₁ < K₂` ⟹ `a₁ < a₂`: a larger coupling puts the density at a strictly larger concentration |
| `coherent_branch_strictMono` | **The coherent order parameter grows strictly with the coupling.** Uses both halves: `E` decreasing moves `a`, `R` increasing moves `r` |
| `exhibits_phase_transition_unique_coherent` | A substrate above threshold has exactly one coherent order parameter |

Six non-vacuity examples in §9, including the two-coupling one: at `D = 1` the
solutions at `K = 3` and `K = 4` both exist and are *strictly* ordered, so
`coherent_branch_strictMono` is not about a constant family.

### Why `critical_coupling_is_threshold` was not edited in place

It lives in §6 and would then depend on §7. It is left as it stands — nothing in
it depends on the new section, which is worth recording — and
`critical_coupling_is_threshold_unique` states the sharpened package. The same
choice was made for `coherent_branch_continuous_at_threshold`: its proof avoids
monotonicity of `E` entirely, and keeping it is what records that no-jump is the
weaker fact.

### What is still open, stated precisely

* **Dynamical selection.** The unique coherent solution is a solution of the
  *equation*. Nothing says a trajectory converges to it, or that it is stable.
  No theorem in the file mentions a trajectory, so this is not a gap in the file
  but a statement it cannot make; it is O20(d) territory.
* **The density.** Unchanged: the von Mises stationary density is an input, not
  derived from the Fokker–Planck operator.
* **Derivatives and rates.** `E` and `R` are strictly monotone, not
  differentiable. `E(a) = 1/2 - a²/16 + O(a⁴)`, `R(a) → 1`, and concavity of `R`
  are all unformalized, and nothing needs them — the threshold theorems still run
  on §5 and §6, which do not import §7.
* **The mean-field limit.** `circularOrderParameter` against
  `order_parameter_complex` is still propagation of chaos, not a lemma.

### Independently checked numerically

Trapezoid quadrature over `[-π, π]` with 2·10⁵ points: `E` strictly decreasing
over `a ∈ [0, 20]` (largest forward difference `-1.2e-4`), `R` strictly
increasing (smallest forward difference `6.4e-5`), and both cross inequalities
`C₂(a)Z(b) < C₂(b)Z(a)`, `M(a)Z(b) < M(b)Z(a)` hold on all 780 pairs from a
40-point grid of `[0, 10]`. The coherent root is `r ≈ 0.3037` at `K = 2.1`,
`0.7242` at `K = 3`, `0.8315` at `K = 4` — strictly increasing, matching
`coherent_branch_strictMono` — and a scan of `R(3r) - r` on `(0, 1]` finds a
single sign change, matching uniqueness. A sanity check on the statements, not
part of the proof; not committed.

### Manuscript

`main.tex`: Table 1's critical-coupling row now reads "exactly one" above
threshold, records `coherent_branch_strictMono`, and moves from
**Theorem (partial)** to **Theorem (conditional)** — the qualifier is now the
assumed density and the missing link to a trajectory, not an unproved part of the
analysis. Derivation 6's account of the threshold replaces its "what remains open
is precisely that uniqueness" paragraph with the fold-then-cross proof and the
monotonicity of `R`, and the following paragraph gains the sharpened packages and
the bifurcation-diagram consequence. The "what remains not established" paragraph
now disclaims dynamical selection rather than uniqueness. `supplementary.tex`:
the `Phase8_SelfConsistency` note gains the same, in more detail, and its scope
sentence is rewritten; the `Phase8_ContinuousField` note gains
`exhibits_phase_transition_unique_coherent`.

Compile gate: overfull hboxes `main` 24 → 24, `supplementary` 13 → 13; zero
undefined references or citations; `grep -i "too large"` clean; Table 1's caption
still ends with "so no row is vacuous" in the compiled PDF; `main` 48 → 50 pages.
Note the gate itself needed repair — see `tasks/lessons.md` on `grep` and
`main.log`, where the naive count reads as `0` rather than `24`.

### Ranking after this pass

1. **O2** — `auto_resonance` is unconstrained by the field (Derivation 6). Cheap,
   and it removes a free class field rather than proving something new. Now the
   only reachable item that touches a class field.
2. **O21** — build §10's germ–measure dictionary at an arbitrary open.
3. **O20(d)** — convergence to an equilibrium. Still blocked, and neither O22 nor
   this pass moves it: `θ̇ → 0` is the *hypothesis* LaSalle's argument starts
   from, and the uniqueness proved here is about the mean-field self-consistency
   equation, not about the finite-`N` dynamics. The state space `V → ℝ` is
   unbounded, and the honest route is to quotient by the phase-shift symmetry and
   work on a torus — a change of state space, not a change of proof.
4. **The mean-field limit** (propagation of chaos), which is what would connect
   items 3 and the whole of `Phase8_SelfConsistency`. A research programme, not a
   task; recorded so the ranking does not keep rediscovering it as the next thing.
