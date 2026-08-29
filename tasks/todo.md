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
| **O4** | **A3 — the `LocalSectionSynchronization` witness is weak.** `cortexSync` sets `phase ≡ 0` and discharges `sync_to_section_eq` by `rfl`; the local sections *are* restrictions by construction | `Phase4_MacroscopicScaling:56,61`, `Examples` §4 | A witness with a non-constant phase field, or a proof that no such witness exists under the current class shape (which would be the more useful outcome, as `contracting_implies_const` was for D1) |
| **O5** | **A4 — the `ThermodynamicCover` witness has constant phase**, which is what makes `thermodynamic_equilibrium` dischargeable at all. This is where Derivation 5's physics lives | `Phase5_GlobalSection:43`, `Examples` §4 | Same shape as O4: a cover at a non-trivial minimum of the Kuramoto potential. `Phase4_RotatingFrame` now characterizes those minima in both directions, so the ingredients exist |
| ~~**O6**~~ | **DONE 2026-08-29.** ~~**D4 — four classes still have no instance:**~~ `PlasticNeuralField`, `StochasticMatrix`, `PseudoRiemannianManifold`, `ContinuousSymmetryGroup`. Nothing headline rests on them, but rule §2 of the Lean `AGENTS.md` applies to them as much as to the others | `Phase8_ContinuousField:155`, `Phase3_CombinatorialThermodynamics:192`, `Phase1_Primitives:47,123` | Each is a short witness. `StochasticMatrix` on `Bool` and `PlasticNeuralField` on the `Duo` substrate of `Examples` §5 are both nearly free. Alternatively delete what is unused, as `VacuumManifold` was |
| **O7** | **C3 — `DiscreteThermodynamics.scalar_magnitude` is arbitrary subject only to non-negativity.** The map from a stress-energy tensor to a scalar is modelling, not derivation | `Phase2_SimplicialBridge:42` | Probably *leave*, but say so in the source: if it is a modelling choice, mark it `[MODELLING]` the way `Phase4_MacroscopicScaling`'s fields are, so it is not mistaken for an oversight. Listed here so the decision gets recorded either way |

### Group 2 — reachable, but real work

| # | Item | What it takes |
|---|---|---|
| **O8** | **The coherent branch, beyond existence.** `supercritical_fixed_point_exists` gives *some* `r ∈ (0,1]`; uniqueness, dynamical selection and continuity in `K` are all unproved, so a discontinuous jump at threshold is not excluded and the bifurcation is not shown supercritical in the technical sense. `K = 2D` exactly is covered by neither theorem | Monotonicity of `R`, or an implicit-function-theorem argument. `R` is nowhere shown increasing. Uniqueness plausibly follows from strict concavity of `R` in `a`, which would be a third bound on the von Mises moments in the style of §5 |
| **O9** | **B1 — the Self's metric is 0/1, and `contracting_implies_const` proves that forces the fixed point to be constant.** The Banach argument is sound; the metric makes its conclusion trivial | A metric on `GlobalSection` built from the measure-theoretic structure — the Prokhorov metric named in `Phase6`'s header, which nothing constructs. Mathlib has `MeasureTheory.LevyProkhorov`; whether `GlobalSection`'s sheafified measures fit its hypotheses is the first thing to check |
| **O10** | **B3 — the σ/gradient-flow link holds for finite substrates only** (`hvol : volume = Measure.count`) | Differentiation under the integral sign with respect to the kernel. Mathlib has `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; the work is in the domination hypotheses |
| **O11** | **B2 — `h_mean` restricts the comparison class** to fields sharing the phase-locked state's mean drift, so minimality is Jensen alone | Model how `Omega_avg` varies with the competitor field. Stated as the honest scope on the theorem; removing it changes what is claimed |
| **O12** | **D2 — there is still no Noether theorem.** The class is now inhabited (`Examples.lean` §11, a `ℤ₂` action on a double well, with symmetry breaking exhibited), but no conserved quantity is constructed and no theorem consumes a symmetry group | Proving an actual Noether theorem over Mathlib is a project in itself, and would first need a *continuous* symmetry group — `ℤ₂` is discrete, so there is no one-parameter family to differentiate along. `ContinuousSymmetryGroup` carries no continuity or homomorphism law at all, which is the first thing to fix if this is ever attempted |

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
