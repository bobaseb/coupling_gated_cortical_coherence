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

1. ~~**Build a `ThermodynamicCover` instance.**~~ **DONE 2026-08-29** — see below.
2. ~~Link Phase 8's abstract gradient-flow theorems to `entropy_production_rate`.~~ **DONE 2026-08-29** — see below.
3. Restate `mesh_refinement_convergence` correctly (sequence of triangulations,
   covering condition, `edge_region` tied to the simplicial data).
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
