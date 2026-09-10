# Agent Rules for the Lean 4 Development

Scoped to `PhysicsOfConsciousness/`. The repository-wide rules in `/AGENTS.md`
still apply; this file adds the ones specific to the formalization, and every
one of them exists because breaking it has already cost this project a
correctness defect. Read `tasks/lessons.md` for the Mathlib API notes and
`Axioms.lean` for the postulate ledger.

## 1. Soundness: where a physical postulate may live

The development declares **zero `axiom`s** and must keep declaring zero. That
number is worth exactly as much as the discipline below.

* **A postulate that mentions a class field must be a field of that class**, never
  a standalone `axiom` quantified over all instances. Three axioms were removed in
  the 2026-08-29 audit for violating this, and all three were *inconsistent*: each
  pinned a free class field across every instance, so exhibiting one instance that
  violates it derives `False`. A standalone axiom is safe only when every symbol it
  constrains is bound by the axiom itself. See `Axioms.lean` §5 for the worked
  refutations.
* **An implicit argument occurring only in a hypothesis is a red flag.** That is the
  precise shape of the `spontaneous_symmetry_breaking_pointwise_min` bug: the
  hypothesis could be discharged by instantiating the implicit with a constant.
  Before adding a hypothesis, ask what instantiation of its metavariables makes it
  free.
* **Axiom laundering.** A theorem provable by `trivial`, `rfl`, or a single `exact`
  of a class field has proved nothing. Class fields that state universally
  quantified inequalities or implications are usually laundered physics. If the
  claim is a mathematical theorem, prove it from Mathlib; if it is irreducible,
  make it an instance obligation and say so.

## 2. Non-vacuity: a class with no instance is as bad as an inconsistent axiom

Every class or structure carrying physical content must be inhabited by a witness
under `Examples/`, and the witness must be checked non-degenerate. The witnesses
sit in one file per phase; `Examples.lean` is their index and says which file
holds which section.

* Before claiming a theorem "holds", check that the structures in its hypotheses
  have instances. `DiscreteThermodynamics` and `ReflexiveBoundary` both went
  unnoticed for a long time; the theorems about them were conditional on
  structures never shown realizable.
* A witness that discharges its obligation trivially (a constant field, `KL = 0`,
  `rfl`) proves inhabitability and nothing more. Prefer one that exercises the
  obligation — and where the trivial one is all that is available, prove *why*, as
  `contracting_implies_const` does for the 0/1 metric in `Examples/Phase6.lean`
  §10. That
  theorem is also the model for what to do next: it stood as the recorded reason
  the Self's witness was empty until the metric was replaced by one built from the
  measures, and it is kept, demoted to a local instance, as the record of why.
* State non-degeneracy as theorems, not comments: measures that are nonzero,
  approximations that genuinely change with `N`, families that really depend on
  their parameter.

## 3. Data classes stay bare; properties live in predicates

`TriangulatedManifold` is data (a complex, an embedding, edge regions). The
geometric conditions live in the predicate `IsRegularTriangulation`. Consumers then
say which they need, in one of the two available ways:

* a **field**, when the structure cannot mean anything without it —
  `DiscreteThermodynamics.regular`;
* a **hypothesis**, when the result quantifies over many instances —
  `mesh_refinement_convergence`.

Do not strengthen a data class to avoid a hypothesis. Do not leave a structure that
claims to derive physics depending on unconstrained data.

## 4. Structure parameters must be recoverable from the type

If a structure takes `[C α]` as an *instance* argument and `C` does not appear in
the resulting type, no projection out of a value can recover it, and the
structure-instance elaborator will try to *synthesize* rather than unify — so a
witness fails with `failed to synthesize C α` even when supplied via `@`. This
happened to `DiscreteThermodynamics` with both `TriangulatedManifold M` and the
`ModelWithCorners`. Make such arguments **explicit parameters** so the type reads
`DiscreteThermodynamics TM I`. Instance arguments are for things a space genuinely
has one of; a space carrying a sequence of triangulations has none.

## 5. Doc-strings carry scope, not just description

Every non-trivial theorem's doc-string states what it does **not** establish. This
is load-bearing: it is how the manuscript's claims and the Lean's claims stay
separable, and reviewers read it. Follow the existing pattern —

* what the theorem proves,
* which hypotheses carry physical content (and that they do),
* what would be needed to remove them.

When a statement is withdrawn or corrected, leave the record in place explaining
why it was wrong (see the mesh-refinement note at the end of
`Phase2_SimplicialBridge.lean`). Deleted code with no explanation gets reinvented.

## 6. Build and verification gate

Toolchain is pinned in `/lean-toolchain` (currently `v4.34.0-rc2`); do not bump it
as a side effect of other work.

```
lake build                                  # must be clean
grep -rn "sorry" PhysicsOfConsciousness/    # must be empty
```

* **Zero warnings, not just zero errors.** Deprecation warnings (`if_pos`,
  `if_neg`, `if_false`), unused-simp-argument and unused-variable linter hits all
  count. Fix them in the same change.
* **`#print axioms` on every new headline result** must report only `propext`,
  `Classical.choice`, `Quot.sound`.
* New files must be added to the root import file `/PhysicsOfConsciousness.lean`,
  or `lake build` will silently not build them.
* To iterate on a proof without a full rebuild, put a scratch file outside the
  library and run `lake env lean <file>.lean`. Do not leave it in the repo.

## 7. Imports and file layout

Files are phase-ordered and the import graph is a DAG; check it before moving a
declaration. `Examples.lean` is the sink: it imports the per-phase witness files
under `Examples/`, each of which imports the phases it witnesses, so the root
aggregator reaches them all through it and lists none of them itself.

The witness files form a DAG of their own, because a witness may need another
witness's substrate. Two files exist only to be that substrate —
`Examples/Bit.lean` (the one-bit eraser, §1) and `Examples/Cortex.lean` (the
three-site cortex, §4) — and a witness that stands on one imports it. The
dependency is often invisible to a reader: `Examples/Phase1.lean` §19 needs
`Examples/Bit.lean` for the `Thermodynamics Bool` *instance* and never names a
declaration from it.

A declaration belongs in the earliest file that can state it — that is why
`IsRegularTriangulation` lives beside `TriangulatedManifold` rather than in the
convergence file that first needed it. When moving a declaration, generalize its
typeclass assumptions to what the *statement* needs (`TopologicalSpace`, not
`PseudoMetricSpace`, if no distance is measured) and delete binders the statement
does not use.

## 8. The manuscript is part of the change

A Lean change that alters what is proved is not finished until `/main.tex` and
`/supplementary.tex` agree with it. In particular:

* Table 1 in `main.tex` maps claims to status; a new theorem, a new witness, or a
  weakened hypothesis changes a row. Status vocabulary in use: `Theorem`,
  `Theorem + instance postulate`, `Theorem (partial)`, `Theorem (conditional)`.
* The per-derivation implementation notes in `supplementary.tex` must state the
  same limitations the doc-strings do.
* Both documents must compile (`pdflatex` twice) with no *new* warnings — check
  the overfull-hbox count against `HEAD` rather than assuming zero.

## 9. Record-keeping

* `tasks/todo.md` is the open-items ledger. Mark items done in place *and* append
  a dated section describing what was built, what it does not establish, and what
  remains — future passes rely on this instead of rediscovering.
* `tasks/lessons.md` collects reusable Mathlib and architecture findings. Add to it
  when an API detail costs more than a few minutes; do not duplicate it here.
* Convert relative dates to absolute in both.
