# 2026-09-16 — Review of 7833bbf and manuscript alignment

## Intent, constraints and success criteria

Review the six formal extensions in `7833bbf`, assess the added leaf
exemption, and align the article, supplement and companion primer with the
actual statements. Preserve the conditional scope, existing chain premises,
reference set and simulation artifacts. Rebuild all affected tracked PDFs
and the existing arXiv bundle; require a clean Lean build, passing publication
gates and no additional LaTeX warnings.

The implementation is a publication change. No Lean result or gate is
modified. Repair of the separate dependency-checking defect below is recorded
as its own change, following the repository's scope constraint.

## Findings and disposition

### The finite-region leaf exemption is justified

`Phase7_FiniteRegion.lean` is a terminal comparison result: positive-mass
cell embeddings preserve a finite matrix's weight and phase correlation,
delimiting the point-support vanishing theorem. Its wired-pair control also
delimits a strict support disadvantage. The supplement now uses those results
explicitly in its hardware comparison and status table.

They need no artificial consumer in `chain` to be meaningful. Their current
role does not identify cortex or a digital device with the cell embedding.
Retain the explicit `ALLOWED_LEAVES` entry; if a real downstream consumer is
introduced, remove the exemption. The rationale is specific to these results,
not a rule that a limitation theorem can never have consumers.

This list governs code consumption, not logical assumptions. `Audit.permitted`
is unchanged, and the Lean audit verifies only `propext`, `Classical.choice`
and `Quot.sound`.

### The leaf detector has false consumers

`simulations/check_leaves.py` matches unqualified tokens across files rather
than resolved Lean constants. Two new modules escape its leaf report:

| Module | What the script counts | Why it is not a dependency |
| --- | --- | --- |
| `Phase6_Locality.lean` | `run` in `Phase5_ContentDynamics`, `ball` in `Phase8_CriticalExponent` | Those are unrelated declarations; neither module imports Locality. |
| `Phase3_PhaseSensor.lean` | `FiniteObservationalLearner` in `Phase3_ObservationalLearning` | The declaration regexp truncates `FiniteObservationalLearner.ofPhaseSensor` at the namespace prefix. The earlier module defines the learner and is imported by the sensor, not conversely. |

Both modules are directly imported only by the root aggregator and their
witnesses. Passing the textual gate therefore does not establish the claimed
absence of other terminal modules. This is a gate-coverage defect, not an
axiom-audit failure.

Separate follow-up: add failing regressions for namespace collisions,
qualified declarations and reverse import dependencies; make consumption
refer to actual module/declaration dependencies; then review the resulting
leaf set. Preserve tests for real consumers and for excluding witness and
aggregator imports. Do not repair the report by widening the baseline before
classifying those results.

### The best-wired theorem has a stronger maximum hypothesis

`no_forced_gap_of_best_wired` quantifies its maximum over every pair,
including `(i,i)`, whose cosine is one. Its selected distinct pair must
therefore have correlation one. Also, `is_valid_coupling` does not require a
zero diagonal, so the all-pairs comparison cannot simply be read as an
off-diagonal maximum.

The theorem and its three-site witness are valid. The supplement, primer and
status table now state the actual scope instead of promising optimality for
an arbitrary best distinct pair. A more general off-diagonal theorem would
need its comparison class specified separately.

### Publication omissions and wording corrected

- N1: normed vector content, site-dependent shared overlap encoders, uniform
  Lipschitz control, and the one-way nonexpansive linear readout result.
- N2: a sensor channel computed from phase/readout fibre counts, with an
  informative learner and uninformative control at the same **squared**
  order parameter `r² = 1/4`.
- N3: the learner's own law determines its installed kernel, stored energy,
  heat and work. Its energy crosses a necessary exclusion line; the result
  supplies no evolving phase–sensor–installation feedback dynamics.
- N4: finite regions preserve discrete weight and correlation; point-support
  vanishing concerns measure-zero support, with no energy pricing or device
  exclusion.
- N5: reconstruction over a declared macrostate family requires distinct
  codes for states more than twice the error tolerance apart; uniqueness of a
  fixed point does not satisfy that criterion.
- N6: local synchronous updates derive causal-past indistinguishability and
  limit guaranteed responsiveness across interventions. Snapshot gluing
  remains possible.

Exact numerical identities in the new text are Lean witness results, not
simulation estimates. No computed simulation numeral is added, no production
sweep is run, and the cited reference sets of all three documents are unchanged.

The commit's hardware-illustration change removes unsupported device labels;
the numerical update is unchanged apart from variable names. The illustration
remains absent from the publication, appropriately.

## Validation and deliverables

- `lake build`: successful, no warnings; audit of 5,028 declarations in
  87 modules, only the three permitted foundational axioms.
- Two final `pdflatex` passes per document: article 42 pages, supplement
  57 pages, primer 96 pages. Zero overfull boxes and zero LaTeX warnings.
  Existing underfull counts are unchanged at 3, 2 and 31 respectively.
- Reviewed rendered pages covering the reconstruction equation, Table 1,
  finite-region exposition, new Table S1 rows and primer explanation.
- All applicable pre-commit hooks pass: prose, hedging (zero flagged
  phrases), Table S1, PDF freshness, figures, arXiv freshness, leaves and
  placeholders. The leaf result has the coverage limitation recorded above.
- Checked PDF source dependencies against the **working-tree** changes and
  build timestamps as well; the commit hook alone reads the staged index.
- `prepare_arxiv.sh`: the refreshed archive compiles from its unpacked
  contents to 75 pages. Its source manifest matches the manuscript.
- `git diff --check` passes. No reference, simulation macro, Lean
  declaration, Python implementation or allowlist is changed.

Tracked sources and PDFs are updated together in the working tree. The
separate leaf-detector repair remains open in `tasks/todo.md`; no R- or
P-item is marked complete by this publication alignment.
