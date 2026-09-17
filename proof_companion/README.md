# Proof companion

[Read the companion PDF](companion.pdf) · [LaTeX source](companion.tex) ·
[Coverage table](generated/coverage.tsv) · [Implementation specification](SPEC.md)

This directory owns the whole exercise of making the repository's Lean proofs
readable and auditable as mathematics. The second coverage stage covers
**116 results in four modules**. Three of them — `Chain`, `Phase5_GlobalSection`
and `Phase8_CriticalExponent` — are covered **completely**: every theorem they
declare has an extracted statement, so the appendix shows what those modules
contain rather than only what the prose discusses. The fourth contributes a
single witness. The long-term scope is the project's own development, with
Mathlib results identified as dependencies rather than expanded into a second
copy of Mathlib.

The current document explains exact and approximate gluing, the stationary
critical exponent, the passive conditional chain, the witnesses and
counterexamples that fence that chain, the no-go result separating discrete
meshes from continuum kernels, and a nonconstant witness.
Its formal appendix is generated from Lean; the mathematical explanations in
`chapters/` are editorial drafts prepared against the source proofs. The current
tool **does not automatically translate arbitrary Lean proofs into English**.
Lean's verification of the source does not certify the prose translation.

## What is implemented

`Extract.lean` re-elaborates a selected source file against the repository's
**Lean v4.34.0-rc2**, then exports:

- Selected declarations' elaborated types, universe parameter names, source
  locations and excerpts, and docstrings.
- Direct constants in both the type and the proof term, including dependencies
  introduced by automation; and the transitive axiom footprint.
- Nested `InfoTree` tactic events with source spans, nearest tactic ancestors,
  syntax kinds, synthetic-syntax flags, and goals before and after each event.
  Each side is printed using its own saved metavariable context.
- Fields of project structures encountered through statement types and their
  field types, including parent structures. This helps expose supplied physical
  conditions.
- A source inventory of anonymous `example` commands in the processed module.

Term proofs remain covered even when their tactic array is empty. Missing or
imported selections, elaboration errors, and selected results using axioms outside
`propext`, `Classical.choice`, and `Quot.sound` fail extraction. The four saved
snapshots contain **4,338 nested tactic records**, including wrapper and macro
events; these are not 4,338 independent mathematical steps.

`GenerateSelection.lean` proposes candidates for the selection by enumerating the
**elaborated environment** — never by matching regular expressions against source,
which `SPEC.md` rules out. It walks the project's own modules, drops names Lean
generated rather than an author wrote, and emits module, name, kind, source line
and whether a docstring is present. It only proposes: curation stays editorial,
and `Extract.lean` re-elaborates whatever is selected.

`render.sh` generates the formal appendix, coverage table, selected physical
fields, and a real three-step witness trace from those snapshots. Its output is
deterministic. The full histories remain in JSON so the PDF stays readable. It
reads each snapshot **once per module** rather than once per selected
declaration; re-parsing a multi-megabyte snapshot per declaration is what stopped
rendering scaling past the twelve-result pilot.

## Layout

| Path | Purpose |
|---|---|
| `Extract.lean` | Lean-native extraction against the pinned compiler |
| `GenerateSelection.lean` | Proposes selection candidates from the elaborated environment |
| `selection.json` | Exact module/declaration selection and stable document IDs |
| `data/*.json` | Saved elaboration snapshots; no simulation results |
| `data/*MANIFEST.sha256` | Source/toolchain and snapshot fingerprints |
| `chapters/*.tex` | Mathematical explanations and explicit scope statements |
| `generated/` | Generated statements, dependency lists, trace, and coverage |
| `companion.tex`, `companion.pdf` | Document entry point and deliverable |
| `BUILD_MANIFEST.sha256` | Fingerprints of the document's inputs and PDF |
| `tests/` | Extraction and rendering regressions |
| `run.sh`, `render.sh` | Build, verification, and rendering commands |

## Reproduce it

Run these commands from the repository root. `run.sh` also locates the root when
called from another directory. Requirements are the repository's existing Lean
toolchain and built dependencies, Bash, `jq`, GNU coreutils, and TeX with XeTeX,
LaTeX, `fontspec`, `fvextra`, `xurl`, TeX Gyre Pagella, DejaVu Sans Mono, and
FreeSerif. The driver can create a local XeLaTeX format when the XeTeX
binary and LaTeX sources are installed but the `xelatex` launcher is absent.
It does not install packages or change the system TeX configuration.

```sh
# Re-elaborate the four selected modules; refresh saved data and fingerprints.
bash proof_companion/run.sh extract

# Regenerate the appendix and trace from saved JSON. Does not invoke Lean.
bash proof_companion/run.sh render

# Render, compile twice, and record the resulting PDF and its inputs.
bash proof_companion/run.sh pdf

# Verify source, snapshot, generated-text, and PDF freshness without Lean or TeX.
bash proof_companion/run.sh check

# Run extraction, rendering, and artifact-freshness regressions.
bash proof_companion/run.sh test
```

Extraction builds the selected modules' `.olean` targets first so imported
artifacts match the source. It writes to a temporary directory and only replaces
the saved data after every module succeeds. Source fingerprints are checked again
before publication of the snapshots, detecting concurrent source edits.
`data/SOURCE_MANIFEST.sha256` conservatively covers **all project library Lean
files**, the root aggregator, the toolchain and Lake pins, the extractor, and the
selection. Therefore a library change can require re-extraction even if it does
not ultimately affect a selected theorem. Newly added files are detected too.

Rendering and PDF compilation can use a saved historical snapshot independently
of the current Lean source. `check` deliberately rejects a snapshot whose input
manifest no longer matches the checkout. It also checks the snapshot hashes,
regenerates and compares the appendix, and verifies the PDF's build manifest.

The pre-commit gate checks freshness on relevant changes. The CI Lean job runs
the extraction fixtures and rendering tests; the repository-gates job checks
the saved deliverables. PDF compilation is performed locally, consistently with
the repository's other tracked PDFs.

## Adapting the tooling to this Lean version

The approach is the same one demonstrated by
[`lean-training-data`](https://github.com/kim-em/lean-training-data): inspect
Lean's elaboration `InfoTree`s and the final declaration environment. That
tool's inspected main branch pins Lean v4.16.0. This directory uses a small
independent implementation against the installed v4.34.0-rc2 APIs, avoiding a
toolchain change or another Lake dependency.

The implementation uses `Parser.parseHeader`, `Elab.processHeader`, and
`Elab.IO.processCommands`, which returns the completed command environment and
information trees. It adapts to the current raw string-position API and options
API. Crucially, `ConstantInfo.value?` needs `allowOpaque := true` to return
theorem proof terms; the term-proof and structure-projection tests catch a
silently empty dependency list. No syntax instrumentation is inserted into
mathematical source files.

The existing tests cover implicit type binders, branching goals, term proofs,
field projections, anonymous-example inventory, repeated-extraction stability,
missing declarations, and elaboration failure. Rendering rejects missing results
and duplicate IDs rather than silently producing an incomplete appendix.
Freshness tests mutate a disposable copy and require rejection of changed or
new Lean inputs, changed snapshots, changed generated statements, and a changed PDF.

## Extending coverage

1. List candidates with
   `lake env lean --run proof_companion/GenerateSelection.lean`, then add a module
   and its fully qualified declarations to `selection.json`, giving every
   declaration a unique, filesystem-safe document ID. Document IDs already in use
   are cited by `chapters/` and must not be renamed.
2. Run `extract` and inspect the statements, dependency lists, and relevant
   structure fields. A theorem name or its docstring is not the specification.
3. Add an explanation to `chapters/` and include it from `companion.tex`. Use
   `\formal{document-id}` to link it to the generated statement. Identify
   physical assumptions and the scope of the conclusion explicitly.
4. Run `pdf`, `test`, and `check`; include updated snapshots, generated files,
   manifests, and PDF together in the change.

The trace excerpt and two highlighted field projections in `render.sh` are
specific to the current gluing/witness sample. They should become configurable
as new kinds of example are added; the shared declaration appendix already
follows the selection file.

## Current limits and next stages

- **Coverage is selected, not complete.** Three modules are complete; the
  development has about 3,000 declarations in 88 files, so there is no
  whole-library coverage claim. Anonymous examples are inventoried but do not yet
  receive their own elaborated-statement/proof records or mathematical
  explanations. Most extracted statements carry no prose: the appendix is a
  complete record for those three modules, the explanations are not.
- **The prose is editorial.** Automatic step narration, grouping and review
  are future work. First compare a generated explanation against the curated
  examples here, including term proofs and assumptions carried by fields.
- **The trace is elaboration data.** Tactic ancestry is preserved, but goal
  strings are not stable goal identifiers or a reconstructed dependency graph
  between individual goals. Macro events and administrative wrappers can share
  ranges. Automated proof narration must distinguish these.
- **Pretty-printing has limits.** Statements preserve quantified hypotheses
  but normal Lean notation can hide implicit arguments at applications and
  proof-valued subterms. Source excerpts and universe names accompany them.
  A fully explicit expression export is a useful next extension.
- **Dependencies are syntactic.** They are direct constants occurring in a
  proof term, not a minimal set of premises. Unused local `let` bindings can
  leave constants in that term. Imported lemmas are not recursively narrated.
- **Structure exposure is bounded.** The current walk follows project statement
  and field types, not arbitrary definition bodies, proof-local instances or
  every Mathlib structure. It is not an exhaustive physical-assumption audit.
- **Human review remains essential.** The mathematical explanations and their
  consistency with the manuscript need independent review. This pilot reports
  no newly established defect in the Lean development.

The next bounded stage is an expression/dependency export with stronger
coverage accounting, followed by configurable trace selection and a measured
trial of automatic narration. The directory and file layout are intended to
remain the home of those stages and the eventual full companion.
