# Agent Rules for Physics of Consciousness Repository

The following rules apply to all AI agents working on this project. These rules must be strictly adhered to without exception.

## 1. Spec-Driven & Test-Driven Development (SDD/TDD)
- **SDD:** Before writing code, state the intent, constraints, and success criteria. Enter plan mode for any non-trivial task.
- **TDD:** Write failing tests first before implementation. Follow the red-green-refactor cycle.

## 2. Python Code Quality & CI/CD
If Python code is introduced to this repository, the following tooling MUST be configured and gated as pre-commit hooks (`.pre-commit-config.yaml`):

*   **Package Management:** Use `uv` for all Python project management, dependency resolution, and virtual environments.

*   **Linting & Formatting:** Use `ruff`.
*   **Static Type Checking:** Use `mypy` with strict settings.
*   **Security Scanning:** Use `bandit` and/or `ruff`'s security rules (`S` rules). Never hardcode secrets.
*   **Dead Code Elimination:** Use `vulture` to find and eliminate dead code.
*   **Cyclomatic Complexity:** Use `radon` and `xenon`. Code complexity must be strictly gated: Cyclomatic complexity must remain **below 10**.
*   **Architecture Enforcement:** Use `tach` to enforce modularity and architectural boundaries.

## 3. General Operating Model
- Treat output as a draft, not ground truth. Stop and list Open Questions if information is missing.
- Default to SRR (Small, Reviewable, Reversible) changes.
- Ensure simplicity. Push back if a simpler solution exists over a clever one.
- Match existing patterns in the codebase. Consistency over novelty.
- If scope expands, stop and split into separate changes.

### Generated simulation results in publications

- Computed numerical results reported in `main.tex` or `supplementary.tex` must be TeX
  macros generated directly by a Python script from saved machine-readable
  simulation summaries or checkpoints. Do not duplicate computed numerals in
  publication prose.
- Commit the generator, generated `.tex` macro file, source summary and a test
  that detects generation drift. The generated file must identify its source
  script and say not to edit it manually.
- Regenerating publication macros must never rerun a production sweep. It reads
  existing compact artifacts; simulation execution remains a separate command.

## 4. Anti-Hallucination Gate for References
- **Verify All References:** Any time a new reference or citation is added to the project (e.g., in `main.tex`), it MUST be verified for correctness via an online web search before being committed. You must independently confirm the authors, title, year, and publication venue. No fabricated or unverified references are allowed.

## 5. The Publication Is Not a Changelog
`main.tex` and `supplementary.tex` state the theory's current state only. The supplement is part of the publication and this rule covers it identically, as it covers the physical-unity paper `unity/main.tex`.

- **No drafting-history narration.** No "earlier drafts claimed X", no "we had recorded Y; that was a misdiagnosis", no "this is no longer assumed", and **no appendix or supplementary section collecting such material**.
- **No internal Markdown references.** State methods and results in the publication instead of referring to `.md` or `.markdown` filenames or links, including design notes and generated reports. Lean theorem names and `.lean` source references are allowed in the supplement and in appendices, never in an article's main text (§9), and code availability may link the repository itself. The same `check-prose` gate enforces this rule in every publication file.
- **The test** is not "is this about our past" but: *does this sentence still make sense to a reader who has never seen a previous draft?* A refutation of an axiom shape is a permanent mathematical fact and stays. "Earlier drafts of this work declared five axioms" is autobiography and goes.
- **Rewrite, do not delete blindly.** Each site becomes a present-tense statement of scope, or is removed once its content is recoverable from one of the destinations below.
- **Where it goes instead:** `CHANGELOG.md` for what a reader of the repository needs; a Lean docstring where the content is technical; `tasks/todo.md` for the working record, whose superseded ledgers are read out of git history rather than kept in the tree.
- **The gate:** `simulations/check_prose.py`, wired into `.pre-commit-config.yaml` as `check-prose`. It scans both publication files for drafting-history markers and fails the commit. It has **no allowlist**, deliberately: an escape hatch with one entry becomes an escape hatch with twenty. Where a pattern has a legitimate non-autobiographical use — a sequence that is no longer monotone, a quantity previously defined in the same document — reword the sentence rather than widen the gate.

The rule exists for the same reason the development declares no axioms: a constraint that lives in prose is negotiable, and one that fails the build is not. The gate catches violations; this section explains them, so that the right sentence gets written the first time.

## 6. A Tracked PDF Is a Deliverable

`main.pdf`, `supplementary.pdf` and `docs/primer.pdf` are tracked in git because `README.md` and `index.html` link them directly. `unity/main.pdf` is tracked and gated from the paper's first commit, before anything links it, so that the gate is already in place on the day a link is added. A reader who follows one of those links never opens the `.tex` file beside it, so for that reader the PDF *is* the document.

- **A source change and its rebuilt PDF belong in the same commit.** Deferring the LaTeX run to a later commit leaves an interval in which the linked artifact says something nobody wrote any more, and nothing else in the repository notices: the sources stay consistent with each other, the Lean build is unaffected, and every other gate here reads `.tex` and `.lean` files rather than the artifacts built from them.
- **The gate:** `simulations/check_pdf_freshness.py`, wired into `.pre-commit-config.yaml` as `check-pdf-freshness`. It derives each PDF's dependency set from the sources on every run — transitive `\input`s and every figure, resolved through `\graphicspath` — so a figure added to the article needs no edit to the script, on the same principle as `prepare_arxiv.sh`. A commit that stages any of those sources without the PDF fails. Rebuild is two `pdflatex` passes; the second resolves the table of contents and cross-references the first one wrote.
- **The advisory half.** `docs/primer.tex` is a companion document, not part of the publication, and it goes stale in a second way: when the manuscript's *content* moves and the primer's explanation of it does not. That has no yes/no answer, so a commit that changes `main.tex` or `supplementary.tex` and leaves the primer untouched is reported and passes, in the manner of `check-hedging`.
- **Naming.** The primer refers to the work as "the manuscript" or "the framework" and defines no acronym for the title. An abbreviation of a title is a second place the title lives, and it is the one nobody updates when the title changes.

## 7. The arXiv Submission Is One Document

`main.tex` and `supplementary.tex` are two documents on this machine and one
document on arXiv: `prepare_arxiv.sh` merges the supplement in as an appendix,
applies the NeurIPS style, packs the sources and compiles the result. Three
failure modes are invisible from either source file, so three gates read the
assembled submission rather than the files it is assembled from.

The same run also writes `arxiv_submit/biorxiv/`: the NeurIPS-styled article
and supplement as two PDFs, because bioRxiv takes supplemental material as a
separate file. They are built from the same styled sources as the merged
document, and the supplement reads the styled article's `.aux`, so the pair
cannot disagree with the arXiv build about numbering.

- **No figure is printed twice.** A figure both files include appears twice in
  the submitted PDF, under two numbers, with two captions and no cross reference
  between them. The two spellings need not match — the article reaches a figure
  through `\graphicspath` and the supplement spells the path out — so the rule is
  about the resolved file. Keep the printing in the document that argues from it
  and point at it from the other: `\usepackage{xr}` and `\externaldocument{main}`
  in the supplement's preamble make `\ref{fig:resonance}` resolve to the
  article's numbering, and the merged document resolves the same label natively.
  A number written by hand is a second place the numbering lives, and it is the
  one nobody updates. **The gate:** `simulations/check_figures.py`, as
  `check-figures`.
- **A built submission is never behind the manuscript.** `arxiv_submit/` is not
  tracked, so no diff shows it going stale, and the person who discovers it is
  the person uploading it. `prepare_arxiv.sh` records the digest of every source
  it packed in `arxiv_submit/BUILD_MANIFEST`; the gate recomputes them and
  re-derives the source set from the `.tex` files, so an added figure is caught
  as well as a changed one. The escape hatch is to have no built submission
  rather than a stale one: `rm -rf arxiv_submit` passes. **The gate:**
  `simulations/check_arxiv_freshness.py`, as `check-arxiv-freshness`.
- **The script fails loudly or not at all.** `prepare_arxiv.sh` edits the sources
  it copies, and a `sed` that matches nothing produces a document that still
  compiles and is no longer the one intended — unstyled, double-spaced, or
  carrying line numbers into a posted preprint. Every edit is checked to have
  changed the file, the appendix merge is checked to have captured every section
  and the S-prefix renumbering, the tarball is packed from the files actually
  copied rather than a hardcoded list, and the submission is compiled *from the
  unpacked tarball*, so a file missing from the archive fails here rather than on
  arXiv's build.

The physical-unity paper has its own build, `unity/prepare_arxiv.sh`, writing
`unity/arxiv_submit/`: the same NeurIPS style, checked edits, compilation from
the unpacked tarball and `BUILD_MANIFEST`, with no merge because its formal
results are an appendix of the one file, and a bioRxiv copy of the same PDF.
Both scripts take those guarantees from `arxiv_assets/arxiv_lib.sh` rather than
from copies of each other, and `check-arxiv-freshness` checks every submission
present against its own document's sources.

The preprint notice in `arxiv_assets/neurips_2026.sty` reads "Preprint." and not
the upstream "Preprint. Under review.": posting to arXiv is not a submission to
anywhere, and the footer of page 1 is not the place to imply one. Local
modifications to that vendored style are listed in its header comment.

## 8. "No Axioms" Is a Claim, So It Is a Gate

Table S1 says the development declares **no axioms** — that `#print axioms` on
any result reports only `propext`, `Classical.choice` and `Quot.sound` — and
the Kuramoto section says the same of every declaration in
`Phase8_CriticalExponent.lean`. Until
`Audit.lean`, nothing checked either sentence, and `lake build` structurally
cannot: a `sorry` is a *warning* and the build exits 0, a fresh `axiom` is a
legal declaration, and a class field promoted back into a standalone postulate
compiles exactly as well as the shape §5 of `Axioms.lean` forbids. That section
records three postulates removed for being **refutable**, so this is a failure
mode with a history in this repository rather than a hypothetical one.

- **The gate:** `Audit.lean`, a default `lake` target, therefore part of
  `lake build` and of the CI Lean job. It walks every declaration the library
  adds to the environment — not a hand-kept list of headline theorems, because
  a list stops covering the next theorem someone writes — collects the axioms
  of each, and throws if anything outside the permitted three appears.
  `sorryAx` is collected like any other axiom, so this is also the only gate
  that fails on a `sorry` in a real declaration. On a passing run it logs the
  footprint it verified: an audit whose output is silence cannot be told from
  an audit that did not run.
- **The local half:** `simulations/check_sorry.py`, as `check-sorry`. The audit
  runs only where Lean runs, which is CI. This is the textual check, in the two
  seconds before the commit, and it additionally sees `example ... := sorry` —
  an `example` adds no constant to the environment, so no sweep will ever find
  it. Comments are stripped first, on the same principle as `check_leaves.py`:
  `Axioms.lean` §5 discusses removed postulates in prose, and a gate that read
  prose would fail on the record of its own success.
- **Widening the permitted set is a manuscript edit.** `Audit.permitted` is the
  executable form of a published sentence. A fourth entry makes Table S1 false,
  so it belongs in the same commit as the `supplementary.tex` change that says
  what the new axiom is and why it is irreducible — and, per §5 of
  `Axioms.lean`, a physical postulate that mentions a class field must be a
  field of that class rather than a standalone axiom at all.

## 9. The Main Text Names No Lean Identifier

A reader of the article never opens the Lean development. An identifier in a
sentence is a pointer that reader cannot follow, and a paragraph carrying
several reads as a code listing. So the main text states each result in words,
and the map from result to declaration lives where a reader who wants it will
look: Table S1 in `supplementary.tex` for the companion, and the
formal-results appendix (`app:formal`) of `unity/main.tex`.

- **The gate:** `simulations/check_lean_names.py`, wired into
  `.pre-commit-config.yaml` as `check-lean-names`. It reads `main.tex` and
  `unity/main.tex` up to `\appendix` (or `\end{document}`), comments removed,
  and fails on any `\texttt{}` span whose final dot-separated segment is a
  declaration under `PhysicsOfConsciousness/`, a module name there, or a
  `.lean` file, and on any identifier written with escaped underscores
  (`conductance\_le\_shell`) outside a span whose final segment is declared.
  The Lean sources decide what a declaration is, so a theorem added tomorrow is
  caught with no edit to the script — the principle of
  `check_pdf_freshness.py` deriving its dependency set from the sources. A
  declaration name used as an ordinary word (`energy`) is prose and passes.
- **The claim maps carry the identifiers.** A result argued from in the main
  text gets its row in the same commit: in Table S1, ending on what the
  identifier does not reach, or in the unity paper's appendix table.
  `check_tableS1.py` still validates Table S1's status column against
  `Chain.lean`.
- **There is no allowlist**, for the reason §5 gives. A sentence that needs an
  identifier to be understood needs rewriting, not an exemption.

## 10. Claims First, Limitations in One Place

The hedging in this repository's prose is structural, not lexical: no single
sentence softens anything, but nearly every paragraph carries a scope clause,
so an article reads as a list of what it does not show. `check-hedging` counts
disclaimers and decides nothing. Where a disclaimer *sits* has a yes/no answer,
so that part is a gate.

- **The rules** (hard on `unity/main.tex` and `main.tex`): a section labelled
  `sec:limitations` exists and disclaimers are unlimited there; every other
  section, the abstract included, carries at most one; the introduction states
  numbered claims as `\claim{label}{text}`, each label defined in the paper, so
  every claim points at the section that argues it. A result that needs a
  scope clause states it once, in its theorem statement, not again in every
  paragraph that uses it.
- **What a disclaimer is** lives in one place, `SCOPE_DISCLAIMER` in
  `check_hedging.py`, so the two gates cannot disagree. The lexicon is
  calibrated on `main.tex` by hand labelling; a pattern that fires on plain
  claims ("the order cannot be improved") is narrowed, not tolerated, because a
  hard gate that punishes ordinary sentences teaches authors to avoid them.
- **Advisory on the supplement.** `supplementary.tex` carries the proofs and
  the claim map, whose rows state scope by design; the hook reports its
  disclaimers per section, worst first, and passes.
- **Move qualification, never delete it.** The gate cannot read meaning. A
  disclaimer taken out of the running text must reappear in `sec:limitations`
  or in a theorem statement. Removing a scope statement to satisfy the count
  trades honesty for a metric, and a reviewer should ask where each removed
  disclaimer went.
- **The gate:** `simulations/check_claims.py`, as `check-claims`. No allowlist,
  for the reason §5 gives.
