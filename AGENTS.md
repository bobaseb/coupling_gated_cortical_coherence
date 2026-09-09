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
`main.tex` and `supplementary.tex` state the theory's current state only. The supplement is part of the publication and this rule covers it identically.

- **No drafting-history narration.** No "earlier drafts claimed X", no "we had recorded Y; that was a misdiagnosis", no "this is no longer assumed", and **no appendix or supplementary section collecting such material**.
- **The test** is not "is this about our past" but: *does this sentence still make sense to a reader who has never seen a previous draft?* A refutation of an axiom shape is a permanent mathematical fact and stays. "Earlier drafts of this work declared five axioms" is autobiography and goes.
- **Rewrite, do not delete blindly.** Each site becomes a present-tense statement of scope, or is removed once its content is recoverable from one of the destinations below.
- **Where it goes instead:** `CHANGELOG.md` for what a reader of the repository needs; a Lean docstring where the content is technical; `tasks/todo.md` and its archives under `_archive/` for the working record.
- **The gate:** `simulations/check_prose.py`, wired into `.pre-commit-config.yaml` as `check-prose`. It scans both publication files for drafting-history markers and fails the commit. It has **no allowlist**, deliberately: an escape hatch with one entry becomes an escape hatch with twenty. Where a pattern has a legitimate non-autobiographical use — a sequence that is no longer monotone, a quantity previously defined in the same document — reword the sentence rather than widen the gate.

The rule exists for the same reason the development declares no axioms: a constraint that lives in prose is negotiable, and one that fails the build is not. The gate catches violations; this section explains them, so that the right sentence gets written the first time.

## 6. A Tracked PDF Is a Deliverable

`main.pdf`, `supplementary.pdf` and `docs/primer.pdf` are tracked in git because `README.md` and `index.html` link them directly. A reader who follows one of those links never opens the `.tex` file beside it, so for that reader the PDF *is* the document.

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

The preprint notice in `arxiv_assets/neurips_2026.sty` reads "Preprint." and not
the upstream "Preprint. Under review.": posting to arXiv is not a submission to
anywhere, and the footer of page 1 is not the place to imply one. Local
modifications to that vendored style are listed in its header comment.
