# PRX submission todos

**Created 2026-09-07.** Written against PRX Life as the working target, because
that is the venue the manuscript was last shaped for
(`tasks/prxlife_editorial_pass.md`). The ledger records that a PRX Life
presubmission enquiry was explicitly declined and that direct submission is an
author decision, not a repository task — so item **A1** gates everything below
that is venue-specific. Items marked **(any venue)** are worth doing regardless
and do not wait on A1.

This file is submission mechanics only. It does not reopen R1–R6, the simulation
programme, or any claim in the manuscript. Nothing here is a reason to change a
result.

**Sourcing note.** APS returns HTTP 403 to automated fetches, so the journal
policy below comes from search summaries of APS's own pages, not from reading
them. Every policy claim in section B and C must be confirmed against the live
page before it is acted on. Repository facts (counts, file contents, numbering)
were verified directly and are marked as such.

---

## A — The gating decision

### A1 — Choose the venue

- [ ] Decide the target journal. *Blocked on the author.*

Everything in B is conditional on this. The manuscript is currently a 36-page
double-spaced `article`-class main text with a 27-page supplement, four main
figures, one main table, five supplement figures and one supplement table — a
shape that suits a journal with flexible length limits and suits a strict-format
journal badly.

The decision is not only about length. `main.tex` Section 7 is an explicitly
philosophical commitment with no data behind it, argued as a commitment and
labelled as one. Some venues will read that as the point of the article and
some as a liability. The manuscript's own three-part framing — a prediction that
can be tested, a composition that can be checked, an identification that can be
argued about — makes it separable if a venue demands it, and the ledger already
records that the formalization and audit papers are viable separately. Do not
pre-emptively split; decide the venue first.

---

## B — APS format conversion (conditional on A1 selecting an APS journal)

### B1 — REVTeX

- [ ] Confirm whether the target requires REVTeX 4.2 at submission or only at
      production, then convert if required.

Verified in repo: `main.tex` is `\documentclass[12pt]{article}` with `natbib`
(`[round]`), `setspace` double spacing and `lineno`. This is not REVTeX. The
conversion is mechanical but touches the float placement overrides at the top of
`main.tex`, the `\cite` redefinition to `\citep`, and the manual
`thebibliography` in `references.tex`.

Do the conversion in one commit that changes no prose. Rebuild and diff the
generated numerals against the macros before and after; a class change must not
move a number.

### B2 — Citation style

- [ ] Reconcile the author–year citation style with the target's requirement.

Verified in repo: `references.tex` is a hand-written `thebibliography` with 27
`\bibitem`s carrying `[Author(Year)]` optional arguments for natbib author–year
rendering. APS journals are numerical. If the target is APS this is a rewrite of
the bibliography source, not a style-file swap.

Per AGENTS.md rule 4, any reference whose fields are touched during the
conversion is re-verified online before commit. A format change is not a licence
to skip verification on a citation that gets retyped.

### B3 — Supplement float numbering **(any venue)** — DONE

- [x] Prefix supplement figure numbers with `S`.

`supplementary.tex` sets `\renewcommand{\thefigure}{S\arabic{figure}}` and
`\setcounter{figure}{0}` immediately after `\section*{Overview}`, alongside the
existing `\thetable` renewal that already produced Table S1. The placement is
deliberate: it is *before* the first supplement figure (which the table lines at
the claims section are not), and it sits inside the region `prepare_arxiv.sh`
copies when merging the supplement in as an appendix, so one edit fixes both
documents.

Verified after rebuild: the standalone supplement renders Figure S1–S5 and
Table S1, and the merged arXiv PDF renders Figure 1–4 / Table 1 for the main
article and Figure S1–S5 / Table S1 for the appendix, with no undefined
references in either. `main.tex` references no supplement figure, so no
cross-reference changed.

This also settles the cosmetic worry about `main.tex` saying "Supplemental
Material" four times while the arXiv build merges the supplement into the same
PDF: the appendix's floats now carry the S prefix the prose implies, so the two
read consistently and no per-build prose rewrite is needed.

---

## C — The essential-versus-supplemental boundary

### C1 — Decide what belongs in the main text or an Appendix

- [ ] Audit the supplement against the target's definition of supplemental
      material and relocate what fails it.

This is the substantive risk at PRX Life and it is not about length. PRX Life
advertises flexible article lengths with no strict page limit; what it does
instead is instruct referees to assess whether Appendix and Supplemental
Material content is genuinely supplemental or is essential to understanding the
manuscript, and whether any of it should be moved into the main text. APS
defines supplemental material narrowly — information *not* essential to
understanding the main results: multimedia, raw or analyzed data, calculation
parameters, computer code, additional technical detail.

Three parts of the supplement are exposed under that definition, in decreasing
order of exposure:

1. **"What a measurement of overlap compatibility would require."** `main.tex`
   Section 7 names the missing observable as the main obstacle to making the
   commitment empirically live and then defers to this section for what one must
   satisfy. That is the article's entire answer to how the interpretive claim
   could ever be tested. A referee applying the instruction above would likely
   ask for it in the main text.
2. **"Why the rate calibration is not derivable."** Section 2.2 asserts that
   $\gamma$ is required and defers here for why it cannot be finessed. The
   argument is short and is the support for a claim the main text makes.
3. **Table S1.** Main Table 1 cross-references it for the complete theorem map
   and witnesses. This predates the two sections above.

Note the shape of the fix. APS treats Appendices as part of the typeset article
and the referee guidance names "Appendix and/or Supplemental Material" as a
pair, so at a journal with no page limit the route is promotion to an Appendix,
not compression. Do not resolve this by cutting the material: each of the three
exists because a main-text claim needs it.

Hold C1 until A1 is decided. The right answer differs by venue and redoing it
twice is wasted work.

### C2 — Keep the supplement presentable without APS help **(any venue)**

- [ ] Read the supplement once as a standalone document, front to back.

APS does not copyedit or typeset supplemental material; it is deposited as-is
under its own URL and its appearance is entirely the author's responsibility.
Twenty-seven pages will receive no publisher error-catching pass. This is a
proofread, not an edit — record anything substantive as a separate item rather
than fixing it inline.

---

## D — Reference and citation mechanics **(any venue)**

### D1 — Cite the Supplemental Material in the reference list

- [ ] Add the Supplemental Material reference-list entry and point the main
      text's four prose mentions at it.

Verified in repo: `references.tex` contains no Supplemental Material entry, and
`main.tex` refers to the supplement in prose only, at lines 117, 326, 372 and
392. APS requires the form `See Supplemental Material at [URL will be inserted
by publisher] for [brief description of material]`, carried as a reference-list
item.

### D2 — Merge the supplement-only references into the main list

- [ ] Add the five references cited only in the supplement to `references.tex`
      as cited by the main article's reference section.

Verified in repo, by comparing the cite keys of both documents:
`pinotsis2023cytoelectric`, `pinotsis2023ephaptic`, `pockett2002`,
`verkhratsky2018`, `voroslakos2018`. APS requires every reference cited in the
supplemental material to appear in the main text's reference section.

These five are already in `references.tex`, which both documents `\input`, so
the fix is about how the submitted main article's bibliography is generated, not
about finding the entries. Confirm after conversion that all 27 appear in the
main article's rendered list rather than only those it cites directly.

### D3 — Final reference and macro read

- [ ] Re-read every citation and every generated numerical macro once, after the
      last prose edit and after any B1/B2 conversion.

Carried from P4. No new citations or macros were introduced by the narrative
passes, but the existing set has not had its final read. Per AGENTS.md rule 4,
verify authors, title, year and venue online for anything that looks wrong.
Do not submit while any source/PDF, estimator or public-description
inconsistency remains.

---

## E — Metadata and policy statements *(author-only)*

### E1 — Author metadata — PARTIALLY CLOSED

- [x] Affiliation and ORCID.
- [ ] Funding, competing interests, author contributions.

The author block now carries the affiliation (Independent Researcher) and
ORCID 0000-0002-5951-0772 alongside the existing name and email.

The remainder is venue-dependent and not required by arXiv. Single-author work
makes an author-contributions statement moot at most venues. Funding and
competing-interest declarations are supplied on the submission form rather
than in the source at APS journals; if the target requires them in the
manuscript, they go in a declarations block beside the AI-use disclosure.

### E2 — Data availability

- [ ] Confirm the target's required data-availability wording and check the
      current statement against it.

Verified in repo: `main.tex` carries a generic "Data and code availability"
section naming the source repository, the regeneration-without-rerunning
guarantee and OpenNeuro ds005620, and stating that raw recordings are not
redistributed. Whether that satisfies the target's template is a venue question.

### E3 — AI-use disclosure

- [ ] Review the "Use of AI tools" section against the target's policy and
      against the full project history.

Verified in repo: the section states that AI tools assisted simulation-code
development and manuscript revision, and that machine checking establishes the
Lean results under their hypotheses without validating biological
interpretations or replacing scientific review. Check the target's required
form and placement; some journals want this in the acknowledgements or a
declarations block rather than as a numbered section.

### E4 — Cover letter

- [ ] Fill the salutation, journal name and journal-specific statements in
      `tasks/cover_letter.md`.

The substantive paragraphs are final and track `main.tex`. Only the
venue-dependent parts are open.

---

## F — Final verification before submission

### F1 — Clean-checkout build and gate run

- [ ] Rebuild both PDFs from a clean checkout; run Lean, the simulation macro
      and report checks, `check_prose`, `check_hedging`, `check_tableS1`,
      `check_leaves` and the Python quality gates; record the exact commit and
      the generated artifacts used for submission.

Carried from P4, where it was completed once. It must be repeated after the last
change, because a REVTeX conversion in particular can silently move a float, a
reference or a generated numeral.

Note the recorded hazard: the `.venv` console scripts embed an absolute
interpreter path, so if the checkout is moved or renamed for the submission
build, run `uv sync --reinstall` in `simulations/` before trusting a green run.

### F2 — Package check

- [ ] Confirm the submission tarball builds and contains every figure the
      sources include.

`prepare_arxiv.sh` was repaired in commit 17d8e4b to read its own sources and
verify what it packs. Re-run it after any B1 conversion, since a class change
alters which files the build touches.

### F3 — Abstract and title conformance

- [ ] Check the abstract against the target's word limit and formatting rules.

Verified in repo: the abstract is 266 words in ten sentences, with no citations
and no equations. The ledger records that the final word cap depends on the A1
decision. One search result attributed a roughly 2500-word article limit with a
100–150-word abstract to PRX Life, but that conflicts with the flexible-length
statement on the same page and reads like a short-format article type; confirm
against the live page rather than acting on it.

---

## Sources to re-check before acting

APS pages could not be fetched directly. Confirm each policy claim above
against these before acting on it:

- https://journals.aps.org/prxlife/authors
- https://journals.aps.org/prxlife/referees/guidelines-for-referees
- https://journals.aps.org/prxlife/authors/editorial-policies-practices
- https://journals.aps.org/authors/supplemental-material-instructions
- https://journals.aps.org/authors/length-guide
