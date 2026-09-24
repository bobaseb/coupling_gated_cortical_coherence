# Neuroscience of Consciousness — submission components

Components the journal collects at submission that are not part of
`main.tex`. Checked against the journal's author guidelines and manuscript
preparation instructions on 2026-09-24:
<https://academic.oup.com/nc/pages/author-guidelines>,
<https://academic.oup.com/nc/pages/general_instructions>.

## Limits and required items

| Requirement | Limit / rule | Status |
|---|---|---|
| Research Article length | ≤ 9,000 words | 8,578 words of main text by `detex -n` (TikZ excluded, references not followed); 247 abstract, 434 notation table, 275 back matter. Main text plus abstract is 8,825; with notation and back matter 9,534, so confirm with the editorial office whether the notation table counts |
| Abstract | ≤ 250 words | 249 words by `detex -n`, generated macros expanded |
| Significance statement | ~120 words, not published | Draft below |
| Sections | Abstract, Introduction, Methods and Materials, Results, Discussion, Summary or Conclusions | Theoretical article; Conclusions section added. Methods live in the Supplemental Material. **Author to confirm this structure is acceptable, or rename sections.** |
| Data availability | Statement after acknowledgements | Present ("Data and code availability") |
| Funding | Named or "none" | Present |
| CRediT roles | Supplied at submission | Draft below; **author to confirm** |
| ORCID | Required for submitting author | Present on title page |
| Suggested reviewers | At least five, with contact details | **Author to supply** |
| Supplementary material | Submitted with the manuscript; not replaceable after acceptance | `supplementary.pdf` |
| File format | Editable format at initial submission, not PDF (general instructions) | **Submit the LaTeX sources**; the author guidelines also say a PDF is usually reliable, so confirm with the editorial office |

## Significance statement (draft, ~115 words)

Many theories treat synchronized brain rhythms as what makes distributed
activity into one conscious experience. This work shows mathematically that
synchrony is not enough. Brain regions can be perfectly synchronized and still
describe the world inconsistently, and a system can have a stable internal
model of itself while failing to track anything outside it. We separate three
conditions — synchrony, agreement between regions about shared content, and an
accurate internal model of the whole state — and prove which follow from which
using machine-checked proofs. The result turns a general appeal to synchrony
into specific measurements, and proposes a comparison between perceived and
unperceived stimuli, matched for synchrony and for how well each region
encodes the stimulus, that could count against the link between these
conditions and conscious content.

## CRediT contributor roles (draft)

Sebastian Bobadilla-Suarez: Conceptualization; Methodology; Software; Formal
analysis; Investigation; Data curation; Visualization; Writing – original
draft; Writing – review & editing.
