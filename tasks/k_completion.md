# K1–K5 completion — 2026-09-15

## Intent, constraints and success criteria

Complete the installed-energy bridge in `tasks/todo.md`, preserving and reviewing
the two inherited, untracked Lean drafts. Prove the product-integral identity,
the mode-price bound and its one-sided stationary threshold consequence, with
concrete witnesses on the existing microscopic hardware. Keep the conversion
constant positive and determined by hardware, and distinguish installed energy
from heat. The threshold applies to the identified scalar mean-field model;
heterogeneous field dynamics and the cortical identification remain inputs.

No simulations, new references, Python code, dependency changes or R/P research
items are required. Retain regression specifications, run them against the
pre-K import set before integration, then require a warning-free `lake build`
and axiom audit. Align both publication sources, tables and the primer, rebuild
all affected tracked PDFs, refresh any existing arXiv bundle and pass the
applicable repository gates. Commit sources and PDFs together.

## Plan

- [x] K1: run the failing identity regression, then verify Fubini independently.
- [x] K2: check mode factorization, expectation and hardware/sign regressions.
- [x] K3: compose the bound with the stationary threshold and consume it in Chain.
- [x] K4: verify below, at and above the threshold, and rejection witnesses.
- [x] K5: align publication and primer, rebuild artifacts and run gates.
- [x] Record exact results and remaining scope; commit the completed change.

## Execution record

The starting tree contained only two untracked drafts:
`Phase9_InstalledCoupling.lean` and `Examples/InstalledCoupling.lean`. Neither
was imported by the root library or witness index. Their pre-existing code is
reviewed as a draft; regression failures in this pass refer to the pre-K import
set, rather than claiming tests preceded the other agent's drafting.

### Proofs and regressions

- K1's regression failed on the absent declaration under the pre-K imports,
  then passed in an isolated scratch file containing only the identity and its
  integrability helper, before work on K2.
- Eight retained specifications in `Examples/InstalledCoupling.lean` failed
  with 16 missing-declaration errors under the pre-K imports, then passed after
  integration. They check the identity, expected-energy bound, positive
  conversion, stationary-density conclusion, strict low-energy witness and
  converse rejection. The Chain interface regression separately failed on its
  absent declaration, then passed; a concrete low-energy rejection is retained
  in `Chain.lean`.
- The inherited factorization and expected bound checked. The priced structure
  now requires positive conversion, which also derives nonnegative prices and
  expected stored energy; without it two negative factors would satisfy a
  purported positive mode price. The condition checks admissibility, not the
  chronology of choosing a constant, which remains a modelling obligation.
- The inherited low-energy example was exactly at the threshold. It is kept,
  with an additional law at agreement probability 1/4 strictly below it. The
  executed law at 3/4 is above it. The dearer half-filled mode rejects the
  converse. The negative-occupancy witness now has a positive coupled mode and
  a negative zero-response mode: stored energy cancels to zero, mean coupling
  remains 4, and the exclusion itself fails despite valid mode-price bounds.
- K3 now includes the actual positive classical stationary density via
  `stationary_iff_vonMises`, as well as the self-consistency equation and the
  absence of growing uniform-state Fourier modes. Chain consumes K3 to derive
  the necessary energy from E56 and E67 for the same arrangement.

### Publication alignment

The abstract and thermodynamic section state the result together with its
limits: installed energy is not heat, conversion is hardware data, the converse
fails, and neither a cortical identification nor a reduction of heterogeneous
spatial dynamics to the scalar model follows. Table 1 includes the derived
necessary condition without changing the eight edge hypotheses. Table S1 and
the implementation notes identify the new declarations and witnesses. The
primer explains the same bound. The existing microscopic-work explanation is
corrected to the expected stored-energy increase from 1/2 to 3/4, matching its
proved mean work `(1 + log 3) / 4` and heat `(log 3) / 4`.

All added witness numerals are exact analytical examples checked in Lean, not
new simulation results. No simulation artifact, generator, reference or Python
source was added or changed.

### Final validation and deliverables

- `lake build` passes without warnings. The default audit checks 4,635
  declarations across 77 modules; every collected axiom is one of `propext`,
  `Classical.choice` and `Quot.sound`. The explicit headline axiom checks agree.
- All three publication/primer PDFs were rebuilt with two `pdflatex` passes.
  Warning signatures match builds of the pre-change sources: zero overfull
  boxes or LaTeX warnings, with the same 2/1/31 pre-existing underfull boxes
  for main/supplement/primer. The new equations, proof text, table rows and
  primer explanation were checked in rendered output. A long identifier and
  an orphaned supplement heading found in this review were fixed.
- `prepare_arxiv.sh` rebuilds the bundle and compiles its unpacked tarball
  successfully to 76 pages. No submission was made.
- All applicable pre-commit hooks pass: `check-prose`, `check-hedging` (zero
  flagged passages), `check-table`, `check-pdf-freshness` (all three PDFs),
  `check-figures` (seven distinct figures), `check-arxiv-freshness`,
  `check-leaves` and `check-sorry` (79 Lean sources). Python-specific hooks
  correctly skip this change. `git diff --check` passes.
- The inherited draft's unused simp argument and the new Chain proof's `letI`
  style warning were repaired, with no linter suppression. Sources, witnesses,
  records and all three PDFs are included in one completion commit.

### Remaining scope

No K item remains. This is a necessary installed-energy condition for the
declared scalar mean-field model. It neither bounds dissipated heat nor gives
the converse, a hardware calibration, heterogeneous-field dynamics or a
cortical identification. The existing R research items and author/journal P
items remain as recorded, outside this pass.
