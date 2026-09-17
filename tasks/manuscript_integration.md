# Manuscript integration rewrite — 2026-09-17

## Intent, constraints and success criteria

The author requested the editorial rewrite proposed after reviewing the recent
formal and numerical additions. Keep coherence, compatibility and
self-representation together as the main argument; present the limits of the
observations before developing the cortical and awakening hypotheses. Reorder
the supplement to give those claims a matching technical reference.

This is a publication edit. Preserve the mathematical results, all eight
connecting hypotheses of each composition, the distinction between installed
energy and heat, the separate state spaces of the witnesses, and the limits of
synthetic validation. Keep the existing references and simulation artifacts;
computed values continue to use generated macros. No new proof, simulation,
dependency or Python implementation is part of this change. Existing unrelated
working-tree changes are outside this pass.

Success means that a reader can follow the three requirements before reaching
the experimental programme, distinguish stationary results from finite-time
observations, and find the assumptions beside the claims they qualify. The
awakening protocol must state the requirements its calibration supports.
Preserve every existing publication citation key, generated result macro and
label across the article and supplement, moving technical detail where needed.
Rebuild affected tracked PDFs and the existing arXiv package, with valid
references, no overfull boxes and passing publication gates.

## Plan

- [x] Rewrite the abstract, introduction and article sequence; integrate the
      numerical findings into the measurement and awakening argument.
- [x] Reorder the supplement, update navigation and incorporate detail moved
      from the article without losing assumptions or results.
- [x] Align the primer's orientation and experimental explanation.
- [x] Review the combined publication against the baseline inventory and
      record any material changes of scope.
- [x] Run the existing publication gates and macro-drift tests, rebuild and
      inspect PDFs, and refresh the assembled arXiv submission.

Editorial validation uses the existing document gates, a before/after inventory
and mathematical review. Tests prescribing prose would duplicate the edit.
The baseline sources, PDFs, logs and inventory are saved in a temporary snapshot;
its location is recorded in `/tmp/manuscript-integration-current`.

## Outcome and validation

The article now develops the three requirements consecutively, then treats
mechanism identification, temporal effects, content decoding and measurement
feasibility before the cortical hypothesis. The abstract, introduction and
discussion state this hierarchy. Supporting thermodynamic models retain the
complete eight-hypothesis table and their distinct resource assumptions.

The supplement begins with the phase theory, installed coupling, content and
reconstruction. Phase controls, recovery, plasticity, compatibility estimation
and EEG methods follow the formal result map. Field calibration and support
comparisons precede the detailed boundary, feedback, learning, supply and
composition models. Moved theorem statements and references use an automatic
counter; Table S1 and the seven unique figures retain their identities.

Three scope clarifications accompany the editorial integration:

- The temporal square-root expression explicitly evaluates the stationary
  branch, `r_ss(K(t))`; applying it to observed recovery requires justified
  tracking and a dynamical onset criterion.
- The failed tracking claim is restricted to the scanned rates, initialization
  and tolerance. Illustrative geometry/phase time-scale ranges are model inputs,
  and fluctuating-coupling findings concern the simulated horizon.
- The protocol uses dependence-aware calibration instead of the inadequate
  100-site minimum. The primer agrees, corrects the delay-exponent reading and
  identifies the stationary-density classification as a Lean theorem.

Validation:

- All 114 existing publication labels, 43 citation keys and 261 used generated
  result macros are retained across the two publication files. No duplicate
  label or new citation key appears. `references.tex`, `simulation_results.tex`
  and `fermi_params.tex` are byte-identical to the baseline. No production sweep
  ran, and no Lean or repository Python implementation changed in this pass.
- All 10 `test_simulation_tex` tests pass, including regeneration drift and
  publication use of the five numerical-extension macro groups.
- Applicable pre-commit hooks pass: prose, advisory hedging (zero flagged
  phrases), Table S1, PDF freshness, figure uniqueness and arXiv freshness.
  Code-only and proof-companion hooks do not apply to these edited files.
- Two LaTeX passes per tracked document produce no LaTeX warnings, unresolved
  references or overfull boxes. Article: 43 pages; supplement: 59; primer: 96.
  Underfull-box counts are 2/2/32, against the snapshot's 3/2/32.
- A separate working-tree check confirms each of the three PDFs is newer than
  all its transitive source dependencies; the pre-commit freshness gate alone
  reads the staged index.
- `prepare_arxiv.sh` rebuilds the submission and compiles the unpacked archive
  successfully to 77 pages. Its source manifest passes the freshness gate.
- Rendered-page review covers the abstract, recovery benchmark, connecting
  hypotheses, supplement navigation and formal table, and the recovery section
  of the assembled arXiv PDF. `git diff --check` passes for this change.

Main source is 6,710 whitespace words including TeX, from 6,874. The rewrite
changes the order and emphasis rather than removing technical coverage.
Baseline files are in `/tmp/manuscript-integration-j279hwb4/`; build and check
logs are `/tmp/manuscript-*.log`. The author approved committing the sources,
rebuilt artifacts and editorial record together on `master`.
