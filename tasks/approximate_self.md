# L3 — Approximate self-prediction, 2026-09-14

## Intent, constraints and success criteria

Quantify the distance from an approximately reconstructed state to the exact
fixed point of the same specified encoding/readout map. Preserve all physical
and representational hypotheses. This does not relax overlap compatibility,
choose a cover or content space, construct a readout, or model time-varying
maps. The publication audit is on hold at the user's request.

For a contraction with factor `q < 1`, a residual at most `ε` implies distance
at most `ε / (1 - q)` from a named fixed point. Use Mathlib's existing
`ContractingWith.dist_le_of_fixedPoint`; completeness and nonemptiness remain
the hypotheses of the existing existence theorem, not of an estimate about
an already supplied fixed point.

If a state with residual at most `ε` is displaced by at most `δ`, prove that
its residual is at most `ε + (1 + q) δ` and its distance from the fixed point
is at most that expression divided by `1 - q`. This is an additive error
estimate with amplification by the inverse contraction gap. The ledger's
phrase "rather than amplifying" must not be read as denying that amplification.

Instantiate the rate `q = exp (-(K - 2D) τ / 2)` for `τ > 0`, `K > 2D`.
For `ε ≥ 0`, bound the radius between `2 ε / ((K - 2D) τ)` and that quantity
plus `ε`. These exact inequalities give the leading near-threshold behaviour
and divergence for fixed `ε > 0`, `τ > 0`; zero residual remains zero above
threshold. Divergence of an upper bound does not establish divergence of any
state's actual error.

On the existing three-site cortex, prove that the silent state has residual
one and distance two from the fixed state, saturating the factor-one-half
bound. At factor one, use an identity encoding/readout with whole-space avatar
to exhibit two distinct fixed points on the same metric. It is a counterexample
to nonexpansive uniqueness, not a local-avatar model or a cortical mechanism.

## Plan

1. [x] Run failing Lean specifications for the bounds and witnesses. The scratch
   file `/tmp/l3-spec.lean` failed on the missing declarations before implementation;
   `/tmp/l3-spec-red.log` records the failures, including zero residual.
2. [x] Prove the general bounds, threshold sandwich and positive/negative
   witnesses in the existing Phase 6 and witness modules.
3. [x] Align article, supplement, status table and primer; rebuild the tracked
   PDFs and the arXiv archive, checking changed pages and baseline warnings.
4. [x] Pass the full Lean build and axiom audit, explicit headline axiom checks,
   applicable repository gates and publication regression tests. Mark L3 done
   and record the result, limitations and remaining work in `tasks/todo.md`.

Stop after L3. L4 requires a separate choice of approximate-gluing model.

## Completed result and verification

The five general theorems live in `Phase6_ReflexiveTopology.lean`. The four
witness theorems and `cortexIdentity` live in `Examples/Phase6.lean`, which is
already included by the witness index. No new library module, import,
dependency, Python source, simulation or reference was needed.

The threshold sandwich follows from the elementary exponential tangent
inequality: `x / (1 + x) ≤ 1 - exp(-x) ≤ x` for positive `x`. It establishes
the claimed scaling as an exact inequality; the development adds no separate
filter-limit theorem. The perturbation estimate is conditional on the supplied
distance between global states and cannot repair incompatible local sections.

`lake build` passes with zero warnings. The axiom audit covers 2,585 declarations
in 45 modules, and the nine explicit headline axiom checks report only
`propext`, `Classical.choice` and `Quot.sound`. The same scratch specifications
that failed before implementation now pass, including zero residual, the
composed error, the threshold sandwich, saturation and nonexpansive failure.

The final regression command passes all 39 tests:

```sh
uv run --directory simulations pytest -q -p no:tach \
  test_simulation_tex.py test_check_figures.py \
  test_check_pdf_freshness.py test_check_arxiv_freshness.py
```

An intervening unittest invocation was terminated before completion; the full
pytest rerun above is the final result. All applicable pre-commit hooks pass;
Python-only hooks skip because no Python changed. The working-tree dependency
check confirms every rebuilt PDF is newer than its resolved source set.

Two LaTeX passes build each tracked document. The article, supplement and
primer have 40, 34 and 77 pages, with zero warnings and overfull boxes, matching
the baseline logs saved before editing. Changed prose, equations, witnesses
and status-table rows were visually inspected. `prepare_arxiv.sh` builds a
clean 51-page submission from its unpacked tarball; manifest freshness passes.
`git diff --check` passes. The publication audit remains on hold.
